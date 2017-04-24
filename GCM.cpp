#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/PredIteratorCache.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include <algorithm>
#include <map>
#include <iterator>

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace{
	struct GCM : public FunctionPass {
		static char ID;
		std::map<BasicBlock*, int> dominatorTreeDepth;
		std::map<Instruction*, bool> visited;
	 	GCM() : FunctionPass(ID) {
	 	//	initializeGCMPass(*PassRegistry::getPassRegistry());
	 	}

	 	void getAnalysisUsage(AnalysisUsage &AU) const override {
	 		AU.addRequired<LoopInfoWrapperPass>();
    		AU.addRequired<DominatorTreeWrapperPass>();
		}

		// Annotates basic blocks with their depths in the dominator tree.
		void annotateBasicBlocks(DomTreeNode *N, DominatorTree *DT, int depth){
			dominatorTreeDepth[N->getBlock()]=depth;
			for (DomTreeNode *Child : N->getChildren())
				annotateBasicBlocks(Child, DT, depth+1);
		}

		// Checks if the instruction "I" is pinned or not.
		bool isPinned(Instruction *I){
			if(isa<PHINode>(I) || isa<TerminatorInst>(I) || isa<ReturnInst>(I) ||
         isa<CallInst>(I) || I->isEHPad() || isa<LandingPadInst>(I) ||
         isa<FuncletPadInst>(I))
				return true;
			else
				return false;
		}

		// Returns the LCA for basic blocks A and B in the dominator tree.
		BasicBlock *findLCA(BasicBlock *a, BasicBlock *b, DominatorTree *DT){
			return DT->findNearestCommonDominator(a, b);
		}

		// Schedules the instruction "I" as late as possible.
		Instruction* scheduleLate(Instruction *I, LoopInfo *LI, DominatorTree *DT){
			if(visited[I])
				return I;
			visited[I]=true;
			BasicBlock *lca = NULL;
			// Iterating over all the uses of "I"
			for (Value::use_iterator i = I->use_begin(), e = I->use_end(); i != e; ++i){
				if(Instruction *UI = dyn_cast<Instruction>(*i)){
					UI = scheduleLate(UI, LI, DT);
					BasicBlock *useBlock = UI->getParent();
					// Checks if the use "UI" of "I" is a phi instruction.
					if (const PHINode *PN = dyn_cast<PHINode>(UI)){
						// Iterating over all the inputs to "UI"
						for (User::op_iterator currentOperand = UI->op_begin(), lastOperand = UI->op_end(); currentOperand != lastOperand; ++currentOperand){
							if (Instruction *inputToUI = dyn_cast<Instruction>(*currentOperand)){
								if(inputToUI == I){
									useBlock = PN->getIncomingBlock(*currentOperand);
									break;
								}
							}
						}
					}
					// Makes sure "lca" is never NULL.
					if(lca!=NULL)
						lca = findLCA(lca, useBlock, DT);
					else
						lca = useBlock;
				}
			}
			BasicBlock *bestBlock = lca;
			BasicBlock *instBlock = I->getParent();

			// Finding the most suitable block in the dominator tree to place instruction "I".
			while(lca != instBlock){
				if((LI->getLoopFor(lca)==NULL && LI->getLoopFor(bestBlock)!=NULL) ||
					(LI->getLoopFor(lca)!=NULL && LI->getLoopFor(bestBlock)!=NULL &&
					LI->getLoopFor(lca)->getLoopDepth() < LI->getLoopFor(bestBlock)->getLoopDepth()))
					bestBlock = lca;
				lca = DT->getNode(lca)->getIDom()->getBlock();
			}

			for (Value::use_iterator i = I->use_begin(), e = I->use_end(); i != e; ++i){
				if(Instruction *UI = dyn_cast<Instruction>(*i)){
					if(!isPinned(I) && UI->getParent()==bestBlock && !isa<PHINode>(*UI)){
						I->moveBefore(UI);
						return I;
					}
				}
			}
			if(!isPinned(I) && bestBlock!=instBlock)
				I->moveBefore(bestBlock->getTerminator());
			//I->moveBefore(bestBlock->getFirstNonPHI());
			return I;
		}

		// Places the instruction "I" in the shallowest basic block possible.
		Instruction* scheduleEarly(Instruction *I, DominatorTree *DT){
			if(visited[I])
				return I;
			visited[I]=true;
			BasicBlock *instBlock = DT->getRootNode()->getBlock();
			// Iterating over all the inputs to "I"
			for (User::op_iterator i = I->op_begin(), e = I->op_end(); i != e; ++i){
				if (Instruction *input = dyn_cast<Instruction>(*i)){
					input = scheduleEarly(input, DT);
					if(dominatorTreeDepth[instBlock] < dominatorTreeDepth[input->getParent()]){
						instBlock = input->getParent();
					}
				}
			}
			if(!isPinned(I) && I->getParent()!=instBlock)
				I->moveBefore(instBlock->getTerminator());
			return I;
		}

	 	bool runOnFunction(Function &F) override {
	 		LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
	 		DominatorTree *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
	 		annotateBasicBlocks(DT->getRootNode(), DT, 0);

	 		for(BasicBlock &BB : F.getBasicBlockList()){
				for(Instruction &I : BB){
					if(isPinned(&I)){
						visited[&I]=true;
						for (User::op_iterator i = I.op_begin(), e = I.op_end(); i != e; ++i){
							if (Instruction *input = dyn_cast<Instruction>(*i)){
								input = scheduleEarly(input, DT);
							}
						}
					}
				}
			}
			visited.clear();
			//errs() << "Scheduled Early\n";

			for(BasicBlock &BB : F.getBasicBlockList()){
				for(Instruction &I : BB){
					if(isPinned(&I)){
						visited[&I]=true;
						for (Value::use_iterator i = I.use_begin(), e = I.use_end(); i != e; ++i){
							if(Instruction *UI = dyn_cast<Instruction>(*i)){
								UI = scheduleLate(UI, &LI, DT);
							}
						}
					}
				}
			}
      		//F.dump();
 			return true;
 		}
 	};
}
char GCM::ID = 'a';

static RegisterPass<GCM> X("gcm", "Global Code Motion",false,false);

/*
 For automatic execution in clang
*/

static void loadPass(const PassManagerBuilder &Builder, legacy::PassManagerBase &PM){
	// While running through 'opt' make sure to first apply the loop simplify transformation.
	// i.e opt -loop-simplify -load <path to GCM.so> -gcm <other flags> <file name>
	PM.add(createLoopSimplifyCFGPass());
 	PM.add(new GCM());
}

static RegisterStandardPasses registerMyGCMInClang(PassManagerBuilder::EP_OptimizerLast, loadPass);
// //static RegisterStandardPasses registerMyGCMInClang(PassManagerBuilder::EP_ModuleOptimizerEarly, loadPass);
static RegisterStandardPasses registerMyGCMInClanginO0(PassManagerBuilder::EP_EnabledOnOptLevel0, loadPass);
