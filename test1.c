#include <stdio.h>
int main(int argc, char const *argv[])
{
	int i=0,a,b,c;
	scanf("%d",&a);
	while(i<10)
	{
		b=a+1;
		i=i+b;
		c=i*2;
	}
	return c;
}