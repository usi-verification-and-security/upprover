/*
 * a1.c
 *
 *  Created on: Sep 9, 2011
 *      Author: amali
 */
#include <stdio.h>
#include <assert.h>

int cat_dog();

int addtwonumbers(int a, int b)
{
	//if(a<0) a=-a;
	//if(b<0) b=-b;

	//if(a<0) a&=0x000FFFFF;
	//if(b<0) b&=0x000FFFFF;

	//if(a<0) a&=0x07FFFFFF;
	//if(b<0) b&=0x07FFFFFF;

	a&=0x000FFFFF;
	b&=0x000FFFFF;

	assert(a >= 0 && b >= 0);

	return a+b;
}

int main(void)
{
	int a, b;
	double c;

	a = cat_dog();//2147483648;
	b = cat_dog();//2147483649;

	c = addtwonumbers(a, b);

	printf("c = %f", c);

	assert(c >= 0);

	return 0;
}
