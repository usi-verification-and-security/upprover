#include <stdlib.h>

int nondet_int();

int get_int (){
  int a = nondet_int();
  __CPROVER_assume(a > 7);
  __CPROVER_assume(a < 10);
  return a;
}


void main(){

  int b = get_int();

  int * arr = malloc (b);


  if (arr == NULL)
	return;


  for (int i = 0; i < b; i++){
    arr[i] = i;
  }

  assert(arr[3] == 3);

}
