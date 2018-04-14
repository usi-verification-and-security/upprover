#include <limits.h>

int main(){
  int a = nondet();
  int b = 2*a;

  if (a <= 0 || a >= 100) return;

  assert (b % 2 == 0);
}
