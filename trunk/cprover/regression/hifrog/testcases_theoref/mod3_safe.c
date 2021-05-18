#include <limits.h>

int main(){
  int a = nondet();
  int b = nondet();

//  if (a <= 0 || a >= 100) return;
  if (b <= 0 || b >= a) return;

  assert (a % b == (a + b) % b);
}

