int main(){
  int a = nondet();

  if (a <= 0 || a >= 100) return;

  int b = a + 1;

  assert (a % 2 == b % 2);
}
