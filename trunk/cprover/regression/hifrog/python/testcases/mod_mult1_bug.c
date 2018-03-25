int main(){
  int a = nondet();

  if (a <= 0 || a >= 100) return;

  int b = a * (a + 1);

  assert (b % 2 == 1);
}
