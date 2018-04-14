int main(){
  int a = nondet();

  if (a < 0) return;

  if (a > 100) return;

  assert (a * a >= 0);
}
