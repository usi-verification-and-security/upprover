int main(){
  int a = nondet();
  int b = nondet();
  int c = nondet();

  if (a < 0 || a > 100) return;
  if (b < 0 || b > 100) return;
  if (c < 0 || c > 100) return;

  assert (a * b * c >= 0);
}

