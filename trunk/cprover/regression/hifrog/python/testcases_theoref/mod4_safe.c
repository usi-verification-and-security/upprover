int main(){
  int a = nondet();
  int b = nondet();

  if (a <= 0 || a >= 100) return;
  if (b <= 0 || b >= 100) return;

  assert (a % b < b);
}

