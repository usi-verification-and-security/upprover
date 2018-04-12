int main(){
  int a = nondet();
  int b = nondet();
  int c = nondet();

  if (a <= 0 || a >= 10) return;
  if (b <= 0 || b >= 10) return;
  if (c <= 0 || c >= 10) return;

  int d = a * b;
  int e = d / c;
  int f = d % c;

  assert (d == e * c );
}
