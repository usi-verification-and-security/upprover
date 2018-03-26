int main(){
  int a = nondet();
  int b = nondet();

  if (a < 0 || a > 100) return;
  if (b < 0 || b > 100) return;

  int c = a * b;
  int d = b * a;

  d++;

  assert (d > c);
}

