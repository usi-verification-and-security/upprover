int main(){
  int a = nondet();
  int b = nondet();

 // if (a <= 0 || a >= 1000) return;
  if (b <= 0 || b >= 1000) return;

  assert (a % b < b);
}

