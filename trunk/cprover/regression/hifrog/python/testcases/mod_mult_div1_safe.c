int main(){
  int a = nondet();
  int b = nondet();

//  if (a <= 0 || a >= 10) return; //This constrain helped bit-blasted verification to run fast. 
  if (b <= 0 || b >= 10) return;

  int c = a / b;
  int d = a % b;

  assert (a == c * b + d);
}

