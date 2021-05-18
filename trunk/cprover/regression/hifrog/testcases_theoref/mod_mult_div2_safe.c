int main(){
  int a = nondet();
  int b = nondet();
  int c = nondet();

//  if (a <= 0 || a >= 10) return;   //constraint a & b are designed to help bit-blasted verification to run fast. So remove it in order to compete. 
//  if (b <= 0 || b >= 10) return;
 // if (c <= 0 || c >= 10) return;
  if (c==0) return;
  int d = a * b;  // this multiplication could be treated as UF
  int e = d / c;
  int f = d % c;

  assert (d == (e * c) + f);
}
