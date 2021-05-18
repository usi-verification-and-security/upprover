int f (int a, int b, int c, int d, int e, int f, 
       int g, int h, int i, int j, int k, int l){
  return a * b * c * d * e * f * g * h * i * j * k * l;
}

int main(){
  int a = nondet();
  int b = nondet();

  if (a < 0 || a > 10) return;
  if (b < 0 || b > 10) return;

  int c = a + 1;
  int d = b;

  int x = f(nondet(), nondet(), nondet(), 
            nondet(), nondet(), nondet(), 
            nondet(), nondet(), nondet(),
            nondet(), nondet(), nondet());

  int y = f(nondet(), nondet(), nondet(), 
            nondet(), nondet(), nondet(), 
            nondet(), nondet(), nondet(),
            nondet(), nondet(), nondet());

  if (x == y) return;

  assert (a + b < c + d); // "--theoref --custom 30,31,32,33,85,86"
}

