int f (int a, int b, int c, int d, int e, int f, 
       int g, int h, int i, int j, int k, int l){
  return a * b * c * d * e * f * g * h * i * j * k * l;
}

int main(){
  int x = f(nondet(), nondet(), nondet(), 
            nondet(), nondet(), nondet(), 
            nondet(), nondet(), nondet(),
            nondet(), nondet(), nondet());

  int y = f(nondet(), nondet(), nondet(), 
            nondet(), nondet(), nondet(), 
            nondet(), nondet(), nondet(),
            nondet(), nondet(), nondet());

  if (x <= y) return;
  if (y <= 0) return;
  assert (x / y > 1); 
}

