int f (int a, int b, int c, int d, int e, int f, 
       int g, int h, int i, int j, int k, int l){
  return a * b * c * d * e * f * g * h * i * j * k * l;
}

int main(){
  int x = nondet();
  int y = f(x, x+1, x+2, x+3, x+4, x+5, 
               x+6, x+7, x+8, x+9, x+10, x+11);

  assert (y % 2 == 0); // to refine this statement, run with "--theoref --custom 12,26,27,28"
}

