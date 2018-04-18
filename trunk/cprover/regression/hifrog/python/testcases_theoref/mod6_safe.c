mod_f(int a , int b)
{
 return a % b;
}

int main() {
  int x = nondetInt();
  int y = 3;
  if (x <= 0 || x >= 120) return;
  assert(mod_f(x,y) < 3);
}
