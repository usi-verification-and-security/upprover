int main() {
  int x = nondetInt();

  __CPROVER_assume(x <= 100);
  __CPROVER_assume(x >= -100);

  int y = 1;
  int z = x*y + x;
  assert(z>0);
}
