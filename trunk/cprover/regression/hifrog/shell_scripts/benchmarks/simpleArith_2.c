int main() {
  float x = nondetFloat();

  __CPROVER_assume(x <= 100);
  __CPROVER_assume(x >= -100);

  int y = 5;
  int z = x/y - y;
  assert(z>3);
}
