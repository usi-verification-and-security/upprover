int main() {
  float x = nondetFloat();

  __CPROVER_assume(x <= 100.0);
  __CPROVER_assume(x >= -100.0);

  float y = 1.98;
  float z = x*y - y;
  assert(z>3.14);
}
