int main() {
  float x = nondetFloat();

  __CPROVER_assume(x <= 100.0);
  __CPROVER_assume(x >= -100.0);

  float y = 1.0;
  float z = x*y;
  float w = x+y;
  assert(z>0.0);
  assert(x>0.0);
}
