int main() {
  float x = nondetFloat();

  __CPROVER_assume(x <= 1.0);
  __CPROVER_assume(x >= -1.0);

  float y = 1.0021451;
  float z = y - x*x;
  assert(z > 0);
}
