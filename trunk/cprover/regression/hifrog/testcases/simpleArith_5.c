int main() {
  float x = nondetFloat();

  __CPROVER_assume(x <= 100.0);
  __CPROVER_assume(x >= -100.0);

  float y = 3.5931;
  float z = x/y - y;
  assert(z>0.09945);
}
