int test()
{
  return 1;
}

int test2(int a)
{
  return a;
}


void main(void)
{
  int k1 = 3;
  int k2 = 2;
  int j = test2(k1);
  int i = test2(k2);
  
  assert(i==j);
}
