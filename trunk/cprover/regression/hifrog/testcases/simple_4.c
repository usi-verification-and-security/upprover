int test()
{
  return 1;
}

int test2(int a)
{
  int j = a;
  return j;
}


void main(void)
{
  int k = 3;
  int j = test2(k);
  k = 3;
  int i = test2(k);
  
  assert(i==j);
}
