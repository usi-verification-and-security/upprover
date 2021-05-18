int test()
{
  return 1;
}

int test2()
{
  return 3;
}


void main(void)
{
  int j = test();
  int i = test2();
  
  assert(j != i);
}
