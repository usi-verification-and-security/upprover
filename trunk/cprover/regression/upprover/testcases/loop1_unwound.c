// sum
// file loop.c line 1
signed int sum(signed int w)
{
  return w + 1;
}

// assert
// file loop.c line 15 function main
// signed int assert(void);
// sum
// file loop.c line 1
signed int sum(signed int w);

// main
// file loop.c line 6
signed int main()
{
  signed int a;
  __CPROVER_assume(a > 0);
  __CPROVER_assume(a < 10);
  signed int i=0;
  if(!(i >= 2))
  {
    a=sum(a);
    a = a + 1;
    /* assertion a >= 0 */
    assert(a >= 0);
    i = i + 1;
    if(!(i >= 2))
    {
      a=sum(a);
      a = a + 1;
      /* assertion a >= 0 */
      assert(a >= 0);
      i = i + 1;
      __CPROVER_assume(!(i < 2));
    }

  }
return 0;
}


