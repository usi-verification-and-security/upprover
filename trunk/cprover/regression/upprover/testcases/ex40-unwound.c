#include <assert.h>

// assert
// file ex40-twice-call-loop-orig.c line 28 function main
//signed int assert(void);
// nondetUInt
// file ex40-twice-call-loop-orig.c line 1
unsigned int nondetUInt();
// sum
// file ex40-twice-call-loop-orig.c line 3
signed int sum(signed int w);

// main
// file ex40-twice-call-loop-orig.c line 19
signed int main()
{
  signed int a;
  __CPROVER_assume(a > 0);
  __CPROVER_assume(a < 30);
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

}

// sum
// file ex40-twice-call-loop-orig.c line 3
signed int sum(signed int w)
{
  signed int s=0;
  unsigned int n=nondetUInt();
  __CPROVER_assume(n > 0u);
  __CPROVER_assume(n < 10u);
  signed int i=0;
  if(!(i >= 2))
  {
    s = (signed int)((unsigned int)s + n + (unsigned int)w);
    i = i + 1;
    if(!(i >= 2))
    {
      s = (signed int)((unsigned int)s + n + (unsigned int)w);
      i = i + 1;
      __CPROVER_assume(!(i < 2));
    }

  }

  return s;
}
