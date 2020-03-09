unsigned int nondetUInt();

int sum (int w)
{
    int s=0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    for (int i = 0; i <2; i++)
    {

   	 s = s+n+w;
    }
    return s;
}

int main()
{
    int a;
    __CPROVER_assume(a>0);
    // __CPROVER_assume(a<30);
    for (int i = 0; i < 2; ++i)
    {
      a=sum(a);
      a++;
      assert(a>=0);
    }

}
//omega FUNCTIONS size is : 4
//summary for 2 sum#0 and sum#1 
