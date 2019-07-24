unsigned int nondetUInt();

int sum ()
{
    int s=0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    for (int i = 0; i <2; i++)
    {

   	 s = s + n - 18;
    }
    return s;
}

int main()
{
    int a;

    a=sum();
    assert( a >= 0);

}

