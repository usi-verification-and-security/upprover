unsigned int nondetUInt();

int sum ()
{
    int s=0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    for (int i = 0; i <2; i++)
    {

   	 s=s+n;
    }
    return s;
}

int main()
{
    int a,b,c;

    a=sum();
    assert(a>=0);

    b=sum();
    assert(b>=0);

    c=a+b;
    assert(c>=0);
}

//after bootstraping function sum have two summaries sum0 and sum1, but 
//in upgrade checking only sum0 is used for both function calls. 
//TODO fix this limitation.

