unsigned int nondetUInt();

int sum ()
{
    int s=0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    for (int i = 0; i <2; i++)
    {

   	 s=s-100;
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

//sum have two summaries, sum0 (with ID=0) and sum1(with ID=1),
//in upgrade checking both sumaries need to be tried, but both should be invalidated.
//Shall we distinguish which summary belong to exactly which function call?
//is this Ok to do the following, and conjoining both summaries?
// summary(non-det)/\ f_sum_unwind1 /\ f_sum_unwind1 --> sum0 /\ sum1 
