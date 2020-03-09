unsigned int nondetUInt();

int sum (int w)
{
    int s=0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

   	s=s+n+w;
    return s;
}

int main()
{
    int w, a,b;
    __CPROVER_assume(w>0);
    __CPROVER_assume(w<10);

    a=sum(w);
    assert(a >= 0);

    b=sum(w);
    assert(b >= 0);

}

//after bootstraping function sum have two summaries sum0 and sum1, but 
//in upgrade checking only sum0 is used for both function calls. 
//TODO fix this limitation.

