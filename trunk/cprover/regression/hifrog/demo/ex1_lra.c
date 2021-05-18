unsigned int nondetUInt();

int sum ()
{
    int s=0;
    unsigned n;
    for (int i = 0; i <100; i++)
    {
   	 n = nondetUInt();
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
