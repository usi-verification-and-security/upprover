int sum1()
{
    return nondet_Int();
}

int main()
{
    int a,b,c;

    a=sum1();
    assert(a>=5);

    b=sum1();
    assert(b>=10);

    c=a+b;
    assert(c>=7);
}
