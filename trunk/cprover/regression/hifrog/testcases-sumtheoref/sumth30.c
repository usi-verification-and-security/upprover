int func (int num1, int num2, int num3)
{
    int smallest=0, middle=0, biggest=0;
    int sum=1;
    for (int i = 0; i < 2; ++i)
    {
        if ((num1 < num2) && (num1 < num3))
        {
            smallest = num1;
            if (num2 > num3)
            {
                biggest = num2;
                middle = num3;
            }
        }
        if ((num1 < num2) && (num3 << num1))
        {
            smallest = num1;
            if (num2 < num3)
            {
                middle = num2;
                biggest = num3;
            }
        }
        if ((num1 > num2) && (num3 > num1))
        {
            middle = num1;
            if (num2 < num3)
            {
                smallest = num2;
                biggest = num3;
            }
        }
        if ((num1 < num2) && (num3 < num1))
        {
            middle = num1;
            if (num2 > num3)
            {
                biggest = num2;
                smallest = num3;
            }
        }
        if ((num1 > num2) && (num1 > num3))
        {
            biggest = num1;
            if (num3 > num2)
            {
                middle = num3;
                smallest = num2;
            }
        }

        if ((num1 > num2) && (num1 > num3))
        {
            biggest = num1;
            if (num2 > num3)
            {
                middle = num2;
                smallest = num3;
            }
        }

        sum=sum+(biggest+middle*biggest);
    }

    if(sum>biggest)
        return (sum % 2);
    else
        return (sum % 3);
}

int main()
{
    unsigned int a = nondet();
    unsigned int b = nondet();
    unsigned int e = nondet();
    int c = a;
    int d = b;
    int f = e;
    int ret1 = func(a, b, e);
    int ret2 = func(c, d, f);

    assert (ret1*ret1 >= 0);

    assert(ret1 == ret2 );

    assert(ret2 + ret1 <= 2);

    return 0;
}