int calculate_output(int a0)
{
    if (a0 == 0)
        return 5;
     
    return a0;
}

int main()
{
    int a0 = 0;
   
    while(1)
    {
        assert(a0 != 5);
        a0 = 5;
    }

    assert(a0 < 5);
}
