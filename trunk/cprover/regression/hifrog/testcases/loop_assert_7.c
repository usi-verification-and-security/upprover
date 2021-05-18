int calculate_output(int a0)
{
    if (a0 == 0)
        return 5;
     
    return a0;
}

int main()
{
    int a0 = 0;
   
    for (int i=0; i < 2; i++)
    {
        a0 = calculate_output(a0);
	assert(a0 != 5);
    }

    assert(a0 != 5);
}
