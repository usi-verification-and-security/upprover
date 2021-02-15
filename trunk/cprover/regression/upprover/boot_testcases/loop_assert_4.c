int calculate_output();

int a0 = 0;

int calculate_output(int a00) {
    if (a00 == 0)
        a00 = 1;
    else if (a00 == 1)
        assert(0);
}

int main()
{
    while(1)
    {
        a0 = calculate_output(a0);
    }
}
