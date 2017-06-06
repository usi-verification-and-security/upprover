int calculate_output();

int a0 = 0;

int calculate_output() {
    if (a0 == 0)
        a0 = 1;
}

int main()
{
    while(1)
    {
        assert(a0 != 1);
        calculate_output();
    }
}
