int calculate_output();

int a0 = 0;

int calculate_output() {
    if (a0 == 0)
        a0 = 1;
    else if (a0 == 1)
        assert(0);
}

int main()
{
    for (int i=0; i < 3; i++)
    {
        while(1)
        {
            calculate_output();
        }
    }
}
