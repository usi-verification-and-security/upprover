int calculate_output();

int a0 = 0;

int calculate_output() {
    if (a0 == 0)
        a0 = 5;
    else if (a0 == 5)
        assert(0);
}

int main()
{
    for(int i=0 ; i<3 ; i++)
    {
        calculate_output();

    }
}
