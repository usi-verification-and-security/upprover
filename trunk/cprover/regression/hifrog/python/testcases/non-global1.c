int calculate_output(int a0) {
    if (a0 == 0)
        return 5;
    else if (a0 == 5)
        assert(0);
}

int main()
{
    int a0 = 0;
    while(1) a0 = calculate_output(a0);
}
