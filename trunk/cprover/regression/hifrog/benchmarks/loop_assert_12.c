int a0 = 0;
int calculate_output(_a0)
{
    if (_a0 == 0)
        return 5;

    return _a0;
}

void loop()
{
    while(1)
    {
        assert(a0 != 5);
        a0 = calculate_output(a0);
    }

    assert(a0 < 5);
}

int main()
{
    int a0 = 0;

    loop();

    assert(a0 == 0);
}

