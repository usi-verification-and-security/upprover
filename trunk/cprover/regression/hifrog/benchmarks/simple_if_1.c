int nondet();

int inc(int x)
{
    return x + 1;
}

void
main()
{
    int y = nondet();
    if(y >= 0 && y < 1)
    {
        int z = inc(y);
        assert(z < 10);
    }
}

