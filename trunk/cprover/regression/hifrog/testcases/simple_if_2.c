float nondet();

float inc(float x)
{
    return x + 1;
}

void
main()
{
    float y = nondet();
    if(y >= 0.43)
    {
        int z = inc(y);
        assert(z < 12.4);
    }
}

