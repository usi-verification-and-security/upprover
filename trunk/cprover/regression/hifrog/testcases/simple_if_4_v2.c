float nondet();

float inc(float x)
{
    return x + 1;
}

void
main()
{
    float y = nondet();
    y++;
    if(y >= 0.0 && y < 1.0)
    {
        float z = inc(y);
        assert(z < 12.4);
    }
}

