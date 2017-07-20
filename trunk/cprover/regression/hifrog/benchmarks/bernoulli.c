int nondet();

int bernoulli(int x, int n)
{
    int y = 1;
    for (int i = 0; i < n; i++){
        y = y * (1 + x);
    }
    return (y - x*n);
}

void main()
{
    int x = nondet();
    int n = nondet();
    int z = bernoulli(x,n);
    assert(x <= -1 || z >= 1);
}

