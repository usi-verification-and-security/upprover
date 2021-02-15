int main()
{
    int i = 0;
    while (i < 1) i++;
    assert(i < 0); //fail
    return 0;
}

