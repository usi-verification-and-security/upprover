int myfunc(int a)
{
    a++;
    return a;
}
int main()
{
    int x = 0;
    x = myfunc(x);
    x = myfunc(x);
    x = myfunc(x);
    assert(x >= 3);
    return 0;
}
