int max(int a, int b)
{
    if(a > b)
        return a;
    return b;
}
int main()
{
    int a = 0;
    int b = 10;
    int c = max(a + 5,b);
    int d = max(20, c);
    assert(d >= 20);
    return 0;
}
