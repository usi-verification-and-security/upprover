//just rename

unsigned int non();

int h(int m){
    return 2 * m;
}
int g(int k){
    return k + 3 ;
}

int f ()
{
    int w, s=0;
    
    unsigned n = non();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    s = s + n;
    w = g(s);
    return w;
}

int main()
{
    int a;

    a=f();
    
    a = h (a);
    
    assert( a>= 5);

}

