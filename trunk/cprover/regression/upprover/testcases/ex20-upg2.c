unsigned int nondetUInt();

int H(int h){
    return 2 * h;
}
int G(int g){
	return g + 1 ;
}

int F()
{
    int f, s=0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    s = s + n;
    f = G(s);
    return f;
}

int main()
{
    int a;

    a=F();
    
    a = H (a);
    
    assert( a>= 5);

}

