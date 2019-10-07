int get_nondet();

//abs
int f(int x) {
    if (x != 0 ) 
    	return x > 0 ? x : -x;
    else
    	return 0;
}

int main() {
    int x = get_nondet();
    __CPROVER_assume(x>0);
    __CPROVER_assume(x<100);
    int y = 0;
    int a, b;

    a = f(x);
    b = f(y);

    a = (2 * a ) - b;
    assert(a >=0 );
}
