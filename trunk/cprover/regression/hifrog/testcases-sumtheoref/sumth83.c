int func(int a, int b) {
    if(a + b > 0){
        return (a + b)/2;
    }
    int m = 1;
    for (int i = 0; i < 10; i++) {
        m += a % b;
    }
    return m;
}

int main() {
    int a = nondet();
    int b = nondet(); 
    __VERIFIER_assume(a > -1000 && a < 1000);
    __VERIFIER_assume(b > -1000 && b < 1000);
    int c = a;
    int d = b;
    int p = func(a, b); 
    int q = func(c, d); 
    assert(p == q);
    assert(2*p == 2*q);
    if(a + b  > 0){
        assert(p == a + b);
    }
    return 0;
}