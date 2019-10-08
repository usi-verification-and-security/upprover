int get_nondet();

//abs
int f(int x) {
    return x >= 0 ? x : -x;
}

int main() {
    int x = get_nondet();

    __CPROVER_assume(x > -10);
    __CPROVER_assume(x < 50);


    x = f(x);
    x = f(x++);
    
    assert(x >= 0);
}
