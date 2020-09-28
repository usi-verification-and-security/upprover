int get_random_small() {
    int r;
    __CPROVER_assume(r > -5 && r < 5);
    return r;
}

int f1(int a, int b) {
    if (a >= b) {
        return 2*a;
    }
    return 2*b;
}

int main() {
    int a = get_random_small();
    int b = get_random_small();
    int d = f1(a,b);
    assert(d >= a+b);
}

