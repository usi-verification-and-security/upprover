short get_nondet_short();

int abs(int x) {
    return x >= 0 ? x : -x;
}

int main() {
    int x = get_nondet_short();
    x = abs(x);
    int y = x + 2;
    assert(y >= 0);
}
