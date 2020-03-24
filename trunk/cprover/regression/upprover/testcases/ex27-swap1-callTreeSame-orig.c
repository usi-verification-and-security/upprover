int get_nondet();

//abs
int f(int x) {
    return x >= 0 ? x : -x;
}

int main() {
    int x = get_nondet();
    int y = get_nondet();

    x = f(x);
    y = f(y);
    y++;
    assert(y+x >= 0);
}
