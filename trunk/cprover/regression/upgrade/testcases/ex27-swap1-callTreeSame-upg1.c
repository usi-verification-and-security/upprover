int get_nondet();

//abs
int f(int x) {
    return x >= 0 ? x : -x;
}

int main() {
    int x = get_nondet();
    int y = get_nondet();

    y = f(y);
    x = f(x);
    
    y++;
    assert(y+x >= 0);
}
