int main() {
    int a = nondet();
    int c = nondet();
    if (a <= 0 || a >= 50) return;
    if (c <= 0 || c >= 50) return;
    int d = a % c;
    if (d <= 0) return;
    assert (a % c > 0);
}
