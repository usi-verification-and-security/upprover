
int a, b, c;
int func() {
	c = b;
	if (a > 0)
		a = b;
	int i, m = 0;
	for (i = 0; i < 100; i++)
		m += a*b;
	return m + 1;
}
void main() {
	a=nondet(); b=nondet();
	if (a <= 0) return -1;
	b = func();
	assert(a == c);

    int p = func();
	int q = func();
	assert(p == q);
}

