int f(int arg) {
    return arg;
}

int v1_in;
int v2_in;
int v1_out;
int v2_out;
int s1_in;
int s2_in;
int s1_out;
int s2_out;


void mix(int t1, int t2, int u1, int u2)
{
    int y1;
    int y2;
    if (u1 == u2) {
        y1 = t1;
        y2 = t2;

        v1_out = f(y1);
        v2_out = f(y2);
    }
    if (t1 == t2) {
        y1 = t1;
        y2 = t2;
        s1_out = f(y1);
        s2_out = f(y2);
    }
}

void main()
{
    int u1;
    int u2;
    int t1;
    int t2;
    int x1;
    int x2;
    int z1;
    int z2;

    u1 = nondet();
    u2 = u1;
    mix(t1, t2, u1, u2);
    z1 = v1_out;
    z2 = v2_out;
    t1 = f(z1);
    t2 = f(z2);
    mix(t1, t2, u1, u2);
    x1 = s1_out;
    x2 = s2_out;
    assert(x1 == x2);
}

