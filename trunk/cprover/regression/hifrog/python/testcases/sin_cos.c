#include <math.h>

double nondet();

double nonlin(double x)
{
    double x_sin = sin(x);
    double x_cos = cos(x);
    return x_sin*x_sin + x_cos*x_cos;
}

void main()
{
    double y = nondet();
    double z = nonlin(y);
    assert(z == 1);
}

