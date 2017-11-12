
int nondet_int(); 

int XXX = 0;

int x(int a) {
    return XXX;
}


int main() {
    int i;
    XXX = nondet_int();
    i = XXX;

    assert (i == x(11));
}
