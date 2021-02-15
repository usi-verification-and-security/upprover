int get_nondet();

//abs
int f(int x) {
    return x >= 0 ? x : -x;
}

int main() {
    int x = get_nondet();
    int y = get_nondet();

   assert(x == y); // should fail if nondet is correctly 
   				  //	encoded with 2 different symbols
}