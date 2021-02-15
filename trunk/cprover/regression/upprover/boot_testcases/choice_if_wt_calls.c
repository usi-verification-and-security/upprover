int nondet_int(); 
int main() {
    int x = nondet_int();
    if (x != -1)    
    	assert (x != -1);
}

