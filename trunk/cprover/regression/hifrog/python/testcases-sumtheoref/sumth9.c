int nondet(){};
int prod(int x , int y) {

	int a = x * y * x;
	int b = y * x * x;
	if (a == b)
		return 2;
	else 
		return 5;
}

int main(){

	int a = nondet();
	int b = nondet();
	int c , d, ret1, ret2;

	ret1 = prod (a , b);
	ret2 = prod (c , d);

	assert (ret1 == ret2);

	assert ( ret1 - ret2 >= 0);
}