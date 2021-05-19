//This bench taken from :~/hi-bench/challenge-bench/sv-comp17/c/array-industry-pattern/array_range_init_false-unreach-call.c

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
#define SIZE 100    //the actuall size in the original bench was 100000

signed int a[SIZE];

int main()
{
	int i;
	for(i = 0; i < SIZE; i++)
	{
		if(i>=0 && i<=10000)
			a[i] = 10;
		else
		a[i] = 0;
	}


	for(i = 0; i < SIZE; i++)
	{
		__VERIFIER_assert(a[i] == 10);
		
	}

	return 0;
}

