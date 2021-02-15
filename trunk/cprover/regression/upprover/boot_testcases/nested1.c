int glob = 0;

void f5 (){
	glob++;
}

int f4 (int n){
	f5();
	if(glob > 0)
		return glob + n -1;
	return n - glob;
}

int f3 (int n){
	return n+1;
}

int f2(int n){
	int m = f3(n);
	return m+1;
}

int f1(int n) {
	int k = f2(n+1);
	return k+1;
}

void main(){
	int x = 1;
	int y = f1(x);
	int z = f4(y);
	assert(y + z >0);
}


		/*
	  main	
	/   |
   f4	f1	
   |	|
   f5	f2	
		|
		f3	
		*/
