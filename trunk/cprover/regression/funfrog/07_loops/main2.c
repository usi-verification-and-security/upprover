#define BOUND 3

char primes[BOUND*2];
int count = 1;

char is_prime_(char a)
{
  for (char i = 1; i < a; i++){
    for (char j = i; j < a; j++){
      if (a == i*j){
         return 0;
      }
    }
  }
  return 1;
}

void fill_primes(){
  while (count < BOUND*2){
    if (is_prime_ (count)){
      primes [count] = 1;
    } else {
      primes [count] = 0;
    }
    count++;
  }
}

char is_prime(char a)
{
  return primes[a];
}

char goldbach (char a){
  for (char i = 1; i < a; i++){
    for (char j = i; j < a; j++){
      if (a == i+j){
        if (is_prime(i) && is_prime(j)){
          return 1;
        }
      }
    }
  }
  return 0;
}

char nondet_char();

void main(void)
{
  fill_primes();
  assert(count == BOUND*2);

  char rnd = nondet_char();
  __CPROVER_assume(rnd <= BOUND);
  __CPROVER_assume(rnd > 1);

  char even = 2*rnd;
  char test = goldbach(even);
  assert (test == 1);
}
