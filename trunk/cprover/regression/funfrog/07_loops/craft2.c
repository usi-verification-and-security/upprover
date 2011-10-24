#define BOUND 3

char primes[BOUND*2 + 1];

char is_prime(char a)
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

void fill_primes(char bound){
  for (unsigned count = 1; count <= bound; count++){
    char tmp = is_prime (count);
    primes [count] = tmp;
  }
}

char goldbach (char a){
  for (char i = 1; i < a; i++){
    for (char j = i; j < a; j++){
      if (a == i+j){
        if (primes[i] && primes[j]){
          return 1;
        }
      }
    }
  }
  return 0;
}

char is_even (char a){
  for (char i = 1; i < a; i++){
      if (a == i+i){
          return 1;
      }
  }
  return 0;
}


char nondet_char();

char get_even(){
  char rnd = nondet_char();
  __CPROVER_assume (rnd <= BOUND);
  __CPROVER_assume (rnd >= 1);
  char even = rnd + rnd;
  return even;
}

void main(void)
{
  char even = get_even();

  assert(is_even(even));

  fill_primes(even);

  for (unsigned i = 1; i <= even; i++){
    assert(primes[i] == is_prime(i));
  }

  assert(!is_prime(even) || even == 2);

  assert(is_prime(even - 1) || even > 9);

  assert(goldbach(even) == 1);

}
