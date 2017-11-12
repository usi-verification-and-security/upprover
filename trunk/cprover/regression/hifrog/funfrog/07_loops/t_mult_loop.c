int nondet_int();

int a;
int b;
int c;
int d;


void do_loop_a(){
  for (int i = 1; i <= 10; i++){
    for (int j = 1; j <= 10; j++){
      int y = i * j;
      if (y > 24){
        a++;
      } else {
        a--;
      }
    }
  }
}

void do_loop_b(){
  for (int i = 1; i <= 10; i++){
    for (int j = 1; j <= 10; j++){
      int y = i * j;
      if (y > 24){
        b++;
      } else {
        b--;
      }
    }
  }
}

void do_loop_c(){
  for (int i = 1; i <= 10; i++){
    for (int j = 1; j <= 10; j++){
      int y = i * j;
      if (y > 24){
        c++;
      } else {
        c--;
      }
    }
  }
}

void do_loop_d(){
  for (int i = 1; i <= 10; i++){
    for (int j = 1; j <= 10; j++){
      int y = i * j;
      if (y > 24){
        d++;
      } else {
        d--;
      }
    }
  }
}
void do_if_assert_a (int q){
  if (q >= 0) {
    assert(a < q);
  } else {
    assert(a > q);
  }
}

void do_if_assert_b (int q){
  if (q >= 0) {
    assert(b < q);
  } else {
    assert(b > q);
  }
}

int nondet_int();

void main(void){
  int rnd = nondet_int();
  if (rnd > 0){
	  a = 0;
	  do_loop_a ();
	  do_if_assert_a (0);
	  do_if_assert_a (-5);
	  b = 0;
	  do_loop_b ();
	  do_if_assert_b (10);
	  do_if_assert_b (-15);
  } else {
          b = 0;
	  do_loop_b();
	  do_if_assert_b (0);
	  do_if_assert_b (-5);
	  a = 0;
	  do_loop_a ();
	  do_if_assert_a (10);
	  do_if_assert_a (-15);

  }

  c = 0;
  d = 0;

  int rnd2 = nondet_int();
  if (rnd2 > 0){
    int rnd3 = nondet_int();
    if (rnd3 > 0){
      do_loop_c();
    } else {
      do_loop_d();
    }
  } else {
    int rnd3 = nondet_int();
    if (rnd3 > 0){
      do_loop_d();
    } else {
      do_loop_c();
    }
  }
}

