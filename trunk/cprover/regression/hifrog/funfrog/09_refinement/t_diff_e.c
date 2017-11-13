int nondet_int();

int a;
int b;

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

int getchar0() {
  return getchar();
}
int getchar1() {
  return getchar();
}
int getchar2() {
  return getchar();
}
int getchar3() {
  return getchar();
}
int getchar4() {
  return getchar();
}
int getchar5() {
  return getchar();
}
int getchar6() {
  return getchar();
}
int getchar7() {
  return getchar();
}

void do_one(){
  a = getchar0() + 10;
}

void do_two(){
  a = getchar1() + 20;
}

void do_three(){
  a = getchar2() - 60;
  b = 50;
}

void do_foor(){
  a = getchar3() + 30;
}

void do_five(){
  a = getchar4() - 55;
  b = 50;
}

void do_six(){
  a = getchar5() + 5;
}

void do_seven(){
  a = getchar6() - 65;
  b = 50;
}

void do_eight(){
  a = getchar7() - 70;
  b = 50;
}


void main(void){
  b = 0;
  if (getchar() > 50){
    if (getchar() > 50){
      if (getchar() > 50){
        do_one();
      } else {
        do_two();
      }
    } else {
      if (getchar() > 50){
        do_three();
      } else {
        do_foor();
      }
    }
  } else {
    if (getchar() > 50){
      if (getchar() > 50){
        do_five();
      } else {
        do_six();
      }
    } else { 
      if (getchar() > 50){
        do_seven();
      } else {
        do_eight();
      }
    }
  }

  b = b - a;
 // if (a >= 0){
   assert (b > 0 || b < - 5);
 // } else {
  //b = b + 10;
   assert (a >= -10 || b > 10);
 // }
}

