int nondet_int();

int a;
int b;

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

int d;
int n;
int k;
int u;
int r;

void test0(){
  u = 5;
  for (int i = 0; i < 10; i++){
    int l = 0;
    if (i < u){
      l = l + 1;
    }
    for (int j = 0; j < l; j++){
      u = u + l - j*2;
    }
    if (u > 10){
      u = u - 50;
    }
  }
  d = u - 50;
  for (int i = 0; i < 10; i++){
    k = k*k - 99;
  }
  __CPROVER_assume (d <= 100);
}

void crash(){
  a = -8;
  b = -7;
}

int irrelevant0(int o, int h){
  int y = 5;
  if (o > h){
    y = y + h;
  } else {
    y = y + o - h;
  }
  return 4 - y;
}

void irrelevant1(int r, int p){
  int g = r + p;
  for (int i = 0; i < 5; i++){
    k = k + irrelevant0(g, i);
  }
  if (u > 0){
    n = n + k;
  }
}

int test(int s, int f)
{
  test0();
  k = 6;
  if (s < 10){
     for (int i = 1; i < 10; i++){
        n = s * i;
     }     
  } else {
     for (int i = 1; i < 10; i++){
        n = n * i;
     }
  }

  n =  n - s*a*10;
  int op = 7 + n - f;
  __CPROVER_assume (d <= 0);
  if (d > 5){
    crash();
  } else {
    irrelevant1(d, u);
  }
  a = a + u + 100;
  if (f > 1){
    a = a + 2;
  }
  b = u - b;
  if (op < 2){
    d = d + op;
    return a + b;
  } else {
    b = b - 1;
    return op + b;
  }
}

char triple (int t1, int t2, int t3)
{
  if (t1 + t2 > t3){
     return t2 + t3;
  } else {
    for (int i = 4; i < 7; i++){
      a = a + i;
    }
    if (a < t3 + t1){
      return (b < t2);
    }
  }
  return (t1 == t2 && t2 == t3); 
}

char common0 (int m1, int m2, int m3)
{
  char res = 0;
  for (int i = -5; i < 5; i++){
    if (m1 + i == m2 - i)
    {
      res = 1;
    } else if (m3 == i){
      res = res && (i == 0);
    }
  }
  return res;
}


char common1 (int m1, int m2, int m3)
{
  return (m1 + m3 != m2 - m3);
}


void main1(void)
{
  a = getchar();
  b = getchar();

  int q = getchar();
  int w = getchar();

  if (triple (q, w, 7)){
    a++;
  } else {
    b--;
  }

  if (common1 (a - b, a + b, 0)){
    int j = test(q, w);
    if (j > 0){
      b = irrelevant0(j, a);
      assert(a>4);
    } else {
      assert(b<10);
    }
  }
}

int irrelevant5(int o, int h){
  int y = 5;
  if (o > h){
    y = y + h;
  } else {
    y = y + o - h;
  }
  return 4 - y;
}

int wrfrw (int i, int aee){
  return i*irrelevant5(i, aee);
}

void main(void){
  main1();
  /*int aee=1;
  for (int i = 1; i< 10; i++){
  for (int j = 1; j< 10; j++){
 
    aee = aee + wrfrw(i, aee);
  }
  }*/
}

