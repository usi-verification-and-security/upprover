int nondet();

int f (int a ){
  if (a < 30)
    return f (a + 1);
  return a - 10;
}


void main(){

  int y = 0;
  int x = nondet();

  if (x > 0) y = f (x);

/*  assert (x < 95 || y >= 0);
  assert (x < 90 || y >= 0);
  assert (x < 85 || y >= 0);
  assert (x < 80 || y >= 0);
  assert (x < 75 || y >= 0);
  assert (x < 70 || y >= 0);
  assert (x < 65 || y >= 0);
  assert (x < 60 || y >= 0);
  assert (x < 55 || y >= 0);
  assert (x < 50 || y >= 0);
  assert (x < 45 || y >= 0);
  assert (x < 40 || y >= 0);
  assert (x < 35 || y >= 0);
  assert (x < 30 || y >= 0);*/
  assert (x < 25 || y >= 0);
  assert (x < 20 || y >= 0);
  assert (x < 15 || y >= 0);
  assert (x < 10 || y >= 0);
  assert (x < 5 || y >= 0);

  assert (y >= 0);
}

