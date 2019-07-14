int u;
int v;

void stub (){
u++;
v++;
//do nothing;
}

int nondet_int();

int main()
{
  u = 0;
  v = 0;

  if (nondet_int()){
    stub();    
    assert (u == 1);
  } else {
    stub();
    assert (v == 1);
  }

  return(0);
}
