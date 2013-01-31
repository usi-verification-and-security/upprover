int a;
int b;

int stub2(){
a++;

}

int stub(){

b++;
}

int dec(){
  return (a + 1 > 0);
}

void main(){
  a = 0;
  b = 0;

if (!dec()){
  stub();
} else {
  stub2();
}

  assert(a > 0);

}
