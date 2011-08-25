#include <stdlib.h>

#ifdef _WIN32
#define random() rand()
#endif

#include "ieee_float.h"

#ifndef NAN
#  define PINF (1.0f/0.0f)
#  define NINF (-1.0f/0.0f)
#  define NZERO (-0.0f)
#  define NAN (PINF + NINF)
#else
#  define PINF INFINITY
#  define NINF -INFINITY
#endif

#define PZERO (0.0f)

float random_float()
{
  union
  {
    float f;
    unsigned i;
  } u;


  unsigned r = ((unsigned) random()) % 20;

  switch(r)
  {
    case 0:
      return PINF;
      break;
    case 1:
      return NINF;
      break;
    case 2:
      return NAN;
      break;
    case 3:
      return PZERO;
      break;
    case 4:
      return NZERO;
      break;
    default: 
      u.i=random();
      u.i=(u.i<<16)^random();
      return u.f;
  }

}

bool eq(const ieee_floatt &a, const ieee_floatt &b)
{
  if(a.is_NaN() && b.is_NaN()) return true;
  if(a.is_infinity() && b.is_infinity() && a.get_sign()==b.get_sign()) return true;
  return a==b;
}

typedef enum { PLUS=0, MINUS=1, MULT=2, DIV=3 } binopt;
typedef enum { EQ=0, NEQ=1, LT=2, LE=3, GT=4, GE=5} binrel;
const char *binopsyms[]={ " + ", " - ", " * ", " / " };
const char *binrelsyms[]={ " == ", " != ", " < ", " <= ", " > ", " >= "};

void check_arithmetic(int i)
{
  ieee_floatt i1, i2, i3, res;
  float f1, f2, f3;

  f1=random_float();
  f2=random_float();
  i1.from_float(f1);
  i2.from_float(f2);
  res=i1;
  f3=f1;

  int op=(binopt)i%4;

  switch(op)
  {
    case PLUS:
      f3+=f2;
      res+=i2;
      break;

    case MINUS:
      f3-=f2;
      res-=i2;
      break;

    case MULT:
      f3*=f2;
      res*=i2;
      break;

    case DIV:
      f3/=f2;
      res/=i2;
      break;

    default:assert(0);
  }

  i3.from_float(f3);

  if(!eq(res, i3))
  {
    const char *opsym=binopsyms[op];
    std::cout << i1 << opsym << i2 << " != " << res << std::endl;
    std::cout << f1 << opsym << f2 << " == " << f3 << std::endl;
    std::cout << integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
      integer2binary(i2.get_fraction(), i1.spec.f+1) << " != " <<
      integer2binary(res.get_fraction(), i1.spec.f+1) <<
      " (" << res.get_fraction() << ")" << std::endl;
    std::cout << integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
      integer2binary(i2.get_fraction(), i1.spec.f+1) << " == " <<
      integer2binary(i3.get_fraction(), i1.spec.f+1) <<
      " (" << i3.get_fraction() << ")" << std::endl;
    std::cout << std::endl;
  }
}

void check_comparison(int i)
{
  ieee_floatt i1, i2;
  float f1, f2;

  bool ires, fres;

  f1=random_float();
  f2=random_float();
  i1.from_float(f1);
  i2.from_float(f2);

  int op=(binrel)i%6;
 
  switch(op) 
  {
    case EQ:
      ires = ieee_equal(i1,i2);
      fres = (f1 == f2);
      break;
    case NEQ:
      ires = ieee_not_equal(i1,i2);
      fres = (f1 != f2);
      break;
    case LT:
      ires = (i1 < i2);
      fres = (f1 < f2);
      break;
    case LE:
      ires = (i1 <= i2);
      fres = (f1 <= f2);
      break;
    case GT:
      ires = (i1 > i2);
      fres = (f1 > f2);
      break;
    case GE:
      ires = (i1 >= i2);
      fres = (f1 >= f2);
      break;
    default:
      assert(0);
  }

  if(ires != fres)
  {
    const char *opsym=binrelsyms[op];
    std::cout << i1 << opsym << i2 << " != " << ires << std::endl;
    std::cout << f1 << opsym << f2 << " == " << fres << std::endl;
    std::cout << integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
      integer2binary(i2.get_fraction(), i1.spec.f+1) << " != " << ires;
    std::cout << integer2binary(i1.get_fraction(), i1.spec.f+1) << opsym <<
      integer2binary(i2.get_fraction(), i1.spec.f+1) << " == " << fres;
    std::cout << std::endl;
  }

}

void check_conversion(int i)
{
  union 
  { 
    float f;
    unsigned i;
  } a, b;

  a.f = random_float();

  ieee_floatt t;
  t.from_float(a.f);

  assert(t.is_float());
  b.f = t.to_float();

  if(a.i != b.i && !((a.f != a.f) && (b.f != b.f)))
  {
    std::cout << "conversion failure: " << a.f << " -> " << t << " -> " 
              << b.f << std::endl;
  }
}

int main()
{
  srand(time(0));
  for(unsigned i=0; i<100000000; i++)
  {
    if(i%100000==0) std::cout << "*********** " << i << std::endl;
    check_arithmetic(i);
    check_comparison(i);
    check_conversion(i);
  }
}
