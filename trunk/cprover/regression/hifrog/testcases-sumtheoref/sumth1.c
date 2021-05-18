    
    int nondet();

    int sub(int y1, int y2){
        return y1-y2;
    }

    int add(int y1, int y2){
        return y1+y2;
    }

    void main()
    {
      int y = nondet();

      unsigned int z = sub(y,y);
      unsigned int x = sub(y,y);
      assert(z == x);  //claim1 verifiable by EUF

      int c = sub(z,x);
      assert(c == 0);  //claim2 verifiable by LRA solver with adjusted adapted EUF sum

      unsigned int zz = add(y,y);
      unsigned int xx = add(y,y);
      assert(zz == xx);  //claim3 verifiable by EUF

      assert (zz+1 > xx);  //claim4 verifiable by LRA
    
  
      int d = sub(zz,xx);  
      assert (d % 2 == 0 ); //claim5 verifiable by Prop only
    } 
