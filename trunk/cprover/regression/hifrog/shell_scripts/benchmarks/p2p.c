#define DllExport //__declspec( dllexport ) 

//-------------------------------------------------------------------------
#define DEFAULT_SMALL_ACCEL     1  // used instead of zero
#define ZERO_TOLERANCE          1.0e-9  // used to trap very small deltas
#define NUM_JOINTS              1
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
//	Local type definitions
//-------------------------------------------------------------------------
typedef struct
{
    // define profile shape
    int a1;  // acceleration, m/s^2 (or rad/s^2 or deg/s^2)
    int a2;  // deceleration, m/s^2 (positive) (or rad/s^2 or deg/s^2)
    int v;   // constant velocity, m/s (or rad/s or deg/s)
    int t1;  // accleration time (duration), s
    int t2;  // duration of constant velocity, s
    int t3;  // deceleration time (duration), s
    // keep track of initial conditions
    int delta;
    int initPos;
    int initVel;
} jointProfile;
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
//	Global variables declaration
//-------------------------------------------------------------------------
jointProfile	jp[NUM_JOINTS];
static int	currentPosition[NUM_JOINTS];
static int	startTime = 0.0;
static int		initialized = 0;
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
//	Routines declaration
//-------------------------------------------------------------------------
void InitilizeTG();

void InitProfile(int, int, int, int, int, int, int);

int CalculateVpeak(int, int, int, int);

void ExtendProfileTime(int, int);

int SolveVelocity(int, int);
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
//	Main function declaration
//-------------------------------------------------------------------------
void DllExport P2P_Joints_TG(int Sample_Time, int Joints_Limits[4], int XYZRPYin[NUM_JOINTS], int XYZRPYfb[NUM_JOINTS], int XYZRPYout[NUM_JOINTS], int *TrajectoryComplete);
//-------------------------------------------------------------------------
#include <math.h>
#include <stdlib.h>

#include <stdio.h>



int jl[4];
int in[NUM_JOINTS];
int fb[NUM_JOINTS];

int fabs_ (int a){
//assert( a != 0 );

  if (a > 0) {
{     int _ret_14=a;
assert( _ret_14 % a == 0 );
//assert( a <= _ret_14 );
//assert( a % _ret_14 == 0 );
assert( _ret_14 >= 1 );
assert( _ret_14 != 0 );
//assert( a != 0 );

return _ret_14; }
  } else {
{     int _ret_16=-a;
assert( _ret_16 % a == 0 );
//assert( a <= _ret_16 );
//assert( a % _ret_16 == 0 );
assert( _ret_16 >= 1 );
assert( _ret_16 != 0 );
//assert( a != 0 );

return _ret_16; }
  }
}

int sqrt_ (int a){
//assert( a > jp[0].t3 );
//assert( a > jp[0].t1 );
//assert( a > jp[0].delta );
//assert( a > in[0] );
//assert( a > fb[0] );
//assert( a != jp[0].t2 );
//assert( a != jp[0].a2 );
//assert( a != jp[0].a1 );
//assert( a != jl[3] );
//assert( a != jl[2] );
//assert( a != jl[1] );
//assert( a != jl[0] );
//assert( a != 0 );

  if (a <= 0){
{     int _ret_22=0;
//assert( a > jp[0].t3 );
//assert( a != jp[0].t2 );
//assert( a > jp[0].t1 );
//assert( a > jp[0].delta );
//assert( a != jp[0].a2 );
//assert( a != jp[0].a1 );
//assert( a != jl[3] );
//assert( a != jl[2] );
//assert( a != jl[1] );
//assert( a != jl[0] );
//assert( a > in[0] );
//assert( a > fb[0] );
//assert( a != 0 );
//assert( a == _ret_22 );

return _ret_22; }
  }
/*  int b = nondet_int();
  __CPROVER_assume(b * b < a + 1);
  __CPROVER_assume(b * b > a - 1);*/

{   int _ret_28=a; //b;
//assert( a > jp[0].t3 );
//assert( a != jp[0].t2 );
//assert( a > jp[0].t1 );
//assert( a > jp[0].delta );
//assert( a != jp[0].a2 );
//assert( a != jp[0].a1 );
//assert( a != jl[3] );
//assert( a != jl[2] );
//assert( a != jl[1] );
//assert( a != jl[0] );
//assert( a > in[0] );
//assert( a > fb[0] );
//assert( a != 0 );
//assert( a == _ret_28 );

return _ret_28; }
}

void DllExport P2P_Joints_TG(int Sample_Time, int Joints_Limits[4], int XYZRPYin[NUM_JOINTS], int XYZRPYfb[NUM_JOINTS], int XYZRPYout[NUM_JOINTS], int *TrajectoryComplete)
{
	int		i;	
	int	tt2;

	if(initialized == 0)
	{
		InitilizeTG(Joints_Limits, XYZRPYin, XYZRPYfb);
		initialized = 1;
	}
																																										
	// Check none of the inputs have changed
	for(i = 0; i < NUM_JOINTS; i++)
	{
		int	currentInput, oldInput;
		// Get pointer to input vector
		currentInput = XYZRPYin[i];
		oldInput = currentPosition[i];
		if(currentInput != oldInput)
		{
			// input has changed, re-initialise profiles
			InitilizeTG(Joints_Limits, XYZRPYin, XYZRPYfb);
			break;
		}
	}	

	for(i = 0; i < NUM_JOINTS; i++)
	{
		int	elapsed;
		int  x, x0, v, v0;

		if(i == 0)
		{
			startTime = startTime + Sample_Time;
			elapsed = startTime;  // Time since profile started
		}

		// Initialise
		x0 = jp[i].initPos;  // starting position
		v0 = jp[i].initVel;  // initial velocity
    
		// Do calculations based on time position on profile
		if((jp[i].t1 < 0.0) || (jp[i].t2 < 0.0) || (jp[i].t3 < 0.0))
		{
			XYZRPYout[i] = XYZRPYfb[i]; // pos = start pos			
			continue;			
		}
		
		if(elapsed <= jp[i].t1)
		{
			// Const. accel only
			x = x0 + v0 * elapsed + (0.5) * jp[i].a1 * elapsed * elapsed;   // x= vt + (at^2) / 2
			v = v0 + jp[i].a1 * elapsed;     // v = u + at, initial velocity is 4th input
			*TrajectoryComplete = -2.0;
		}
		
		if((elapsed > jp[i].t1) && (elapsed <= (jp[i].t1 + jp[i].t2)))
		{
			// In constant velocity region
			// Work out distance travelled during Const. accel
			x = x0 + v0 * jp[i].t1 + (0.5) * jp[i].a1 * jp[i].t1 * jp[i].t1;
			// Add on distance so far from const. vel
			x = x + (jp[i].v*(elapsed - jp[i].t1));
			v = jp[i].v;
			*TrajectoryComplete = -2.0;
		}
		
		if((elapsed > (jp[i].t1 + jp[i].t2)) && (elapsed <= (jp[i].t1 + jp[i].t2 + jp[i].t3)))
		{
			tt2 = jp[i].t1 + jp[i].t2; // total time to t2
			
			// In constant deceleration region
			// Work out distance travelled during Const. accel
			x = x0 + v0 * jp[i].t1 + (0.5) * jp[i].a1 * jp[i].t1 * jp[i].t1;
			// Add on distance from const. vel            
			x = x + (jp[i].v * jp[i].t2);
			// Add on distance so far from decel.
			x = x + ((jp[i].v * (elapsed - tt2)) - (0.5) * jp[i].a2 * (elapsed - tt2) * (elapsed - tt2));
			// Reduce velocity
			v = jp[i].v - (jp[i].a2 * (elapsed - tt2));
			*TrajectoryComplete = -2.0;
		}
		
		if(elapsed > (jp[i].t1 + jp[i].t2 + jp[i].t3))
		{
			x = XYZRPYin[i]; // end point
			v = 0;
			*TrajectoryComplete = 2.0;
		}
		
		// Output profile
		XYZRPYout[i] = x;		
	}
}


int nondet_int(){
{ 	int _ret_128=rand();
assert( _ret_128 != 0 );

return _ret_128; }
}

void InitilizeTG()
{
//assert( jp[0].t3 >= 0 );
//assert( jp[0].t1 >= 0 );
//assert( jp[0].initVel >= 0 );
//assert( jp[0].initPos >= 0 );
//assert( jl[3] >= 0 );
//assert( jl[2] >= 0 );
//assert( jl[1] >= 0 );
//assert( jl[1] != jp[0].a1 );
//assert( jl[0] >= 0 );
//assert( jl[0] != jp[0].delta );
//assert( in[0] >= 0 );
//assert( in[0] != jp[0].a1 );
//assert( fb[0] >= 0 );
//assert( fb[0] != jp[0].initVel );

	// Create the profiles for each joint
	int		i;
	int	totalTime;
	int	maxTime=0;
    int delta0, delta1, delta2, vMax;

	// Get initialize time
	// (Time zero, subtracted from future sample times to get elapsed time)
	startTime = 0.0;

    vMax = jl[0];

    delta0 = nondet_int();
    delta1 = nondet_int();
    delta2 = nondet_int();

    if(delta0 != 0 && delta1 != 0 && delta2 == 0) vMax = 2 * vMax;
    if(delta0 != 0 && delta1 == 0 && delta2 != 0) vMax = 2 * vMax;
    if(delta0 == 0 && delta1 != 0 && delta2 != 0) vMax = 2 * vMax;

    if(delta0 != 0 && delta1 == 0 && delta2 == 0) vMax = 3 * vMax;
    if(delta0 == 0 && delta1 == 0 && delta2 != 0) vMax = 3 * vMax;
    if(delta0 == 0 && delta1 != 0 && delta2 == 0) vMax = 3 * vMax;
    

	for(i = 0; i < NUM_JOINTS; i++)
	{
		currentPosition[i] = in[i];

		InitProfile(i, fb[i],	// start
					in[i],		// end

					jl[0],		// max vel


					jl[1],		// initial vel
					jl[2],		// acceleration
					jl[3]		// deceleration
					);

		
		totalTime = jp[i].t1 + jp[i].t2 + jp[i].t3;
		
		if(totalTime > maxTime) maxTime = totalTime;
	}

	//Profile Extension	
	for(i = 0; i < NUM_JOINTS; i++)
	{		
		if((jp[i].t1 + jp[i].t2 + jp[i].t3) < maxTime)
		{				
				ExtendProfileTime(i, maxTime);
		}
	}// end for - profile extension
assert( totalTime != vMax );
assert( maxTime != vMax );
assert( maxTime >= totalTime );
//assert( jp[0].v <= vMax );
//assert( jp[0].v != totalTime );
//assert( jp[0].v != maxTime );
//assert( jp[0].t3 <= vMax );
//assert( jp[0].t2 <= maxTime );
//assert( jp[0].t2 != jp[0].v );
//assert( jp[0].a2 != totalTime );
//assert( jp[0].a2 != maxTime );
//assert( jp[0].a2 != jp[0].t1 );
//assert( jp[0].a1 != totalTime );
//assert( jp[0].a1 != maxTime );
//assert( jp[0].a1 != jp[0].t3 );
//assert( jp[0].a1 != jp[0].t2 );
//assert( jp[0].a1 != jp[0].t1 );
//assert( jl[3] != jp[0].t2 );
//assert( jl[3] >= jp[0].a2 );
//assert( jl[3] % jp[0].a2 == 0 );
//assert( jl[2] != totalTime );
//assert( jl[2] != maxTime );
//assert( jl[1] != jp[0].delta );
//assert( in[0] >= jp[0].delta );
//assert( fb[0] != jp[0].a1 );
assert( delta2 > vMax );
assert( delta2 > totalTime );
assert( delta2 > maxTime );
assert( delta2 > jp[0].v );
assert( delta2 > jp[0].t3 );
assert( delta2 > jp[0].t2 );
assert( delta2 > jp[0].t1 );
assert( delta2 > jp[0].delta );
assert( delta2 > jp[0].a2 );
assert( delta2 > jp[0].a1 );
assert( delta2 > jl[3] );
assert( delta2 > jl[2] );
assert( delta2 > jl[1] );
assert( delta2 > in[0] );
assert( delta2 > i );
assert( delta2 > fb[0] );
assert( delta1 > vMax );
assert( delta1 > totalTime );
assert( delta1 > maxTime );
assert( delta1 > jp[0].v );
assert( delta1 > jp[0].t3 );
assert( delta1 > jp[0].t2 );
assert( delta1 > jp[0].t1 );
assert( delta1 > jp[0].delta );
assert( delta1 > jp[0].a2 );
assert( delta1 > jp[0].a1 );
assert( delta1 > jl[3] );
assert( delta1 > jl[2] );
assert( delta1 > jl[1] );
assert( delta1 > in[0] );
assert( delta1 > i );
assert( delta1 > fb[0] );
assert( delta1 != delta2 );
assert( delta0 > vMax );
assert( delta0 > totalTime );
assert( delta0 > maxTime );
assert( delta0 > jp[0].v );
assert( delta0 > jp[0].t3 );
assert( delta0 > jp[0].t2 );
assert( delta0 > jp[0].t1 );
assert( delta0 > jp[0].delta );
assert( delta0 > jp[0].a2 );
assert( delta0 > jp[0].a1 );
assert( delta0 > jl[3] );
assert( delta0 > jl[2] );
assert( delta0 > jl[1] );
assert( delta0 > in[0] );
assert( delta0 > i );
assert( delta0 > fb[0] );
assert( delta0 != delta2 );
assert( delta0 != delta1 );
assert( vMax >= 0 );
assert( maxTime >= 0 );
//assert( jp[0].t3 >= 0 );
//assert( jp[0].t1 >= 0 );
//assert( jp[0].a2 != 0 );
//assert( jp[0].a1 != 0 );
//assert( jl[3] >= 0 );
//assert( jl[2] >= 0 );
//assert( jl[1] >= 0 );
//assert( in[0] >= 0 );
assert( i == 1 );
//assert( fb[0] >= 0 );
assert( delta2 != 0 );
assert( delta1 != 0 );
assert( delta0 != 0 );
//assert( jl[1] == jp[0].initVel );
//assert( jl[0] == vMax );
//assert( fb[0] == jp[0].initPos );

}

int main() {
    int i;

    int j;
//    for( j = 0;j < 1000; j++){ 
	printf("%d\n",j);
    //int res = 1;
	for(i = 0; i < 4; i++)
	{
         jl[i] = rand();
         //res = res && (jl[i] > 0);
         jl[i] &= 0x000000FF;
         //__CPROVER_assume(jl[i] > 0);
    }

    for(i = 0; i < NUM_JOINTS; i++)
	{
        in[i] = nondet_int();
        fb[i] = nondet_int();
        in[i] &= 0x0000000F;
        fb[i] &= 0x0000000F;
    }
    //if (res){
      InitilizeTG();
    //}
//}
{     int _ret_215=0;
assert( _ret_215 == 0 );
//assert( jl[3] == 41 );
//assert( jl[2] == 237 );
//assert( jl[1] == 184 );
//assert( jl[0] == 250 );
assert( j == -1073745392 );
//assert( in[0] == 8 );
assert( i == -1 );
//assert( fb[0] == 13 );
//assert( jl[1] == jp[0].initVel );
//assert( fb[0] == jp[0].initPos );

return _ret_215; }
}

void InitProfile(int i, int start, int end, int vMax, int v0, int aMax, int dMax)
{
assert( vMax >= 0 );
assert( v0 >= 0 );
assert( start >= 0 );
//assert( jp[0].t3 >= 0 );
//assert( jp[0].t1 >= 0 );
//assert( jp[0].initVel >= 0 );
//assert( jp[0].initVel != start );
//assert( jp[0].initPos >= 0 );
//assert( jp[0].delta != vMax );
//assert( jp[0].a1 != v0 );
//assert( jl[1] == v0 );
//assert( jl[0] == vMax );
assert( i == 0 );
assert( i <= vMax );
assert( i <= v0 );
assert( i <= start );
assert( i <= jp[0].t3 );
assert( i <= jp[0].t1 );
assert( i <= jp[0].initVel );
assert( i <= jp[0].initPos );
//assert( fb[0] == start );
assert( end >= i );
assert( end >= 0 );
assert( end == in[0] );
assert( end != jp[0].a1 );
assert( dMax >= i );
assert( dMax >= 0 );
assert( dMax == jl[3] );
//assert( aMax >= i );
//assert( aMax >= 0 );
//assert( aMax == jl[2] );

	// DESCRIPTION
	// -----------
	// Fill in the jointProfile structure with values that meet the criteria
	// Basically means working out the 3 times - acceleration (t1)
	//                                         - constant vel (t2)
	//                                         - deceleration (t3)
	//
	////////////////////////////////////////////////////////////////////////////

	int	delta, x1, x2, x3;          // position variables
	int	tVmax, tVpeak;              // time variables
	int	a1, d1;                     // acceleration variables
	int	vPeak;
	int	v0c;                        // v0 checked


	// Save initial inputs
	jp[i].delta   = end - start;
	jp[i].initPos = start;
	jp[i].initVel = v0;

	// Building profile, approach used is to calculate corner times
	// In other words accelerate & decelerate at maximums

	// Step 0: Input checking
	a1 = (aMax==0) ? DEFAULT_SMALL_ACCEL : aMax;
	d1 = (dMax==0) ? DEFAULT_SMALL_ACCEL : dMax;

	// Step 1: Calculate position delta desired
	delta = end - start;
	
	if(delta < 0)
	{
		// Compute with +ve delta
		delta = fabs_(delta);
		// Take v0 into account
		v0c = -v0;
	}
	
	else
	{
		v0c = v0;
	}
	
	// Step 2: Acceleration time
	// Choose minimum time from time when v=vMax or it's time to start decelerating.
	// The latter time is determined by when we reach the peak velocity necessary
	// for this delta.
	vPeak = CalculateVpeak(delta, v0c, aMax, dMax);
        if (a1 == 0){
		tVmax = (vMax - v0c) * 1000;
		tVpeak = (vPeak - v0c) * 1000;
        } else {
		tVmax = (vMax - v0c) / a1;
		tVpeak = (vPeak - v0c) / a1;
	}
	if(tVpeak < tVmax) // choose minimum time and corresponding velocity
	{
		jp[i].t1 = tVpeak;
		jp[i].v = vPeak;
	}
	
	else
	{
		jp[i].t1 = tVmax;
		jp[i].v = vMax;
	}
	
	// NOTE: t1 will be < 0 if v0c > vMax
	if(v0c > vMax)  // Case 3
	{
		jp[i].t1 = -tVmax;
		jp[i].v = vMax;
		a1 = -fabs_(d1);         // We actually need to decelerate first
		// Note: could use -a1 but to be consistent with case 5, use -d1 instead.
		// It is assumed that |a1| > |d1|, so above is not optimal time choice	
	}
	
	if(v0c > vPeak) // Case 5.  vPeak is velocity it's possible to decelerate from without exceeding delta.
	{
		// Actually need to decelerate below zero, then accelerate
		a1 = -fabs_(d1); // Using d1 for magnitude of a1 to prevent possibility of imaginary result
		d1 = -fabs_(d1); // both acclerations now opposite of 'normal'
		vPeak = -CalculateVpeak(delta, v0c, a1, d1); // -ve root
		
		if(fabs_(vPeak) > vMax) vPeak = -fabs_(vMax);    // clip velocity if required
		
		tVpeak = (vPeak - v0c) / a1;
		jp[i].t1 = tVpeak;
		jp[i].v = vPeak;
	}
	
	// Step 3: Deceleration time
	// Calculate time to decelerate from velocity achieved in step 2 to 0.
	if (d1 == 0){
		jp[i].t3 = jp[i].v * 1000;
	} else {
		jp[i].t3 = jp[i].v / d1;            // either d1 > 0, or both v & d1 < 0
	}

  // Step 4: Contant velocity time
	// Calculate distances travelled in Steps 1 & 2, subtract from delta, coast for time
	// required to cover this distance
	x1 = v0c * (jp[i].t1) + ( (a1) * (jp[i].t1) * (jp[i].t1) ) / 2;
	x3 = ((d1)*(jp[i].t3)*(jp[i].t3)/2);
	x2 = delta - (x1 + x3);
	
	//if (fabs_(x2) < ZERO_TOLERANCE) x2 = 0;
        if (jp[i].v == 0){
		jp[i].t2 = x2 * 1000;
	} else {
		jp[i].t2 = (x2 / jp[i].v);               // may be very big              // v > 0
	}
	jp[i].a1 = a1;
	jp[i].a2 = d1;
	
	if((end - start) < 0)
	{
		jp[i].a1 = -jp[i].a1;
		jp[i].a2 = -jp[i].a2;
		jp[i].v  = -jp[i].v;
	}  
//assert( dMax == jl[3] );
////assert( aMax == jl[2] );

}

void ExtendProfileTime(int i, int totalTime)
{
//assert( jp[0].t3 == 0 || jp[0].t3 == 1 || jp[0].t3 == 14 );
//assert( jp[0].t3 % jp[0].t1 == 0 );
//assert( jp[0].t2 < jp[0].t3 );
//assert( jp[0].t2 != 0 );
//assert( jp[0].t1 > jp[0].t2 );
//assert( jp[0].t1 == 1 || jp[0].t1 == 2 || jp[0].t1 == 3 || jp[0].t1 == 9 );
//assert( jp[0].t1 != 0 );
//assert( jp[0].delta >= 0 );
//assert( jp[0].delta > jp[0].t2 );
//assert( jp[0].a1 <= -1 );
//assert( jp[0].a1 < jp[0].t3 );
//assert( jp[0].a1 < jp[0].t1 );
//assert( jp[0].a1 < jp[0].delta );
//assert( jp[0].a1 % jl[3] == 0 );
//assert( jp[0].a1 != jp[0].t2 );
//assert( jp[0].a1 != 0 );
//assert( jl[3] >= jp[0].t1 );
//assert( jl[3] > jp[0].t2 );
//assert( jl[3] > jp[0].a1 );
//assert( jl[3] == jp[0].a2 );
//assert( jl[3] % jp[0].a1 == 0 );
//assert( jl[3] != jp[0].t3 );
//assert( jl[2] > jp[0].t3 );
//assert( jl[2] > jp[0].t2 );
//assert( jl[2] > jp[0].t1 );
//assert( jl[2] > jp[0].delta );
//assert( jl[2] > jp[0].a1 );
//assert( jl[1] > jp[0].t3 );
//assert( jl[1] > jp[0].t2 );
//assert( jl[1] > jp[0].t1 );
//assert( jl[1] > jp[0].delta );
//assert( jl[1] > jp[0].a1 );
//assert( jl[1] == jp[0].initVel );
//assert( jl[0] >= jp[0].t3 );
//assert( jl[0] > jp[0].t2 );
//assert( jl[0] > jp[0].a1 );
//assert( jl[0] == jp[0].v );
//assert( in[0] >= jp[0].t1 );
//assert( in[0] >= jp[0].delta );
//assert( in[0] > jp[0].t2 );
//assert( in[0] > jp[0].a1 );
//assert( in[0] != jp[0].t3 );
assert( i > jp[0].t2 );
assert( i > jp[0].a1 );
assert( i == totalTime );
assert( i == 0 );
assert( i <= jp[0].t3 );
assert( i <= jp[0].delta );
assert( i < jp[0].t1 );
assert( i < jl[3] );
assert( i < jl[2] );
assert( i < jl[1] );
assert( i < jl[0] );
assert( i < in[0] );
//assert( fb[0] >= i );
//assert( fb[0] > jp[0].t2 );
//assert( fb[0] > jp[0].a1 );
//assert( fb[0] == jp[0].initPos );
//assert( fb[0] != jp[0].delta );

	int newV;
	
	newV = SolveVelocity(i, totalTime);
	
	// Check to see if we now need to decelerate, where we didn't before
	// (New v is < V0, old v wasn't)
	if((newV < jp[i].initVel) && (jp[i].v >= jp[i].initVel))
	{
		jp[i].a1 *= - fabs_(jp[i].a2);
		newV = SolveVelocity(i, totalTime);    // Resolve velocity now that initial acceleration has changed
	}

	jp[i].t1 = (newV - jp[i].initVel) / jp[i].a1;
	
	if (jp[i].t1 < 0)
	{
		jp[i].a1 *= -1;
		jp[i].t1 *= -1;
	}

	jp[i].t3 = newV / jp[i].a2;
	
	if (jp[i].t3 < 0)
	{
		jp[i].a2 *= -1;
		jp[i].t3 *= -1;
	}

	jp[i].t2 = totalTime - jp[i].t1 - jp[i].t3;
	jp[i].v  = newV;
//assert( jp[0].t3 <= newV );
//assert( jp[0].t2 < newV );
//assert( jp[0].t2 <= jp[0].t3 );
//assert( jp[0].t1 != newV );
//assert( jp[0].t1 >= jp[0].t3 );
//assert( jp[0].t1 >= jp[0].t2 );
//assert( jp[0].delta >= jp[0].t2 );
//assert( jp[0].a1 < newV );
//assert( jp[0].a1 < jp[0].t3 );
//assert( jp[0].a1 != jp[0].t2 );
//assert( jp[0].a1 < jp[0].t1 );
//assert( jp[0].a1 < jp[0].delta );
//assert( jl[3] != newV );
//assert( jl[3] != jp[0].t3 );
//assert( jl[3] > jp[0].t2 );
//assert( jl[3] != jp[0].t1 );
//assert( jp[0].a1 % jl[3] == 0 );
//assert( jl[3] > jp[0].a1 );
//assert( jl[3] % jp[0].a1 == 0 );
//assert( jl[2] > newV );
//assert( jl[2] > jp[0].t3 );
//assert( jl[2] > jp[0].t2 );
//assert( jl[2] != jp[0].t1 );
//assert( jl[2] > jp[0].delta );
//assert( jl[2] > jp[0].a1 );
//assert( jl[1] > newV );
//assert( jl[1] > jp[0].t3 );
//assert( jl[1] > jp[0].t2 );
//assert( jl[1] > jp[0].t1 );
//assert( jl[1] > jp[0].delta );
//assert( jl[1] > jp[0].a1 );
//assert( in[0] != newV );
//assert( in[0] != jp[0].t3 );
//assert( in[0] > jp[0].t2 );
//assert( in[0] >= jp[0].delta );
//assert( in[0] > jp[0].a1 );
assert( i < newV );
assert( i <= jp[0].t3 );
assert( i >= jp[0].t2 );
assert( i <= jp[0].t1 );
assert( i <= jp[0].delta );
assert( i > jp[0].a1 );
assert( i < jl[3] );
assert( i < jl[2] );
assert( i < jl[1] );
assert( i < in[0] );
//assert( fb[0] >= jp[0].t2 );
//assert( fb[0] != jp[0].delta );
//assert( fb[0] > jp[0].a1 );
//assert( fb[0] >= i );
assert( newV >= 1 );
assert( newV != 0 );
//assert( jp[0].t3 == 0 || jp[0].t3 == 1 || jp[0].t3 == 14 );
//assert( jp[0].t2 <= 0 );
//assert( jp[0].t1 >= 0 );
//assert( jp[0].delta >= 0 );
//assert( jp[0].a1 <= -1 );
//assert( jp[0].a1 != 0 );
assert( i == 0 );
//assert( jp[0].v == newV );
//assert( jl[3] == jp[0].a2 );
//assert( jl[1] == jp[0].initVel );
//assert( jl[0] == newV );
assert( i == totalTime );
//assert( fb[0] == jp[0].initPos );

}

int CalculateVpeak(int x, int v0, int a, int d)
{
assert( x >= 0 );
assert( v0 != x );
//assert( jp[0].delta <= x );
//assert( jp[0].delta != v0 );
//assert( jp[0].a1 != x );
//assert( jp[0].a1 != v0 );
//assert( jl[1] >= v0 );
//assert( jl[1] != x );
//assert( in[0] >= jp[0].delta );
//assert( in[0] >= 0 );
//assert( in[0] != jp[0].a1 );
assert( d <= jl[3] );
//assert( a <= jl[2] );

	///////////////////////////////////////////////////////////////////////////////////////////
	// DESCRIPTION:
	// ------------
	// Calculate the velocity required to arrive at position x in minimum time.
	// Do the calculations as if x is always +ve, invert velocities & accelerations
	// if x is actually -ve.
	// Eqn for position is: x = v0t1 + (at1^2)/2 + (dt3^2)/2
	// where t1 is the acceleration time and t3 is the deceleration time.
	// V0 can be either +ve or -ve.
	// Vp is the theoretical peak velocity that would be achieved if there was no
	// period of constant velocity (ie. constant acceleration followed immediately
	// by contant deceleration).
	// Some identities: a = (Vp - V0)/t1
	//                  d = Vp/t3
	// therefore:       t1 = (Vp - V0)/a
	// and              t3 = Vp /d
	// substituing these into the position equation, gives a quadratic in the form ax^2 + bx + c = 0
	// The roots of a quadratic are x = (-b +- sqrt_(b^2 - 4ac)) / 2a
	// We can use this to solve for Vp in terms of a, d, V0 and x
	// the 2 roots are: Vp = (+1) sqrt_[ (2d(V0^2 + 2ax)) / (d + a) ]
	// and              Vp = (-1) sqrt_[ (2d(V0^2 + 2ax)) / (d + a) ]
	//
	// The followint ACII art shows x as the area under the velocity curve specified by V0, Vp, a and d:
	// 
	//    |
	//    |
	// Vp +     ^
	//    |    / \
	//    | a /   \ d
	//    |  /     \
	//    | /       \
	// V0 +/         \
	//    |     x     \
	//    |            \
	//    |             \
	//  --|-----+--------+---
	//    |  t1 |   t3   |
	//
	///////////////////////////////////////////////////////////////////////////////////////////
	// Code & comments start
	
	int num, den, result;
	
	num = d * (v0 * v0 + 2.0 * a * x);
	den = d + a; // should both be +ve   

	// Error checking
	if(den == 0)
{ 		int _ret_428=0.0;
assert( v0 != x );
assert( result != x );
assert( result != v0 );
assert( num != x );
assert( num != v0 );
//assert( jp[0].v != num );
//assert( jp[0].delta <= x );
//assert( jp[0].delta != v0 );
//assert( jp[0].delta != result );
//assert( jp[0].delta != num );
//assert( jp[0].a2 != result );
//assert( jp[0].a2 != num );
//assert( jp[0].a1 != x );
//assert( jp[0].a1 != v0 );
//assert( jp[0].a1 != result );
//assert( jp[0].a1 != num );
//assert( jl[2] != result );
//assert( jl[2] != num );
//assert( jl[1] != x );
//assert( jl[1] >= v0 );
//assert( jl[1] != result );
//assert( jl[1] != num );
//assert( jl[0] != result );
//assert( jl[0] != num );
//assert( in[0] >= jp[0].delta );
//assert( in[0] != jp[0].a1 );
//assert( fb[0] != result );
//assert( fb[0] != num );
assert( den != x );
assert( den != num );
assert( den != jp[0].t2 );
assert( den != jp[0].t1 );
assert( den != jp[0].delta );
assert( den != jp[0].a1 );
assert( den != in[0] );
assert( d <= jl[3] );
//assert( a != result );
//assert( a != num );
//assert( a <= jl[2] );
assert( x >= 0 );
assert( result >= 0 );
//assert( in[0] >= 0 );
assert( den != 0 );
assert( result == _ret_428 );

return _ret_428; }
	
	result = num /den;
	
	if(result <= 0)
	{
		// Other reason it could occur is if a < d < 0 and v0^2+2ax < 0
{ 		int _ret_435=0.0;
assert( v0 != x );
assert( result != x );
assert( result != v0 );
assert( num != x );
assert( num != v0 );
//assert( jp[0].v != num );
//assert( jp[0].delta <= x );
//assert( jp[0].delta != v0 );
//assert( jp[0].delta != result );
//assert( jp[0].delta != num );
//assert( jp[0].a2 != result );
//assert( jp[0].a2 != num );
//assert( jp[0].a1 != x );
//assert( jp[0].a1 != v0 );
//assert( jp[0].a1 != result );
//assert( jp[0].a1 != num );
//assert( jl[2] != result );
//assert( jl[2] != num );
//assert( jl[1] != x );
//assert( jl[1] >= v0 );
//assert( jl[1] != result );
//assert( jl[1] != num );
//assert( jl[0] != result );
//assert( jl[0] != num );
//assert( in[0] >= jp[0].delta );
//assert( in[0] != jp[0].a1 );
//assert( fb[0] != result );
//assert( fb[0] != num );
assert( den != x );
assert( den != num );
assert( den != jp[0].t2 );
assert( den != jp[0].t1 );
assert( den != jp[0].delta );
assert( den != jp[0].a1 );
assert( den != in[0] );
assert( d <= jl[3] );
//assert( a != result );
//assert( a != num );
//assert( a <= jl[2] );
assert( x >= 0 );
assert( result >= 0 );
//assert( in[0] >= 0 );
assert( den != 0 );
assert( result == _ret_435 );

return _ret_435; }
	}
	
{ 	int _ret_438=sqrt_(result); // Use +ve root
assert( v0 != x );
assert( result != x );
assert( result != v0 );
assert( num != x );
assert( num != v0 );
//assert( jp[0].v != num );
//assert( jp[0].delta <= x );
//assert( jp[0].delta != v0 );
//assert( jp[0].delta != result );
//assert( jp[0].delta != num );
//assert( jp[0].a2 != result );
//assert( jp[0].a2 != num );
//assert( jp[0].a1 != x );
//assert( jp[0].a1 != v0 );
//assert( jp[0].a1 != result );
//assert( jp[0].a1 != num );
//assert( jl[2] != result );
//assert( jl[2] != num );
//assert( jl[1] != x );
//assert( jl[1] >= v0 );
//assert( jl[1] != result );
//assert( jl[1] != num );
//assert( jl[0] != result );
//assert( jl[0] != num );
//assert( in[0] >= jp[0].delta );
//assert( in[0] != jp[0].a1 );
//assert( fb[0] != result );
//assert( fb[0] != num );
assert( den != x );
assert( den != num );
assert( den != jp[0].t2 );
assert( den != jp[0].t1 );
assert( den != jp[0].delta );
assert( den != jp[0].a1 );
assert( den != in[0] );
assert( d <= jl[3] );
//assert( a != result );
//assert( a != num );
//assert( a <= jl[2] );
assert( x >= 0 );
assert( result >= 0 );
//assert( in[0] >= 0 );
assert( den != 0 );
assert( result == _ret_438 );

return _ret_438; }
}

int SolveVelocity(int i, int totalTime)
{
//assert( jp[0].t3 == 0 || jp[0].t3 == 1 || jp[0].t3 == 14 );
//assert( jp[0].t3 % jp[0].t1 == 0 );
//assert( jp[0].t2 < jp[0].t3 );
//assert( jp[0].t2 != 0 );
//assert( jp[0].t1 > jp[0].t2 );
//assert( jp[0].t1 == 1 || jp[0].t1 == 2 || jp[0].t1 == 3 || jp[0].t1 == 9 );
//assert( jp[0].t1 != 0 );
//assert( jp[0].delta >= 0 );
//assert( jp[0].delta > jp[0].t2 );
//assert( jp[0].a1 <= -1 );
//assert( jp[0].a1 < jp[0].t3 );
//assert( jp[0].a1 < jp[0].t1 );
//assert( jp[0].a1 < jp[0].delta );
//assert( jp[0].a1 % jl[3] == 0 );
//assert( jp[0].a1 != jp[0].t2 );
//assert( jp[0].a1 != 0 );
//assert( jl[3] >= jp[0].t1 );
//assert( jl[3] > jp[0].t2 );
//assert( jl[3] > jp[0].a1 );
//assert( jl[3] == jp[0].a2 );
//assert( jl[3] % jp[0].a1 == 0 );
//assert( jl[3] != jp[0].t3 );
//assert( jl[2] > jp[0].t3 );
//assert( jl[2] > jp[0].t2 );
//assert( jl[2] > jp[0].t1 );
//assert( jl[2] > jp[0].delta );
//assert( jl[2] > jp[0].a1 );
//assert( jl[1] > jp[0].t3 );
//assert( jl[1] > jp[0].t2 );
//assert( jl[1] > jp[0].t1 );
//assert( jl[1] > jp[0].delta );
//assert( jl[1] > jp[0].a1 );
//assert( jl[1] == jp[0].initVel );
//assert( jl[0] >= jp[0].t3 );
//assert( jl[0] > jp[0].t2 );
//assert( jl[0] > jp[0].a1 );
//assert( jl[0] == jp[0].v );
//assert( in[0] >= jp[0].t1 );
//assert( in[0] >= jp[0].delta );
//assert( in[0] > jp[0].t2 );
//assert( in[0] > jp[0].a1 );
//assert( in[0] < jl[2] );
//assert( in[0] < jl[1] );
//assert( in[0] != jp[0].t3 );
//assert( in[0] != jl[3] );
//assert( in[0] != jl[0] );
//assert( in[0] != 0 );
assert( i > jp[0].t2 );
assert( i > jp[0].a1 );
assert( i == totalTime );
assert( i == 0 );
assert( i <= jp[0].t3 );
assert( i <= jp[0].delta );
assert( i < jp[0].t1 );
assert( i < jl[3] );
assert( i < jl[2] );
assert( i < jl[1] );
assert( i < jl[0] );
assert( i < in[0] );
//assert( fb[0] >= i );
//assert( fb[0] > jp[0].t2 );
//assert( fb[0] > jp[0].a1 );
//assert( fb[0] == jp[0].initPos );
//assert( fb[0] <= in[0] );
//assert( fb[0] != jp[0].delta );

	// Given an existing profile, extend the total time it takes.
	// This is done by re-calculating the maximum velocity to use (Vp).
	// The velocity is calculated from the equation for total distance, Eqn 1:
	// x = V0(t1) + 0.5a(t1)^2 + Vp(t2) + 0.5d(t3)^2
	// This is very similar to the technique used in building the initial profile.

	int a,b,c;       // coefficients of x in ax^2+bx+c=0
	int sqop;        // square root operand
	int Vp1, Vp2;    // 2 roots of quadratic

	// The expressions for these terms come from substituting for t1, t2 and t3 in Eqn 1,
	// and then re-arranging to get a quadratic in terms of Vp.
	// Note:
	// t1 = (Vp - V0)/a     where a is acceleration
	// t3 = Vp / d          where d is deceleration
	// t2 = T - t1 - t3     where T is totalTime for the new profile

	// This condition causes a divide by zero error, but
	// it should be a valid physical choice for a1, a2
	// To get around the problem, using the following HACK
	if(jp[i].a1 == (-jp[i].a2))
		jp[i].a1 *= 1; //0.9999


	a = -((1 / (2 * jp[i].a1)) + (1 / (2 * jp[i].a2)));
	b = (jp[i].initVel / jp[i].a1) + totalTime;
	c = -(((jp[i].initVel * jp[i].initVel)/(2 * jp[i].a1)) + jp[i].delta);

	// The roots of a quadratic are
	// x = (-b +- sqrt_(b^2 - 4ac))/2a
	sqop = (b * b) - (4 * a * c);
	
	if (sqop < 0)
{ 		int _ret_476=jp[i].v; // use existing velocity
assert( _ret_476 != sqop );
//assert( jp[0].t3 <= sqop );
//assert( jp[0].t3 <= _ret_476 );
//assert( jp[0].t2 < sqop );
//assert( jp[0].t2 < _ret_476 );
//assert( jp[0].t2 < jp[0].t3 );
//assert( jp[0].t3 % jp[0].t1 == 0 );
//assert( jp[0].t1 > jp[0].t2 );
//assert( jp[0].delta > jp[0].t2 );
//assert( jp[0].a1 < sqop );
//assert( jp[0].a1 < _ret_476 );
//assert( jp[0].a1 < jp[0].t3 );
//assert( jp[0].a1 != jp[0].t2 );
//assert( jp[0].a1 < jp[0].t1 );
//assert( jp[0].a1 < jp[0].delta );
//assert( jl[2] != sqop );
//assert( jl[2] > jp[0].t3 );
//assert( jl[2] > jp[0].t2 );
//assert( jl[2] > jp[0].t1 );
//assert( jl[2] > jp[0].delta );
//assert( jl[2] > jp[0].a1 );
//assert( jl[1] != sqop );
//assert( jl[1] > jp[0].t3 );
//assert( jl[1] > jp[0].t2 );
//assert( jl[1] > jp[0].t1 );
//assert( jl[1] > jp[0].delta );
//assert( jl[1] > jp[0].a1 );
//assert( in[0] != sqop );
//assert( in[0] != _ret_476 );
//assert( in[0] != jp[0].t3 );
//assert( in[0] > jp[0].t2 );
//assert( in[0] >= jp[0].t1 );
//assert( in[0] >= jp[0].delta );
//assert( in[0] > jp[0].a1 );
//assert( in[0] < jl[2] );
//assert( in[0] < jl[1] );
//assert( fb[0] > jp[0].t2 );
//assert( fb[0] != jp[0].delta );
//assert( fb[0] > jp[0].a1 );
//assert( fb[0] <= in[0] );
//assert( c != sqop );
//assert( c > _ret_476 );
//assert( c > jp[0].t3 );
//assert( c > jp[0].t2 );
//assert( c > jp[0].t1 );
//assert( c > jp[0].delta );
//assert( c > jp[0].a1 );
//assert( c != jl[2] );
//assert( c != jl[1] );
//assert( c > in[0] );
//assert( c > fb[0] );
assert( b <= sqop );
assert( b < _ret_476 );
assert( b <= jp[0].t3 );
assert( b < jp[0].t1 );
assert( b <= jp[0].delta );
assert( b != jp[0].a1 );
assert( b < jl[2] );
assert( b < jl[1] );
assert( b < in[0] );
assert( b <= fb[0] );
assert( b < c );
//assert( a <= sqop );
//assert( a < _ret_476 );
//assert( a <= jp[0].t3 );
//assert( a > jp[0].t2 );
//assert( a < jp[0].t1 );
//assert( a <= jp[0].delta );
//assert( a > jp[0].a1 );
//assert( a < jl[2] );
//assert( a < jl[1] );
//assert( a < in[0] );
//assert( a <= fb[0] );
//assert( a < c );
//assert( a >= b );
//assert( Vp2 > sqop );
//assert( Vp2 > _ret_476 );
//assert( Vp2 > jp[0].t3 );
//assert( Vp2 > jp[0].t2 );
//assert( Vp2 > jp[0].t1 );
//assert( Vp2 > jp[0].delta );
//assert( Vp2 > jp[0].a1 );
//assert( Vp2 > jl[2] );
//assert( Vp2 > jl[1] );
//assert( Vp2 > in[0] );
//assert( Vp2 > fb[0] );
//assert( Vp2 > c );
//assert( Vp2 > b );
//assert( Vp1 != sqop );
//assert( Vp1 != _ret_476 );
//assert( Vp1 != jp[0].t3 );
//assert( Vp1 > jp[0].t2 );
//assert( Vp1 >= jp[0].t1 );
//assert( jp[0].a1 % Vp1 == 0 );
//assert( Vp1 > jp[0].a1 );
//assert( Vp1 % jp[0].a1 == 0 );
//assert( Vp1 != jl[2] );
//assert( Vp1 != jl[1] );
//assert( Vp1 != in[0] );
//assert( Vp1 != fb[0] );
//assert( Vp1 != c );
//assert( Vp1 > b );
//assert( Vp1 > a );
//assert( Vp1 < Vp2 );
assert( sqop >= 0 );
assert( _ret_476 >= 1 );
assert( _ret_476 != 0 );
//assert( jp[0].t3 == 0 || jp[0].t3 == 1 || jp[0].t3 == 14 );
//assert( jp[0].t2 != 0 );
//assert( jp[0].t1 != 0 );
//assert( jp[0].t1 == 1 || jp[0].t1 == 2 || jp[0].t1 == 3 || jp[0].t1 == 9 );
//assert( jp[0].delta >= 0 );
//assert( jp[0].a1 <= -1 );
//assert( jp[0].a1 != 0 );
//assert( in[0] != 0 );
//assert( c != 0 );
assert( b <= 0 );
//assert( a == 0 );
//assert( Vp2 == 134516633 );
//assert( Vp1 >= 1 );
//assert( Vp1 != 0 );
//assert( jp[0].v == _ret_476 );
//assert( jl[1] == jp[0].initVel );
//assert( fb[0] == jp[0].initPos );
//assert( a == totalTime );
//assert( a == i );
//assert( Vp1 == jp[0].a2 );
//assert( Vp1 == jl[3] );

return _ret_476; }
	
	if (a == 0)
{ 		int _ret_479=jp[i].v;
assert( _ret_479 != sqop );
//assert( jp[0].t3 <= sqop );
//assert( jp[0].t3 <= _ret_479 );
//assert( jp[0].t2 < sqop );
//assert( jp[0].t2 < _ret_479 );
//assert( jp[0].t2 < jp[0].t3 );
//assert( jp[0].t3 % jp[0].t1 == 0 );
//assert( jp[0].t1 > jp[0].t2 );
//assert( jp[0].delta > jp[0].t2 );
//assert( jp[0].a1 < sqop );
//assert( jp[0].a1 < _ret_479 );
//assert( jp[0].a1 < jp[0].t3 );
//assert( jp[0].a1 != jp[0].t2 );
//assert( jp[0].a1 < jp[0].t1 );
//assert( jp[0].a1 < jp[0].delta );
//assert( jl[2] != sqop );
//assert( jl[2] > jp[0].t3 );
//assert( jl[2] > jp[0].t2 );
//assert( jl[2] > jp[0].t1 );
//assert( jl[2] > jp[0].delta );
//assert( jl[2] > jp[0].a1 );
//assert( jl[1] != sqop );
//assert( jl[1] > jp[0].t3 );
//assert( jl[1] > jp[0].t2 );
//assert( jl[1] > jp[0].t1 );
//assert( jl[1] > jp[0].delta );
//assert( jl[1] > jp[0].a1 );
//assert( in[0] != sqop );
//assert( in[0] != _ret_479 );
//assert( in[0] != jp[0].t3 );
//assert( in[0] > jp[0].t2 );
//assert( in[0] >= jp[0].t1 );
//assert( in[0] >= jp[0].delta );
//assert( in[0] > jp[0].a1 );
//assert( in[0] < jl[2] );
//assert( in[0] < jl[1] );
//assert( fb[0] > jp[0].t2 );
//assert( fb[0] != jp[0].delta );
//assert( fb[0] > jp[0].a1 );
//assert( fb[0] <= in[0] );
//assert( c != sqop );
//assert( c > _ret_479 );
//assert( c > jp[0].t3 );
//assert( c > jp[0].t2 );
//assert( c > jp[0].t1 );
//assert( c > jp[0].delta );
//assert( c > jp[0].a1 );
//assert( c != jl[2] );
//assert( c != jl[1] );
//assert( c > in[0] );
//assert( c > fb[0] );
assert( b <= sqop );
assert( b < _ret_479 );
assert( b <= jp[0].t3 );
assert( b < jp[0].t1 );
assert( b <= jp[0].delta );
assert( b != jp[0].a1 );
assert( b < jl[2] );
assert( b < jl[1] );
assert( b < in[0] );
assert( b <= fb[0] );
assert( b < c );
//assert( a <= sqop );
//assert( a < _ret_479 );
//assert( a <= jp[0].t3 );
//assert( a > jp[0].t2 );
//assert( a < jp[0].t1 );
//assert( a <= jp[0].delta );
//assert( a > jp[0].a1 );
//assert( a < jl[2] );
//assert( a < jl[1] );
//assert( a < in[0] );
//assert( a <= fb[0] );
//assert( a < c );
//assert( a >= b );
//assert( Vp2 > sqop );
//assert( Vp2 > _ret_479 );
//assert( Vp2 > jp[0].t3 );
//assert( Vp2 > jp[0].t2 );
//assert( Vp2 > jp[0].t1 );
//assert( Vp2 > jp[0].delta );
//assert( Vp2 > jp[0].a1 );
//assert( Vp2 > jl[2] );
//assert( Vp2 > jl[1] );
//assert( Vp2 > in[0] );
//assert( Vp2 > fb[0] );
//assert( Vp2 > c );
//assert( Vp2 > b );
//assert( Vp1 != sqop );
//assert( Vp1 != _ret_479 );
//assert( Vp1 != jp[0].t3 );
//assert( Vp1 > jp[0].t2 );
//assert( Vp1 >= jp[0].t1 );
//assert( jp[0].a1 % Vp1 == 0 );
//assert( Vp1 > jp[0].a1 );
//assert( Vp1 % jp[0].a1 == 0 );
//assert( Vp1 != jl[2] );
//assert( Vp1 != jl[1] );
//assert( Vp1 != in[0] );
//assert( Vp1 != fb[0] );
//assert( Vp1 != c );
//assert( Vp1 > b );
//assert( Vp1 > a );
//assert( Vp1 < Vp2 );
assert( sqop >= 0 );
assert( _ret_479 >= 1 );
assert( _ret_479 != 0 );
//assert( jp[0].t3 == 0 || jp[0].t3 == 1 || jp[0].t3 == 14 );
//assert( jp[0].t2 != 0 );
//assert( jp[0].t1 != 0 );
//assert( jp[0].t1 == 1 || jp[0].t1 == 2 || jp[0].t1 == 3 || jp[0].t1 == 9 );
//assert( jp[0].delta >= 0 );
//assert( jp[0].a1 <= -1 );
//assert( jp[0].a1 != 0 );
//assert( in[0] != 0 );
//assert( c != 0 );
assert( b <= 0 );
//assert( a == 0 );
//assert( Vp2 == 134516633 );
//assert( Vp1 >= 1 );
//assert( Vp1 != 0 );
//assert( jp[0].v == _ret_479 );
//assert( jl[1] == jp[0].initVel );
//assert( fb[0] == jp[0].initPos );
//assert( a == totalTime );
//assert( a == i );
//assert( Vp1 == jp[0].a2 );
//assert( Vp1 == jl[3] );

return _ret_479; }
	
	Vp1 = ((- b) + sqrt_(sqop)) / (2 * a);
	Vp2 = ((- b) - sqrt_(sqop)) / (2 * a);

	// Use velocity with smallest absolute value
	if (fabs_(Vp1) <= fabs_(Vp2))
{ 		int _ret_486=Vp1;
assert( _ret_486 != sqop );
//assert( jp[0].t3 <= sqop );
//assert( jp[0].t3 <= _ret_486 );
//assert( jp[0].t2 < sqop );
//assert( jp[0].t2 < _ret_486 );
//assert( jp[0].t2 < jp[0].t3 );
//assert( jp[0].t3 % jp[0].t1 == 0 );
//assert( jp[0].t1 > jp[0].t2 );
//assert( jp[0].delta > jp[0].t2 );
//assert( jp[0].a1 < sqop );
//assert( jp[0].a1 < _ret_486 );
//assert( jp[0].a1 < jp[0].t3 );
//assert( jp[0].a1 != jp[0].t2 );
//assert( jp[0].a1 < jp[0].t1 );
//assert( jp[0].a1 < jp[0].delta );
//assert( jl[2] != sqop );
//assert( jl[2] > jp[0].t3 );
//assert( jl[2] > jp[0].t2 );
//assert( jl[2] > jp[0].t1 );
//assert( jl[2] > jp[0].delta );
//assert( jl[2] > jp[0].a1 );
//assert( jl[1] != sqop );
//assert( jl[1] > jp[0].t3 );
//assert( jl[1] > jp[0].t2 );
//assert( jl[1] > jp[0].t1 );
//assert( jl[1] > jp[0].delta );
//assert( jl[1] > jp[0].a1 );
//assert( in[0] != sqop );
//assert( in[0] != _ret_486 );
//assert( in[0] != jp[0].t3 );
//assert( in[0] > jp[0].t2 );
//assert( in[0] >= jp[0].t1 );
//assert( in[0] >= jp[0].delta );
//assert( in[0] > jp[0].a1 );
//assert( in[0] < jl[2] );
//assert( in[0] < jl[1] );
//assert( fb[0] > jp[0].t2 );
//assert( fb[0] != jp[0].delta );
//assert( fb[0] > jp[0].a1 );
//assert( fb[0] <= in[0] );
//assert( c != sqop );
//assert( c > _ret_486 );
//assert( c > jp[0].t3 );
//assert( c > jp[0].t2 );
//assert( c > jp[0].t1 );
//assert( c > jp[0].delta );
//assert( c > jp[0].a1 );
//assert( c != jl[2] );
//assert( c != jl[1] );
//assert( c > in[0] );
//assert( c > fb[0] );
assert( b <= sqop );
assert( b < _ret_486 );
assert( b <= jp[0].t3 );
assert( b < jp[0].t1 );
assert( b <= jp[0].delta );
assert( b != jp[0].a1 );
assert( b < jl[2] );
assert( b < jl[1] );
assert( b < in[0] );
assert( b <= fb[0] );
assert( b < c );
//assert( a <= sqop );
//assert( a < _ret_486 );
//assert( a <= jp[0].t3 );
//assert( a > jp[0].t2 );
//assert( a < jp[0].t1 );
//assert( a <= jp[0].delta );
//assert( a > jp[0].a1 );
//assert( a < jl[2] );
//assert( a < jl[1] );
//assert( a < in[0] );
//assert( a <= fb[0] );
//assert( a < c );
//assert( a >= b );
//assert( Vp2 > sqop );
//assert( Vp2 > _ret_486 );
//assert( Vp2 > jp[0].t3 );
//assert( Vp2 > jp[0].t2 );
//assert( Vp2 > jp[0].t1 );
//assert( Vp2 > jp[0].delta );
//assert( Vp2 > jp[0].a1 );
//assert( Vp2 > jl[2] );
//assert( Vp2 > jl[1] );
//assert( Vp2 > in[0] );
//assert( Vp2 > fb[0] );
//assert( Vp2 > c );
//assert( Vp2 > b );
//assert( Vp1 != sqop );
//assert( Vp1 != _ret_486 );
//assert( Vp1 != jp[0].t3 );
//assert( Vp1 > jp[0].t2 );
//assert( Vp1 >= jp[0].t1 );
//assert( jp[0].a1 % Vp1 == 0 );
//assert( Vp1 > jp[0].a1 );
//assert( Vp1 % jp[0].a1 == 0 );
//assert( Vp1 != jl[2] );
//assert( Vp1 != jl[1] );
//assert( Vp1 != in[0] );
//assert( Vp1 != fb[0] );
//assert( Vp1 != c );
//assert( Vp1 > b );
//assert( Vp1 > a );
//assert( Vp1 < Vp2 );
assert( sqop >= 0 );
assert( _ret_486 >= 1 );
assert( _ret_486 != 0 );
//assert( jp[0].t3 == 0 || jp[0].t3 == 1 || jp[0].t3 == 14 );
//assert( jp[0].t2 != 0 );
//assert( jp[0].t1 != 0 );
//assert( jp[0].t1 == 1 || jp[0].t1 == 2 || jp[0].t1 == 3 || jp[0].t1 == 9 );
//assert( jp[0].delta >= 0 );
//assert( jp[0].a1 <= -1 );
//assert( jp[0].a1 != 0 );
//assert( in[0] != 0 );
//assert( c != 0 );
assert( b <= 0 );
//assert( a == 0 );
//assert( Vp2 == 134516633 );
//assert( Vp1 >= 1 );
//assert( Vp1 != 0 );
//assert( jp[0].v == _ret_486 );
//assert( jl[1] == jp[0].initVel );
//assert( fb[0] == jp[0].initPos );
//assert( a == totalTime );
//assert( a == i );
//assert( Vp1 == jp[0].a2 );
//assert( Vp1 == jl[3] );

return _ret_486; }
	
	else
{ 		int _ret_489=Vp2;
assert( _ret_489 != sqop );
//assert( jp[0].t3 <= sqop );
//assert( jp[0].t3 <= _ret_489 );
//assert( jp[0].t2 < sqop );
//assert( jp[0].t2 < _ret_489 );
//assert( jp[0].t2 < jp[0].t3 );
//assert( jp[0].t3 % jp[0].t1 == 0 );
//assert( jp[0].t1 > jp[0].t2 );
//assert( jp[0].delta > jp[0].t2 );
//assert( jp[0].a1 < sqop );
//assert( jp[0].a1 < _ret_489 );
//assert( jp[0].a1 < jp[0].t3 );
//assert( jp[0].a1 != jp[0].t2 );
//assert( jp[0].a1 < jp[0].t1 );
//assert( jp[0].a1 < jp[0].delta );
//assert( jl[2] != sqop );
//assert( jl[2] > jp[0].t3 );
//assert( jl[2] > jp[0].t2 );
//assert( jl[2] > jp[0].t1 );
//assert( jl[2] > jp[0].delta );
//assert( jl[2] > jp[0].a1 );
//assert( jl[1] != sqop );
//assert( jl[1] > jp[0].t3 );
//assert( jl[1] > jp[0].t2 );
//assert( jl[1] > jp[0].t1 );
//assert( jl[1] > jp[0].delta );
//assert( jl[1] > jp[0].a1 );
//assert( in[0] != sqop );
//assert( in[0] != _ret_489 );
//assert( in[0] != jp[0].t3 );
//assert( in[0] > jp[0].t2 );
//assert( in[0] >= jp[0].t1 );
//assert( in[0] >= jp[0].delta );
//assert( in[0] > jp[0].a1 );
//assert( in[0] < jl[2] );
//assert( in[0] < jl[1] );
//assert( fb[0] > jp[0].t2 );
//assert( fb[0] != jp[0].delta );
//assert( fb[0] > jp[0].a1 );
//assert( fb[0] <= in[0] );
//assert( c != sqop );
//assert( c > _ret_489 );
//assert( c > jp[0].t3 );
//assert( c > jp[0].t2 );
//assert( c > jp[0].t1 );
//assert( c > jp[0].delta );
//assert( c > jp[0].a1 );
//assert( c != jl[2] );
//assert( c != jl[1] );
//assert( c > in[0] );
//assert( c > fb[0] );
assert( b <= sqop );
assert( b < _ret_489 );
assert( b <= jp[0].t3 );
assert( b < jp[0].t1 );
assert( b <= jp[0].delta );
assert( b != jp[0].a1 );
assert( b < jl[2] );
assert( b < jl[1] );
assert( b < in[0] );
assert( b <= fb[0] );
assert( b < c );
//assert( a <= sqop );
//assert( a < _ret_489 );
//assert( a <= jp[0].t3 );
//assert( a > jp[0].t2 );
//assert( a < jp[0].t1 );
//assert( a <= jp[0].delta );
//assert( a > jp[0].a1 );
//assert( a < jl[2] );
//assert( a < jl[1] );
//assert( a < in[0] );
//assert( a <= fb[0] );
//assert( a < c );
//assert( a >= b );
//assert( Vp2 > sqop );
//assert( Vp2 > _ret_489 );
//assert( Vp2 > jp[0].t3 );
//assert( Vp2 > jp[0].t2 );
//assert( Vp2 > jp[0].t1 );
//assert( Vp2 > jp[0].delta );
//assert( Vp2 > jp[0].a1 );
//assert( Vp2 > jl[2] );
//assert( Vp2 > jl[1] );
//assert( Vp2 > in[0] );
//assert( Vp2 > fb[0] );
//assert( Vp2 > c );
//assert( Vp2 > b );
//assert( Vp1 != sqop );
//assert( Vp1 != _ret_489 );
//assert( Vp1 != jp[0].t3 );
//assert( Vp1 > jp[0].t2 );
//assert( Vp1 >= jp[0].t1 );
//assert( jp[0].a1 % Vp1 == 0 );
//assert( Vp1 > jp[0].a1 );
//assert( Vp1 % jp[0].a1 == 0 );
//assert( Vp1 != jl[2] );
//assert( Vp1 != jl[1] );
//assert( Vp1 != in[0] );
//assert( Vp1 != fb[0] );
//assert( Vp1 != c );
//assert( Vp1 > b );
//assert( Vp1 > a );
//assert( Vp1 < Vp2 );
assert( sqop >= 0 );
assert( _ret_489 >= 1 );
assert( _ret_489 != 0 );
//assert( jp[0].t3 == 0 || jp[0].t3 == 1 || jp[0].t3 == 14 );
//assert( jp[0].t2 != 0 );
//assert( jp[0].t1 != 0 );
//assert( jp[0].t1 == 1 || jp[0].t1 == 2 || jp[0].t1 == 3 || jp[0].t1 == 9 );
//assert( jp[0].delta >= 0 );
//assert( jp[0].a1 <= -1 );
//assert( jp[0].a1 != 0 );
//assert( in[0] != 0 );
//assert( c != 0 );
assert( b <= 0 );
//assert( a == 0 );
//assert( Vp2 == 134516633 );
//assert( Vp1 >= 1 );
//assert( Vp1 != 0 );
//assert( jp[0].v == _ret_489 );
//assert( jl[1] == jp[0].initVel );
//assert( fb[0] == jp[0].initPos );
//assert( a == totalTime );
//assert( a == i );
//assert( Vp1 == jp[0].a2 );
//assert( Vp1 == jl[3] );

return _ret_489; }
}
