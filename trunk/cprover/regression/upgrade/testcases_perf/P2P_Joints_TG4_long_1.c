#include <math.h>
#include <stdlib.h>

#include "P2P_Joints_TG4.h"

int nondet_int();

// The interface is made to comply with an earlier, trapezoidal velocity trajectory generator, so some of the inputs are ignored.
void main()
{
int i;

int Sample_Time = nondet_int();

int Joints_Limits[4];

    for(i = 0; i < 4; i++)
    {
         Joints_Limits[i] = nondet_int();
         Joints_Limits[i] &= 0x000000FF;
    }

int XYZRPYin[NUM_JOINTS];
int XYZRPYfb[NUM_JOINTS];

    for(i = 0; i < NUM_JOINTS; i++)
    {
        XYZRPYin[i] = nondet_int();
        XYZRPYfb[i] = nondet_int();
        XYZRPYin[i] &= 0x0000000F;
        XYZRPYfb[i] &= 0x0000000F;
    }


int XYZRPYout[NUM_JOINTS];

int TrajectoryComplete;
int VelocitiesOut[NUM_JOINTS];

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
		static int  position, velocity;

		if(i == 0)
		{
			elapsedTime = elapsedTime + Sample_Time;	// Time since profile started
		}

		if(elapsedTime <= endTime)
		{
			static int t6, t3, t10;		// temporary variables for position
			static int t14, t4, t8, t9;	// temporary variables for velocity

			// Calculate current position on the spline
			t3 = elapsedTime * elapsedTime;
			t6 = t3 * t3;
			position = jp[i].a0 + jp[i].a1 * elapsedTime + jp[i].a2 * t3 + jp[i].a3 * t3 * elapsedTime + jp[i].a4 * t6 + jp[i].a5 * t6 * elapsedTime;

			// Calculate current velocity on the spline
			t9 = elapsedTime * elapsedTime;
			t4 = endTime * endTime;
			t8 = endTime * endTime * endTime * endTime;
			velocity = -30 * (jp[i].x0 - jp[i].xf) * t9 * (t4 - 2 * elapsedTime * endTime + t9) / t8 / endTime;
			TrajectoryComplete = -1;

		} else {
			position = currentPosition[i];				// Stop and hold exactly at the commanded position
			velocity = 0;
			TrajectoryComplete = 1;
			elapsedTime = endTime + 5*Sample_Time;	// Stop timer at some value after total movement time to prevent overflow
		}
		
		// Output profile
		XYZRPYout[i] = position;
		VelocitiesOut[i] = velocity;
		assert (TrajectoryComplete == 1 || TrajectoryComplete == -1);
	}
}

void InitilizeTG(int jl[4], int in[], int fb[])
{
	// Create the profiles for each joint
	int		i;

	// Set initial time and positions
	// (Time zero, subtracted from future sample times to get elapsed time)
	elapsedTime = 0;

	// Positions are memorized in order to check if the input (=endpoints) have changed later
	for(i = 0; i < NUM_JOINTS; i++) {
		currentPosition[i] = in[i];
	}

	// Select total movement time
	SelectMovementTime(	jl[0],		// max velocity
						jl[2],		// max acceleration
						in,			// trajectory endpoints
						fb);		// trajectory starting points

	// Initialize trajectories
	for(i = 0; i < NUM_JOINTS; i++)
	{
			InitProfile(i,		// joint number
						fb[i],	// start
						in[i]);	// end	
		//assert(jp[i].a4 > jl[0]);				
	}
}

void SelectMovementTime(int vMax, int aMax, int XYZRPYin[], int XYZRPYfb[]) {

	int i = 0;
	int delta;
	int largestDelta = 0;
	int deltaJoint = 0;

	// Input checking:
	if (vMax == 0) {
		vMax = DEFAULT_SMALL_ACCEL;
	}
	if(aMax == 0) {
		aMax = DEFAULT_SMALL_ACCEL;
	}
	if (vMax < 0) {
		vMax = -1*vMax;	// abs()
	}
	if (aMax < 0) {
		aMax = -1*aMax;	// abs()
	}

	// Finding the joint that has the largest movement

	for(i = 0; i < NUM_JOINTS; i++)
	{
		delta = XYZRPYin[i] - XYZRPYfb[i];

		// Movements in the negative direction are handled in the same
		// way as positive movements
		if (delta < 0) {
			delta = -1*delta;	// abs()
		}

		if(delta >= largestDelta) {
			largestDelta = delta;
			deltaJoint = i;
		}
                //assert (delta >= 0 || delta < -100000);
	}

	// SELECTING THE TOTAL TRAJECTORY TIME:

	if (largestDelta == 0) {
		// No movement was commanded
		endTime = 0;

	} else {
		// For a P2P movement, with vo,vf,a0,af = 0,
		// top velocity can be calculated as:
		// TopVel = (-15*(x0-xf)) / (8*tf), so:
		int tfVel= (15*(largestDelta)) / (8*vMax);

		// On the other hand, top acceleration can be calculated as:
		// TopAcc = (-45*(x0-xf)) / (8*tf^2), so:
		int tfAcc = sqrt((45*(largestDelta)) / (8*aMax));

		// The longer of the above times should be selected
		// to fulfill both maximum parameter requirements:
		if (tfVel > tfAcc) {
			endTime = tfVel;
		} else {
			endTime = tfAcc;
		}
	}
}

void InitProfile(int i, int X0, int Xf)
{
	// DESCRIPTION
	// -----------
	// Calculates coefficients needed to evaluate the spline
	// First, a value is selected for the total movement time.
	// Second, coefficient values are calculated, details can be found in the         
	// related Maple -file.
	////////////////////////////////////////////////////////////////////////////

	int tf = endTime;

	jp[i].x0 = X0;
	jp[i].xf = Xf;

	if (tf == 0) {
		// No movement was commanded, hold start position
		jp[i].a0 = X0;
		jp[i].a1 = 0;
		jp[i].a2 = 0;
		jp[i].a3 = 0;
		jp[i].a4 = 0;
		jp[i].a5 = 0;
		
	} else {
		// SOLVING THE SPLINE COEFFICIENTS, SEE THE RELATED MAPLE FILE FOR DETAILS
		int t1,t2,t7;
		t1 = X0 - Xf;
		t2 = tf * tf;
		t7 = t2 * t2;
		jp[i].a0 = X0;
		jp[i].a1 = 0;
		jp[i].a2 = 0;
		jp[i].a3 = -10 / t2 / tf * t1;
		jp[i].a4 = 15 / t7 * t1;
		jp[i].a5 = -6 / t7 / tf * t1;
	}
}

