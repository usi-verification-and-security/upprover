#define DllExport __declspec( dllexport ) 

//-------------------------------------------------------------------------
#define DEFAULT_SMALL_ACCEL     0  // used instead of zero
#define ZERO_TOLERANCE          0  // used to trap very small deltas
#define NUM_JOINTS              1
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
//	Local type definitions
//-------------------------------------------------------------------------
typedef struct
{
    // define profile shape
	int a0,a1,a2,a3,a4,a5;	// spline coefficients
	int x0, xf;				// starting and final positions

} jointProfile;
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
//	Global variables declaration
//-------------------------------------------------------------------------
jointProfile	jp[NUM_JOINTS];
static int	currentPosition[NUM_JOINTS];
static int	elapsedTime = 0;
static int	endTime = 0;
static int		initialized = 0;
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
//	Main function declaration
//-------------------------------------------------------------------------
void P2P_Joints_TG(int Sample_Time, int Joints_Limits[4], int XYZRPYin[NUM_JOINTS], int XYZRPYfb[NUM_JOINTS], int XYZRPYout[NUM_JOINTS], int *TrajectoryComplete, int VelocitiesOut[NUM_JOINTS]);
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
//	Routines declaration
//-------------------------------------------------------------------------
void InitilizeTG(int jl[4], int in[], int fb[]);
void SelectMovementTime(int vMax, int aMax, int XYZRPYin[], int XYZRPYfb[]);
void InitProfile(int i, int X0, int Xf);

//-------------------------------------------------------------------------
