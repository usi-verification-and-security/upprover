#define DllExport //__declspec( dllexport ) 

//-------------------------------------------------------------------------
#define DEFAULT_SMALL_ACCEL     0.0001  // used instead of zero
#define ZERO_TOLERANCE          1.0e-9  // used to trap very small deltas
#define NUM_JOINTS              4
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
