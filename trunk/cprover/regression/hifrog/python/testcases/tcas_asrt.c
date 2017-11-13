
/*  -*- Last-Edit:  Fri Jan 29 11:13:27 1993 by Tarak S. Goradia; -*- */
/* $Log: tcas.c,v $
 * Revision 1.2  1993/03/12  19:29:50  foster
 * Correct logic bug which didn't allow output of 2 - hf
 * */

#include <stdio.h>

#define OLEV       600		/* in feets/minute */
#define MAXALTDIFF 600		/* max altitude difference in feet */
#define MINSEP     300          /* min separation in feet */
#define NOZCROSS   100		/* in feet */
				/* variables */

typedef int bool;

int Cur_Vertical_Sep;
bool High_Confidence;
bool Two_of_Three_Reports_Valid;

int Own_Tracked_Alt;
int Own_Tracked_Alt_Rate;
int Other_Tracked_Alt;

int Alt_Layer_Value;		/* 0, 1, 2, 3 */
int Positive_RA_Alt_Thresh[4];

int Up_Separation;
int Down_Separation;

				/* state variables */
int Other_RAC;			/* NO_INTENT, DO_NOT_CLIMB, DO_NOT_DESCEND */
#define NO_INTENT 0
#define DO_NOT_CLIMB 1
#define DO_NOT_DESCEND 2

int Other_Capability;		/* TCAS_TA, OTHER */
#define TCAS_TA 1
#define OTHER 2

int Climb_Inhibit;		/* true/false */

#define UNRESOLVED 0
#define UPWARD_RA 1
#define DOWNWARD_RA 2

void initialize()
{
assert(Alt_Layer_Value==Climb_Inhibit);
assert(Alt_Layer_Value==Cur_Vertical_Sep);
assert(Alt_Layer_Value==Down_Separation);
assert(Alt_Layer_Value==High_Confidence);
assert(Alt_Layer_Value==Other_Capability);
assert(Alt_Layer_Value==Other_Tracked_Alt);
assert(Alt_Layer_Value==Own_Tracked_Alt);
assert(Alt_Layer_Value==Own_Tracked_Alt_Rate);
assert(Alt_Layer_Value==Two_of_Three_Reports_Valid);
assert(Alt_Layer_Value==Up_Separation);
assert(Alt_Layer_Value==0);
    Positive_RA_Alt_Thresh[0] = 400;
    Positive_RA_Alt_Thresh[1] = 500;
    Positive_RA_Alt_Thresh[2] = 640;
    Positive_RA_Alt_Thresh[3] = 740;
}

int ALIM ()
{
assert(Alt_Layer_Value>=0);
assert(Climb_Inhibit==-1||Climb_Inhibit==0||Climb_Inhibit==1||Climb_Inhibit==4||Climb_Inhibit==9);
assert(Cur_Vertical_Sep!=0);
assert(High_Confidence==-1||High_Confidence==1);
assert(High_Confidence!=0);
assert(Other_Capability==0||Other_Capability==1||Other_Capability==2);
assert(Two_of_Three_Reports_Valid==-1||Two_of_Three_Reports_Valid==0||Two_of_Three_Reports_Valid==1);
assert(Alt_Layer_Value<Cur_Vertical_Sep);
assert(Climb_Inhibit<Cur_Vertical_Sep);
assert(Cur_Vertical_Sep!=Down_Separation);
assert(Cur_Vertical_Sep>High_Confidence);
assert(Cur_Vertical_Sep>Other_Capability);
assert(Cur_Vertical_Sep!=Other_Tracked_Alt);
assert(Cur_Vertical_Sep!=Own_Tracked_Alt);
assert(Cur_Vertical_Sep>Own_Tracked_Alt_Rate);
assert(Cur_Vertical_Sep>Two_of_Three_Reports_Valid);
assert(Down_Separation!=High_Confidence);
assert(Down_Separation!=Other_Capability);
assert(Down_Separation!=Other_Tracked_Alt);
assert(High_Confidence!=Own_Tracked_Alt);
assert(High_Confidence!=Own_Tracked_Alt_Rate);
assert(Other_Capability!=Other_Tracked_Alt);
assert(Other_Capability!=Own_Tracked_Alt);
assert(Other_Capability!=Own_Tracked_Alt_Rate);
assert(Other_Capability!=Up_Separation);
assert(Other_Tracked_Alt!=Own_Tracked_Alt);
assert(Other_Tracked_Alt!=Own_Tracked_Alt_Rate);
assert(Own_Tracked_Alt!=Own_Tracked_Alt_Rate);
 return Positive_RA_Alt_Thresh[Alt_Layer_Value];
}

int Inhibit_Biased_Climb ()
{
assert(Alt_Layer_Value>=-1);
assert(Climb_Inhibit>=-1);
assert(Cur_Vertical_Sep!=0);
assert(High_Confidence==-1||High_Confidence==1);
assert(High_Confidence!=0);
assert(Other_Capability==0||Other_Capability==1||Other_Capability==2);
assert(Two_of_Three_Reports_Valid==-1||Two_of_Three_Reports_Valid==0||Two_of_Three_Reports_Valid==1);
assert(Alt_Layer_Value<Cur_Vertical_Sep);
assert(Climb_Inhibit<Cur_Vertical_Sep);
assert(Cur_Vertical_Sep>High_Confidence);
assert(Cur_Vertical_Sep>Other_Capability);
assert(Cur_Vertical_Sep!=Own_Tracked_Alt);
assert(Cur_Vertical_Sep>Own_Tracked_Alt_Rate);
assert(Cur_Vertical_Sep>Two_of_Three_Reports_Valid);
assert(Down_Separation!=High_Confidence);
assert(Down_Separation!=Other_Capability);
assert(High_Confidence!=Own_Tracked_Alt);
assert(Other_Capability!=Other_Tracked_Alt);
assert(Other_Capability!=Own_Tracked_Alt);
assert(Other_Capability!=Up_Separation);
assert(Other_Tracked_Alt!=Own_Tracked_Alt_Rate);
    return (Climb_Inhibit ? Up_Separation + NOZCROSS : Up_Separation);
}

bool Non_Crossing_Biased_Climb()
{
assert(Alt_Layer_Value>=-1);
assert(Climb_Inhibit>=-1);
assert(Cur_Vertical_Sep!=0);
assert(High_Confidence==-1||High_Confidence==1);
assert(High_Confidence!=0);
assert(Other_Capability==0||Other_Capability==1||Other_Capability==2);
assert(Two_of_Three_Reports_Valid==-1||Two_of_Three_Reports_Valid==0||Two_of_Three_Reports_Valid==1);
assert(Alt_Layer_Value<Cur_Vertical_Sep);
assert(Climb_Inhibit<Cur_Vertical_Sep);
assert(Cur_Vertical_Sep>High_Confidence);
assert(Cur_Vertical_Sep>Other_Capability);
assert(Cur_Vertical_Sep!=Own_Tracked_Alt);
assert(Cur_Vertical_Sep>Own_Tracked_Alt_Rate);
assert(Cur_Vertical_Sep>Two_of_Three_Reports_Valid);
assert(Down_Separation!=High_Confidence);
assert(Down_Separation!=Other_Capability);
assert(High_Confidence!=Own_Tracked_Alt);
assert(Other_Capability!=Other_Tracked_Alt);
assert(Other_Capability!=Own_Tracked_Alt);
assert(Other_Capability!=Up_Separation);
assert(Other_Tracked_Alt!=Own_Tracked_Alt_Rate);
    int upward_preferred;
    int upward_crossing_situation;
    bool result;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred)
    {
	result = !(Own_Below_Threat()) || ((Own_Below_Threat()) && (!(Down_Separation >= ALIM())));
    }
    else
    {	
	result = Own_Above_Threat() && (Cur_Vertical_Sep >= MINSEP) && (Up_Separation >= ALIM());
    }
    return result;
}

bool Non_Crossing_Biased_Descend()
{
assert(Alt_Layer_Value>=-1);
assert(Climb_Inhibit>=-1);
assert(Cur_Vertical_Sep!=0);
assert(High_Confidence==-1||High_Confidence==1);
assert(High_Confidence!=0);
assert(Other_Capability==0||Other_Capability==1||Other_Capability==2);
assert(Two_of_Three_Reports_Valid==-1||Two_of_Three_Reports_Valid==0||Two_of_Three_Reports_Valid==1);
assert(Alt_Layer_Value<Cur_Vertical_Sep);
assert(Climb_Inhibit<Cur_Vertical_Sep);
assert(Cur_Vertical_Sep>High_Confidence);
assert(Cur_Vertical_Sep>Other_Capability);
assert(Cur_Vertical_Sep!=Own_Tracked_Alt);
assert(Cur_Vertical_Sep>Own_Tracked_Alt_Rate);
assert(Cur_Vertical_Sep>Two_of_Three_Reports_Valid);
assert(Down_Separation!=High_Confidence);
assert(Down_Separation!=Other_Capability);
assert(High_Confidence!=Own_Tracked_Alt);
assert(Other_Capability!=Other_Tracked_Alt);
assert(Other_Capability!=Own_Tracked_Alt);
assert(Other_Capability!=Up_Separation);
assert(Other_Tracked_Alt!=Own_Tracked_Alt_Rate);
    int upward_preferred;
    int upward_crossing_situation;
    bool result;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred)
    {
	result = Own_Below_Threat() && (Cur_Vertical_Sep >= MINSEP) && (Down_Separation >= ALIM());
    }
    else
    {
	result = !(Own_Above_Threat()) || ((Own_Above_Threat()) && (Up_Separation >= ALIM()));
    }
    return result;
}

bool Own_Below_Threat()
{
assert(Alt_Layer_Value>=0);
assert(Climb_Inhibit>=-1);
assert(Cur_Vertical_Sep!=0);
assert(High_Confidence==-1||High_Confidence==1);
assert(High_Confidence!=0);
assert(Other_Capability==0||Other_Capability==1||Other_Capability==2);
assert(Two_of_Three_Reports_Valid==-1||Two_of_Three_Reports_Valid==0||Two_of_Three_Reports_Valid==1);
assert(Up_Separation>=0);
assert(Alt_Layer_Value<Cur_Vertical_Sep);
assert(Alt_Layer_Value!=Up_Separation);
assert(Climb_Inhibit<Cur_Vertical_Sep);
assert(Cur_Vertical_Sep!=Down_Separation);
assert(Cur_Vertical_Sep>High_Confidence);
assert(Cur_Vertical_Sep>Other_Capability);
assert(Cur_Vertical_Sep!=Other_Tracked_Alt);
assert(Cur_Vertical_Sep!=Own_Tracked_Alt);
assert(Cur_Vertical_Sep>Own_Tracked_Alt_Rate);
assert(Cur_Vertical_Sep>Two_of_Three_Reports_Valid);
assert(Down_Separation!=High_Confidence);
assert(Down_Separation!=Other_Capability);
assert(High_Confidence!=Own_Tracked_Alt);
assert(High_Confidence!=Own_Tracked_Alt_Rate);
assert(High_Confidence!=Up_Separation);
assert(Other_Capability!=Other_Tracked_Alt);
assert(Other_Capability!=Own_Tracked_Alt);
assert(Other_Capability!=Own_Tracked_Alt_Rate);
assert(Other_Capability!=Up_Separation);
assert(Other_Tracked_Alt!=Own_Tracked_Alt_Rate);
assert(Own_Tracked_Alt!=Own_Tracked_Alt_Rate);
    return (Own_Tracked_Alt < Other_Tracked_Alt);
}

bool Own_Above_Threat()
{
assert(Alt_Layer_Value>=-1);
assert(Climb_Inhibit==-1||Climb_Inhibit==0||Climb_Inhibit==1||Climb_Inhibit==4||Climb_Inhibit==9);
assert(Cur_Vertical_Sep!=0);
assert(Down_Separation>=0);
assert(High_Confidence==-1||High_Confidence==1);
assert(High_Confidence!=0);
assert(Other_Capability==0||Other_Capability==1||Other_Capability==2);
assert(Two_of_Three_Reports_Valid==-1||Two_of_Three_Reports_Valid==0||Two_of_Three_Reports_Valid==1);
assert(Alt_Layer_Value<Cur_Vertical_Sep);
assert(Climb_Inhibit<Cur_Vertical_Sep);
assert(Cur_Vertical_Sep>High_Confidence);
assert(Cur_Vertical_Sep>Other_Capability);
assert(Cur_Vertical_Sep!=Own_Tracked_Alt);
assert(Cur_Vertical_Sep>Own_Tracked_Alt_Rate);
assert(Cur_Vertical_Sep>Two_of_Three_Reports_Valid);
assert(Cur_Vertical_Sep!=Up_Separation);
assert(Down_Separation!=High_Confidence);
assert(Down_Separation!=Other_Capability);
assert(Down_Separation!=Two_of_Three_Reports_Valid);
assert(High_Confidence!=Own_Tracked_Alt);
assert(Other_Capability!=Other_Tracked_Alt);
assert(Other_Capability!=Own_Tracked_Alt);
assert(Other_Capability!=Up_Separation);
assert(Other_Tracked_Alt!=Own_Tracked_Alt_Rate);
    return (Other_Tracked_Alt < Own_Tracked_Alt);
}

int alt_sep_test()
{
assert(Alt_Layer_Value>=-1);
assert(Climb_Inhibit>=-1);
assert(High_Confidence==-1||High_Confidence==0||High_Confidence==1);
assert(Other_Capability==0||Other_Capability==1||Other_Capability==2);
assert(Two_of_Three_Reports_Valid==-1||Two_of_Three_Reports_Valid==0||Two_of_Three_Reports_Valid==1);
assert(Down_Separation!=Other_Capability);
assert(Other_Capability!=Up_Separation);
    bool enabled, tcas_equipped, intent_not_known;
    bool need_upward_RA, need_downward_RA;
    int alt_sep;

    enabled = High_Confidence && (Own_Tracked_Alt_Rate <= OLEV) && (Cur_Vertical_Sep > MAXALTDIFF);
    tcas_equipped = Other_Capability == TCAS_TA;
    intent_not_known = Two_of_Three_Reports_Valid && Other_RAC == NO_INTENT;
    
    alt_sep = UNRESOLVED;
    
    if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped))
    {
	need_upward_RA = Non_Crossing_Biased_Climb() && Own_Below_Threat();
	need_downward_RA = Non_Crossing_Biased_Descend() && Own_Above_Threat();
	if (need_upward_RA && need_downward_RA)
        /* unreachable: requires Own_Below_Threat and Own_Above_Threat
           to both be true - that requires Own_Tracked_Alt < Other_Tracked_Alt
           and Other_Tracked_Alt < Own_Tracked_Alt, which isn't possible */
	    alt_sep = UNRESOLVED;
	else if (need_upward_RA)
	    alt_sep = UPWARD_RA;
	else if (need_downward_RA)
	    alt_sep = DOWNWARD_RA;
	else
	    alt_sep = UNRESOLVED;
    }
    
    return alt_sep;
}

main(argc, argv)
int argc;
char *argv[];
{
    if(argc < 13)
    {
	fprintf(stdout, "Error: Command line arguments are\n");
	fprintf(stdout, "Cur_Vertical_Sep, High_Confidence, Two_of_Three_Reports_Valid\n");
	fprintf(stdout, "Own_Tracked_Alt, Own_Tracked_Alt_Rate, Other_Tracked_Alt\n");
	fprintf(stdout, "Alt_Layer_Value, Up_Separation, Down_Separation\n");
	fprintf(stdout, "Other_RAC, Other_Capability, Climb_Inhibit\n");
	exit(1);
    }
    initialize();
    Cur_Vertical_Sep = atoi(argv[1]);
    High_Confidence = atoi(argv[2]);
    Two_of_Three_Reports_Valid = atoi(argv[3]);
    Own_Tracked_Alt = atoi(argv[4]);
    Own_Tracked_Alt_Rate = atoi(argv[5]);
    Other_Tracked_Alt = atoi(argv[6]);
    Alt_Layer_Value = atoi(argv[7]);
    Up_Separation = atoi(argv[8]);
    Down_Separation = atoi(argv[9]);
    Other_RAC = atoi(argv[10]);
    Other_Capability = atoi(argv[11]);
    Climb_Inhibit = atoi(argv[12]);

    fprintf(stdout, "%d\n", alt_sep_test());
    exit(0);
}

