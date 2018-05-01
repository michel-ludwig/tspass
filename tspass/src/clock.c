/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     CLOCK                              * */
/* *                                                        * */
/* *  $Module:   CLOCK                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1999, 2000, 2001                  * */
/* *  MPI fuer Informatik                                   * */
/* *                                                        * */
/* *  Copyright (C) 2008-2009                               * */
/* *  Michel Ludwig (michel.ludwig@gmail.com)               * */
/* *  University of Liverpool                               * */
/* *                                                        * */
/* *  This program is free software; you can redistribute   * */
/* *  it and/or modify it under the terms of the GNU        * */
/* *  General Public License as published by the Free       * */
/* *  Software Foundation; either version 2 of the License, * */
/* *  or (at your option) any later version.                * */
/* *                                                        * */
/* *  This program is distributed in the hope that it will  * */
/* *  be useful, but WITHOUT ANY WARRANTY; without even     * */
/* *  the implied warranty of MERCHANTABILITY or FITNESS    * */
/* *  FOR A PARTICULAR PURPOSE.  See the GNU General Public * */
/* *  License for more details.                             * */
/* *                                                        * */
/* *  You should have received a copy of the GNU General    * */
/* *  Public License along with this program; if not, write * */
/* *  to the Free Software Foundation, Inc., 59 Temple      * */
/* *  Place, Suite 330, Boston, MA  02111-1307  USA         * */
/* *                                                        * */
/* *                                                        * */
/* $Revision: 1.2 $                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

#include "clock.h"

#include <assert.h>
#include <sys/time.h>
#include <sys/resource.h>

/**************************************************************/
/* Global Variables                                           */
/**************************************************************/

float      clock_Akku[clock_TYPESIZE];
CLOCK_TMS  clock_Counters[clock_TYPESIZE];

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

#define ONE_MILLION 1000000

static void add_timeval(const CLOCK_TMS *t1, const CLOCK_TMS *t2,
                        CLOCK_TMS *result)
{
  result->tv_sec = t1->tv_sec + t2->tv_sec;
  result->tv_usec = t1->tv_usec + t2->tv_usec;
  if(result->tv_usec >= ONE_MILLION) {
    result->tv_sec += result->tv_usec / ONE_MILLION;
    result->tv_usec %= ONE_MILLION;
  }
}

static void subtract_timeval(const CLOCK_TMS *t1, const CLOCK_TMS *t2,
                             CLOCK_TMS *result)
{
  CLOCK_TMS y;
  y.tv_sec = t2->tv_sec;
  y.tv_usec = t2->tv_usec;
  /* Perform the carry for the later subtraction by updating y. */
  if (t1->tv_usec < y.tv_usec) {
    int nsec = (y.tv_usec - t1->tv_usec) / ONE_MILLION + 1;
    y.tv_usec -= ONE_MILLION * nsec;
    y.tv_sec += nsec;
  }
  if (t1->tv_usec - y.tv_usec > ONE_MILLION) {
    int nsec = (t1->tv_usec - y.tv_usec) / ONE_MILLION;
    y.tv_usec += ONE_MILLION * nsec;
    y.tv_sec -= nsec;
  }

  /* Compute the time remaining to wait.
    tv_usec is certainly positive. */
  result->tv_sec = t1->tv_sec - y.tv_sec;
  result->tv_usec = t1->tv_usec - y.tv_usec;
}

void clock_Init(void)
/*********************************************************
  INPUT:   None.
  EFFECT:  Initializes the clock Module.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
  int i;

  for (i = 0; i < clock_TYPESIZE; ++i) {
    clock_InitCounter(i);
  }

}

void clock_InitCounter(CLOCK_CLOCKS ClockCounter)
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  The clock counter <ClockCounter> is initialized.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
  clock_Akku[ClockCounter] = 0;
}


void clock_StartCounter(CLOCK_CLOCKS ClockCounter)
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  The clock counter <ClockCounter> is started.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  struct rusage rus;
  
  if(getrusage(RUSAGE_SELF, &rus) < 0) {
    return;
  }
  add_timeval(&rus.ru_utime, &rus.ru_stime, &(clock_Counters[ClockCounter]));
#endif /* CLOCK_NO_TIMING */
}


void clock_StopPassedTime(CLOCK_CLOCKS ClockCounter) 
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  Stores the number of seconds passed since given
           counter was started in the according
           accumulator.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  clock_Akku[ClockCounter] = clock_GetSeconds(ClockCounter);
#endif
}


void clock_StopAddPassedTime(CLOCK_CLOCKS ClockCounter) 
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  Adds the number of seconds passed since given
           counter was started to the according
           accumulator.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  clock_Akku[ClockCounter] += clock_GetSeconds(ClockCounter);
#endif
}


double clock_GetSeconds(CLOCK_CLOCKS ClockCounter)
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  Computes the number of seconds spent by the
           counter.
  RETURNS: The number of seconds spent by the counter as
           a float.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  CLOCK_TMS difference;
  CLOCK_TMS newtime;
  struct rusage rus;
  
  if(getrusage(RUSAGE_SELF, &rus) < 0) {
    return 0;
  }
  add_timeval(&rus.ru_utime, &rus.ru_stime, &newtime);
  subtract_timeval(&newtime, &clock_Counters[ClockCounter], &difference);

  return ((double) difference.tv_sec
          + (difference.tv_usec /(double)ONE_MILLION));

#else /* CLOCK_NO_TIMING */
  return 0;
#endif /* ! CLOCK_NO_TIMING */
}

void clock_PrintTime(CLOCK_CLOCKS ClockCounter)
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  The time is printed in format hh:mm:ss.dd to stdout
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  unsigned long   hours, minutes;
  double seconds;

  seconds   = clock_Akku[ClockCounter];
  hours     = seconds/3600;
  seconds  -= hours*3600;
  minutes   = seconds/60;
  seconds  -= minutes*60;
  if (seconds >= 10.0)
    printf("%lu:%02lu:%2.2f (%gs)", hours, minutes, seconds, clock_Akku[ClockCounter]);
  else
    printf("%lu:%02lu:0%2.2f (%gs)", hours, minutes, seconds, clock_Akku[ClockCounter]);
#else
  fputs(" No Timing on this machine. ",stdout);
#endif
}
