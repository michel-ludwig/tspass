/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     CLOCK                              * */
/* *                                                        * */
/* *  $Module:   CLOCK                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1999, 2001                  * */
/* *  MPI fuer Informatik                                   * */
/* *                                                        * */
/* *  Copyright (C) 2008-2009                               * */
/* *  Michel Ludwig (michel.ludwig@liverpool.ac.uk)         * */
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
/* $Revision: 1.3 $                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


#ifndef _CLOCK_
#define _CLOCK_

// #include "gettimeofday.h"
#include "misc.h"
#include <sys/types.h>
#include <sys/time.h>

typedef enum {
  clock_BACKTRACK,
  clock_OVERALL,
  clock_INPUT,
  clock_CNF,
  clock_REDUCTION,
  clock_INFERENCE,
  clock_TRANSL,
  clock_MODELCONSTRUCTION,
  clock_TYPESIZE
} CLOCK_CLOCKS;


typedef struct timeval CLOCK_TMS;

void   clock_Init(void);
void   clock_InitCounter(CLOCK_CLOCKS);
void   clock_StartCounter(CLOCK_CLOCKS);
void   clock_StopPassedTime(CLOCK_CLOCKS);
void   clock_StopAddPassedTime(CLOCK_CLOCKS);
double  clock_GetSeconds(CLOCK_CLOCKS);
void   clock_PrintTime(CLOCK_CLOCKS);

#endif
