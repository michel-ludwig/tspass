/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     ALARM                              * */
/* *                                                        * */
/* *  $Module:   ALARM                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 2006                                    * */
/* *  MPI fuer Informatik                                   * */
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



/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "alarm.h"

/**************************************************************/
/* Globals                                                    */
/**************************************************************/

static int alarm_TIMEOUT;  /* Set to 1 if the SPASS time polling detects out of time, we
		      do not use BOOL because of Windows incompatability*/

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

static void alarm_OutOfTime(void)
/**************************************************************
  INPUT:   The global alarm_TIMEOUT variable.
  RETURNS: None.
  EFFECT:  Exits the program unless alarm_TIMEOUT is TRUE, meaning
           that the SPASS mainloop has already detected the timeout.
***************************************************************/
{
  if (alarm_TIMEOUT != 1) {
    printf("\nTSPASS %s ", vrs_VERSION);
    puts("\nSPASS beiseite: Ran out of time. TSPASS was killed.\n");
    exit(EXIT_FAILURE);
  }
}

static void alarm_SigHandler(int Signal)
/**************************************************************
  INPUT:   A signal.
  RETURNS: None.
  EFFECT:  Calls the handler for the signal.
***************************************************************/
{
  if (Signal == SIGALRM)
    alarm_OutOfTime();
}

void alarm_Init(void)
/*********************************************************
  INPUT:   None.
  EFFECT:  Initializes the alarm module.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
  alarm_TIMEOUT = 0;
  signal(SIGALRM, alarm_SigHandler);
}

void alarm_Off(void)
/*********************************************************
  INPUT:   None.
  EFFECT:  Turns off the alarm module.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
  alarm_TIMEOUT = 1;
}


void alarm_SetAlarm(int Seconds)
/**************************************************************
  INPUT:   A duration in seconds.
  RETURNS: None.
  EFFECT:  Starts an alarm that will triger after duration 
           seconds.
***************************************************************/
{
  alarm(Seconds);
}
