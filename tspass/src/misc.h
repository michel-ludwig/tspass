/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                MISCELLANEOUS                           * */
/* *                                                        * */
/* *  $Module:   MISC                                       * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000, 2001      * */
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
/* $Revision: 1.11 $                                       * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/



#ifndef _MISC_
#define _MISC_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#define __USE_FIXED_PROTOTYPES__

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <limits.h>
#include <stdarg.h>

#include "version.h"

/**************************************************************/
/* More basic types and macros                                */
/**************************************************************/

#if defined(TRUE)
#undef TRUE
#endif

#if defined(FALSE)
#undef FALSE
#endif

#ifndef SEEK_END
#define SEEK_END 2
#endif


#define misc_ERROROUT     stderr
#define misc_USERERROROUT stderr

typedef enum { FALSE=0, TRUE=1 } BOOL;

typedef void*           POINTER;
typedef unsigned int    NAT;

/* Limits for EARL data types */
#define NAT_MAX UINT_MAX


/**************************************************************/
/* Inline Functions                                           */
/**************************************************************/

static __inline__ void misc_Error(void)
{
  fflush(misc_USERERROROUT);
  fflush(stdout);
  fflush(stderr);
#ifdef CHECK
  abort();
#else
  exit(EXIT_FAILURE);
#endif
}

static __inline__ BOOL misc_SmallerThan(int i, int j)
{
  return (BOOL)(i < j);
}

#define misc_StartErrorReport()        misc_StartErrorReporting(__FILE__,__LINE__)
#define misc_StartUserErrorReport()    fflush(stdout)
#define misc_FinishUserErrorReport()   misc_Error()

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

void  misc_StartErrorReporting(const char*, int);
void  misc_FinishErrorReport(void);
void  misc_ErrorReport(const char * , ...);
void  misc_UserErrorReport(const char * , ...);

void  misc_PrintChar(NAT Number, char Character);
void  misc_DumpCore(void);
void  misc_DumpCoreOut(const char*);
int   misc_ReturnValue(void);
int   misc_Max(int, int);

FILE* misc_OpenFile(const char*, const char*);
void  misc_CloseFile(FILE*, const char*);

#ifdef __cplusplus
}
#endif

#endif
