/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     SUBSUMPTION                        * */
/* *                                                        * */
/* *  $Module:   SUBSUMPTION                                * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1999, 2000                  * */
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
/* $Revision: 1.2 $                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/




#ifndef _SUBSUMPTION_
#define _SUBSUMPTION_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "list.h"
#include "misc.h"
#include "unify.h"
#include "component.h"
#include "vector.h"
#include "clause.h"

/**************************************************************/
/* Functions                                                 */
/**************************************************************/

static __inline__ int subs_NoException(void)
{
  return -1;
}

void subs_Init(void);
void subs_Free(void);
BOOL subs_Subsumes(CLAUSE, CLAUSE, int, int);
BOOL subs_SubsumesBasic(CLAUSE, CLAUSE, int, int);
BOOL subs_SubsumesWithSignature(CLAUSE, CLAUSE, BOOL, LIST*);
BOOL subs_Idc(CLAUSE, CLAUSE);
BOOL subs_IdcRes(CLAUSE, int, int);
BOOL subs_IdcEq(CLAUSE, CLAUSE);
BOOL subs_IdcEqMatch(CLAUSE, CLAUSE, SUBST);
BOOL subs_IdcEqMatchExcept(CLAUSE, int, CLAUSE, int, SUBST);
#endif

