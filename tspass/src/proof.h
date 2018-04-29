/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                    PROOF SEARCH                        * */
/* *                                                        * */
/* *  $Module:   PROOF                                      * */
/* *                                                        * */
/* *  Copyright (C) 1997, 1998, 1999, 2000                  * */
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
/* $Revision: 1.1.1.1 $                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/



#ifndef _PROOF_H_
#define _PROOF_H_

#include "search.h"
#include "list.h"
#include "flags.h"

PROOFSEARCH proof_ProofSearch(PROOFSEARCH Search, LIST ProblemClauses,
          FLAGSTORE InputFlags, LIST UserPrecedence, 
                                   int *BoundApplied, BOOL NativeClauseInput);

#endif

