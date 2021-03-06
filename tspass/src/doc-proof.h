/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                 PROOF DOCUMENTATION                    * */
/* *                                                        * */
/* *  $Module:   DOCPROOF                                   * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 2000, 2001            * */
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
/* $Revision: 1.1.1.1 $                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/



#ifndef _DOC_PROOF_
#define _DOC_PROOF_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "clause.h"
#include "st.h"
#include "sharing.h"
#include "search.h"
#include "doc-proof.h"
#include "proofcheck.h"

/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

extern int dp_DEPTH;


/**************************************************************/
/* Macros                                                     */
/**************************************************************/ 

static __inline__ int dp_ProofDepth(void)
{
  return dp_DEPTH;
}

static __inline__ void dp_SetProofDepth(int Depth)
{
  dp_DEPTH = Depth;
}


/**************************************************************/
/* Functions                                                  */
/**************************************************************/        

void dp_Init(void);
LIST dp_PrintProof(PROOFSEARCH, LIST, const char*);

#endif
