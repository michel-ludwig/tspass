/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *        SCANNER FOR SPASS INTERACTIVE MODULE            * */
/* *                                                        * */
/* *  $Module:   KIV                                        * */ 
/* *                                                        * */
/* *  Copyright (C) 1997, 1998, 1999, 2001                  * */
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


/* $RCSfile: iascanner.l,v $ */

%{

#include <ctype.h>   /* for isprint */
#include <errno.h>
#include "misc.h"
#include "memory.h"
#include "symbol.h"
#include "term.h"
#include "ia.h"
#include "iaparser.h"

extern NAT dfg_LINENUMBER;  /* defined in dfgparser.y */

%}

%option noyywrap
/* Force the scanner to read the input character by character */
%option always-interactive
%option nounput

%%

and				return IA_AND;
equal				return IA_EQUAL;
equiv				return IA_EQUIV;
exists				return IA_EXISTS;
false				return IA_FALSE;
forall				return IA_FORALL;
implied				return IA_IMPLIED;
implies				return IA_IMPLIES;
not				return IA_NOT;
or				return IA_OR;
true				return IA_TRUE;
prove				return IA_PROVE;
[0-9]+				{ unsigned long n;
                                  errno = 0;
                                  n = strtoul(yytext, NULL, 10);
				  if (errno != 0 || n > INT_MAX) {
                                    misc_StartUserErrorReport();
                                    misc_UserErrorReport("\n Number too big in line %d.\n",
							 dfg_LINENUMBER);
                                    misc_FinishUserErrorReport();
                                  }
                                  ia_lval.number = (int) n;
                                  return IA_NUM;
                                }
[a-zA-Z0-9_]+			{ ia_lval.string = (char*) memory_Malloc(yyleng+1);
				  strcpy(ia_lval.string, yytext);
                                  return IA_ID;
                                }
[ \t]+				/* ignore */
"\n"				dfg_LINENUMBER++;
[-()\[\],\.]			return yytext[0];
.				{ misc_StartUserErrorReport();
                                  misc_UserErrorReport("\n Illegal character '");
				  if (isprint((int)yytext[0]))
				    misc_UserErrorReport("%c",yytext[0]);
				  else
				    misc_UserErrorReport("\\x%x", (unsigned int) yytext[0]);
				  misc_UserErrorReport("' in line %d.\n", dfg_LINENUMBER);
                                  misc_FinishUserErrorReport();
                                }

%%
