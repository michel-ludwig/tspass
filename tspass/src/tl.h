/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     TEMPORAL LOGIC                     * */
/* *                                                        * */
/* *  Copyright (C) 2008-2011                               * */
/* *  Michel Ludwig (michel.ludwig@gmail.com)               * */
/* *  University of Liverpool                               * */
/* *                                                        * */
/* *  This program is free software; you can redistribute   * */
/* *  it and/or modify it under the terms of the GNU        * */
/* *  General Public License as published by the Free       * */
/* *  Software Foundation; either version 3 of the License, * */
/* *  or (at your option) any later version.                * */
/* *                                                        * */
/* *  This program is distributed in the hope that it will  * */
/* *  be useful, but WITHOUT ANY WARRANTY; without even     * */
/* *  the implied warranty of MERCHANTABILITY or FITNESS    * */
/* *  FOR A PARTICULAR PURPOSE.  See the GNU General Public * */
/* *  License for more details.                             * */
/* *                                                        * */
/* *  You should have received a copy of the GNU General    * */
/* *  Public License along with this program; if not, see   * */
/* *  <http://www.gnu.org/licenses/>.                       * */
/* *                                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

#ifndef _TL_H_
#define _TL_H_

#include "clause.h"
#include "flags.h"
#include "foldfg.h"
#include "list.h"
#include "search.h"
#include "term.h"

/**************************************************************/
/* Global Variables and Constants (Only seen by macros)       */
/**************************************************************/

extern SYMBOL  tl_ALWAYS;
extern SYMBOL  tl_SOMETIME;
extern SYMBOL  tl_NEXT;
extern SYMBOL  tl_LOOPSEARCHCONSTANT;
extern SYMBOL  tl_TEMP_SUCC;
extern SYMBOL  tl_ZERO;

/**************************************************************/
/* Access to the first-order symbols.                         */
/**************************************************************/

static __inline__ SYMBOL tl_Always(void)
{
  return tl_ALWAYS;
}

static __inline__ SYMBOL tl_Next(void)
{
  return tl_NEXT;
}

static __inline__ SYMBOL tl_Sometime(void)
{
  return tl_SOMETIME;
}

static __inline__ SYMBOL tl_LoopSearchConstant(void)
{
  return tl_LOOPSEARCHCONSTANT;
}

static __inline__ SYMBOL tl_TemporalZeroConstant(void)
{
  return tl_ZERO;
}

static __inline__ SYMBOL tl_TemporalSuccessorFunction(void)
{
  return tl_TEMP_SUCC;
}

/**************************************************************/
/* */
/**************************************************************/

static __inline__ SYMBOL tl_TemporalVariable(TERM Atom)
{
  TERM FirstArgument;
  SYMBOL TopSymbol;

  if(!term_IsComplex(Atom)) {
    return symbol_Null();
  }
  FirstArgument = term_FirstArgument(Atom);
  TopSymbol = term_TopSymbol(FirstArgument);

  if(symbol_IsVariable(TopSymbol)) {
    return TopSymbol;
  }
  else if(symbol_Equal(TopSymbol, tl_TemporalZeroConstant())) {
    return symbol_Null();
  }
  else { // step atom
    return term_TopSymbol(term_FirstArgument(FirstArgument));
  }
}

/*
 * 't' must not contain a sign, i.e. be negated.
 */
static __inline__ BOOL tl_IsUniversalAtom(TERM t)
{
  return (term_IsComplex(t) && term_IsVariable(term_FirstArgument(t)));
}

/*
 * 't' must not contain a sign, i.e. be negated.
 */
static __inline__ BOOL tl_IsLoopSearchMarkerAtom(TERM t)
{
  return (!term_IsComplex(t));
}

/*
 * 't' must not contain a sign, i.e. be negated.
 */
static __inline__ BOOL tl_IsInitialAtom(TERM t)
{
  return (term_IsComplex(t)
      && symbol_Equal(term_TopSymbol(term_FirstArgument(t)), tl_TemporalZeroConstant()));
}

static __inline__ BOOL tl_IsUniversalClause(CLAUSE Clause)
{
  for(int i = clause_FirstLitIndex(); i <= clause_LastAntecedentLitIndex(Clause); ++i) {
    TERM Term = clause_LiteralAtom(clause_GetLiteral(Clause, i));
    if(!tl_IsUniversalAtom(Term)) {
      return FALSE;
    }
  }
  return TRUE;
}

static __inline__ BOOL tl_IsLoopSearchClause(CLAUSE Clause)
{
  for(int i = clause_FirstLitIndex(); i <= clause_LastAntecedentLitIndex(Clause); ++i) {
    TERM Term = clause_LiteralAtom(clause_GetLiteral(Clause, i));
    if(tl_IsLoopSearchMarkerAtom(Term)) {
      return TRUE;
    }
  }
  return FALSE;
}

BOOL tl_IsStepAtom(TERM t);

static __inline__ BOOL tl_IsUniversalLiteral(LITERAL l)
{
  return tl_IsUniversalAtom(clause_LiteralAtom(l));
}

static __inline__ BOOL tl_IsStepLiteral(LITERAL l)
{
  return tl_IsStepAtom(clause_LiteralAtom(l));
}

/* A step clause must
   - use the same temporal variable
   - contain at least one step atom
   - only contain negative universal atoms
   - every other atom must be a step atom
 */
static __inline__ BOOL tl_IsStepClause(CLAUSE Clause)
{
  BOOL containsStepAtom;
  SYMBOL temporalVariable = symbol_Null();

  if(clause_NumOfConsLits(Clause) != 0) {
    return FALSE;
  }

  for(int i = clause_FirstAntecedentLitIndex(Clause); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);

    /* the only non-complex terms are loop search markers, and are ignored */
    if(term_IsComplex(Atom)) {

      if(tl_IsUniversalAtom(Atom)) {
        if(i > clause_LastAntecedentLitIndex(Clause)) {
          return FALSE;
        }
      }
      else if(!tl_IsStepAtom(Atom)) {
        return FALSE;
      }
      else {
        containsStepAtom = TRUE;
      }

      if(symbol_Equal(temporalVariable, symbol_Null())) {
        temporalVariable = tl_TemporalVariable(Atom);
      }
      else if(!symbol_Equal(temporalVariable, tl_TemporalVariable(Atom))) {
        return FALSE;
      }
    }
  }

  return containsStepAtom;
}


/* A terminating step clause must
   - use the same temporal variable
   - only contain negative universal atoms
   - no other literals
 */
static __inline__ BOOL tl_IsTerminatingStepClause(CLAUSE Clause)
{
  NAT i;
  SYMBOL temporalVariable = symbol_Null();
  
  if(!(clause_NumOfConsLits(Clause) == 0 && clause_NumOfSuccLits(Clause) == 0)) {
    return FALSE;
  }

  for(i = clause_FirstAntecedentLitIndex(Clause); i <= clause_LastAntecedentLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);

    /* the only non-complex terms are loop search markers */
    if(term_IsComplex(Atom)) {
      if(!tl_IsUniversalLiteral(Lit)) {
        return FALSE;
      }
      if(symbol_Equal(temporalVariable, symbol_Null())) {
        temporalVariable = tl_TemporalVariable(Atom);
      }
      else if(!symbol_Equal(temporalVariable, tl_TemporalVariable(Atom))) {
        return FALSE;
      }
    }
  }
  return TRUE;
}

static __inline__ BOOL tl_ContainsExactlyOneLoopSearchMarker(CLAUSE Clause,
                                                             LITERAL* MarkerLiteral)
{
  BOOL LoopSearchMarkerFound = FALSE;
  
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);    

    /* the only non-complex terms are loop search markers */
    if(!term_IsComplex(Atom)) {
      if(LoopSearchMarkerFound) {
        if(MarkerLiteral) {
          *MarkerLiteral = NULL;
        }
        return FALSE;
      }
      else {
        LoopSearchMarkerFound = TRUE;
        if(MarkerLiteral) {
          *MarkerLiteral = Lit;
        }
      }
    }
  }
  if(!LoopSearchMarkerFound) {
    if(MarkerLiteral) {
      *MarkerLiteral = NULL;
    }
    return FALSE;
  }
  return TRUE;
}

static __inline__ BOOL tl_IsTemporalOperator(TERM t)
{
  SYMBOL TopSymbol = term_TopSymbol(t);
  return (TopSymbol == tl_Always() || TopSymbol == tl_Next() || TopSymbol == tl_Sometime());
}

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void tl_Init(PRECEDENCE);
void tl_Free(void);

void tl_TranslateToFOL(LIST ClauseList, BOOL* predicateMap, FLAGSTORE Flags, PRECEDENCE Precedence, BOOL UniversalClauses);

void tl_InitEventualityInformation(LIST eventualitiesList, PRECEDENCE precedence);
void tl_DeleteEventualityInformation(NAT numEventualities);

void tl_CreateLoopSearchMarker(NAT i, CLAUSE eventualityClause, PRECEDENCE precedence);

CLAUSE tl_CreateLoopSearchStepClause(NAT i, CLAUSE eventualityClause, LIST litList, FLAGSTORE flags, PRECEDENCE precedence);

CLAUSE tl_CreateNextLoopSearchStepClause(CLAUSE terminatingLoopSearchClause, LITERAL loopSearchMarkerLiteral, FLAGSTORE flags, PRECEDENCE precedence);

BOOL tl_ContainsLoopSearchMarker(CLAUSE Clause);

BOOL tl_ContainsLoopSearchMarkerForEventuality(CLAUSE eventualityClause, CLAUSE Clause, LITERAL* loopSearchMarkerLiteral);

void tl_AttachProofSearch(PROOFSEARCH Search);

void tl_ComputeTemporalOrdering(LIST InputClauses, FLAGSTORE Flags);

LIST tl_PerformConstantFlooding(LIST ClauseList, LIST ConstantList, FLAGSTORE Flags);

BOOL tl_IsMostMonadicNegativeUniversalClause(CLAUSE Clause);

BOOL tl_ContainsTemporalOperator(TERM t);

typedef enum {INITIAL_FORMULA, UNIVERSAL_FORMULA, STEP_FORMULA,
              EVENTUALITY_FORMULA, UNDEFINED} DSNF_TYPE;

DSNF_TYPE tl_FormulaType(TERM t);

static __inline__ BOOL tl_IsInitialFormula(TERM t)
{
  return (tl_FormulaType(t) == INITIAL_FORMULA);
}

static __inline__ BOOL tl_IsUniversalFormula(TERM t)
{
  return (tl_FormulaType(t) == UNIVERSAL_FORMULA);
}

static __inline__ BOOL tl_IsEventualityFormula(TERM t)
{
  return (tl_FormulaType(t) == EVENTUALITY_FORMULA);
}

CLAUSE tl_ClausifyAndTemporaliseStepFormula(TERM t, BOOL* predicateMap, FLAGSTORE Flags, PRECEDENCE Precedence);

CLAUSE tl_ClausifyAndTemporaliseEventualityFormula(TERM EventualityFormula, BOOL* predicateMap, BOOL* Unsatisfiable,
                                                   FLAGSTORE Flags, PRECEDENCE Precedence);

LIST tl_ListOfConstants(LIST ClauseList);

LIST tl_PerformLoopSearchTests(CLAUSE EventualityClause, PROOFSEARCH Search);

CLAUSE tl_SimplifyLoopSearchMarkers(PROOFSEARCH Search, CLAUSE Clause, FLAGSTORE Flags,
                                    PRECEDENCE Precedence);

void tl_PrintLoopSearchClausesUpTo(LITERAL MarkerLiteral, SHARED_INDEX index);

LIST tl_GetClausesWithSmallerLoopSearchIndex(LITERAL MarkerLiteral, SHARED_INDEX index);

BOOL tl_UsableContainsUniversalClauses(PROOFSEARCH Search);

CLAUSE tl_FindUsableUniversalClause(PROOFSEARCH Search);

CLAUSE tl_FindUsableNonLoopSearchClause(PROOFSEARCH Search);

CLAUSE tl_FindUsableLoopSearchClause(PROOFSEARCH Search);

TEMPORAL_TYPE tl_DetermineTemporalType(CLAUSE Clause);

void tl_EnsureNoUniversalLiteralIsMaximal(CLAUSE StepClause);

//**************************************** Model Construction ****************************************//

static __inline__ BOOL tl_IsPLTLLiteral(LITERAL Lit)
{
  return (list_Length(term_ArgumentList(clause_LiteralAtom(Lit))) <= 1);
}

static __inline__ BOOL tl_IsPLTLClause(CLAUSE Clause)
{
  if(clause_NumOfConsLits(Clause) != 0) {
    return FALSE;
  }
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    if(!tl_IsPLTLLiteral(Lit)) {
      return FALSE;
    }
  }
  return TRUE;
}

/**
 * CAUTION: 'List' must be a list of step clauses.
 **/
LIST tl_ListOfSymbolsFromLeftHandSides(LIST List);

void tl_ConstructModel(PROOFSEARCH Search, FLAGSTORE Flags, LIST ListOfLeftHandSideSymbols);

#endif
