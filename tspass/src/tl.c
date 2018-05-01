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
#include "tl.h"

#include "assert.h"
#include "clock.h"
#include "cnf.h"
#include "foldfg.h"
#include "flags.h"
#include "hasharray.h"
#include "proof.h"
#include "search.h"


#define MAX(a,b) ((a) >= (b) ? (a) : (b))

SYMBOL tl_LOOPSEARCHCONSTANT;

SYMBOL  tl_ALWAYS;
SYMBOL  tl_NEXT;
SYMBOL  tl_SOMETIME;

SYMBOL  tl_SHIELD;
SYMBOL  tl_TEMP_SUCC;
SYMBOL  tl_ZERO;

LIST    tl_SYMBOLS;

HASH tl_POSITIVE_EVENTUALITY_HASH, tl_NEGATIVE_EVENTUALITY_HASH;

EVENTUALITY_INF* tl_EVENTUALITY_CONSTS;
NAT tl_LOOPSEARCH_MARKER_INDEX_MAP[symbol__MAXSIGNATURE]; /* a mapping from loop search marker to their loop
                                                             search indexes, i.e. s_i^L -> i*/
CLAUSE tl_LOOPSEARCH_MARKER_EVENTUALITY_MAP[symbol__MAXSIGNATURE]; /* a mapping from loop search marker to their eventuality
                                                                      clauses, i.e. s_i^L -> L */
/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  FUNCTIONS                                             * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

void tl_Init(PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A precedence.
  RETURNS: Nothing.
  SUMMARY: Initializes the Temporal Logic Module.
  EFFECTS: The precedence of the temporal logic symbols is set
	   in <Precedence>.
  CAUTION: MUST BE CALLED BEFORE ANY OTHER tl-FUNCTION.
***************************************************************/
{ 
  tl_LOOPSEARCHCONSTANT = symbol_CreateFunction("c^l", 0, symbol_STATLEX, Precedence);

  tl_ALWAYS   = symbol_CreateJunctor("always", 1, symbol_STATLEX, Precedence);
  tl_NEXT     = symbol_CreateJunctor("next", 1, symbol_STATLEX, Precedence);
  tl_SOMETIME = symbol_CreateJunctor("sometime", 1, symbol_STATLEX, Precedence);

  tl_TEMP_SUCC = symbol_CreateFunction("temp_succ", 1, symbol_STATLEX, Precedence);
  tl_SHIELD    = symbol_CreateFunction("temp_shield", 1, symbol_STATLEX, Precedence);
  tl_ZERO      = symbol_CreateFunction("temp_zero", 0, symbol_STATLEX, Precedence);

  tl_SYMBOLS =
    list_Cons((POINTER)tl_LOOPSEARCHCONSTANT, list_Cons((POINTER)tl_ALWAYS,
                                              list_Cons((POINTER)tl_NEXT,
                                              list_Cons((POINTER)tl_TEMP_SUCC,
                                              list_Cons((POINTER)tl_SHIELD,
                                              list_Cons((POINTER)tl_ZERO,
                                              list_List((POINTER)tl_SOMETIME)))))));
}

void tl_Free(void)
/**************************************************************
  INPUT:   None.
  RETURNS: void.
  EFFECT:  The tl related memory used by the tl module is freed.
***************************************************************/
{
  list_Delete(tl_SYMBOLS);
}

typedef enum {INITIAL_TRANSFORMATION, UNIVERSAL_TRANSFORMATION, STEP_TRANSFORMATION}
     TRANSFORMATION_TYPE;

void tl_TransformPredicateToFOL(TERM term, BOOL* predicateMap, TRANSFORMATION_TYPE Type,
                                SYMBOL FreeVariable)
{
  SYMBOL PredicateSymbol = symbol_Null();
  TERM NewTerm = NULL;
  SYMBOL Symbol = tl_ZERO;

#ifdef CHECK
  assert(term_IsAtom(term));
#endif

  PredicateSymbol = term_TopSymbol(term);

  if((PredicateSymbol == fol_True()) || (PredicateSymbol == fol_False())) {
    return;
  }

  switch(Type) {
    case UNIVERSAL_TRANSFORMATION:
      Symbol = FreeVariable; // fall through here
    case INITIAL_TRANSFORMATION:
      NewTerm = term_Create(Symbol, list_Nil());
    break;
    case STEP_TRANSFORMATION:
      NewTerm = term_Create(tl_TEMP_SUCC, list_List(term_Create(FreeVariable, list_Nil())));
    break;
  }

  if(!predicateMap[symbol_Index(PredicateSymbol)]) {
    symbol_SetArity(PredicateSymbol, symbol_Arity(PredicateSymbol) + 1);
    predicateMap[symbol_Index(PredicateSymbol)] = TRUE;
  }

  term_RplacArgumentList(term, list_Nconc(list_List(NewTerm),
                                          term_ArgumentList(term)));
}

/**
 * 'VariableList' is actually supposed to be a list of variable terms(!).
 **/
SYMBOL tl_FindFreeVariable(LIST VariableList)
{
  LIST VariableSymbolList = list_Nil();
  SYMBOL toReturn = 1;
  for(LIST Scan = VariableList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    VariableSymbolList = list_Cons((POINTER) term_TopSymbol((TERM) list_Car(Scan)),
                                   VariableSymbolList);
  }

  VariableSymbolList = list_Sort(VariableSymbolList, (BOOL (*)(POINTER, POINTER)) symbol_LessVariable);

  for(LIST Scan = VariableSymbolList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Var = (SYMBOL) list_Car(Scan);

    if(toReturn < Var) {
      break;
    }
    else if(toReturn == Var) {
      toReturn = Var + 1;
    }
  }

  list_Delete(VariableSymbolList);
  return toReturn;
}

void tl_TranslateClauseToFOL(CLAUSE Clause, BOOL* predicateMap, BOOL UniversalClauses,
                             FLAGSTORE Flags, PRECEDENCE Precedence)
{
  LIST VariableList = list_Nil();
  SYMBOL FreeVariable = symbol_Null();

  if(UniversalClauses) {
    VariableList = clause_ListOfVariables(Clause);
    FreeVariable = tl_FindFreeVariable(VariableList);
  }

  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);
    TRANSFORMATION_TYPE Type = (UniversalClauses ? UNIVERSAL_TRANSFORMATION
                                                 : INITIAL_TRANSFORMATION);

    tl_TransformPredicateToFOL(Atom, predicateMap, Type, FreeVariable);
  }
  list_Delete(VariableList);
  clause_OrientAndReInit(Clause, Flags, Precedence);
}

void tl_TranslateToFOL(LIST ClauseList, BOOL* predicateMap, FLAGSTORE Flags, PRECEDENCE Precedence,
                       BOOL UniversalClauses)
{
  if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    printf("\n------------------TEMPORAL-LOGIC-TRANSLATION-START-----------------------");
    if(UniversalClauses) {
      printf("\nFor universal clauses:");
    }
    else {
      printf("\nFor initial clauses:");
    }
  }

  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);

    if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
      printf("\n");
      clause_Print(Clause);
      printf("   ");
    }
    tl_TranslateClauseToFOL(Clause, predicateMap, UniversalClauses,
                            Flags, Precedence);
    if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
      printf(" -> ");
      clause_Print(Clause);
    }
  }

  if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    printf("\n------------------TEMPORAL-LOGIC-TRANSLATION-STOP------------------------");
  }
}

/**
 * 'Clause' must be an eventuality clause.
 **/
static __inline__ TERM tl_GetEventualityTerm(CLAUSE Clause)
{
  #ifdef CHECK
  if(clause_Length(Clause) != 1 || clause_NumOfConsLits(Clause) != 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_GetEventualityTerm:");
    misc_ErrorReport("\n Illegal input clause: not an eventuality.");
    misc_FinishErrorReport();
  }
#endif
  return ((clause_NumOfAnteLits(Clause) == 0) ? clause_LiteralSignedAtom(clause_FirstSuccedentLit(Clause))
                                              : clause_LiteralSignedAtom(clause_FirstAntecedentLit(Clause)));
}

/**
 * 't' must be an eventuality term.
 **/
EVENTUALITY_INF* tl_GetEventualityInformation(TERM t)
{
  BOOL NegativeEventuality = symbol_Equal(term_TopSymbol(t), fol_Not());
  t = (NegativeEventuality ? term_FirstArgument(t) : t);
  HASH RootHash = (NegativeEventuality ? tl_NEGATIVE_EVENTUALITY_HASH
                                       : tl_POSITIVE_EVENTUALITY_HASH);
  unsigned int RootKey = symbol_Index(term_TopSymbol(t));
  unsigned int SecondKey;
  LIST SecondHashList = hsh_Get(RootHash, (POINTER) RootKey);
  LIST EventualityList;
  HASH SecondHash;
  TERM SecondTerm;

  if(list_Empty(SecondHashList)) {
#ifdef CHECK
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_GetEventualityInformation:");
    misc_ErrorReport("\n Eventuality not found.");
    misc_FinishErrorReport();
#endif
    return NULL;
  }
  else {
    SecondHash = (HASH) list_First(SecondHashList);
  }

  if(list_Length(term_ArgumentList(t)) == 2) {
    SecondTerm = term_SecondArgument(t);
  }
  else {
      SecondTerm = term_FirstArgument(t);
  }
  SecondKey = ((list_Length(term_ArgumentList(t)) == 1 || symbol_Equal(term_TopSymbol(SecondTerm), tl_LOOPSEARCHCONSTANT)
                                                       || symbol_IsVariable(term_TopSymbol(SecondTerm)))
                                                      ? symbol_Null()
                                                      : symbol_Index(term_TopSymbol(SecondTerm))); // temporal variable comes first
  EventualityList = hsh_Get(SecondHash, (POINTER) SecondKey);
  if(list_Empty(EventualityList)) {
#ifdef CHECK
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_GetEventualityInformation:");
    misc_ErrorReport("\n Eventuality not found.");
    misc_FinishErrorReport();
#endif
    return NULL;
  }
  else {
    return (EVENTUALITY_INF*) list_First(EventualityList);
  }
}

void tl_AddEventualityInformation(TERM t, EVENTUALITY_INF* inf)
{
  BOOL NegativeEventuality = symbol_Equal(term_TopSymbol(t), fol_Not());
  t = (NegativeEventuality ? term_FirstArgument(t) : t);
  HASH RootHash = (NegativeEventuality ? tl_NEGATIVE_EVENTUALITY_HASH
                                       : tl_POSITIVE_EVENTUALITY_HASH);
  unsigned int RootKey = symbol_Index(term_TopSymbol(t));
  unsigned int SecondKey;
  LIST SecondHashList = hsh_Get(RootHash, (POINTER) RootKey);
  LIST EventualityList;
  HASH SecondHash;
  BOOL SecondHashFound = FALSE;
  TERM SecondTerm;

  for(LIST Scan = SecondHashList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST Pair = list_Car(Scan);

    if(list_PairFirst(Pair) == (POINTER) RootKey) {
      SecondHashFound = TRUE;
      break;
    }
  }

  if(list_Empty(SecondHashList)) {
    SecondHash = hsh_Create();
    hsh_Put(RootHash, (POINTER) RootKey, SecondHash);
  }
  else {
      SecondHash = (HASH) list_First(SecondHashList);
  }
  if(list_Length(term_ArgumentList(t)) == 2) {
    SecondTerm = term_SecondArgument(t);
  }
  else {
      SecondTerm = term_FirstArgument(t);
  }
  SecondKey = ((list_Length(term_ArgumentList(t)) == 1 || symbol_Equal(term_TopSymbol(SecondTerm), tl_LOOPSEARCHCONSTANT)
                                                       || symbol_IsVariable(term_TopSymbol(SecondTerm)))
                                                      ? symbol_Null()
                                                      : symbol_Index(term_TopSymbol(SecondTerm))); // temporal variable comes first
  EventualityList = hsh_Get(SecondHash, (POINTER) SecondKey);

  if(list_Empty(EventualityList)) {
    hsh_Put(SecondHash, (POINTER) SecondKey, inf);
  }
  else {
#ifdef CHECK
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_AddEventualityInformation:");
    misc_ErrorReport("\n An entry for this eventuality exists already.");
    misc_FinishErrorReport();
#endif
  }
}

static __inline__ SYMBOL tl_GetEventualitySymbol(CLAUSE Clause)
{
#ifdef CHECK
  if(clause_Length(Clause) != 1 || clause_NumOfConsLits(Clause) != 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_GetEventualitySymbol:");
    misc_ErrorReport("\n Illegal input clause: not an eventuality.");
    misc_FinishErrorReport();
  }
#endif
  return ((clause_NumOfAnteLits(Clause) == 0) ? clause_LiteralPredicate(clause_FirstSuccedentLit(Clause))
                                              : clause_LiteralPredicate(clause_FirstAntecedentLit(Clause)));
}

static __inline__ LITERAL tl_GetEventualityLiteral(CLAUSE Clause)
{
#ifdef CHECK
  if(clause_Length(Clause) != 1 || clause_NumOfConsLits(Clause) != 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_GetEventualityLiteral:");
    misc_ErrorReport("\n Illegal input clause: not an eventuality.");
    misc_FinishErrorReport();
  }
#endif
  return ((clause_NumOfAnteLits(Clause) == 0) ? clause_FirstSuccedentLit(Clause)
                                              : clause_FirstAntecedentLit(Clause));
}

BOOL tl_IsStepAtom(TERM t)
{
  TERM firstArgument;

  if(!term_IsComplex(t)) {
    return FALSE;
  }
  firstArgument = term_FirstArgument(t);
  if(!term_IsComplex(firstArgument)) {
    return FALSE;
  }

  return (term_TopSymbol(firstArgument) == tl_TEMP_SUCC && term_IsVariable(term_FirstArgument(firstArgument)));
}


SYMBOL tl_CreateLoopSearchConstant(SYMBOL EventualitySymbol, PRECEDENCE Precedence)
{
  char Name[symbol__SYMBOLMAXLEN];

  snprintf(Name, sizeof(Name) - 1, "c(%s)", symbol_Name(EventualitySymbol));
  return symbol_CreateFunction(Name, 0, symbol_STATMUL, Precedence);
}

/* <eventualitiesList> a list containing eventuality clauses */
void tl_InitEventualityInformation(LIST eventualitiesList, PRECEDENCE Precedence)
{
  unsigned int i;
  NAT numEventualities = list_Length(eventualitiesList);
  LIST Scan;
  tl_EVENTUALITY_CONSTS = (numEventualities == 0 ? NULL : memory_Malloc(numEventualities * sizeof(*tl_EVENTUALITY_CONSTS)));
  tl_POSITIVE_EVENTUALITY_HASH = hsh_Create();
  tl_NEGATIVE_EVENTUALITY_HASH = hsh_Create();
  i = 0;
  for(Scan = eventualitiesList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);
    SYMBOL Ev = tl_GetEventualitySymbol(Clause);
    tl_EVENTUALITY_CONSTS[i].eventualitySymbol = Ev;
    tl_EVENTUALITY_CONSTS[i].map = NULL;
    tl_EVENTUALITY_CONSTS[i].markerCount = 0;
    tl_EVENTUALITY_CONSTS[i].mapSize = 0;
    tl_AddEventualityInformation(tl_GetEventualityTerm(Clause), tl_EVENTUALITY_CONSTS + i);
    ++i;
  }
}

void tl_DeleteEventualityInformationHash(HASH h)
{
  LIST EntryList = hsh_GetAllEntries(h);

  for(LIST Scan = EntryList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    HASH h2 = (HASH) list_Car(Scan);

    hsh_Delete(h2);
  }
  list_Delete(EntryList);
  hsh_Delete(h);
}

void tl_DeleteEventualityInformation(NAT numEventualities)
{

  tl_DeleteEventualityInformationHash(tl_POSITIVE_EVENTUALITY_HASH);
  tl_DeleteEventualityInformationHash(tl_NEGATIVE_EVENTUALITY_HASH);

  for(unsigned int i = 0; i < numEventualities; ++i) {
    SYMBOL EventualitySymbol = tl_EVENTUALITY_CONSTS[i].eventualitySymbol;
    memory_Free(tl_EVENTUALITY_CONSTS[i].map,
                tl_EVENTUALITY_CONSTS[i].mapSize * sizeof(*tl_EVENTUALITY_CONSTS[i].map));
    if(!symbol_IsFreed(EventualitySymbol)) { // a symbol might be deleted twice if it appears
                                             // both in a negative and positive eventuality
      symbol_Delete(EventualitySymbol);
    }
  }
  if(numEventualities > 0) { // check necessary for SPASS's internal 'memory_Free' method
    memory_Free(tl_EVENTUALITY_CONSTS, numEventualities * sizeof(*tl_EVENTUALITY_CONSTS));
  }
}

void tl_AddLoopSearchSymbol(SYMBOL s, EVENTUALITY_INF *inf)
{
  if(!inf->map || inf->markerCount + 1 >= inf->mapSize) {
    /* we double the size of the map whenever it has become full */
    NAT NewSize = (inf->mapSize == 0) ? 1 : inf->mapSize * 2;
    SYMBOL* p = memory_Malloc(NewSize * sizeof(*(inf->map)));
    if(inf->map) {
      memcpy(p, inf->map, inf->mapSize * sizeof(*(inf->map)));
      memory_Free(inf->map, inf->mapSize * sizeof(*(inf->map)));
    }
    inf->map = p;
    inf->mapSize = NewSize;
  }
  inf->map[inf->markerCount] = s;
  ++inf->markerCount;
}

void tl_CreateLoopSearchMarker(NAT i, CLAUSE eventualityClause, PRECEDENCE precedence)
{
  SYMBOL NewMarkerSymbol, EventualitySymbol;
  TERM EventualityTerm = tl_GetEventualityTerm(eventualityClause);
  BOOL NegativeEventuality = symbol_Equal(term_TopSymbol(EventualityTerm), fol_Not());
  TERM SubTerm = NULL;
  EVENTUALITY_INF *EventualityInformation = tl_GetEventualityInformation(EventualityTerm);
  char* NotString = (NegativeEventuality ? "not-" : "");
  char Name[symbol__SYMBOLMAXLEN];
  char* SubTermName = "";
  
  if(NegativeEventuality) {
    EventualityTerm = term_FirstArgument(EventualityTerm);
  }
  EventualitySymbol = term_TopSymbol(EventualityTerm);
  SubTerm = (list_Length(term_ArgumentList(EventualityTerm)) == 2 ? term_SecondArgument(EventualityTerm)
                                                                  : NULL);
  if(SubTerm) {
    SYMBOL SubTermSymbol = term_TopSymbol(SubTerm);
    SubTermName = symbol_IsVariable(SubTermSymbol) ? "x" : symbol_Name(SubTermSymbol); 
  }

  if(SubTerm) {
    snprintf(Name, sizeof(Name), "s^%s%s(%s)_%i", NotString, symbol_Name(EventualitySymbol),
                                                  SubTermName, i);  
  }
  else {
    snprintf(Name, sizeof(Name), "s^%s%s_%i", NotString, symbol_Name(EventualitySymbol), i);
  }
  NewMarkerSymbol = symbol_CreatePredicate(Name, 0, symbol_STATMUL, precedence);
  /* Loop search markers have a weight of 0. */
  symbol_SetWeight(NewMarkerSymbol, 0);
  symbol_AddProperty(NewMarkerSymbol, LOOPSEARCHMARKER);
  tl_AddLoopSearchSymbol(NewMarkerSymbol, EventualityInformation);
  tl_LOOPSEARCH_MARKER_INDEX_MAP[symbol_Index(NewMarkerSymbol)] = i;
  tl_LOOPSEARCH_MARKER_EVENTUALITY_MAP[symbol_Index(NewMarkerSymbol)] = eventualityClause;
}

TERM tl_CreateStepTerm(SYMBOL variable)
{
  return term_Create(tl_TEMP_SUCC, list_List(term_Create(variable, list_Nil())));
}

static __inline__ void tl_MakeStepAtom(TERM Atom, SYMBOL variable)
{
  if(symbol_Equal(term_TopSymbol(Atom), fol_Not())) {
    Atom = term_FirstArgument(Atom);
  }
  
#ifdef CHECK
  if(list_Length(term_ArgumentList(Atom)) < 1) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_MakeStepAtom:");
    misc_ErrorReport("\n Illegal input. Literal with no arguments given.");
    misc_FinishErrorReport();
  }
#endif

  TERM TemporalArgument = term_FirstArgument(Atom);

  term_RplacFirstArgument(Atom, tl_CreateStepTerm(variable));
  term_Delete(TemporalArgument);
}

/**
 *   CAUTION: the marker with index i must already exist!
 **/
CLAUSE tl_CreateLoopSearchStepClause(NAT i, CLAUSE eventualityClause, LIST litList, FLAGSTORE flags,
                                                                      PRECEDENCE precedence)
{
  SYMBOL EventualitySymbol = tl_GetEventualitySymbol(eventualityClause);
  EVENTUALITY_INF *inf = tl_GetEventualityInformation(tl_GetEventualityTerm(eventualityClause));
  SYMBOL LoopSearchMarker = inf->map[i];
  SYMBOL LoopSearchConstant = tl_LoopSearchConstant();
  CLAUSE toReturn = NULL;
  LITERAL LoopSearchMarkerLit;
  LITERAL EventualityLit = clause_LiteralCopy(tl_GetEventualityLiteral(eventualityClause));
  BOOL PositiveEventualityLiteral = clause_LiteralIsPositive(EventualityLit);
  TERM EventualityAtom = clause_LiteralAtom(EventualityLit);
  LIST LiteralVariables = list_Nil();
  LIST Scan;
  int NumLits = list_Length(litList);
  int j;
  SYMBOL temporalVariableSymbol;

  /* Find a free temporal variable */
  for(LIST Scan = litList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM Atom = clause_LiteralAtom(list_Car(Scan));
    LiteralVariables = list_Nconc(term_VariableSymbols(Atom), LiteralVariables);
  }
  temporalVariableSymbol = symbol_FindUnusedVariable(LiteralVariables);
  list_Delete(LiteralVariables);

  toReturn = clause_CreateBody(NumLits + 1 + 1);
  clause_SetNumOfConsLits(toReturn, 0);
  clause_SetNumOfAnteLits(toReturn, NumLits + 1 + (PositiveEventualityLiteral ? 0 : 1));
  clause_SetNumOfSuccLits(toReturn, (PositiveEventualityLiteral ? 1 : 0));

  LoopSearchMarkerLit = clause_LiteralCreate(term_Create(fol_Not(),
                                                        list_List(term_Create(LoopSearchMarker,
                                                                  list_Nil()))),  toReturn);
#ifdef CHECK
  if(symbol_Arity(EventualitySymbol) == 0 || symbol_Arity(EventualitySymbol) > 2) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_CreateLoopSearchStepClause:");
    misc_ErrorReport("\n Illegal input. Eventuality symbol has wrong arity.");
    misc_FinishErrorReport();
  }
#endif
  if(symbol_Arity(EventualitySymbol) == 2
     && symbol_IsVariable(term_TopSymbol(term_SecondArgument(EventualityAtom)))) {
    TERM secondArgument = term_SecondArgument(EventualityAtom);
    term_RplacSecondArgument(EventualityAtom, term_Create(LoopSearchConstant, list_Nil()));
    term_Delete(secondArgument);
  }
  tl_MakeStepAtom(EventualityAtom, temporalVariableSymbol);

  j = clause_FirstAntecedentLitIndex(toReturn);
  for(Scan = litList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LITERAL Lit = list_Car(Scan);

    clause_SetLiteral(toReturn, j, Lit);
    clause_LiteralSetOwningClause(Lit, toReturn);
    tl_MakeStepAtom(clause_LiteralAtom(Lit), temporalVariableSymbol);
    ++j;
  }
  clause_SetLiteral(toReturn, j, LoopSearchMarkerLit);
  clause_LiteralSetOwningClause(LoopSearchMarkerLit, toReturn);
  clause_SetLiteral(toReturn, (PositiveEventualityLiteral ? clause_FirstSuccedentLitIndex(toReturn) : j + 1),
                    EventualityLit);
  clause_LiteralSetOwningClause(EventualityLit, toReturn);
  clause_ReInit(toReturn, flags, precedence);

  return toReturn;
}

CLAUSE tl_CreateNextLoopSearchStepClause(CLAUSE terminatingLoopSearchClause, LITERAL loopSearchMarkerLiteral, FLAGSTORE flags, PRECEDENCE precedence)
{
  CLAUSE toReturn;
  SYMBOL loopSearchMarkerSymbol = term_TopSymbol(clause_LiteralAtom(loopSearchMarkerLiteral));
  NAT i = tl_LOOPSEARCH_MARKER_INDEX_MAP[symbol_Index(loopSearchMarkerSymbol)];
  CLAUSE EventualityClause = tl_LOOPSEARCH_MARKER_EVENTUALITY_MAP[symbol_Index(loopSearchMarkerSymbol)];
  EVENTUALITY_INF *inf = tl_GetEventualityInformation(tl_GetEventualityTerm(EventualityClause));
  if(i + 1 >= inf->markerCount) { // only create a new loop search marker when we have to!
    tl_CreateLoopSearchMarker(i + 1, EventualityClause, precedence);
  }
  LIST LiteralList = list_Nil();
  int j;

  for(j = clause_FirstLitIndex(); j <= clause_LastLitIndex(terminatingLoopSearchClause); ++j) {
    LITERAL Literal = clause_GetLiteral(terminatingLoopSearchClause, j);

    if(Literal != loopSearchMarkerLiteral) {
      LiteralList = list_Cons(clause_LiteralCopy(Literal), LiteralList);
    }
  }

  toReturn = tl_CreateLoopSearchStepClause(i + 1, EventualityClause, LiteralList, flags, precedence);
  list_Delete(LiteralList);

  return toReturn;
}

BOOL tl_ContainsLoopSearchMarkerForEventuality(CLAUSE eventualityClause, CLAUSE Clause, LITERAL *loopSearchMarkerLiteral)
{
  EVENTUALITY_INF *inf = tl_GetEventualityInformation(tl_GetEventualityTerm(eventualityClause));
  int i, j;

  for(i = 0; i < inf->markerCount; ++i) {
    SYMBOL s = inf->map[i];
    for (j = clause_FirstLitIndex(); j < clause_Length(Clause); ++j) {
      if(term_ContainsSymbol(clause_GetLiteralAtom(Clause, j), s)) {
        if(loopSearchMarkerLiteral) {
          *loopSearchMarkerLiteral = clause_GetLiteral(Clause, j);
        }
        return TRUE;
      }
    }
  }
  return FALSE;
}

BOOL tl_ContainsLoopSearchMarker(CLAUSE Clause)
{
  int i;

  for (i = clause_FirstLitIndex(); i < clause_Length(Clause); ++i) {
    TERM Atom = clause_GetLiteralAtom(Clause, i);
    if(!term_IsComplex(Atom) && symbol_IsLoopSearchMarker(term_TopSymbol(Atom))) {
      return TRUE;
    }
  }
  return FALSE;
}

static int tl_FindLoopSearchMarker(CLAUSE Clause)
{
  int i;

  for (i = clause_FirstLitIndex(); i < clause_Length(Clause); ++i) {
    TERM Atom = clause_GetLiteralAtom(Clause, i);
    if(!term_IsComplex(Atom) && symbol_IsLoopSearchMarker(term_TopSymbol(Atom))) {
      return i;
    }
  }
  return -1;
}

static BOOL tl_TestMonadicValidity(FLAGSTORE InputFlags, PRECEDENCE InputPrecedence, TERM Term, PROOFSEARCH OldSearch)
{
  BOOL Result;
  PROOFSEARCH Search = prfs_Create();
  PRECEDENCE Precedence = prfs_Precedence(Search);
  FLAGSTORE Flags = prfs_Store(Search);
  LIST ClauseList;
  LIST SymbolList = list_Nil();
  int BoundApplied = -1;

  flag_TransferSetFlags(InputFlags, Flags);
  symbol_TransferPrecedence(InputPrecedence, Precedence);

  // deactivate the temporal mode
  TEMPORAL_MODE = FALSE;
  /* 'Term' is negated in cnf_QueryFlotter. */
  ClauseList = cnf_QueryFlotter(Search, Term, &SymbolList, TRUE);

//   prfs_SetSplitCounter(Search, flag_GetFlagValue(Flags, flag_SPLITS));
  prfs_SetLoops(Search, -1);
//   prfs_SetBacktrackedClauses(Search, 0);

  Search = proof_ProofSearch(Search, ClauseList,
                                     Flags, list_Nil(), &BoundApplied, FALSE);
  // reactivate the temporal mode
  TEMPORAL_MODE = TRUE;
  
  if(list_Empty(prfs_EmptyClauses(Search))) {
    Result = FALSE;
  }
  else {
    Result = TRUE;
  }
//   /* Prepare the term stamp */
//   if (term_StampOverflow(sharing_StampID(WOIndex)))
//     sharing_ResetAllTermStamps(WOIndex);
//   if (term_StampOverflow(sharing_StampID(UsIndex)))
//     sharing_ResetAllTermStamps(UsIndex);

  // transfer the statistics from the old search object to the new one
  prfs_SetDerivedClauses(OldSearch, prfs_DerivedClauses(OldSearch) + prfs_DerivedClauses(Search));
  prfs_SetKeptClauses(OldSearch, prfs_KeptClauses(OldSearch) + prfs_KeptClauses(Search));
  prfs_SetInputClauses(OldSearch, prfs_InputClauses(OldSearch) + prfs_InputClauses(Search));
  prfs_SetForwardSubsumedClauses(OldSearch, prfs_ForwardSubsumedClauses(OldSearch) + prfs_ForwardSubsumedClauses(Search));
  prfs_SetBackwardSubsumedClauses(OldSearch, prfs_BackwardSubsumedClauses(OldSearch) + prfs_BackwardSubsumedClauses(Search));

  /*  symbol_ResetSkolemIndex(); */
  prfs_Delete(Search);
  list_Delete(ClauseList);
  /* delete the newly created Skolem constants to avoid cluttering up the signature */
  if (flag_GetFlagValue(InputFlags, flag_DOCPROOF)) {
    list_Delete(SymbolList);
  }
  else {
    symbol_DeleteSymbolList(SymbolList);
  }

  return Result;
}

void tl_AttachProofSearch(PROOFSEARCH Search)
{
  prfs_SetEventualityLoopSearchInformation(Search, tl_EVENTUALITY_CONSTS);
}

static LIST tl_GetLoopSearchStepClausesFromIndex(CLAUSE eventualityClause, NAT i, SHARED_INDEX index, BOOL Terminating)
{
  LIST TermList, toReturn = list_Nil();
  EVENTUALITY_INF *inf = tl_GetEventualityInformation(tl_GetEventualityTerm(eventualityClause));
  SYMBOL LoopSearchMarkerSymbol = inf->map[i];

  TERM loopSearchMarkerTerm = term_Create(LoopSearchMarkerSymbol, list_Nil());
// printf("inf term: ");term_Print(loopSearchMarkerTerm);printf("\n");

  TermList = st_GetUnifier(cont_LeftContext(), sharing_Index(index), cont_RightContext(), loopSearchMarkerTerm);
// printf("length %i\n", list_Length(TermList));
  for(; !list_Empty(TermList); TermList = list_Pop(TermList)) {
    LIST LitList;
    TERM term = list_Car(TermList);

    
//     TERM 
// printf("term: ");term_Print(list_Car(TermList));printf("\n");
    if(term_IsVariable(term)) {
      continue;
    }

    for(LitList = sharing_NAtomDataList(term); !list_Empty(LitList); LitList = list_Cdr(LitList)) {
      CLAUSE Clause;

      Clause = clause_LiteralOwningClause(list_Car(LitList));

// printf("Clause found: ");clause_Print(Clause);printf("\n");
      if(!Terminating || tl_IsTerminatingStepClause(Clause)) {
        toReturn = list_Cons(Clause, toReturn);
      }
// else {
// printf("discarding it\n");
// }
    }
  }

  term_Delete(loopSearchMarkerTerm);

  return toReturn;
}

static LIST tl_GetTerminatingLoopSearchStepClausesFromIndex(CLAUSE eventualityClause, NAT i, SHARED_INDEX index)
{
  if(!eventualityClause) {
    return list_Nil();
  }
  return tl_GetLoopSearchStepClausesFromIndex(eventualityClause, i, index, TRUE);
}

LIST tl_GetTerminatingLoopSearchStepClauses(CLAUSE EventualityClause, NAT i, PROOFSEARCH Search)
{
  LIST toReturn = list_Nil();
  toReturn = tl_GetTerminatingLoopSearchStepClausesFromIndex(EventualityClause, i, prfs_UsableSharingIndex(Search));
  toReturn = list_Nconc(toReturn,
                        tl_GetTerminatingLoopSearchStepClausesFromIndex(EventualityClause, i,
                                                                        prfs_WorkedOffSharingIndex(Search)));
  return toReturn;
}

NAT tl_LastLoopIterationIndex(CLAUSE EventualityClause)
{
  EVENTUALITY_INF *inf = tl_GetEventualityInformation(tl_GetEventualityTerm(EventualityClause));
  
  return inf->markerCount - 1;
}

LIST tl_ExtractLiteralAtoms(CLAUSE terminatingLoopSearchClause)
{
  LIST toReturn = list_Nil();
  int i;

  for(i = clause_FirstAntecedentLitIndex(terminatingLoopSearchClause); i <= clause_LastAntecedentLitIndex(terminatingLoopSearchClause); ++i) {
    LITERAL Literal = clause_GetLiteral(terminatingLoopSearchClause, i);
    TERM Atom = clause_LiteralAtom(Literal);
    if(term_IsComplex(Atom)) { /* don't get the loop search marker */
      toReturn = list_Cons(Atom, toReturn);
    }
  }

  return toReturn;
}

NAT tl_ComputeAtomWeight(TERM t)
{
  NAT toReturn = 0;

  if(term_IsVariable(t)) {
    return 1; // FIXME: hardcoded value for now
  }
  else {
    toReturn = symbol_Weight(term_TopSymbol(t));
  }
  if(term_IsComplex(t)) {
    for(LIST Scan = term_ArgumentList(t); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
       toReturn += tl_ComputeAtomWeight(list_Car(Scan));
    }
  }

  return toReturn;
}

LIST tl_ExtractUniversalAtoms(CLAUSE StepClause)
{
  LIST toReturn = list_Nil();

  for(int i = clause_FirstAntecedentLitIndex(StepClause); i <= clause_LastLitIndex(StepClause); ++i) {
    TERM Atom = clause_LiteralAtom(clause_GetLiteral(StepClause, i));
    if(tl_IsUniversalAtom(Atom)) {
      toReturn = list_Cons(Atom, toReturn);
    }
  }
  return toReturn;
}

void tl_ComputeTemporalOrdering(LIST InputClauses, FLAGSTORE Flags)
{
  /* Currently we only support the KBO.
   * We set the weight of tl_TEMP_SUCC such that it is bigger than any symbol
   * occurring on the left-hand sides of step clauses.
   */
  LIST LeftHandAtoms = list_Nil();
  NAT MaxWeight = 0;

  for(LIST Scan = InputClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    if(!tl_IsStepClause(Clause)) {
      continue;
    }

    LeftHandAtoms = list_Nconc(tl_ExtractUniversalAtoms(Clause), LeftHandAtoms);
  }

  for(LIST Scan = LeftHandAtoms; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    NAT Weight = tl_ComputeAtomWeight(list_Car(Scan));

    if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
      printf("\nWeight of the atom "); term_Print(list_Car(Scan)); printf(" is %i.", Weight);
    }
    MaxWeight = MAX(MaxWeight, Weight);
  }

  if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    printf("\nWeight of the temporal successor function set to %i.", MaxWeight + 1);
  }
  symbol_SetWeight(tl_TEMP_SUCC, MaxWeight + 1);
  list_Delete(LeftHandAtoms);
}

/**
 * CAUTION: 'SortedList' must be sorted ascendingly!
 **/
LIST list_SortedInsertDuplicateFree(LIST SortedList, POINTER P, BOOL (*Less)(POINTER, POINTER))
{
  POINTER FirstElement;
  LIST Prev;

  if(list_Empty(SortedList)) {
    return list_List(P);
  }

  FirstElement = list_Car(SortedList);

  if(P == FirstElement) {
    return SortedList;
  }
  else if(Less(P, FirstElement)) {
    return list_Cons(P, SortedList);
  }

  Prev = SortedList;
  for(LIST Scan = list_Cdr(SortedList); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    POINTER Element = list_Car(Scan);

    if(Element == P) {
      return SortedList;
    }
    else if(Less(P, Element)) {
      list_InsertNext(Prev, P);
      return SortedList;
    }

    Prev = Scan;
  }
  /* we have reached the end of the list, i.e. Prev points to the last element */
  list_InsertNext(Prev, P);

  return SortedList;
}

// CAUTION: first list argument has to be a sorted list!
LIST list_SortedMergeDuplicateFree(LIST SortedList, LIST UnsortedList, BOOL (*Test)(POINTER, POINTER))
{
  LIST toReturn = SortedList;

  for(LIST Scan = UnsortedList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    toReturn = list_SortedInsertDuplicateFree(toReturn, list_Car(Scan), Test);
  }

  return toReturn;
}

LIST tl_GetFreeVariablesExceptTemporal(LIST AtomsList)
{
  LIST toReturn = list_Nil();

  for(LIST Scan = AtomsList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM Atom = list_Car(AtomsList);

    if(list_Length(term_ArgumentList(Atom)) <= 1) {
      continue;
    }

    for(LIST Scan2 = list_Cdr(term_ArgumentList(Atom)); !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
      LIST VariableSymbolList = term_VariableSymbols(list_Car(Scan2));
      toReturn = list_SortedMergeDuplicateFree(toReturn, VariableSymbolList, (BOOL (*)(POINTER, POINTER))symbol_LessVariable);
      list_Delete(VariableSymbolList);
    }
  }

  return toReturn;
}

/** 
 * 'List' is a list of lists!
 **/
TERM tl_BuildDNF(LIST List, SYMBOL FreeVariable)
{
  LIST termArgumentList = list_Nil();

  for(LIST Scan = List; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST AtomList = list_Car(Scan);
    LIST VariableSymbolListExceptTemporal = tl_GetFreeVariablesExceptTemporal(AtomList);
    LIST VariableTermListExceptTemporal = list_Nil();

    /* we still need to remove the replacement variable for the loop search constant */
    list_DeleteOneFromList(&VariableSymbolListExceptTemporal, (POINTER)FreeVariable);

    for(LIST Scan2 = VariableSymbolListExceptTemporal; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
      VariableTermListExceptTemporal = list_Cons(term_Create((SYMBOL)list_Car(Scan2), list_Nil()), VariableTermListExceptTemporal);
    }
    list_Delete(VariableSymbolListExceptTemporal);

    if(list_Empty(VariableTermListExceptTemporal)) {
      termArgumentList = list_Cons(term_Create(fol_And(), AtomList), termArgumentList);
    }
    else {
      termArgumentList = list_Cons(fol_CreateQuantifier(fol_Exist(), VariableTermListExceptTemporal, list_List(term_Create(fol_And(), AtomList))), termArgumentList);
    }
  }
  return term_Create(fol_Or(), termArgumentList);
}

static __inline__ void tl_FixLoopSearchAtom(TERM Atom, SYMBOL temporalVariable, SYMBOL constReplacementVariable)
{
  TERM UniversalArgument = term_FirstArgument(Atom);

  term_RplacFirstArgument(Atom, term_Create(temporalVariable, list_Nil()));
  term_Delete(UniversalArgument);

  if(list_Length(term_ArgumentList(Atom)) >= 2) {
    term_ReplaceConstant(Atom, tl_LoopSearchConstant(), constReplacementVariable);
  }
}

/**
 * Computes H^L_i(x).
 **/
TERM tl_BuildLoopSearchSubformula(LIST TerminatingStepClauses, SYMBOL* TemporalVariable, SYMBOL* FreeVariable)
{
  LIST AtomsList = list_Nil();
  SYMBOL MaxVar = symbol_FirstVariable();
  SYMBOL temporalVariableSymbol;
  SYMBOL replacementVariableSymbol;
  TERM Term;

  if(list_Empty(TerminatingStepClauses)) {
    if(TemporalVariable) {
      *TemporalVariable = symbol_FirstVariable();
    }

    if(FreeVariable) {
      *FreeVariable = symbol_FirstVariable() + 1;
    }
    return NULL;
  }

  for(LIST list = TerminatingStepClauses; !list_Empty(list); list = list_Cdr(list)) {
    SYMBOL SubMaxVar = symbol_FirstVariable();
    LIST ExtractedList = tl_ExtractLiteralAtoms(list_Car(list));
    LIST SubAtomList = term_CopyTermList(ExtractedList);
    list_Delete(ExtractedList);

    for(LIST Scan2 = SubAtomList; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
      SYMBOL SubSubMaxVar;

      
      SubSubMaxVar = term_MaxVar(list_Car(Scan2));
      if(symbol_GreaterVariable(SubSubMaxVar, SubMaxVar)) {
        SubMaxVar = SubSubMaxVar;
      }
    }
    if(symbol_GreaterVariable(SubMaxVar, MaxVar)) {
      MaxVar = SubMaxVar;
    }
    AtomsList = list_Cons(SubAtomList, AtomsList);
  }

  /* FIXME: do it like this for now, could be improved, though*/
  temporalVariableSymbol = MaxVar + 1;
  replacementVariableSymbol = MaxVar + 2;

  if(TemporalVariable) {
    *TemporalVariable = temporalVariableSymbol;
  }

  if(FreeVariable) {
    *FreeVariable = replacementVariableSymbol;
  }

#ifdef CHECK
  if(!symbol_GreaterVariable(symbol__MAXSTANDARDVAR, temporalVariableSymbol)
                      || !symbol_GreaterVariable(symbol__MAXSTANDARDVAR, replacementVariableSymbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_BuildIntermediateLoopSearchResult:");
    misc_ErrorReport("\n Number of standard variables exceeded!");
    misc_FinishErrorReport();
  }
#endif

  for(LIST Scan = AtomsList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    for(LIST Scan2 = list_Car(Scan); !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
      tl_FixLoopSearchAtom(list_Car(Scan2), temporalVariableSymbol, replacementVariableSymbol);
    }
  }
  Term = tl_BuildDNF(AtomsList, replacementVariableSymbol);

  /* Cleanup */
  list_Delete(AtomsList); /* the lists inside AtomsList are moved into the term */

  return Term;
}

void tl_UnifyVariables(TERM Hi, TERM Hi2, SYMBOL TemporalVariable, SYMBOL TemporalVariable2, SYMBOL FreeVariable, SYMBOL FreeVariable2)
{
  LIST UsedVariableList = list_Cons((POINTER)TemporalVariable,
                              list_Cons((POINTER)TemporalVariable2,
                                  list_Cons((POINTER)FreeVariable,
                                      list_List((POINTER)FreeVariable2))));
  SYMBOL UnusedVariable = symbol_FindUnusedVariable(UsedVariableList);
  TERM UnusedVariableTerm = term_Create(UnusedVariable, list_Nil());
  TERM FreeVariable2Term = term_Create(FreeVariable2, list_Nil());
  TERM TemporalVariable2Term = term_Create(TemporalVariable2, list_Nil());

  fol_ReplaceVariable(Hi, TemporalVariable, UnusedVariableTerm);
  fol_ReplaceVariable(Hi, FreeVariable, FreeVariable2Term);
  fol_ReplaceVariable(Hi, UnusedVariable, TemporalVariable2Term);

  term_Delete(UnusedVariableTerm);
  term_Delete(FreeVariable2Term);
  term_Delete(TemporalVariable2Term);
  list_Delete(UsedVariableList);
}

/**
 * CAUTION: the substitution is done regardless of whether the subterm in question
 *          is a variable or not
 **/
CLAUSE tl_PerformConstantFloodingClause(CLAUSE Clause, SYMBOL ConstantSymbol, BOOL IncreaseClauseNumber)
{
  CLAUSE toReturn = NULL;
  TERM ConstantTerm = NULL, ShieldTerm = NULL;
  LIST VariableSymbolList = list_Nil();
  SYMBOL FreeVariable = symbol_Null();
  
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);

    // check if the literal can contain non-temporal variables
    if(list_Length(term_ArgumentList(Atom)) <= 1) {
      continue;
    }
    // we collect all the variables, there can only be one; starting from the second sub term
    for(LIST Scan = list_Cdr(term_ArgumentList(Atom)); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      TERM SubTerm = list_Car(Scan);
      VariableSymbolList = list_Nconc(term_VariableSymbols(SubTerm), VariableSymbolList);
    }
  }
  
  // no variable has been found; hence, no substitution can be done
  if(list_Empty(VariableSymbolList)) { // 'VariableSymbolList' is then NULL
    return NULL;
  }

  FreeVariable = (SYMBOL) list_Car(VariableSymbolList);
  // consistency checking; we start from the second list element
  for(LIST Scan = list_Cdr(VariableSymbolList); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Variable = (SYMBOL) list_Car(Scan);
    if(!symbol_Equal(FreeVariable, Variable)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In tl_PerformConstantFloodingClause:");
      misc_ErrorReport("\n Illegal input clause: contains at least two free variables.");
      misc_FinishErrorReport();
    }
  }
  list_Delete(VariableSymbolList);

  ConstantTerm = term_Create(ConstantSymbol, list_Nil());
  toReturn = clause_Copy(Clause);

  // finally, perform the substitution
  ShieldTerm = term_Create(tl_SHIELD, list_List(term_Create(FreeVariable, list_Nil())));
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(toReturn); ++i) {
    LITERAL Lit = clause_GetLiteral(toReturn, i);
    TERM Atom = clause_LiteralAtom(Lit);
    // first we replace shielded variables
    term_ReplaceSubtermBy(Atom, ShieldTerm, ConstantTerm);
    // and only after that the remaining free variables in order to avoid
    // substituting into a shielded variable
    term_ReplaceVariable(Atom, FreeVariable, ConstantTerm);
  }
  term_Delete(ShieldTerm);
  term_Delete(ConstantTerm);

  if(IncreaseClauseNumber) {
    clause_NewNumber(toReturn);
  }

  return toReturn;
}

BOOL tl_TranslationIsGround(CLAUSE Clause)
{
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);
    LIST ArgumentList = list_Nil();

    ArgumentList = term_ArgumentList(Atom);
    if(list_Length(ArgumentList) <= 1) {
      continue;
    }
    // start from the second argument; skip the temporal variable
    ArgumentList = list_Cdr(ArgumentList);
    for(LIST Scan = ArgumentList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      TERM t = (TERM) list_Car(Scan);

      if(!term_IsGround(t)) {
        return FALSE;
      }
    }
  }
  return TRUE;
}

// Note that this method is also called for constant-flooding the eventuality clauses
LIST tl_PerformConstantFlooding(LIST ClauseList, LIST ConstantList, FLAGSTORE Flags)
{
  LIST NewClauseList = list_Nil();
  LIST FreeVarClauseList = list_Nil(), GroundClauseList = list_Nil();
  BOOL GroundClauseFound = FALSE;

  // first, we search for all the clauses that have to be constant-flooded
  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);
    clause_Normalize(Clause); // required later
    
    if(tl_TranslationIsGround(Clause)) {
      GroundClauseList = list_Cons(Clause, GroundClauseList);
    }
    else {
      FreeVarClauseList = list_Cons(Clause, FreeVarClauseList);
    }
  }

  if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    printf("\n-------------------------CONSTANT-FLOODING START-------------------------");
  }

  for(LIST Scan = FreeVarClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan), FloodedClause = NULL;
    LIST NewClauseList2 = list_Nil();

    if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
      printf("\nPerforming constant flooding for the clause "); clause_Print(Clause);
    }

    for(LIST Scan2 = ConstantList; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
      SYMBOL Constant = (SYMBOL) list_Car(Scan2);

      // don't perform constant-flooding with the temporal zero constant
      if(symbol_Equal(Constant, tl_ZERO)) {
        continue;
      }

      // we don't assign a new clause number now; we do it later if required
      FloodedClause = tl_PerformConstantFloodingClause(Clause, Constant, FALSE);
      if(!FloodedClause) {
        misc_StartErrorReport();
        misc_ErrorReport("\n In tl_PerformConstantFlooding:");
        misc_ErrorReport("\n tl_PerformConstantFloodingClause returned NULL!");
        misc_FinishErrorReport();
      }
      clause_Normalize(FloodedClause);

      // finally, we check if we have such a clause already; we don't want to
      // create clauses twice (especially, eventuality clauses, see 'tl_AddEventualityInformation')
      GroundClauseFound = FALSE;
      for(LIST Scan3 = GroundClauseList; !list_Empty(Scan3); Scan3 = list_Cdr(Scan3)) {
        CLAUSE GroundClause = (CLAUSE) list_Car(GroundClauseList);

        // both input clauses are normalised
        if(clause_Equal(GroundClause, FloodedClause)) {
          GroundClauseFound = TRUE;
          break;
        }
      }
      if(!GroundClauseFound) {
        clause_NewNumber(FloodedClause);
        NewClauseList2 = list_Cons(FloodedClause, NewClauseList2);
      }
      else {
        clause_Delete(FloodedClause);
      }
    }

    if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
      printf("\n  Constant flooded clauses obtained: ");
      for(LIST Scan2 = NewClauseList2; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
        printf("\n    "); clause_Print((CLAUSE) list_Car(Scan2));
      }
    }
    NewClauseList = list_Nconc(NewClauseList, NewClauseList2);
  }

  list_Delete(FreeVarClauseList);
  list_Delete(GroundClauseList);

  if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    printf("\n-------------------------CONSTANT-FLOODING STOP--------------------------");
  }

  return NewClauseList;
}

BOOL tl_IsMostMonadicNegativeUniversalClause(CLAUSE Clause)
{
  SYMBOL Variable = symbol_Null();
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);

    if(!clause_LiteralIsNegative(Lit)
     || list_Length(term_ArgumentList(Atom)) > 1 + 1) { /* + temporal variable */
      return FALSE;
    }

    // check if every literal is 'universal' and has the same temporal variable
    if(list_Length(term_ArgumentList(Atom)) >= 1) {
      TERM varTerm = term_FirstArgument(Atom);
      SYMBOL topSymbol = term_TopSymbol(varTerm);

      if(!symbol_IsVariable(topSymbol)) {
        return FALSE;
      }
      if(symbol_Equal(Variable, symbol_Null())) {
        Variable = topSymbol;
      }
      else if(!symbol_Equal(Variable, topSymbol)) {
        return FALSE;
      }
    }
  }
  return TRUE;
}

BOOL tl_ContainsTemporalOperator(TERM t)
{
  if(tl_IsTemporalOperator(t)) {
    return TRUE;
  }
  for(LIST Scan = term_ArgumentList(t); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    if(tl_ContainsTemporalOperator(list_Car(Scan))) {
      return TRUE;
    }
  }
  return FALSE;
}

static BOOL tl_IsDisjunctionOfLiterals(TERM t)
{
  if(fol_IsLiteral(t)) { // works for 'true' and 'false'
    return TRUE;
  }
  
  if(!symbol_Equal(term_TopSymbol(t), fol_Or())) {
    return FALSE;
  }

  for(LIST Scan = term_ArgumentList(t); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM SubTerm = (TERM) list_Car(Scan);
    if(symbol_Equal(term_TopSymbol(SubTerm), fol_Or())) { 
      if(!tl_IsDisjunctionOfLiterals(SubTerm)) {
        return FALSE;
      }
    }
    else if(!fol_IsLiteral(SubTerm)) {
      return FALSE;
    }
  }
  return TRUE;
}

static BOOL tl_IsConjunctionOfPositiveLiterals(TERM t)
{
  if(fol_IsPositiveLiteral(t)) { // works for 'true' and 'false'
    return TRUE;
  }
  
  if(!symbol_Equal(term_TopSymbol(t), fol_And())) {
    return FALSE;
  }

  for(LIST Scan = term_ArgumentList(t); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM SubTerm = (TERM) list_Car(Scan);
    
    if(symbol_Equal(term_TopSymbol(SubTerm), fol_And())) {
      if(!tl_IsConjunctionOfPositiveLiterals(SubTerm)) {
        return FALSE;
      }
    }
    else if(!fol_IsPositiveLiteral(SubTerm)) {
      return FALSE;
    }
  }
  return TRUE;
}

DSNF_TYPE tl_FormulaType(TERM t)
{
  TERM FirstSubTerm, ImplicationTerm, LeftTerm, RightTerm;
  if(!tl_ContainsTemporalOperator(t)) {
    return INITIAL_FORMULA;
  }
  if(!symbol_Equal(term_TopSymbol(t), tl_Always())) {
    return UNDEFINED;
  }
  FirstSubTerm = term_FirstArgument(t);
  if(!tl_ContainsTemporalOperator(FirstSubTerm)) {
    return UNIVERSAL_FORMULA;
  }
  if(symbol_Equal(term_TopSymbol(FirstSubTerm), fol_All())) {
    LIST Variables;
    FirstSubTerm = term_SecondArgument(FirstSubTerm);
    Variables = term_VariableSymbols(term_FirstArgument(FirstSubTerm));
    Variables = list_DeleteDuplicates(Variables, (BOOL (*)(POINTER, POINTER)) symbol_Equal);
    unsigned int NumVariables = list_Length(Variables);
    list_Delete(Variables);
    if(NumVariables >= 2) {
      return UNDEFINED;
    }
  }
  if(symbol_Equal(term_TopSymbol(FirstSubTerm), tl_Sometime())) {
    if(fol_IsLiteral(term_FirstArgument(FirstSubTerm))) {
      return EVENTUALITY_FORMULA;
    }
    else {
      return UNDEFINED;
    }
  }
  ImplicationTerm = FirstSubTerm;
  if(!symbol_Equal(term_TopSymbol(ImplicationTerm), fol_Implies())) {
    return UNDEFINED;
  }
  LeftTerm = term_FirstArgument(ImplicationTerm);
  if(!symbol_Equal(term_TopSymbol(term_SecondArgument(ImplicationTerm)), tl_Next())) {
    return UNDEFINED;
  }
  RightTerm = term_FirstArgument(term_SecondArgument(ImplicationTerm));
  if(!tl_IsConjunctionOfPositiveLiterals(LeftTerm) || !tl_IsDisjunctionOfLiterals(RightTerm)) {
    return UNDEFINED;
  }
  //FIXME: checks for the number of variables and the variable itself could be added
  return STEP_FORMULA;
}

static __inline__ void tl_DecomposeStepFormula(TERM Formula, TERM *LeftTerm, TERM *RightTerm)
{
  Formula = term_FirstArgument(Formula); // drop the 'always' operator
  if(symbol_Equal(term_TopSymbol(Formula), fol_All())) {
    Formula = term_SecondArgument(Formula); // drop the universal quantifier
  }
  *LeftTerm = term_FirstArgument(Formula);
  *RightTerm = term_FirstArgument(term_SecondArgument(Formula));
}

static LIST tl_CreateLiteralList(TERM t)
{
  LIST toReturn = list_Nil();
  
  if(fol_IsLiteral(t)) {
    return list_List(t);
  }
  for(LIST Scan = term_ArgumentList(t); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM SubTerm = (TERM) list_Car(Scan);
    LIST NewList = list_Nil();

    if(symbol_Equal(term_TopSymbol(SubTerm), fol_And())
       || symbol_Equal(term_TopSymbol(SubTerm), fol_Or())) {
       NewList = tl_CreateLiteralList(SubTerm);
    }
    else if(fol_IsLiteral(SubTerm)) {
      NewList = list_List(SubTerm);
    }
    else {
      misc_StartErrorReport();
      misc_ErrorReport("\n In tl_CreateLiteralList:");
      misc_ErrorReport("\n Illegal input.");
      misc_FinishErrorReport();
    }
    toReturn = list_Nconc(toReturn, NewList);
  }
  return toReturn;
}

// this method would also work if there were several free variables in 'Atom'
static void tl_InsertVariableShields(TERM Atom, SYMBOL TemporalVariable)
{
  LIST VariableSymbolList = term_VariableSymbols(Atom);
  LIST SeenVariableSymbolList = list_Nil();
  for(LIST Scan = VariableSymbolList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Variable = (SYMBOL) list_Car(Scan);

    // we don't want to shield the temporal variable or substitute variables that
    // we have encountered already
    if(symbol_Equal(TemporalVariable, Variable)
       || list_Member(SeenVariableSymbolList, (POINTER) Variable, (BOOL (*)(POINTER, POINTER))symbol_Equal)) {
      continue;
    }
    else {
      TERM NewTerm = term_Create(tl_SHIELD, list_List(term_Create(Variable, list_Nil())));
      term_ReplaceVariable(Atom, Variable, NewTerm);
      term_Delete(NewTerm);
      SeenVariableSymbolList = list_Cons((POINTER) Variable, SeenVariableSymbolList);
    }
  }

  list_Delete(SeenVariableSymbolList);
  list_Delete(VariableSymbolList);
}

CLAUSE tl_ClausifyAndTemporaliseStepFormula(TERM t, BOOL* predicateMap, FLAGSTORE Flags, PRECEDENCE Precedence)
{
  CLAUSE toReturn = NULL;
  LIST VariableListLeft = list_Nil(), VariableListRight = list_Nil();
  LIST LeftClauseLitList = list_Nil(), RightClauseLitList = list_Nil();
  TERM LeftTerm = NULL, RightTerm = NULL;
  LIST LeftFormulaLitList = list_Nil(), RightFormulaLitList = list_Nil();
  SYMBOL TemporalVariable;
  BOOL Tautology = FALSE;

  tl_DecomposeStepFormula(t, &LeftTerm, &RightTerm);
  
  LeftFormulaLitList = tl_CreateLiteralList(LeftTerm);
  RightFormulaLitList = tl_CreateLiteralList(RightTerm);
  
  //check whether the step formula in question is a tautology, i.e. iff
  // the left-hand side contains 'false' or the right-hand side contains
  // true (or not(false))
  for(LIST Scan = LeftFormulaLitList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM LiteralTerm = (TERM) list_Car(Scan);

    if(fol_IsNegativeLiteral(LiteralTerm)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In tl_ClausifyAndTemporaliseStepFormula:");
      misc_ErrorReport("\n Illegal input clause: negative literal in left-hand side.");
      misc_FinishErrorReport();    
    }

    if(fol_IsFalse(LiteralTerm)) {
      Tautology = TRUE;
      break;
    }
  }

  for(LIST Scan = RightFormulaLitList; !Tautology && !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM LiteralTerm = (TERM) list_Car(Scan);

    if(fol_IsTrue(LiteralTerm)
       || (symbol_Equal(term_TopSymbol(LiteralTerm), fol_Not())
           && fol_IsFalse(term_FirstArgument(LiteralTerm)))) {
      Tautology = TRUE;
      break;
    }
  }

  if(Tautology) {
    list_Delete(LeftFormulaLitList);
    list_Delete(RightFormulaLitList);
    LIST LitList = list_List(term_Create(fol_True(), list_Nil()));
    toReturn = clause_Create(list_Nil(), list_Nil(), LitList, Flags, Precedence);
    list_Delete(LitList);
    return toReturn;
  }

  VariableListLeft = fol_FreeVariables(LeftTerm);
  VariableListRight = fol_FreeVariables(RightTerm);
  VariableListLeft = list_Nconc(VariableListLeft, VariableListRight);
  TemporalVariable = tl_FindFreeVariable(VariableListLeft);

  for(LIST Scan = LeftFormulaLitList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM LiteralTerm = (TERM) list_Car(Scan);
    TERM CopyLiteralTerm;
    
    if(!fol_IsTrue(LiteralTerm)) {
      CopyLiteralTerm = term_Copy(LiteralTerm);    
      tl_TransformPredicateToFOL(CopyLiteralTerm, predicateMap, UNIVERSAL_TRANSFORMATION,
                                 TemporalVariable);
      LeftClauseLitList = list_Cons(CopyLiteralTerm, LeftClauseLitList);
    }
  }

  for(LIST Scan = RightFormulaLitList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM LiteralTerm = (TERM) list_Car(Scan);
    TERM CopyLiteralTerm;
    BOOL LiteralIsNegative = symbol_Equal(term_TopSymbol(LiteralTerm), fol_Not());
    
    if(!fol_IsFalse(LiteralTerm)
       && !(LiteralIsNegative && fol_IsTrue(term_FirstArgument(LiteralTerm)))) {
      // don't copy the 'not' operator
      LiteralTerm = (LiteralIsNegative ? term_FirstArgument(LiteralTerm) : LiteralTerm); 
      CopyLiteralTerm = term_Copy(LiteralTerm);
      tl_TransformPredicateToFOL(CopyLiteralTerm, predicateMap, STEP_TRANSFORMATION,
                                 TemporalVariable);
      tl_InsertVariableShields(CopyLiteralTerm, TemporalVariable);
      if(!LiteralIsNegative) {
        RightClauseLitList = list_Cons(CopyLiteralTerm, RightClauseLitList);
      }
      else {
        LeftClauseLitList = list_Cons(CopyLiteralTerm, LeftClauseLitList);
      }
    }
  }

  list_Delete(VariableListLeft); // VariableListRight has been appended to VariableListLeft

  toReturn = clause_Create(list_Nil(), LeftClauseLitList, RightClauseLitList, Flags, Precedence);
  list_Delete(LeftClauseLitList);
  list_Delete(RightClauseLitList);
  list_Delete(LeftFormulaLitList);
  list_Delete(RightFormulaLitList);
  return toReturn;
}

// formula(always(forall([x], sometime(q(x))))).
CLAUSE tl_ClausifyAndTemporaliseEventualityFormula(TERM EventualityFormula, BOOL* predicateMap, BOOL* Unsatisfiable,
                                                   FLAGSTORE Flags, PRECEDENCE Precedence)
{
  CLAUSE toReturn = NULL;
  TERM EventualityAtom;
  LIST NegativeLiteralList = list_Nil(), PositiveLiteralList = list_Nil();
  LIST VariableList;
  SYMBOL FreeVariable;
  BOOL NegativeEventuality = FALSE;
  
  EventualityFormula = term_FirstArgument(EventualityFormula); // skip the 'always' operator
  if(symbol_Equal(term_TopSymbol(EventualityFormula), fol_All())) {
    EventualityFormula = term_SecondArgument(EventualityFormula);
  }
  EventualityFormula = term_FirstArgument(EventualityFormula); // skip the 'sometime' operator
  NegativeEventuality = symbol_Equal(term_TopSymbol(EventualityFormula), fol_Not());
  EventualityAtom = (NegativeEventuality ? term_FirstArgument(EventualityFormula)
                                         : EventualityFormula);

  if((!NegativeEventuality && symbol_Equal(term_TopSymbol(EventualityAtom), fol_True()))
    || (NegativeEventuality && symbol_Equal(term_TopSymbol(EventualityAtom), fol_False()))) {
    // the eventuality is actually a tautology
    *Unsatisfiable = FALSE;
    return NULL;
  }
  
  if((!NegativeEventuality && symbol_Equal(term_TopSymbol(EventualityAtom), fol_False()))
    || (NegativeEventuality && symbol_Equal(term_TopSymbol(EventualityAtom), fol_True()))) {
    // the eventuality cannot be satisfied
    *Unsatisfiable = TRUE;
    return NULL;
  }
  
  // copy the atom
  EventualityAtom = term_Copy(EventualityAtom);                                       
  if(NegativeEventuality) {
    NegativeLiteralList = list_List(EventualityAtom);
  }
  else {
    PositiveLiteralList = list_List(EventualityAtom);
  }
  VariableList = term_ListOfVariables(EventualityAtom);
  FreeVariable = tl_FindFreeVariable(VariableList);
  list_Delete(VariableList);

  tl_TransformPredicateToFOL(EventualityAtom, predicateMap, UNIVERSAL_TRANSFORMATION,
                             FreeVariable);

  toReturn = clause_Create(list_Nil(), NegativeLiteralList, PositiveLiteralList, Flags, Precedence);
  list_Delete(NegativeLiteralList);
  list_Delete(PositiveLiteralList);

  return toReturn;
}

LIST tl_ListOfConstants(LIST ClauseList)
{
  LIST toReturn = list_Nil();

  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    
    toReturn = list_Nconc(toReturn, clause_ListOfConstants(Clause));
  }

  toReturn = list_DeleteDuplicates(toReturn, (BOOL (*)(POINTER, POINTER)) symbol_Equal);

  return toReturn;
}


/**********************************************************
  INPUT:   A clause and a list of clauses
  RETURNS: TRUE iff the clause subsumes one of the clauses
           contained in the list, except for the loop search
           markers.
  CAUTION:
***********************************************************/
static BOOL tl_LoopSearchClauseSubsumesList(CLAUSE Clause, LIST ClauseList)
{
  int LoopSearchIndex = tl_FindLoopSearchMarker(Clause);
  assert(LoopSearchIndex >= 0);

  if(list_Empty(ClauseList)) {
    return FALSE;
  }

  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE PartnerClause = (CLAUSE) list_Car(Scan);
    int PartnerLoopSearchIndex = tl_FindLoopSearchMarker(PartnerClause);
    assert(PartnerLoopSearchIndex >= 0);
    if(subs_Subsumes(Clause, PartnerClause, LoopSearchIndex, PartnerLoopSearchIndex)) {
      return TRUE;
    }
  }

  return FALSE;
}

static BOOL tl_LoopSearchListSubsumesList(LIST ClauseList1, LIST ClauseList2)
{

  for(LIST Scan = ClauseList1; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);

    if(!tl_LoopSearchClauseSubsumesList(Clause, ClauseList2)) {
      return FALSE;
    }
  }

  return TRUE;
}

static LIST tl_ComputeLoopSearchResult(LIST ClauseList, FLAGSTORE Flags,
                                                          PRECEDENCE Precedence)
{
  LIST toReturn = list_Nil();
  SYMBOL NewVariable = symbol_Null();

  LIST VariableList = clause_ListOfVariablesInClauseList(ClauseList);
  NewVariable = tl_FindFreeVariable(VariableList);
  list_Delete(VariableList);

  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE LoopSearchClause = list_Car(Scan), NewClause;
    LIST NewLiteralList = list_Nil(), LiteralList;

    LiteralList = tl_ExtractLiteralAtoms(LoopSearchClause);
    for(LIST Scan2 = LiteralList; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
      TERM Term = term_Copy(list_Car(Scan2));

      term_ReplaceConstant(Term, tl_LOOPSEARCHCONSTANT, NewVariable);
      NewLiteralList = list_Cons(Term, NewLiteralList);
    }

    NewClause = clause_Create(list_Nil(), NewLiteralList, list_Nil(),
                              Flags, Precedence);
    clause_SetFromLoopSearch(NewClause);
    toReturn = list_Cons(NewClause, toReturn);
    list_Delete(NewLiteralList);
    list_Delete(LiteralList);
  }

  return toReturn;
}

static void tl_PrintLoopSearchCandidateClauses(CLAUSE EventualityClause, int index, LIST ClauseList)
{
  printf("\nLoop search candidate clauses (index %i) for the eventuality: ", index);
  clause_Print(EventualityClause);
  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    printf("\n"); clause_Print(list_Car(Scan));
  }
  printf("\nNumber of clauses: %i", list_Length(ClauseList));
}

static LIST tl_PerformSubsumptionLoopSearchTests(CLAUSE EventualityClause, PROOFSEARCH Search)
{
  LIST toReturn = list_Nil();

  FLAGSTORE Flags = prfs_Store(Search);
  PRECEDENCE Precedence = prfs_Precedence(Search);
  LIST iClauseList = list_Nil(), iSuccClauseList = list_Nil();

  int lastIterationIndex = tl_LastLoopIterationIndex(EventualityClause);

  if(lastIterationIndex >= 1) {
    iClauseList = tl_GetTerminatingLoopSearchStepClauses(EventualityClause, 0, Search);
    if(flag_GetFlagValue(Flags, flag_PLOOPCAND) && !list_Empty(iClauseList)) {
      tl_PrintLoopSearchCandidateClauses(EventualityClause, 0, iClauseList);
    }
  }

  for(int i = 0; i < lastIterationIndex; ++i) {
    iSuccClauseList = tl_GetTerminatingLoopSearchStepClauses(EventualityClause, i + 1, Search);

    if(flag_GetFlagValue(Flags, flag_PLOOPCAND) && !list_Empty(iSuccClauseList)) {
        tl_PrintLoopSearchCandidateClauses(EventualityClause, i + 1, iSuccClauseList);
    }
    if(!list_Empty(iClauseList) && !list_Empty(iSuccClauseList)) { // they can become empty due to subsumption deletion
      if(tl_LoopSearchListSubsumesList(iClauseList, iSuccClauseList)
        && tl_LoopSearchListSubsumesList(iSuccClauseList, iClauseList)) {
        LIST NewClauses = tl_ComputeLoopSearchResult(iSuccClauseList, Flags, Precedence);
        if (flag_GetFlagValue(Flags, flag_PGIVEN)) {
          printf("\nFound Loop Formula (Eventuality="); clause_Print(EventualityClause); printf(", i=%i):", i);

          printf("\niClauseList:");
          for(LIST Scan = iClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
            printf("\n"); clause_Print(list_Car(Scan));
          }
          printf("\niSuccClauseList:");
          for(LIST Scan = iSuccClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
            printf("\n"); clause_Print(list_Car(Scan));
          }
          printf("\nlength: %i, length: %i", list_Length(iClauseList), list_Length(iSuccClauseList));

          printf("\nLoop clauses:");
          for(LIST Scan = NewClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
            printf("\n"); clause_Print(list_Car(Scan));
          }
        }
        prfs_IncSuccessfulLoopSearches(Search);
        toReturn = list_Nconc(NewClauses,
                              toReturn);
      }
  
      list_Delete(iClauseList);
      iClauseList = iSuccClauseList;
    }
  }
  if(iClauseList) {
    list_Delete(iClauseList);
  }

  return toReturn;
}

static LIST tl_PerformLogicalLoopSearchTests(CLAUSE EventualityClause, PROOFSEARCH Search)
{
  LIST toReturn = list_Nil();
  FLAGSTORE Flags = prfs_Store(Search);
  PRECEDENCE Precedence = prfs_Precedence(Search);

  int lastIterationIndex = tl_LastLoopIterationIndex(EventualityClause);

  SYMBOL temporalVariableSymbol, previousTemporalVariableSymbol;
  SYMBOL replacementVariableSymbol, previousReplacementVariableSymbol;
  LIST iClauseList = list_Nil(), iSuccClauseList = list_Nil();
  
  TERM Hi = NULL, Hi2 = NULL;

  if(lastIterationIndex >= 1) {
    iClauseList = tl_GetTerminatingLoopSearchStepClauses(EventualityClause, 0, Search);
    Hi = tl_BuildLoopSearchSubformula(iClauseList, &temporalVariableSymbol, &replacementVariableSymbol);
    previousTemporalVariableSymbol = temporalVariableSymbol;
    previousReplacementVariableSymbol = replacementVariableSymbol;
    if(flag_GetFlagValue(Flags, flag_PLOOPCAND) && !list_Empty(iClauseList)) {
      tl_PrintLoopSearchCandidateClauses(EventualityClause, 0, iClauseList);
    }
  }

  for(int i = 0; i < lastIterationIndex; ++i) {
    iSuccClauseList = tl_GetTerminatingLoopSearchStepClauses(EventualityClause, i + 1, Search);
    if(flag_GetFlagValue(Flags, flag_PLOOPCAND) && !list_Empty(iSuccClauseList)) {
      tl_PrintLoopSearchCandidateClauses(EventualityClause, i + 1, iSuccClauseList);
    }
    Hi2 = tl_BuildLoopSearchSubformula(iSuccClauseList, &temporalVariableSymbol, &replacementVariableSymbol);

    /* we still need to make sure that Hi and Hi2 share the same temporal and free variable */
    if(Hi && Hi2 &&
       (previousTemporalVariableSymbol != temporalVariableSymbol
         || previousReplacementVariableSymbol != replacementVariableSymbol)) {
      tl_UnifyVariables(Hi, Hi2, previousTemporalVariableSymbol,
                                 temporalVariableSymbol,
                                 previousReplacementVariableSymbol,
                                 replacementVariableSymbol);
    }

    previousTemporalVariableSymbol = temporalVariableSymbol;
    previousReplacementVariableSymbol = replacementVariableSymbol;

    if(Hi && Hi2) {
      TERM equivTerm = fol_CreateQuantifier(fol_All(), list_List(term_Create(temporalVariableSymbol, list_Nil())),
                                            list_List(fol_CreateQuantifier(fol_All(), list_List(term_Create(replacementVariableSymbol, list_Nil())),
                                            list_List(term_Create(fol_Equiv(), list_Cons(term_Copy(Hi),
                                                      list_List(term_Copy(Hi2))))))));

      if (flag_GetFlagValue(Flags, flag_PGIVEN)) {
        printf("\n equiv term: "); term_Print(equivTerm);
      }
      /* equivTerm deleted after this */
      BOOL valid = tl_TestMonadicValidity(Flags, Precedence, equivTerm, Search);


      if(valid) {
        prfs_IncSuccessfulLoopSearches(Search);
        LIST LoopFormulaClauses = tl_ComputeLoopSearchResult(iSuccClauseList, Flags, Precedence);
        if (flag_GetFlagValue(Flags, flag_PGIVEN)) {
          printf("\nFound Loop Formula (Eventuality="); clause_Print(EventualityClause); printf(", i=%i):", i);
          for(LIST Scan = LoopFormulaClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
            printf("\n"); clause_Print(list_Car(Scan));
          }
        }
        toReturn = list_Nconc(LoopFormulaClauses, toReturn);
      }
    }

    list_Delete(iClauseList);
    if(Hi) { /* this non-null check is necessary */
      term_Delete(Hi);
    }

    iClauseList = iSuccClauseList;
    Hi = Hi2;
  }

  if(Hi) { /* this non-null check is necessary */
    term_Delete(Hi);
  }
  if(iClauseList) {
    list_Delete(iClauseList);
  }
  return toReturn;
}


LIST tl_PerformLoopSearchTests(CLAUSE EventualityClause, PROOFSEARCH Search)
{
  FLAGSTORE Flags = prfs_Store(Search);

  if (flag_GetFlagValue(Flags, flag_LOOPSEARCHTEST) == flag_LOOPSEARCHTESTLOGICAL) {
    return tl_PerformLogicalLoopSearchTests(EventualityClause, Search);
  }
  else {
    return tl_PerformSubsumptionLoopSearchTests(EventualityClause, Search);
  }
}

CLAUSE tl_SimplifyLoopSearchMarkers(PROOFSEARCH Search, CLAUSE Clause, FLAGSTORE Flags,
         PRECEDENCE Precedence)
{
  LIST LiteralsToDelete = list_Nil();
  SYMBOL LoopSearchMarker = symbol_Null();
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);
    if(symbol_IsLoopSearchMarker(term_TopSymbol(Atom))) { // found a loop search marker
      SYMBOL NewLoopSearchMarker = term_TopSymbol(Atom);
      if(!symbol_Equal(LoopSearchMarker, symbol_Null())) {
        if(!symbol_Equal(LoopSearchMarker, NewLoopSearchMarker)) {
          prfs_IncDifferentMarkerClauses(Search, 1);
          if(flag_GetFlagValue(Flags, flag_PDIFFMARK)) {
            printf("\nDifferent loop search markers: "); clause_Print(Clause);
          }
          clause_Delete(Clause);
          return NULL;
        }
        else {
          LiteralsToDelete = list_Cons((POINTER) i, LiteralsToDelete);
        }
      }
      else {
        LoopSearchMarker = NewLoopSearchMarker;
      }
    }
  }
  clause_DeleteLiterals(Clause, LiteralsToDelete, Flags, Precedence);
  list_Delete(LiteralsToDelete);
  return Clause;
}


void tl_PrintLoopSearchClausesUpTo(LITERAL MarkerLiteral, SHARED_INDEX index)
{
  SYMBOL LoopSearchMarkerSymbol = term_TopSymbol(clause_LiteralAtom(MarkerLiteral));
  NAT i = tl_LOOPSEARCH_MARKER_INDEX_MAP[symbol_Index(LoopSearchMarkerSymbol)];
  CLAUSE EventualityClause = tl_LOOPSEARCH_MARKER_EVENTUALITY_MAP[symbol_Index(LoopSearchMarkerSymbol)];
  
  for(int j = 0; j < i; ++j) {
    LIST ClauseList = tl_GetLoopSearchStepClausesFromIndex(EventualityClause, j, index, FALSE);
    
    if(!list_Empty(ClauseList)) {
      printf("\nFound loop search clauses with an index %i for the loop search marker ", j); symbol_Print(LoopSearchMarkerSymbol);
      for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
        printf("\n\t"); clause_Print(list_Car(Scan));
      }

    }
    
    list_Delete(ClauseList);
  }
}


LIST tl_GetClausesWithSmallerLoopSearchIndex(LITERAL MarkerLiteral, SHARED_INDEX index)
{
  SYMBOL LoopSearchMarkerSymbol = term_TopSymbol(clause_LiteralAtom(MarkerLiteral));
  NAT i = tl_LOOPSEARCH_MARKER_INDEX_MAP[symbol_Index(LoopSearchMarkerSymbol)];
  CLAUSE EventualityClause = tl_LOOPSEARCH_MARKER_EVENTUALITY_MAP[symbol_Index(LoopSearchMarkerSymbol)];
  
  for(int j = 0; j < i; ++j) {
    LIST ClauseList = tl_GetLoopSearchStepClausesFromIndex(EventualityClause, j, index, FALSE);
    
    if(!list_Empty(ClauseList)) {
      return ClauseList;
    }
  }
  return NULL;
}

BOOL tl_UsableContainsUniversalClauses(PROOFSEARCH Search)
{
  LIST UsableClauseList = prfs_UsableClauses(Search);
  for(LIST Scan = UsableClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);
    if(clause_GetTemporalType(Clause) == UNIVERSAL) {
      return TRUE;
    }
  }
  return FALSE;
}

CLAUSE tl_FindUsableUniversalClause(PROOFSEARCH Search)
{
  LIST UsableClauseList = prfs_UsableClauses(Search);
  for(LIST Scan = UsableClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);
    if(clause_GetTemporalType(Clause) == UNIVERSAL) {
      return Clause;
    }
  }
  return NULL;
}

CLAUSE tl_FindUsableNonLoopSearchClause(PROOFSEARCH Search)
{
  LIST UsableClauseList = prfs_UsableClauses(Search);
  for(LIST Scan = UsableClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);
    if(!(clause_GetTemporalType(Clause) == TERMINATING_LOOPSEARCH
         || clause_GetTemporalType(Clause) == LOOPSEARCH)) {
      return Clause;
    }
  }
  return NULL;
}

CLAUSE tl_FindUsableLoopSearchClause(PROOFSEARCH Search)
{
  LIST UsableClauseList = prfs_UsableClauses(Search);
  for(LIST Scan = UsableClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);
    if(clause_GetTemporalType(Clause) == TERMINATING_LOOPSEARCH
         || clause_GetTemporalType(Clause) == LOOPSEARCH) {
      return Clause;
    }
  }
  return NULL;
}

TEMPORAL_TYPE tl_DetermineTemporalType(CLAUSE Clause)
{
  SYMBOL TemporalVariable = symbol_Null();
  BOOL FoundLoopSearchMarker = FALSE;
  BOOL FoundInitialAtom = FALSE;
  BOOL FoundUniversalAtom = FALSE, FoundPositiveUniversalAtom = FALSE;
  BOOL FoundStepAtom = FALSE;

  if(clause_IsEmptyClause(Clause)) {
    return UNIVERSAL;
  }
  
  for(int i = clause_FirstAntecedentLitIndex(Clause); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    TERM Atom = clause_LiteralAtom(Lit);
    SYMBOL LitTemporalVariable = symbol_Null();
    
    if(tl_IsLoopSearchMarkerAtom(Atom)) {
      FoundLoopSearchMarker = TRUE;
      continue;
    }
    if(tl_IsInitialAtom(Atom)) {
      FoundInitialAtom = TRUE;
      continue;
    }
    LitTemporalVariable = tl_TemporalVariable(Atom);
    if(symbol_Equal(TemporalVariable, symbol_Null())) {
      TemporalVariable = LitTemporalVariable;
    }
    else if(!symbol_Equal(TemporalVariable, LitTemporalVariable)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In tl_DetermineTemporalType:");
      misc_ErrorReport("\n Illegal input clause: contains wrong temporal variables.");
      misc_FinishErrorReport();
    }
    
    if(tl_IsUniversalAtom(Atom)) {
      FoundUniversalAtom = TRUE;
      if(clause_LiteralIsPositive(Lit)) {
        FoundPositiveUniversalAtom = TRUE;
      }
    }
    else if(tl_IsStepAtom(Atom)) {
      FoundStepAtom = TRUE;
    }
  }
  if(FoundInitialAtom && (FoundUniversalAtom || FoundStepAtom)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In tl_DetermineTemporalType:");
      misc_ErrorReport("\n Illegal input clause: contains mixture of literals.");
      misc_FinishErrorReport();
  }
  if(FoundInitialAtom) {
    return INITIAL_TYPE;
  }
  if(FoundStepAtom) {
    if(FoundPositiveUniversalAtom) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In tl_DetermineTemporalType:");
      misc_ErrorReport("\n Illegal input clause: step clause with positive universal atom.");
      misc_FinishErrorReport();
    }
    if(FoundLoopSearchMarker) {
      return LOOPSEARCH;
    }
    return STEP;
  }
  if(!FoundUniversalAtom) {
    if(FoundLoopSearchMarker) {
      return TERMINATING_LOOPSEARCH;
    }
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_DetermineTemporalType:");
    misc_ErrorReport("\n Illegal input clause."); clause_Print(Clause);
    misc_FinishErrorReport();
  }
  if(FoundLoopSearchMarker) {
    return TERMINATING_LOOPSEARCH;
  }
  return UNIVERSAL;
}

void tl_EnsureNoUniversalLiteralIsMaximal(CLAUSE StepClause)
{
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(StepClause); ++i) {
    LITERAL Lit = clause_GetLiteral(StepClause, i);
    TERM Atom = clause_LiteralAtom(Lit);
    if(tl_IsUniversalAtom(Atom) || list_Length(term_ArgumentList(Atom)) == 0) {
        clause_LiteralClearFlag(Lit, MAXIMAL);
        clause_LiteralClearFlag(Lit, STRICTMAXIMAL);
    }
  }
}

/////////////////////////////////////// Model Construction ///////////////////////////////////////

typedef HASH HERBRANDMODEL;

static __inline__ HERBRANDMODEL tl_CreateHerbrandModel()
{
  return hsh_Create();
}

static __inline__ void tl_DeleteHerbrandModel(HERBRANDMODEL Model)
{
  hsh_Delete(Model);
}

static __inline__ BOOL tl_Models(HERBRANDMODEL Model, SYMBOL Symbol)
{
  return !list_Empty(hsh_Get(Model, (POINTER)symbol_Index(Symbol)));
}

static __inline__ LIST tl_GetAllSymbols(HERBRANDMODEL Model)
{
  return hsh_GetAllEntries(Model);
}

static __inline__ BOOL tl_ModelsLiteral(HERBRANDMODEL Model, LITERAL Lit)
{
  SYMBOL LiteralSymbol = clause_LiteralSymbol(Lit);
  if(clause_LiteralIsNegative(Lit)) {
    return !tl_Models(Model, LiteralSymbol);
  }
  else {
    return tl_Models(Model, LiteralSymbol);
  }
}

static __inline__ BOOL tl_ModelsClause(HERBRANDMODEL Model, CLAUSE Clause)
{
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    if(tl_ModelsLiteral(Model, Lit)) {
      return TRUE;
    }
  }
  return FALSE;
}

static __inline__ BOOL tl_ModelsClauseList(HERBRANDMODEL Model, LIST ClauseList)
{
  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    
    if(!tl_ModelsClause(Model, Clause)) {
      return FALSE;
    }
  }
  return TRUE;
}

static __inline__ void tl_AddSymbol(HERBRANDMODEL Model, SYMBOL Symbol)
{
  hsh_Put(Model, (POINTER)symbol_Index(Symbol), Model); // use the 'Model' pointer so that
                                                        // the hash arry consistency checks succeeds
}

static void tl_PrintHerbrandModel(HERBRANDMODEL Model)
{
  LIST Predicates = symbol_GetAllPredicates();
  printf("{");
  BOOL firstElement = TRUE;
  for(LIST Scan = Predicates; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Symbol = (SYMBOL) list_Car(Scan);
    if(symbol_Arity(Symbol) == 1
       && tl_Models(Model, Symbol)) { // we only care about propositional 'variables'
      if(!firstElement) {
        printf(", ");
      }
      else {
        firstElement = FALSE;
      }
      symbol_Print(Symbol);
    }
  }
  printf("}");
  list_Delete(Predicates);
}

static BOOL tl_ModelsEqual(HERBRANDMODEL Model1, HERBRANDMODEL Model2)
{
  BOOL toReturn = TRUE;
  LIST Predicates = symbol_GetAllPredicates();
  for(LIST Scan = Predicates; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Symbol = (SYMBOL) list_Car(Scan);
    if(symbol_Arity(Symbol) == 1) { // we only care about propositional 'variables'
      if((tl_Models(Model1, Symbol) && !tl_Models(Model2, Symbol))
          || (!tl_Models(Model1, Symbol) && tl_Models(Model2, Symbol))) {
        toReturn = FALSE;
        break;
      }
    }
  }
  list_Delete(Predicates);
  return toReturn;
}

/**
 * CAUTION: the clause must be properly initialised!
 **/
static LITERAL tl_MaxPropositionalLiteral(CLAUSE Clause, PRECEDENCE Precedence)
{
  LITERAL MaxLiteral = NULL;
  SYMBOL MaxAtomSymbol = symbol_Null();
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL ActLiteral = clause_GetLiteral(Clause, i);
    SYMBOL ActAtomSymbol;

    if(!MaxLiteral) {
      MaxLiteral = clause_GetLiteral(Clause, i);
      MaxAtomSymbol = term_TopSymbol(clause_LiteralAtom(MaxLiteral));
      continue;
    }
    ActAtomSymbol = term_TopSymbol(clause_LiteralAtom(ActLiteral));
    if(symbol_PrecedenceGreater(Precedence, ActAtomSymbol, MaxAtomSymbol)) {
      MaxLiteral = ActLiteral;
      MaxAtomSymbol = ActAtomSymbol;
    }
  }
  if(!MaxLiteral) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_MaxPropositionalLiteral:");
    misc_ErrorReport("\n Illegal input clause: no maximal literal found!");
    misc_FinishErrorReport();
  }
  return MaxLiteral;
}

// a little hack to avoid defining new sorting methods that can take an additional parameter
static PRECEDENCE clauseComparisonPrecedence = NULL;

static __inline__ BOOL tl_EqualPropositionalLiteral(LITERAL Lit1, LITERAL Lit2)
{
  SYMBOL Symbol1 = term_TopSymbol(clause_LiteralAtom(Lit1));
  SYMBOL Symbol2 = term_TopSymbol(clause_LiteralAtom(Lit2));
  if(!clauseComparisonPrecedence) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_GreaterEqualPropositionalLiteral:");
    misc_ErrorReport("\n Comparison precedence not set.");
    misc_FinishErrorReport();
    return FALSE;
  }
  if(Symbol1 == Symbol2) {
    return (clause_LiteralIsNegative(Lit1) && clause_LiteralIsNegative(Lit2))
           || (!clause_LiteralIsNegative(Lit1) && !clause_LiteralIsNegative(Lit2));
  }
  return FALSE;
}

static __inline__ BOOL tl_GreaterPropositionalLiteral(LITERAL Lit1, LITERAL Lit2)
{
  SYMBOL Symbol1 = term_TopSymbol(clause_LiteralAtom(Lit1));
  SYMBOL Symbol2 = term_TopSymbol(clause_LiteralAtom(Lit2));
  if(!clauseComparisonPrecedence) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_GreaterEqualPropositionalLiteral:");
    misc_ErrorReport("\n Comparison precedence not set.");
    misc_FinishErrorReport();
    return FALSE;
  }
  if(Symbol1 == Symbol2) {
    return clause_LiteralIsNegative(Lit1) && !clause_LiteralIsNegative(Lit2);
  }
  return symbol_PrecedenceGreater(clauseComparisonPrecedence, Symbol1, Symbol2);
}

static __inline__ BOOL tl_GreaterEqualPropositionalLiteral(LITERAL Lit1, LITERAL Lit2)
{
  return tl_GreaterPropositionalLiteral(Lit1, Lit2) || tl_GreaterPropositionalLiteral(Lit1, Lit2);
}

static BOOL tl_PropositionalClausesLessEqual(CLAUSE Clause1, CLAUSE Clause2)
{
  BOOL toReturn = TRUE;
  LIST LiteralList1 = clause_GetLiteralList(Clause1);
  LIST LiteralList2 = clause_GetLiteralList(Clause2);
  LIST Scan1 = list_Nil(), Scan2 = list_Nil();
  if(!clauseComparisonPrecedence) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_PropositionalClausesLessEqual:");
    misc_ErrorReport("\n Comparison precedence not set.");
    misc_FinishErrorReport();
    return FALSE;
  }

  LiteralList1 = list_Sort(LiteralList1, (BOOL (*)(POINTER, POINTER))tl_GreaterEqualPropositionalLiteral);
  LiteralList2 = list_Sort(LiteralList2, (BOOL (*)(POINTER, POINTER))tl_GreaterEqualPropositionalLiteral);

  Scan1 = LiteralList1;
  Scan2 = LiteralList2;
  
  while(!list_Empty(Scan1) && !list_Empty(Scan2)) {
    LITERAL Lit1 = (LITERAL) list_Car(Scan1);
    LITERAL Lit2 = (LITERAL) list_Car(Scan2);
    if(tl_GreaterPropositionalLiteral(Lit1, Lit2)) {
      toReturn = FALSE;
      break;
    }
    else if(tl_GreaterPropositionalLiteral(Lit2, Lit1)) {
      toReturn = TRUE;
      break;
    }

    Scan1 = list_Cdr(Scan1);
    Scan2 = list_Cdr(Scan2);
  }
  if(list_Empty(Scan1) || list_Empty(Scan2)) {
      toReturn = list_Empty(Scan1);
  }
  
  list_Delete(LiteralList1);
  list_Delete(LiteralList2);

  return toReturn;
}

static HERBRANDMODEL tl_ConstructHerbrandModelForPropositionalClauses(LIST ClauseList, PRECEDENCE Precedence, FLAGSTORE Flags)
{
  HERBRANDMODEL toReturn = tl_CreateHerbrandModel();
  clauseComparisonPrecedence = Precedence;
  LIST SortedClauseList = list_Sort(list_Copy(ClauseList), (BOOL (*)(POINTER, POINTER))tl_PropositionalClausesLessEqual);
  clauseComparisonPrecedence = NULL;
  for(LIST Scan = SortedClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    LITERAL MaxLiteral = tl_MaxPropositionalLiteral(Clause, Precedence);
    SYMBOL MaxSymbol = clause_LiteralSymbol(MaxLiteral);

    if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
      printf("\nConsidering the clause "); clause_Print(Clause);
    }
    if(clause_LiteralIsNegative(MaxLiteral)) {
      if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
        printf("\n\tMaximal literal is negative.");
      }
      continue;
    }
    if(tl_ModelsClause(toReturn, Clause)) {
      if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
        printf("\n\tClause is already true in the partial model.");
      }
      continue;
    }
    tl_AddSymbol(toReturn, MaxSymbol);
    if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
      printf("\n\tSymbol '"); symbol_Print(MaxSymbol); printf("' is productive.");
    }
  }
  list_Delete(SortedClauseList);

  if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
    printf("\nModel constructed: "); tl_PrintHerbrandModel(toReturn);
  }
  return toReturn;
}

/**
 * CAUTION: 'Unordered' means unordered propositional fine-grained step resolution!
 **/
static PROOFSEARCH tl_SaturateClauseSetUnderFineGrainedStepResolutionSearch(LIST ClauseList, BOOL Propositional,
                                                                            BOOL Unordered, PRECEDENCE Precedence)
{
  PROOFSEARCH Search = prfs_Create();
  FLAGSTORE Flags = prfs_Store(Search);
  int BoundApplied = -1;
  BOOL OldTemporalMode = TEMPORAL_MODE;

  flag_SetFlagValue(Flags, flag_AUTO, flag_OFF); // has to be turned as it changes the precedence
  flag_SetFlagValue(Flags, flag_PPROBLEM, flag_OFF);
  flag_SetFlagValue(Flags, flag_SELECT, flag_SELECTOFF);
  flag_SetFlagValue(Flags, flag_IORE, flag_ORDEREDRESOLUTIONNOEQUATIONS);
  flag_SetFlagValue(Flags, flag_IOFC, flag_FACTORINGONLYRIGHT);
  flag_SetFlagValue(Flags, flag_ROBV, flag_ROBVON);
  flag_SetFlagValue(Flags, flag_RTAUT, flag_RTAUTSYNTACTIC);
  flag_SetFlagValue(Flags, flag_RFSUB, flag_RFSUBON);
  flag_SetFlagValue(Flags, flag_RBSUB, flag_RBSUBON);
  flag_SetFlagValue(Flags, flag_FULLRED, flag_FULLREDON);
  flag_SetFlagValue(Flags, flag_WDRATIO, 5);
  flag_SetFlagValue(Flags, flag_CNFOPTSKOLEM, flag_CNFOPTSKOLEMOFF);

  if(Unordered) {
    flag_SetFlagValue(Flags, flag_UNORDEREDFINEGRAINEDSTEPRESOLUTION, flag_UNORDEREDFINEGRAINEDSTEPRESOLUTIONON);
    flag_SetFlagValue(Flags, flag_IOFC, flag_FACTORINGOFF); // the deletion of duplicate literals is done with 'ROBV'
  }
  else {
    flag_SetFlagValue(Flags, flag_UNORDEREDFINEGRAINEDSTEPRESOLUTION, flag_UNORDEREDFINEGRAINEDSTEPRESOLUTIONOFF);  
  }

  // get our precedence in
  if(Precedence) {
    symbol_TransferPrecedence(Precedence, prfs_Precedence(Search));
  }

  // Reinitialise all the clauses
  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    clause_ClearFlags(Clause);
    clause_OrientAndReInit(Clause, Flags, Precedence);
  }

  if(Propositional) {
  // deactivate the temporal mode
    TEMPORAL_MODE = FALSE;
  }
  else {
    TEMPORAL_MODE = TRUE;
  }

//   prfs_SetSplitCounter(Search, flag_GetFlagValue(Flags, flag_SPLITS));
  prfs_SetLoops(Search, -1);
//   prfs_SetBacktrackedClauses(Search, 0);
  
  Search = proof_ProofSearch(Search, ClauseList,
                                     Flags, list_Nil(), &BoundApplied, FALSE);

  TEMPORAL_MODE = OldTemporalMode;

  // transfer the statistics from the old search object to the new one
//   prfs_SetDerivedClauses(OldSearch, prfs_DerivedClauses(OldSearch) + prfs_DerivedClauses(Search));
//   prfs_SetKeptClauses(OldSearch, prfs_KeptClauses(OldSearch) + prfs_KeptClauses(Search));
//   prfs_SetInputClauses(OldSearch, prfs_InputClauses(OldSearch) + prfs_InputClauses(Search));
//   prfs_SetForwardSubsumedClauses(OldSearch, prfs_ForwardSubsumedClauses(OldSearch) + prfs_ForwardSubsumedClauses(Search));
//   prfs_SetBackwardSubsumedClauses(OldSearch, prfs_BackwardSubsumedClauses(OldSearch) + prfs_BackwardSubsumedClauses(Search));

  /*  symbol_ResetSkolemIndex(); */
  list_Delete(ClauseList);
//   if (flag_GetFlagValue(InputFlags, flag_DOCPROOF)) {

  return Search;
}

static __inline__ PROOFSEARCH tl_SaturatePropositionalClauseSetSearch(LIST ClauseList, PRECEDENCE Precedence)
{
  return tl_SaturateClauseSetUnderFineGrainedStepResolutionSearch(ClauseList, TRUE, FALSE, Precedence);
}

static LIST tl_SaturateClauseSetUnderFineGrainedStepResolution(LIST ClauseList, BOOL Propositional,
                                                               BOOL Unordered, PRECEDENCE Precedence)
{
  PROOFSEARCH Search = tl_SaturateClauseSetUnderFineGrainedStepResolutionSearch(ClauseList, Propositional, Unordered, Precedence);
  if(!list_Empty(prfs_EmptyClauses(Search))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In tl_SaturatePropositionalClauseSet:");
    misc_ErrorReport("\n Unsatisfiable clause set given.");
    misc_FinishErrorReport();  
  }
  LIST toReturn = prfs_WorkedOffClauses(Search);
  for(LIST Scan = toReturn; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    clause_MakeUnshared(Clause, prfs_WorkedOffSharingIndex(Search));    
  }
  prfs_SetWorkedOffClauses(Search, list_Nil());
  prfs_Delete(Search);

  return toReturn;
}

static __inline__ LIST tl_SaturatePropositionalClauseSet(LIST ClauseList, PRECEDENCE Precedence)
{
  return tl_SaturateClauseSetUnderFineGrainedStepResolution(ClauseList, TRUE, FALSE, Precedence);
}

/**
 * CAUTION: 'ClauseList' has to be saturated!
 **/
static HERBRANDMODEL tl_ConstructHerbrandModelForPropositionalClausesWithImpliedEventuality(LIST ClauseList, CLAUSE EventualityClause,
                                                                                            PRECEDENCE Precedence, FLAGSTORE Flags)
{
  LIST NewClauseList = list_Nil();
  LIST ModelConstructionClauseList = ClauseList;
  PROOFSEARCH Search = NULL;
  HERBRANDMODEL toReturn = NULL;

  if(EventualityClause) {
    LITERAL EventualityLiteral = tl_GetEventualityLiteral(EventualityClause);
    TERM EventualityAtom = clause_LiteralAtom(EventualityLiteral);
    LIST EventualityLiteralList = list_List(term_Copy(EventualityAtom));
    CLAUSE NegatedEventualityClause = NULL;

    if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
      printf("\nChecking whether the eventuality can be satisfied... ");
    }

    if(clause_LiteralIsNegative(EventualityLiteral)) {
      NegatedEventualityClause = clause_Create(list_Nil(), EventualityLiteralList, list_Nil(), Flags, Precedence);  
    }
    else {
      NegatedEventualityClause = clause_Create(list_Nil(), list_Nil(), EventualityLiteralList, Flags, Precedence);
    }
    list_Delete(EventualityLiteralList);

    NewClauseList = clause_CopyClauseList(ClauseList);
    NewClauseList = list_Cons(NegatedEventualityClause, NewClauseList);

    Search = tl_SaturatePropositionalClauseSetSearch(NewClauseList, Precedence); // 'NewClauseList' is deleted after thia


    if(!list_Empty(prfs_EmptyClauses(Search))) { // 'ClauseList' implies the negated eventuality
      if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
        printf("Found a contradiction.");
      }
      ModelConstructionClauseList = ClauseList;
    }
    else {
      if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
        printf("No contradiction found.");
      }
      ModelConstructionClauseList = prfs_WorkedOffClauses(Search);
    }

  // 
  //   // transfer the statistics from the old search object to the new one
  //   prfs_SetDerivedClauses(OldSearch, prfs_DerivedClauses(OldSearch) + prfs_DerivedClauses(Search));
  //   prfs_SetKeptClauses(OldSearch, prfs_KeptClauses(OldSearch) + prfs_KeptClauses(Search));
  //   prfs_SetInputClauses(OldSearch, prfs_InputClauses(OldSearch) + prfs_InputClauses(Search));
  //   prfs_SetForwardSubsumedClauses(OldSearch, prfs_ForwardSubsumedClauses(OldSearch) + prfs_ForwardSubsumedClauses(Search));
  //   prfs_SetBackwardSubsumedClauses(OldSearch, prfs_BackwardSubsumedClauses(OldSearch) + prfs_BackwardSubsumedClauses(Search));
  // 
  //   /*  symbol_ResetSkolemIndex(); */

  //   list_Delete(ClauseList);
  //
  }

  if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
    printf("\nBuilding the model:");
  }
  toReturn = tl_ConstructHerbrandModelForPropositionalClauses(ModelConstructionClauseList, Precedence, Flags);

  if(EventualityClause) {
    prfs_Delete(Search);
//     clause_DeleteClauseList(NewClauseList);/**/
  }

  return toReturn;
}

static __inline__ void tl_PropositionalAtomToUniversalAtom(TERM Atom)
{
  term_Delete(term_FirstArgument(Atom));
  term_RplacFirstArgument(Atom, term_Create(symbol_FirstVariable(), list_Nil()));
}

static __inline__ void tl_InitialPropositionalClauseToUniversalClause(CLAUSE Clause)
{
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    tl_PropositionalAtomToUniversalAtom(clause_LiteralAtom(Lit));
  }
  clause_Normalize(Clause);
}

static __inline__ LIST tl_ExtractStepSignedAtomsFromPropositionalStepClause(CLAUSE Clause)
{
  LIST toReturn = list_Nil();
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    if(tl_IsStepAtom(clause_LiteralAtom(Lit))) {
      toReturn = list_Cons(term_Copy(clause_LiteralSignedAtom(Lit)), toReturn);
    }
  }
  return toReturn;
}

static __inline__ LIST tl_ExtractUniversalSignedAtomsFromPropositionalStepClause(CLAUSE Clause)
{
  LIST toReturn = list_Nil();
  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    if(tl_IsUniversalAtom(clause_LiteralAtom(Lit))) {
      toReturn = list_Cons(clause_LiteralSignedAtom(Lit), toReturn);
    }
  }
  return toReturn;
}

static CLAUSE tl_RightHandSideOfStepClauseToClause(CLAUSE Clause, PRECEDENCE Precedence, FLAGSTORE Flags)
{
  CLAUSE toReturn = NULL;
  LIST SignedStepAtoms = tl_ExtractStepSignedAtomsFromPropositionalStepClause(Clause);
  for(LIST Scan = SignedStepAtoms; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM SignedAtom = (TERM) list_Car(Scan);
    TERM Atom = (term_TopSymbol(SignedAtom) == fol_Not() ? term_FirstArgument(SignedAtom)
                                                         : SignedAtom);
    tl_PropositionalAtomToUniversalAtom(Atom);
  }
  toReturn = clause_CreateFromLiterals(SignedStepAtoms, FALSE, FALSE, TRUE, Flags, Precedence);
  list_Delete(SignedStepAtoms);
  return toReturn;
}

static __inline__ BOOL tl_ModelsLeftHandSideOfStepClause(HERBRANDMODEL Model, CLAUSE StepClause)
{
  BOOL toReturn = TRUE;
  LIST LeftHandSideSignedAtoms = tl_ExtractUniversalSignedAtomsFromPropositionalStepClause(StepClause);
  for(LIST Scan = LeftHandSideSignedAtoms; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM SignedAtom = (TERM) list_Car(Scan);
    assert(term_TopSymbol(SignedAtom) == fol_Not());
    if(!tl_Models(Model, term_TopSymbol(term_FirstArgument(SignedAtom)))) {
      toReturn = FALSE;
      break;
    }
  }
  list_Delete(LeftHandSideSignedAtoms);
  return toReturn;
}

static LIST tl_TriggeredStepClauses(HERBRANDMODEL Model, LIST StepClauses)
{
  LIST toReturn = list_Nil();
  for(LIST Scan = StepClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE StepClause = (CLAUSE) list_Car(Scan);
    if(tl_ModelsLeftHandSideOfStepClause(Model, StepClause)) {
      toReturn = list_Cons(StepClause, toReturn);
    }
  }
  return toReturn;
}

/**
 * CAUTION: 'List' must be a list of symbols
 **/
static __inline__ BOOL tl_ModelsLeftHandSide(HERBRANDMODEL Model, LIST List)
{
  for(LIST Scan = List; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Symbol = (SYMBOL) list_Car(Scan);
    if(!tl_Models(Model, Symbol)) {
      return FALSE;
    }
  }
  return TRUE;
}

/**
 * CAUTION: 'List' must be a list of symbol lists
 **/
static __inline__ BOOL tl_ModelsLeftHandSides(HERBRANDMODEL Model, LIST List)
{
  for(LIST Scan = List; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST List2 = (LIST) list_Car(Scan);
    if(tl_ModelsLeftHandSide(Model, List2)) {
      return TRUE;
    }
  }
  return FALSE;
}

/**
 * CAUTION: 'List' must be a list of symbol lists
 **/
static __inline__ unsigned long tl_NumberOfLeftHandSidesModelled(HERBRANDMODEL Model, LIST List)
{
  unsigned long toReturn = 0;
  for(LIST Scan = List; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST List2 = (LIST) list_Car(Scan);
    if(tl_ModelsLeftHandSide(Model, List2)) {
      ++toReturn;
    }
  }
  return toReturn;
}

static __inline__ BOOL tl_ModelsEventuality(HERBRANDMODEL Model, CLAUSE EventualityClause)
{
  LITERAL EventualityLiteral = tl_GetEventualityLiteral(EventualityClause);
  SYMBOL EventualitySymbol = tl_GetEventualitySymbol(EventualityClause);
  return (clause_LiteralIsNegative(EventualityLiteral) ? !tl_Models(Model, EventualitySymbol)
                                                       : tl_Models(Model, EventualitySymbol));
}

static __inline__ LIST tl_ListOfCriticalStepClauses(CLAUSE EventualityClause, PROOFSEARCH Search)
{
	return tl_GetTerminatingLoopSearchStepClauses(EventualityClause, 0, Search);
}

/*/
 * Returns a list of symbol lists!
 **/
static LIST tl_ListOfCriticalLeftHandSidesAsSymbols(CLAUSE EventualityClause, PROOFSEARCH Search)
{
  LIST toReturn = list_Nil();
  LIST TerminatingStepClauses =  tl_ListOfCriticalStepClauses(EventualityClause, Search);

  for(LIST Scan = TerminatingStepClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    LIST SymbolList = list_Nil();

    for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
      TERM Atom = clause_LiteralAtom((LITERAL) clause_GetLiteral(Clause, i));
      const int argumentCount = list_Length(term_ArgumentList(Atom));
      assert(argumentCount <= 1);
      if(argumentCount == 1) {
        SymbolList = list_Cons((POINTER) term_TopSymbol(Atom), SymbolList);
      }
    }
    toReturn = list_Cons(SymbolList, toReturn);
  }
  list_Delete(TerminatingStepClauses);
  return toReturn;
}

static __inline__ BOOL tl_ContainsSymbol(LIST List, SYMBOL Symbol)
{
  for(LIST Scan = List; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      SYMBOL Symbol2 = (SYMBOL) list_Car(Scan);
      if(symbol_Equal(Symbol, Symbol2)) {
        return TRUE;
      }
  }
  return FALSE;
}

LIST tl_ListOfSymbolsFromLeftHandSides(LIST List)
{
  LIST toReturn = list_Nil();
  for(LIST Scan = List; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);

    for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
      LITERAL Lit = (LITERAL) clause_GetLiteral(Clause, i);
      TERM Atom = clause_LiteralAtom(Lit);
      const int argumentCount = list_Length(term_ArgumentList(Atom));
      assert(argumentCount <= 1);
      if(argumentCount == 1 && tl_IsUniversalLiteral(Lit)) { // we only consider propositional literals
        SYMBOL Symbol = term_TopSymbol(Atom);
        if(!tl_ContainsSymbol(toReturn, Symbol)) {
          toReturn = list_Cons((POINTER) Symbol, toReturn);
        }
      }
    }
  }
  return toReturn;
}

static LIST tl_ComputeSymbolListWithCriticalSymbolsFirst(LIST CriticalLeftHandSidesAsSymbols, LIST ListOfLeftHandSideSymbols,
                                                                                              unsigned long* NumberOfCriticalSymbols)
{
  LIST toReturn = list_Nil();
  for(LIST Scan = CriticalLeftHandSidesAsSymbols; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST SymbolList = (LIST) list_Car(Scan);
    for(LIST Scan2 = SymbolList; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
      SYMBOL Symbol = (SYMBOL) list_Car(Scan2);
      if(!tl_ContainsSymbol(toReturn, Symbol)) {
        toReturn = list_Cons((POINTER) Symbol, toReturn);
      }
    }
  }
  if(NumberOfCriticalSymbols) {
    *NumberOfCriticalSymbols = list_Length(toReturn);
  }
  for(LIST Scan = ListOfLeftHandSideSymbols; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Symbol = (SYMBOL) list_Car(Scan);
    if(!tl_ContainsSymbol(toReturn, Symbol)) {
      toReturn = list_Nconc(toReturn, list_List((POINTER) Symbol));
    }
  }
  return toReturn;
}

typedef struct
{
  unsigned long length;
  unsigned long *indexes;
} SUBSET_HELP, *SUBSET;
/*
typedef struct
{
  ARRAY subSet;
  ARRAY tuple;
} ORDERINGINDEX_HELP, *ORDERINGINDEX;

static __inline__ ORDERINGINDEX tl_CreateOrderingIndex(int n)
{
  ORDERINGINDEX toReturn = memory_Malloc(sizeof(ORDERINGINDEX_HELP));
  toReturn->subSet.indexes = memory_Malloc(n * sizeof(unsigned long));
  toReturn->tuple.indexes = memory_Malloc(n * sizeof(unsigned long));
  toReturn->subSet.length = n;
  toReturn->tuple.length = n;
return toReturn;
}
*/
static __inline__ SUBSET tl_CreateSubSet(int n)
{
  SUBSET toReturn = memory_Malloc(sizeof(SUBSET_HELP));
  toReturn->indexes = memory_Malloc(n * sizeof(unsigned long));
  toReturn->length = n;
  return toReturn;
}

static __inline__ void tl_DeleteSubSet(SUBSET SubSet)
{
  if(SubSet) {
    memory_Free(SubSet->indexes, MAX(1, SubSet->length) * sizeof(unsigned long));
    memory_Free(SubSet, sizeof(*SubSet));
  }
}

static __inline__ SUBSET tl_CopySubSet(SUBSET SubSet)
{
  SUBSET toReturn = tl_CreateSubSet(MAX(1, SubSet->length));
  toReturn->length = SubSet->length;
  memcpy(toReturn->indexes, SubSet->indexes, MAX(1, SubSet->length) * sizeof(*SubSet->indexes));
  return toReturn;
}

/*---UNUSED---
static void tl_PrintOrderingIndex(SUBSET SubSet)
{
  printf("\n(");
  for(unsigned long i = 0; i < Index->subSet.length; ++i) {
    if(i > 0) {
      printf(", ");
    }
    printf("%lu", Index->subSet.indexes[i]);
  }
  printf(")-(");
 for(unsigned long i = 0; i < Index->tuple.length; ++i) {
    if(i > 0) {
      printf(", ");
    }
    printf("%lu", Index->tuple.indexes[i]);
  }
}
*/

/*---UNUSED---
static void tl_PrintSubSet(SUBSET SubSet)
{
  if(!SubSet) {
    printf("(NULL)");
    return;
  }
  printf("{");
  printf("length %lu: ", SubSet->length);
  for(unsigned long i = 0; i < SubSet->length; ++i) {
    if(i > 0) {
      printf(", ");
    }
      printf("%lu", SubSet->indexes[i]);
  }
  printf("}");
}
*/

static __inline__ BOOL tl_IsEmptySubSet(SUBSET SubSet)
{
  return (SubSet && SubSet->length == 0 && SubSet->indexes[0] == 0);
}

static __inline__ SUBSET tl_CreateEmptySubSet()
{
  SUBSET toReturn = tl_CreateSubSet(1);
  toReturn->indexes[0] = 0;
  toReturn->length = 0;
  return toReturn;
}

static __inline__ SUBSET tl_CreateFirstProperSubSet()
{
  SUBSET toReturn = tl_CreateSubSet(1);
  toReturn->indexes[0] = 1;
  toReturn->length = 1;
  return toReturn;
}

static __inline__ SUBSET tl_CreateFullSubSet(unsigned long SetSize)
{
  SUBSET toReturn = tl_CreateSubSet(SetSize);
  for(unsigned long i = 0; i < SetSize; ++i) {
    toReturn->indexes[i] = i + 1;
  }
  return toReturn;
}

static SUBSET tl_NextSubSet(SUBSET SubSet, unsigned long GlobalSetSize)
{
  SUBSET toReturn = NULL;
  if(GlobalSetSize == 0 || !SubSet) {
    return tl_CreateEmptySubSet();
  }

  if(tl_IsEmptySubSet(SubSet)) {
    return tl_CreateFirstProperSubSet();
  }

  // are we finished yet?
  if(SubSet->indexes[0] + SubSet->length - 1 == GlobalSetSize) {
    // we have computed all the subsets, so start over again
    if(SubSet->length == GlobalSetSize) {
      return tl_CreateEmptySubSet();
    }
    else { // continue with the subsets of SubSet->length + 1
      toReturn = tl_CreateSubSet(SubSet->length + 1);
      for(unsigned long i = 0; i < SubSet->length + 1; ++i) {
        toReturn->indexes[i] = i + 1;
      }
      return toReturn;
    }
  }

  toReturn = tl_CreateSubSet(SubSet->length);
  memcpy(toReturn->indexes, SubSet->indexes, SubSet->length * sizeof(*(SubSet->indexes)));
  // compute the next subset using a bit addition scheme
  for(unsigned long i = SubSet->length; i > 0; --i) {
    if(SubSet->indexes[i - 1] + (SubSet->length - i) == GlobalSetSize) {
      continue;
    }
    else {
      unsigned long startValue = SubSet->indexes[i - 1] + 1;
      for(unsigned long j = i - 1; j < toReturn->length; ++j) {
        toReturn->indexes[j] = startValue;
        ++startValue;
      }
      break;
    }
  }

  return toReturn;
}

static __inline__ SUBSET tl_MergeSubsets(SUBSET SubSet1, unsigned long globalSetSize1,
                                         SUBSET SubSet2)
{
  if(SubSet1->length == 0 && SubSet2->length == 0) {
    return tl_CreateEmptySubSet();
  }
  SUBSET toReturn = tl_CreateSubSet(SubSet1->length + SubSet2->length);
  if(!tl_IsEmptySubSet(SubSet1)) {
    memcpy(toReturn->indexes, SubSet1->indexes, SubSet1->length * sizeof(*(SubSet1->indexes)));
  }
  if(!tl_IsEmptySubSet(SubSet2)) {
    for(unsigned long i = 0; i < SubSet2->length; ++i) {
      toReturn->indexes[i + SubSet1->length] = globalSetSize1 + SubSet2->indexes[i];
    }
  }
  return toReturn;
}

static __inline__ BOOL tl_SubSetsEqual(SUBSET S1, SUBSET S2)
{
  if(!S1 || !S2) {
    return FALSE;
  }
  if(S1->length != S2->length) {
    return FALSE;
  }
  for(unsigned long i = 0; i < S1->length; ++i) {
    if(S1->indexes[i] != S2->indexes[i]) {
      return FALSE;
    }
  }
  return TRUE;
}

static __inline__ BOOL tl_SubSetListContains(LIST List, SUBSET SubSet)
{
  return list_Member(List, SubSet, (BOOL (*)(POINTER, POINTER)) tl_SubSetsEqual);
}

static __inline__ void tl_DeleteSubSetList(LIST List, BOOL DeleteListItself)
{
  for(LIST Scan = List; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    tl_DeleteSubSet((SUBSET) list_Car(Scan));
  }
  if(DeleteListItself) {
    list_Delete(List);
  }
}

static __inline__ LIST tl_CopySubSetList(LIST List)
{
  return list_CopyWithElement(List, (POINTER (*)(POINTER)) tl_CopySubSet);
}

/**
 * CAUTION: the indices in 'SubSet' have to be in increasing order!
 **/
static PRECEDENCE tl_CreatePrecedence(SUBSET SubSet, LIST CriticalSymbols)
{
  unsigned long counter = 1, elementsAdded = 0;
  PRECEDENCE toReturn = symbol_CreatePrecedence();
  HASH ConsideredSymbolsHash = hsh_Create();
  LIST ConsideredSymbolsList = list_Nil();
  LIST SymbolList = symbol_GetAllSymbols();
  symbol_ReinitOrderingCounter();
  for(LIST Scan = CriticalSymbols; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Symbol = (SYMBOL) list_Car(Scan);
    if(SubSet->indexes[elementsAdded] == counter) {
      hsh_Put(ConsideredSymbolsHash, (POINTER) Symbol, ConsideredSymbolsHash);
      ConsideredSymbolsList = list_Cons((POINTER) Symbol, ConsideredSymbolsList);
      ++elementsAdded;
      if(elementsAdded == SubSet->length) {
        break;
      }
    }
    ++counter;
  }
  for(LIST Scan = SymbolList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Symbol = (SYMBOL) list_Car(Scan);
      if(list_Empty(hsh_Get(ConsideredSymbolsHash, (POINTER) Symbol))) {
        symbol_SetIncreasedOrdering(toReturn, Symbol);
      }
  }
  for(LIST Scan = ConsideredSymbolsList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Symbol = (SYMBOL) list_Car(Scan);
    symbol_SetIncreasedOrdering(toReturn, Symbol);    
  }
  list_Delete(SymbolList);
  list_Delete(ConsideredSymbolsList);
  hsh_Delete(ConsideredSymbolsHash);

  return toReturn;
}

/* ---UNUSED---
static PRECEDENCE tl_CreatePrecedenceWithSymbolsMinimal(LIST CriticalSymbolsList)
{
  SUBSET FullSet = tl_CreateFullSubSet(list_Length(CriticalSymbolsList));
  PRECEDENCE toReturn = tl_CreatePrecedence(FullSet, CriticalSymbolsList);
  tl_DeleteSubSet(FullSet);

  return toReturn;
}
*/

static void tl_DeleteNegatedEventualityLiteral(CLAUSE Clause, CLAUSE EventualityClause, FLAGSTORE Flags, PRECEDENCE Precedence)
{
  LITERAL EventualityLiteral = tl_GetEventualityLiteral(EventualityClause);
  BOOL EventualityIsPositive = clause_LiteralIsPositive(EventualityLiteral);
  SYMBOL EventualitySymbol = term_TopSymbol(clause_LiteralAtom(EventualityLiteral));
  LIST LiteralIndicesList = list_Nil();

  for(int i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); ++i) {
    LITERAL Lit = clause_GetLiteral(Clause, i);
    SYMBOL LiteralSymbol = term_TopSymbol(clause_LiteralAtom(Lit));
    BOOL IsPositive = clause_LiteralIsPositive(Lit);
    if(symbol_Equal(EventualitySymbol, LiteralSymbol)
       && (EventualityIsPositive || IsPositive)
       && (!IsPositive || !EventualityIsPositive)) { /* !EventualityIsPositive and IsPositive have the same polarity */
       LiteralIndicesList = list_Cons((POINTER) i, LiteralIndicesList);
    }
  }
  clause_DeleteLiterals(Clause, LiteralIndicesList, Flags, Precedence);
  list_Delete(LiteralIndicesList);
}

static void tl_DeleteNegatedEventualityLiteralFromClauseList(LIST ClauseList, CLAUSE EventualityClause, FLAGSTORE Flags, PRECEDENCE Precedence)
{
  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);

    tl_DeleteNegatedEventualityLiteral(Clause, EventualityClause, Flags, Precedence);
  }
}

static BOOL tl_ContainsNegatedEventualityClause(LIST ClauseList, CLAUSE EventualityClause)
{
  LITERAL EventualityLiteral = tl_GetEventualityLiteral(EventualityClause);
  BOOL EventualityIsPositive = clause_LiteralIsPositive(EventualityLiteral);
  SYMBOL EventualitySymbol = term_TopSymbol(clause_LiteralAtom(EventualityLiteral));

  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);

    if(clause_Length(Clause) == 1) {
      LITERAL Lit = clause_GetLiteral(Clause, clause_FirstLitIndex());
      SYMBOL LiteralSymbol = term_TopSymbol(clause_LiteralAtom(Lit));
      BOOL IsPositive = clause_LiteralIsPositive(Lit);
      if(symbol_Equal(EventualitySymbol, LiteralSymbol)
        && (EventualityIsPositive || IsPositive)
        && (!IsPositive || !EventualityIsPositive)) { /* !EventualityIsPositive and IsPositive have the same polarity */
        return TRUE;
      }
    }
  }
  return FALSE;
}

static LIST tl_DeleteLoopSearchClauses(LIST ClauseList)
{
  LIST toReturn = list_Nil();

  for(LIST Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);

    if(clause_GetTemporalType(Clause) != LOOPSEARCH && clause_GetTemporalType(Clause) != TERMINATING_LOOPSEARCH) {
      toReturn = list_Cons(Clause, toReturn);
    }
    else {
      clause_Delete(Clause);
    }
  }
  list_Delete(ClauseList);
  return toReturn;
}

static HERBRANDMODEL tl_FindFirstOccurrence(HERBRANDMODEL TemporalModelForSuccessor, LIST TemporalModelList)
{
  for(LIST Scan = TemporalModelList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    HERBRANDMODEL Model = (HERBRANDMODEL) list_Car(Scan);
    if(tl_ModelsEqual(Model, TemporalModelForSuccessor)) {
      return Model;
    }
  }
  return NULL;
}

static void tl_PrintTemporalModel(LIST HerbrandModelList, unsigned long backJumpPoint)
{
  unsigned long TimePoint = 0;
  printf("\n\nTemporal model constructed:");
  for(LIST Scan = HerbrandModelList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    HERBRANDMODEL Model = (HERBRANDMODEL) list_Car(Scan);
    printf("\n-------------------- %lu", TimePoint);
    printf("\n"); tl_PrintHerbrandModel(Model);
    ++TimePoint;
  }
  printf("\n--------------------> %lu", backJumpPoint);
}

static BOOL tl_IsOriginalSymbol(SYMBOL Symbol)
{
  char* Name = symbol_Name(Symbol);
  return strlen(Name) == 0 || Name[0] != '_';
}

static HERBRANDMODEL tl_NewModelWithoutNonOriginalSymbols(HERBRANDMODEL Model)
{

  LIST Predicates = symbol_GetAllPredicates();
  HERBRANDMODEL toReturn = tl_CreateHerbrandModel();
  for(LIST Scan = Predicates; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Symbol = (SYMBOL) list_Car(Scan);
    if(symbol_Arity(Symbol) == 1
       && tl_Models(Model, Symbol)
       && tl_IsOriginalSymbol(Symbol)) { // we only care about propositional 'variables'
       tl_AddSymbol(toReturn, Symbol);
    }
  }

  list_Delete(Predicates);
  return toReturn;
}

/*
static LIST tl_ShrinkTemporalModel(LIST HerbrandModelList, unsigned long *backJumpPoint)
{
  LIST toReturn = list_Nil();
  unsigned long initialBackJumpPoint = *backJumpPoint;
  unsigned long positionInOldModel = 0;
  for(LIST Scan = HerbrandModelList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST Scan2 = list_Cdr(Scan);
    HERBRANDMODEL Model = (HERBRANDMODEL) list_Car(Scan);
    toReturn = list_Nconc(toReturn, list_List(Model));
    while(!list_Empty(Scan2)) {
      ++positionInOldModel;
      HERBRANDMODEL NextModel = (HERBRANDMODEL) list_Car(Scan2);
      if(tl_ModelsEqual(Model, NextModel)) {
        tl_DeleteHerbrandModel(NextModel);
        if(positionInOldModel <= initialBackJumpPoint) {
          --*backJumpPoint;
        }
      }
      else {
        break;
      }
      Scan = Scan2;
      Scan2 = list_Cdr(Scan2);
    }
  }
  list_Delete(HerbrandModelList);
  return toReturn;
}
*/

static LIST tl_ReduceTemporalModel(LIST HerbrandModelList, unsigned long *backJumpPoint)
{
  LIST toReturn = list_Nil();
  for(LIST Scan = HerbrandModelList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    HERBRANDMODEL Model = (HERBRANDMODEL) list_Car(Scan);
    toReturn = list_Nconc(toReturn, list_List(tl_NewModelWithoutNonOriginalSymbols(Model)));
  }
  return toReturn;
}

void tl_ConstructModel(PROOFSEARCH Search, FLAGSTORE Flags, LIST ListOfLeftHandSideSymbols)
{
  PRECEDENCE Precedence = NULL;
  LIST WorkedOffClauses = prfs_WorkedOffClauses(Search);
  LIST InitialClauses = list_Nil(), UniversalClauses = list_Nil(), StepClauses = list_Nil();
  unsigned long TimePoint = 0, i = 0, ConstructedTimePoints = 0;
  unsigned long backJumpPoint = 0, oldPeriodStart = 0;
  unsigned long temporaryModelLength = 0;
  BOOL runConstruction = TRUE;
  HERBRANDMODEL ZeroModel = NULL, PreviousModel = NULL;
  LIST ConsideredSymbolList = list_Nil();
  LIST ConsideredClauseList = list_Nil();
  CLAUSE EventualityClause = (list_Empty(prfs_EventualityClauses(Search)) ? NULL
                                                                          : list_First(prfs_EventualityClauses(Search)));
  LIST TemporalModelList = list_Nil(), Previous = list_Nil();
  LIST CriticalLeftHandSides = list_Nil();
  SUBSET LastCriticalSubSet = NULL;
  unsigned long NumberOfLeftHandSideSymbols = 0, NumberOfCriticalSymbols = 0, NumberOfNonCriticalSymbols = 0;
  HASH SubSetHash = NULL;
  unsigned int ModelHeuristicsCounter = 1;
  SUBSET CriticalSubSet = NULL, NonCriticalSubSet = NULL;

  if(list_Length(prfs_EventualityClauses(Search)) > 1) {
    printf("\nModel construction can only work if there is exactly one eventuality contained in the problem.");
    return;
  }

  for(LIST Scan = WorkedOffClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    if(!tl_IsPLTLClause(Clause)) {
      printf("\nNot a problem in PLTL: cannot construct a model.");
      return;
    }
  }

  clock_StartCounter(clock_MODELCONSTRUCTION);

  SubSetHash = hsh_Create();

  if(EventualityClause) {
    CriticalLeftHandSides = tl_ListOfCriticalLeftHandSidesAsSymbols(EventualityClause, Search);
    ConsideredSymbolList = tl_ComputeSymbolListWithCriticalSymbolsFirst(CriticalLeftHandSides, ListOfLeftHandSideSymbols, &NumberOfCriticalSymbols);
    NumberOfLeftHandSideSymbols = list_Length(ConsideredSymbolList);
    NumberOfNonCriticalSymbols = NumberOfLeftHandSideSymbols - NumberOfCriticalSymbols;
    CriticalSubSet = (NumberOfCriticalSymbols > 0) ? tl_CreateFirstProperSubSet() : tl_CreateEmptySubSet();
    NonCriticalSubSet = (NumberOfCriticalSymbols > 0) ? tl_CreateEmptySubSet() : tl_CreateFirstProperSubSet();
  }
  Precedence = symbol_CopyPrecedence(prfs_Precedence(Search));

  // Make them unshared now
  for(LIST Scan = WorkedOffClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);
    clause_MakeUnshared(Clause, prfs_WorkedOffSharingIndex(Search));
  }
  prfs_SetWorkedOffClauses(Search, list_Nil());

  fputs("\n---------------------MODEL-CONSTRUCTION-START----------------------", stdout);
  if(EventualityClause) {
    printf("\nEventuality: "); term_Print(tl_GetEventualityTerm(EventualityClause));
  }
  if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
    printf("\nCritical Left-Hand Sides of Step Clauses:");
    if(list_Empty(CriticalLeftHandSides)) {
      printf("None found.");
    }
    else {
      for(LIST Scan = CriticalLeftHandSides; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
        LIST LeftHandSide = (LIST) list_Car(Scan);
        printf("\n <UniversalSet> and {");
        for(LIST Scan2 = LeftHandSide; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
          SYMBOL Symbol = (SYMBOL) list_Car(Scan2);
          if(Scan2 != LeftHandSide) {
            printf(", ");
          }
          symbol_Print(Symbol);
        }
        printf("}");
      }
    }
  }

  if(flag_IsUnorderedModelConstructionEnabled(Flags)) {
    WorkedOffClauses = tl_DeleteLoopSearchClauses(WorkedOffClauses);
    WorkedOffClauses = tl_SaturateClauseSetUnderFineGrainedStepResolution(WorkedOffClauses, FALSE, TRUE, Precedence);
  }

  // First of all, separate the different clauses
  for(LIST Scan = WorkedOffClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = (CLAUSE) list_Car(Scan);

    TEMPORAL_TYPE TemporalType = clause_GetTemporalType(Clause);
    switch(TemporalType) {
      case INITIAL_TYPE:
        tl_InitialPropositionalClauseToUniversalClause(Clause);
        InitialClauses = list_Cons(Clause, InitialClauses);
      break;
      case STEP:
        StepClauses = list_Cons(Clause, StepClauses);
        continue;
      break;
      case UNIVERSAL:
        UniversalClauses = list_Cons(Clause, UniversalClauses);
        continue;
      break;
      default:
        clause_Delete(Clause);
      break;
    }
  }
  if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
    printf("\nInitial Clauses:");
    clause_PrintClauseList(InitialClauses);
    printf("\nStep Clauses:");
    clause_PrintClauseList(StepClauses);
    printf("\nUniversal Clauses:");
    clause_PrintClauseList(UniversalClauses);
  }

  if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
    printf("\n\n---------------------------- Time point 0");
    printf("\nUsing the precedence: "); symbol_PrintPrecedence(Precedence);
  }
  ConsideredClauseList = list_Append(InitialClauses, list_Copy(UniversalClauses));
  if(EventualityClause) {
    LIST List = ConsideredClauseList;
    ConsideredClauseList = tl_SaturatePropositionalClauseSet(clause_CopyClauseList(ConsideredClauseList), Precedence);
    list_Delete(List);
  }
  ZeroModel = tl_ConstructHerbrandModelForPropositionalClausesWithImpliedEventuality(ConsideredClauseList, EventualityClause,
                                                                                     Precedence, Flags);
  PreviousModel = ZeroModel;
  TemporalModelList = list_Cons(ZeroModel, TemporalModelList);
  if(EventualityClause) {
    clause_DeleteClauseList(ConsideredClauseList);
  }
  else {
    list_Delete(ConsideredClauseList);
  }

  TimePoint = 1;
  ConstructedTimePoints = 1;
  while(runConstruction) {
    HERBRANDMODEL TemporalModel = NULL;
    PRECEDENCE ConsideredPrecedence = Precedence;
    BOOL IsCritical = FALSE;

    if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
      printf("\n\n---------------------------- Time point %lu (%lu)", TimePoint, ConstructedTimePoints);
    }

    LIST TriggeredStepClauses = tl_TriggeredStepClauses(PreviousModel, StepClauses);
    ConsideredClauseList = clause_CopyClauseList(UniversalClauses);
    for(LIST Scan = TriggeredStepClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      CLAUSE Clause = (CLAUSE) list_Car(Scan);
      ConsideredClauseList = list_Cons(tl_RightHandSideOfStepClauseToClause(Clause, Precedence, Flags), ConsideredClauseList);
    }

    if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
      printf("\nTriggered step clauses at the previous time point: ");
      clause_PrintClauseList(TriggeredStepClauses);
    }

    if(tl_ModelsLeftHandSides(PreviousModel, CriticalLeftHandSides)) {
      ConsideredPrecedence = NULL; // we are looking for a new precedence in here
      IsCritical = TRUE;
      SUBSET SubSet = NULL;
      unsigned long minimalNumberOfTriggeredStepClauses = ULONG_MAX;
      HERBRANDMODEL FirstOccurrenceOfPreviousModel = tl_FindFirstOccurrence(PreviousModel, TemporalModelList);
      LIST SubSetList = hsh_Get(SubSetHash, FirstOccurrenceOfPreviousModel);
      PRECEDENCE TestPrecedence = NULL;
      LIST SaturatedClauseList = list_Nil();
      HERBRANDMODEL TestModel = NULL;
      // a heuristic which tries to keep the number of triggered step clauses minimal is implemented here, but currently
      // it is disabled; increase 'ModelHeuristicsCounter' if you want to use it
      for(unsigned int i = 0; i < ModelHeuristicsCounter; ++i) {
        unsigned long numberOfTriggeredStepClauses = 0;
        while(TRUE) {
          SUBSET OldCriticalSubSet = NULL;
          SUBSET OldSubSet = SubSet;
          SubSet = tl_MergeSubsets(CriticalSubSet, NumberOfCriticalSymbols, NonCriticalSubSet);

          // CAUTION: 'LastCriticalSubSet' is NULL in the first iteration
          if(tl_SubSetsEqual(SubSet, LastCriticalSubSet)) { // we have made a full circle
            if(!tl_SubSetListContains(SubSetList, OldSubSet)) {
              tl_DeleteSubSet(OldSubSet);
            }
            tl_DeleteSubSetList(SubSetList, FALSE);
            hsh_DelItem(SubSetHash, FirstOccurrenceOfPreviousModel);
            SubSetList = list_Nil();
          }
          else {
            tl_DeleteSubSet(OldSubSet);
          }

          OldCriticalSubSet = CriticalSubSet;
          CriticalSubSet = tl_NextSubSet(CriticalSubSet, NumberOfCriticalSymbols);
          tl_DeleteSubSet(OldCriticalSubSet);
          if(tl_IsEmptySubSet(CriticalSubSet)) {
            SUBSET OldNonCriticalSubSet = NonCriticalSubSet;
            NonCriticalSubSet = tl_NextSubSet(NonCriticalSubSet, NumberOfNonCriticalSymbols);
            tl_DeleteSubSet(OldNonCriticalSubSet);

            if(tl_IsEmptySubSet(NonCriticalSubSet)) {
              if(NumberOfCriticalSymbols == 0) {
                tl_DeleteSubSet(NonCriticalSubSet);
                NonCriticalSubSet = tl_CreateFirstProperSubSet();
              }
              else {
                tl_DeleteSubSet(CriticalSubSet);
                CriticalSubSet = tl_CreateFirstProperSubSet();
              }
            }
          }

          if(!tl_SubSetListContains(SubSetList, SubSet)) {
            break;
          }
        }
        TestPrecedence = tl_CreatePrecedence(SubSet, ConsideredSymbolList);
        if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
          printf("\nTrying the precedence: "); symbol_PrintPrecedence(TestPrecedence);
        }
        if(!flag_IsUnorderedModelConstructionEnabled(Flags)) {
          SaturatedClauseList = tl_SaturatePropositionalClauseSet(clause_CopyClauseList(ConsideredClauseList), TestPrecedence);
        }
        else {
          SaturatedClauseList = ConsideredClauseList;
        }
        TestModel = tl_ConstructHerbrandModelForPropositionalClauses(SaturatedClauseList, TestPrecedence, Flags);
        if(!flag_IsUnorderedModelConstructionEnabled(Flags)) {
          clause_DeleteClauseList(SaturatedClauseList);
        }

        if(ModelHeuristicsCounter > 1) {
          numberOfTriggeredStepClauses = tl_NumberOfLeftHandSidesModelled(TestModel, CriticalLeftHandSides);
        }

        if(ModelHeuristicsCounter == 1 || numberOfTriggeredStepClauses < minimalNumberOfTriggeredStepClauses) {
          if(ConsideredPrecedence) {
            symbol_DeletePrecedence(ConsideredPrecedence);
          }
          if(TemporalModel) {
            tl_DeleteHerbrandModel(TemporalModel);
          }
          ConsideredPrecedence = TestPrecedence;
          minimalNumberOfTriggeredStepClauses = numberOfTriggeredStepClauses;
          TemporalModel = TestModel;
        }
        else {
          symbol_DeletePrecedence(TestPrecedence);
          tl_DeleteHerbrandModel(TestModel);
        }
      }

      tl_DeleteSubSet(LastCriticalSubSet);
      LastCriticalSubSet = tl_CopySubSet(SubSet);
      hsh_Put(SubSetHash, FirstOccurrenceOfPreviousModel, SubSet);
    }
    else { // no critical left-hand side has been modelled in the previous time point, i.e. the eventuality
           // can be fulfilled at this time point
      if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
        printf("\nUsing the precedence: "); symbol_PrintPrecedence(ConsideredPrecedence);
      }
      if(flag_IsUnorderedModelConstructionEnabled(Flags)) {
        if(EventualityClause && !tl_ContainsNegatedEventualityClause(ConsideredClauseList, EventualityClause)) {
          if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
            printf("\nThe clause set does not imply the negated eventuality.");
          }
          ConsideredClauseList = list_Cons(clause_Copy(EventualityClause), ConsideredClauseList);
          tl_DeleteNegatedEventualityLiteralFromClauseList(ConsideredClauseList, EventualityClause, Flags, ConsideredPrecedence);
        }
        TemporalModel = tl_ConstructHerbrandModelForPropositionalClauses(ConsideredClauseList, ConsideredPrecedence, Flags);
      }
      else { /* ordered model construction */
        // there is no need to saturate because the eventuality will have to be added anyway
        TemporalModel = tl_ConstructHerbrandModelForPropositionalClausesWithImpliedEventuality(ConsideredClauseList, EventualityClause,
                                                                                               ConsideredPrecedence, Flags);
      }
    }

    list_Delete(TriggeredStepClauses);

#ifdef CHECK
    if(!tl_ModelsClauseList(TemporalModel, ConsideredClauseList)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n ERROR: Model construction did not succeed.");
      misc_FinishErrorReport();
    }
#endif
    clause_DeleteClauseList(ConsideredClauseList);

    if(IsCritical) {
      symbol_DeletePrecedence(ConsideredPrecedence);
    }

    i = 0;
    Previous = list_Nil();
    for(LIST Scan = TemporalModelList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      HERBRANDMODEL Model = (HERBRANDMODEL) list_Car(Scan);

      if(tl_ModelsEqual(TemporalModel, Model)) {
        BOOL EventualitySatisfiedInBetween = FALSE;

        if(EventualityClause) {
          for(LIST Scan2 = Scan; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
            HERBRANDMODEL Model2 = (HERBRANDMODEL) list_Car(Scan2);

            if(tl_ModelsEventuality(Model2, EventualityClause)) {
              EventualitySatisfiedInBetween = TRUE;
              break;
            }
          }
        }
        if(!EventualityClause || EventualitySatisfiedInBetween) {
          tl_DeleteHerbrandModel(TemporalModel);
          backJumpPoint = i;
          runConstruction = FALSE;
          break;
        }
        else if(flag_GetFlagValue(Flags, flag_ELIMINATEREDUNDANTCYCLES)) {
          // first we transfer the subsets that may have been assigned to the old occurrence to the new one
          LIST SubSets = hsh_Get(SubSetHash, Model);
          hsh_PutList(SubSetHash, TemporalModel, list_Copy(SubSets));
          hsh_DelItem(SubSetHash, Model);
          //we now delete the models from this one up to (but not including) 'TemporalModel'
          for(LIST Scan2 = Scan; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
            HERBRANDMODEL ModelToBeDeleted = (HERBRANDMODEL) list_Car(Scan2);

            SubSets = hsh_Get(SubSetHash, ModelToBeDeleted);
            if(!list_Empty(SubSets)) {
              tl_DeleteSubSetList(SubSets, FALSE);
              hsh_DelItem(SubSetHash, ModelToBeDeleted);
            }
            tl_DeleteHerbrandModel(ModelToBeDeleted);
          }
          // delete the list elements as well
          if(Previous) {
            list_Delete(list_Cdr(Previous));
            list_Rplacd(Previous, list_Nil());
          }
          else {
            list_Delete(TemporalModelList);
            TemporalModelList = list_Nil();
          }
        }
        TimePoint = list_Length(TemporalModelList);
        break;
      }
      ++i;
      Previous = Scan;
    }
    if(runConstruction) {
      ++ConstructedTimePoints;
      ++TimePoint;
      TemporalModelList = list_Nconc(TemporalModelList, list_List(TemporalModel));
      PreviousModel = TemporalModel;
    }
  }
  if(flag_GetFlagValue(Flags, flag_PMODELCONSTRUCTIONSTEPS)) {
    printf("\n----------------------------");
  }

  tl_PrintTemporalModel(TemporalModelList, backJumpPoint);

  temporaryModelLength = list_Length(TemporalModelList);
  oldPeriodStart = list_Length(TemporalModelList) - backJumpPoint;

  LIST ReducedTemporalModelList = tl_ReduceTemporalModel(TemporalModelList, &backJumpPoint);

  clock_StopPassedTime(clock_MODELCONSTRUCTION);
/*
  printf("\n");
  printf("\nLength of the temporary model: %lu", temporaryModelLength);
  printf("\nLength of the temporary periodic part: %lu", oldPeriodStart);
*/
  printf("\n");
  printf("\nReduced model:");
  printf("\n---------------");

  tl_PrintTemporalModel(ReducedTemporalModelList, backJumpPoint);

  printf("\n");
  printf("\nTSPASS spent "); clock_PrintTime(clock_MODELCONSTRUCTION); printf(" on model construction.");
  printf("\nNumber of minimal critical merged step clauses: %u", list_Length(CriticalLeftHandSides));
  printf("\nNumber of symbols in left-hand sides of step clauses: %lu", NumberOfLeftHandSideSymbols);
  printf("\nNumber of critical symbols: %lu", NumberOfCriticalSymbols);
  printf("\nNumber of constructed time points: %lu", ConstructedTimePoints);
  printf("\nLength of the model: %u", list_Length(ReducedTemporalModelList));
  printf("\nLength of the periodic part: %lu", list_Length(ReducedTemporalModelList) - backJumpPoint);

  fputs("\n---------------------MODEL-CONSTRUCTION-STOP-----------------------", stdout);

  // cleaning up
  tl_DeleteSubSet(CriticalSubSet);
  tl_DeleteSubSet(NonCriticalSubSet);
  tl_DeleteSubSet(LastCriticalSubSet);
  list_Delete(ConsideredSymbolList);
  list_Delete(WorkedOffClauses);
  clause_DeleteClauseList(InitialClauses);
  clause_DeleteClauseList(UniversalClauses);
  clause_DeleteClauseList(StepClauses);
  list_DeleteWithElement(TemporalModelList, (void (*)(POINTER))tl_DeleteHerbrandModel);
  list_DeleteWithElement(ReducedTemporalModelList, (void (*)(POINTER))tl_DeleteHerbrandModel);
  list_DeleteWithElement(CriticalLeftHandSides, (void (*)(POINTER)) list_Delete);
  LIST EntriesList = hsh_GetAllEntries(SubSetHash);
  for(LIST Scan = EntriesList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SUBSET SubSet = (SUBSET) list_Car(Scan);
    tl_DeleteSubSet(SubSet);
  }
  list_Delete(EntriesList);
  hsh_Delete(SubSetHash);
  symbol_DeletePrecedence(Precedence);
}
