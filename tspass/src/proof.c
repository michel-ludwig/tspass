/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                   PROOF SEARCH                         * */
/* *                                                        * */
/* *  $Module:   PROOF                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000, 2001      * */
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
/* $Revision: 1.9 $                                       * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

#include "analyze.h" /* not modular!!! */
#include "clock.h" /* not modular!!! */
#include "proof.h"
#include "rules-inf.h"
#include "rules-red.h"
#include "rules-sort.h"
#include "rules-split.h"
#include "terminator.h"
#include "tl.h"

/**************************************************************/
/* Clause Selection Functions                                 */
/**************************************************************/

static CLAUSE top_SelectClauseDepth(LIST List, FLAGSTORE Flags)
/**************************************************************
  INPUT:   A list of clauses and a flag store.
  RETURNS: A clause selected from the list.
  EFFECT:  This function selects a clause from the list according
           to the following criteria:
     1. minimal depth
           2. minimal weight
     3a. maximal number of variable occurrences, if the flag
         'PrefVar' is TRUE
     3b. minimal number of variable occurrences, if 'PrefVar'
         is FALSE
***************************************************************/
{
  CLAUSE Result;
  NAT    Vars,NewVars,Weight,Depth,NewDepth;

  Result = (CLAUSE)list_Car(List);
  Depth  = clause_Depth(Result);
  Weight = clause_Weight(Result);
  Vars   = clause_NumberOfVarOccs(Result);
  List   = list_Cdr(List);

  while (!list_Empty(List)) {
    NewDepth =  clause_Depth(list_Car(List));
    if (NewDepth <= Depth) {
      if (NewDepth < Depth || clause_Weight(list_Car(List)) < Weight) {
        Depth  = NewDepth;
        Result = (CLAUSE)list_Car(List);
        Weight = clause_Weight(Result);
        Vars   = clause_NumberOfVarOccs(list_Car(List));
      }
      else {
        if (clause_Weight(list_Car(List)) == Weight) {
          NewVars = clause_NumberOfVarOccs(list_Car(List));
          if (flag_GetFlagValue(Flags, flag_PREFVAR)) {
            if (Vars < NewVars) {
              Depth  = NewDepth;
              Result = (CLAUSE)list_Car(List);
              Weight = clause_Weight(Result);
              Vars   = NewVars;
            }
          }
          else {
            if (Vars > NewVars) {
              Depth  = NewDepth;
              Result = (CLAUSE)list_Car(List);
              Weight = clause_Weight(Result);
              Vars   = NewVars;
            }
          }
        }
      }
    }
    List = list_Cdr(List);
  }

  return Result;
}


static CLAUSE top_SelectMinimalWeightClause(LIST List, FLAGSTORE Flags)
/**************************************************************
  INPUT:   A list of clauses and a flag store.
  RETURNS: A clause selected from the list.
  EFFECT:  This function selects a clause with minimal weight.
           If more than one clause has minimal weight and the flag
     'PrefVar' is TRUE, a clause with maximal number of variable
     occurrences is selected. If 'PrefVar' is FALSE, a clause with
     minimal number of variable occurrences is selected.
     If two clauses are equal with respect to the two criteria
     the clause with the smaller list position is selected.
  CAUTION: THE LIST HAS TO BY SORTED BY WEIGHT IN ASCENDING ORDER!
***************************************************************/
{
  CLAUSE Result;
  NAT    Vars, NewVars, Weight;

#ifdef CHECK
  /* Check invariant: List has to be sorted by weight (ascending) */
  LIST Scan;
  Weight = clause_Weight(list_Car(List));
  for (Scan = list_Cdr(List); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    NAT NewWeight;
    NewWeight = clause_Weight(list_Car(Scan));
    if (NewWeight < Weight) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In top_SelectMinimalConWeightClause: clause list ");
      misc_ErrorReport("isn't sorted by weight");
      misc_FinishErrorReport();
    }
    Weight = NewWeight;
  }
#endif

  Result = (CLAUSE)list_Car(List);
  Weight = clause_Weight(Result);
  Vars   = clause_NumberOfVarOccs(Result);
  List   = list_Cdr(List);

  while (!list_Empty(List)) {
    if (clause_Weight(list_Car(List)) == Weight) {
      NewVars = clause_NumberOfVarOccs(list_Car(List));
      if (flag_GetFlagValue(Flags, flag_PREFVAR)) {
        if (Vars < NewVars) {
          Result = (CLAUSE)list_Car(List);
          Weight = clause_Weight(Result);
          Vars   = NewVars;
        }
      }
      else
        if (Vars > NewVars) {
          Result = (CLAUSE)list_Car(List);
          Weight = clause_Weight(Result);
          Vars   = NewVars;
        }
    }
    else
      return Result;
    List = list_Cdr(List);
  }
  return Result;
}


static CLAUSE top_SelectMinimalConWeightClause(LIST List, FLAGSTORE Flags)
/**************************************************************
  INPUT:   A non-empty list of clauses and a flag store.
  RETURNS: A clause selected from the list.
  EFFECT:  This function selects a clause from the list in a
           similar way as the function top_SelectMinimalWeightClause.
     The only difference is that conjecture clauses are
     preferred over axiom clauses, because their weight
     is divided by a factor given by the flag 'PrefCon'.
***************************************************************/
{
  CLAUSE Result;
  NAT    NewWeight,Weight, NewVars, Vars, Factor;

  Result = (CLAUSE)list_Car(List);
  Factor = flag_GetFlagValue(Flags, flag_PREFCON);
  Weight = clause_Weight(Result);
  if (clause_GetFlag(Result, CONCLAUSE))
    Weight = Weight / Factor;
  Vars   = clause_NumberOfVarOccs(list_Car(List));
  List   = list_Cdr(List);

  while (!list_Empty(List)) {
    NewWeight = clause_Weight(list_Car(List));
    if (clause_GetFlag(list_Car(List),CONCLAUSE))
      NewWeight = NewWeight / Factor;
    if (NewWeight < Weight) {
      Weight = NewWeight;
      Result = list_Car(List);
      Vars   = clause_NumberOfVarOccs(list_Car(List));
    }
    else {
      if (NewWeight == Weight) {
        NewVars = clause_NumberOfVarOccs(list_Car(List));
        if (flag_GetFlagValue(Flags, flag_PREFVAR)) {
          if (Vars < NewVars) {
            Result = (CLAUSE)list_Car(List);
            Weight = NewWeight;
            Vars   = NewVars;
          }
        }
        else
          if (Vars > NewVars) {
            Result = (CLAUSE)list_Car(List);
            Weight = NewWeight;
            Vars   = NewVars;
          }
      }
    }

    List = list_Cdr(List);
  }
  return Result;
}


/*static CLAUSE top_SelectClauseDepth(LIST List)*/
/**************************************************************
  INPUT:   A list of clauses.
  RETURNS: A clause selected from the list.
  EFFECT:  
***************************************************************/
/*{
  CLAUSE Result;
  int    Min, Depth;

  Result = (CLAUSE)list_Car(List);
  Depth  = clause_Depth(Result);
  Min    = Depth * clause_Weight(Result);
  List   = list_Cdr(List);

  if (Depth == 0)
    return Result;

  while (!list_Empty(List)) {
    Depth =  clause_Depth(list_Car(List));
    if (Min > Depth * clause_Weight(list_Car(List))) {
      Result = list_Car(List);
      if (Depth == 0)
  return Result;
      Min    = clause_Depth(Result) * clause_Weight(Result);
    }
    List = list_Cdr(List);
  }

  return Result;
}*/


static LIST top_GetLiteralsForSplitting(CLAUSE Clause, BOOL SuccedentOnly)
/**************************************************************
  INPUT:   A clause and a flag whether only succedent literals should be
           considered
  RETURNS: A list of literal indices where every single
           literal doesn't share any variables with other literals.
           So these literals can be split as units.
           If SuccedentOnly is TRUE, only succedent lits are considered
***************************************************************/
{
  LIST* Variables;  /* An array, mapping literal index to list of variables */
  int   i, j, EndIndex;
  BOOL  Stop;
  LIST  Failed, Result;

  Result   = list_Nil();
  EndIndex = (SuccedentOnly ? clause_FirstSuccedentLitIndex(Clause) : clause_FirstLitIndex());

  /* Special case: clause is ground, so return all literals */
  if (clause_IsGround(Clause)) {
    for (i = clause_LastLitIndex(Clause); i >= EndIndex; i--)
      Result = list_Cons((POINTER)i, Result);
    return Result;
  }

  Variables = memory_Malloc(sizeof(LIST) * clause_Length(Clause));
  /* Initialize the array */
  for (i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); i++)
    Variables[i] = term_VariableSymbols(clause_GetLiteralAtom(Clause, i));

  /* <Failed> is the set of literals that share variables with other literals */
  Failed = list_Nil();
  for (i = clause_LastLitIndex(Clause); i >= EndIndex; i--) {
    if (list_Empty(Variables[i]))
      Result = list_Cons((POINTER)i, Result);
    else if (!list_PointerMember(Failed, (POINTER)i)) {
      /* We don't know yet whether the literal shares variables */
      Stop = FALSE;
      for (j = clause_FirstLitIndex();
        j <= clause_LastLitIndex(Clause) && !Stop; j++) {
        if (i != j && list_HasIntersection(Variables[i], Variables[j])) {
          Stop   = TRUE;  /* Literal isnt candidate for "optimal" splitting */
          Failed = list_Cons((POINTER)i, Failed);
          Failed = list_Cons((POINTER)j, Failed);
        }
      }
      if (!Stop)
        Result = list_Cons((POINTER)i, Result);
    }
  }

  /* Cleanup */
  for (i = clause_FirstLitIndex(); i <= clause_LastLitIndex(Clause); i++)
    list_Delete(Variables[i]);
  memory_Free(Variables, sizeof(LIST) * clause_Length(Clause));
  list_Delete(Failed);
  return Result;
}


static int top_GetOptimalSplitLiteralIndex(PROOFSEARCH Search, CLAUSE Clause,
             BOOL Usables)
/**************************************************************
  INPUT:   A proofsearch object, a clause and a boolean flag.
  RETURNS: The index of the positive literal from <Clause>
           with the greatest number of instances (maybe 0) within
     the WorkedOff/Usable sets of the proof search object.
     The literal mustn't share any variables with other literals.
     If the clause doesn't have a suitable literal, a negative
     number is returned.
  EFFECT:  If <Usables> is FALSE, only the number of instances
     within the WorkedOff set is considered, otherwise
     the number of instances within both clause sets is considered.
***************************************************************/
{
  LIST    SplitLits;
  LITERAL Literal;
  NAT     Count, MaxInstances;
  int     Result;

  MaxInstances = -1;
  SplitLits    = top_GetLiteralsForSplitting(Clause, 
         flag_GetFlagValue(prfs_Store(Search), flag_SPLITHEURISTIC) == flag_SPLITHEURISTICSTANDARD);
  Result       = -1;

  for ( ; !list_Empty(SplitLits); SplitLits = list_Pop(SplitLits)) {
    Literal = clause_GetLiteral(Clause, (int)list_Car(SplitLits));
    /* Count the number of instances */
    Count = prfs_GetNumberOfInstances(Search, Literal, Usables);
    if (Count > MaxInstances) {
      Result = (int)list_Car(SplitLits);
      MaxInstances = Count;
    }
  }
  return Result;
}


/* EK: hier lassen oder nach search.c oder nach rules-split.c? */
static CLAUSE top_GetPowerfulSplitClause(PROOFSEARCH Search, BOOL Usables,
          int* LitIndex)
/**************************************************************
  INPUT:   A proofsearch object, a boolean flag and a pointer to a literal
           index which is used as return value.
  RETURNS: A clause from the usable set that was selected as given clause.
           Iff no suitable clause was found NULL is returned and <*LitIndex>
     is set to -1.
     Iff a suitable clause was found, this clause is returned and
     <*LitIndex> is set to the index of the "optimal" literal, that
           is a literal that can be split off as unit witha high reduction
           potential
  EFFECT:  This function selects a clause from the "usable" set and
           a literal that are "optimal" for the application of the splitting
     rule with respect to the following criteria:
           1) the literal must occur in the succedent of the non-horn clause,
     2) the literal mustn't share any variables with other literals,
           3) the clause must have a solved constraint,
     4) the atom must have the maximum number of instances
              a) within the set of "workedoff" clauses, iff <Usables>=FALSE
              b) within the set of "usable" and "workedoff" clauses,
                 iff "Usables"=TRUE
     5) the atom must have at least one instance in another clause.
***************************************************************/
{
  LIST   Scan, SplitLits;
  NAT    MaxNrOfInstances, NrOfInstances;
  CLAUSE Clause, OptimalClause;
  TERM   Atom;
  SHARED_INDEX WOIndex, UsIndex;

  OptimalClause    = NULL;
  *LitIndex        = -1;
  MaxNrOfInstances = 0;
  WOIndex          = prfs_WorkedOffSharingIndex(Search);
  UsIndex          = prfs_UsableSharingIndex(Search);

  /* Prepare the term stamp */
  if (term_StampOverflow(sharing_StampID(WOIndex)))
    sharing_ResetAllTermStamps(WOIndex);
  if (Usables && term_StampOverflow(sharing_StampID(UsIndex)))
    sharing_ResetAllTermStamps(UsIndex);
  term_StartStamp();

  for (Scan = prfs_UsableClauses(Search); !list_Empty(Scan);
       Scan = list_Cdr(Scan)) {
    Clause = list_Car(Scan);

    if (clause_HasSolvedConstraint(Clause) && 
        clause_Length(Clause) > 1 &&
       (!clause_IsHornClause(Clause) || 
       (flag_GetFlagValue(prfs_Store(Search), flag_SPLITHEURISTIC) == flag_SPLITHEURISTICGROUND &&
        clause_GetFlag(Clause, CONCLAUSE) &&  /* Split non-Horn clauses or input conjecture clauses */
        clause_Depth(Clause) == 0))) {
      /* Get a list of splittable literal indices */
      SplitLits = top_GetLiteralsForSplitting(Clause, 
          flag_GetFlagValue(prfs_Store(Search), flag_SPLITHEURISTIC) == flag_SPLITHEURISTICSTANDARD);
      for ( ; !list_Empty(SplitLits); SplitLits = list_Pop(SplitLits)) {
        LITERAL Literal;

        Literal = clause_GetLiteral(Clause, (int)list_Car(SplitLits));
        Atom    = clause_LiteralAtom(Literal);
        if (!term_AlreadyVisited(Atom)) {
          /* Don't visit atom more than once */
          term_SetTermStamp(Atom);
          /* Count the number of instances */
          NrOfInstances = prfs_GetNumberOfInstances(Search, Literal, Usables);
          if (NrOfInstances > MaxNrOfInstances || OptimalClause == NULL ||
              (NrOfInstances == MaxNrOfInstances &&
              /* Prefer shorter clauses for splitting! */
              clause_Length(Clause) < clause_Length(OptimalClause))) {
            OptimalClause    = Clause;
            MaxNrOfInstances = NrOfInstances;
            *LitIndex        = (int)list_Car(SplitLits);
          }
        }
      }
    }
  }
  term_StopStamp();

  /* The splittable literal must have at least one instance to be useful */
  /* reducing other clauses. If <Usables> is TRUE, the literal must even */
  /* have two instances, since the literal of the given clause is in the */
  /* usable index, too.                                                  */
  if (OptimalClause != (CLAUSE)NULL &&
      (MaxNrOfInstances == 0 || (Usables && MaxNrOfInstances == 1)) &&
      (clause_Depth(OptimalClause) != 0 ||
       flag_GetFlagValue(prfs_Store(Search), flag_SPLITHEURISTIC) != flag_SPLITHEURISTICGROUND))
  {
    *LitIndex     = -1;
    OptimalClause = NULL;
  }

  return OptimalClause;
}

static CLAUSE proof_SelectGivenClause(LIST ClauseList, FLAGSTORE Flags, int* Counter)
{
  CLAUSE GivenClause = NULL;
  
  if ((*Counter) % flag_GetFlagValue(Flags, flag_WDRATIO) == 0) {
    GivenClause = top_SelectClauseDepth(ClauseList, Flags);
  }
  else {
    if (flag_GetFlagValue(Flags, flag_PREFCON) != flag_PREFCONUNCHANGED) {
      GivenClause = top_SelectMinimalConWeightClause(ClauseList,
                Flags);
    }
    else {
      GivenClause = top_SelectMinimalWeightClause(ClauseList,
                    Flags);
    }
  }
  ++(*Counter); /* EK: hier lassen, oder eine Klammerebene nach aussen? */
  return GivenClause;
}

static LIST top_FullReductionSelectGivenComputeDerivables(PROOFSEARCH Search,
                CLAUSE *SplitClause,
                int *Counter, int *LoopClauseCounter)
/**************************************************************
  INPUT:   A proof search object, a pointer to a clause resulting from a
           previous splitting step, and a pointer to an integer counter.
  RETURNS: A list of derived clauses.
  EFFECT:  In this function a clause is selected from the set of
           "usable" clauses. After a clause was selected as "given clause",
     inferences between the given clause and the "worked off" clauses
     are made. The selection works as follows:
     1) If <*SplitClause> is not NULL, the split clause
        is selected as "given clause". <*SplitClause> should result
        from splitting
     2) If <*SplitClause> is NULL, we try to find a clause that is
        "optimal" for splitting. This is done by selecting a literal
        <L> in a clause, such that <L> is variable-disjoint from
        the rest of the clause, and the atom of <L> has the maximum
        number of instances within the set of "usable" and "workoff"
        clauses.
     3) If the previous steps failed, a clause is selected by weight
        or by depth, depending on the parameters "WDRatio", "PrefVar"
        and "PrefCon". Then splitting is tried on the selected clause.
        If the clause is a non-horn clause, we try to find a positive
        literal <L> and a set of negative literals <N>, such that <N>
        and <L> are variable disjoint from the rest of the clause.
***************************************************************/
{
  CLAUSE     GivenClause, TerminatorClause;
  LIST       Derivables, SplitLits;
  FLAGSTORE  Flags;
  PRECEDENCE Precedence;
  int        LitIndex;
  LITERAL MarkerLiteral;

  GivenClause   = NULL;
  Derivables    = list_Nil();
  Flags         = prfs_Store(Search);
  Precedence    = prfs_Precedence(Search);
  MarkerLiteral = NULL;
  
  /* 1) If the last given clause was split or if backtracking was applied, */
  /* then choose the clause resulting from the splitting step as        */
  /* given clause.                                                      */
  /* ATTENTION: Since the <SplitClause> might have been reduced since   */
  /* the time the variable was set, we have to check whether            */
  /* <SplitClause> is still element of the set of usable clauses.       */
  if (*SplitClause != NULL &&
      list_PointerMember(prfs_UsableClauses(Search), *SplitClause))
    GivenClause = *SplitClause;

  *SplitClause = NULL;

  if (GivenClause == NULL) {
    if (prfs_SplitCounter(Search) != 0)
      /* 2) Try to find an "optimal" splitting clause, that doesn't share */
      /*    variables with any other literal.                             */
      GivenClause = top_GetPowerfulSplitClause(Search, TRUE, &LitIndex);

    if (GivenClause != NULL) {
      /* Found "optimal" split clause, so apply splitting */
      SplitLits = list_List(clause_GetLiteral(GivenClause, LitIndex));
      *SplitClause = prfs_DoSplitting(Search, GivenClause, SplitLits);
      list_Delete(SplitLits);
    }
    else {
      /* 3) Splitting wasn't applied, so use the other strategies */
      GivenClause = proof_SelectGivenClause(prfs_UsableClauses(Search), Flags, Counter);
      if((*Counter) % 5 == 0
         && TEMPORAL_MODE && (clause_GetTemporalType(GivenClause) == LOOPSEARCH
                               || clause_GetTemporalType(GivenClause) == TERMINATING_LOOPSEARCH)) {
        CLAUSE PotentialNonLoopSearchClause = tl_FindUsableNonLoopSearchClause(Search);
        if(PotentialNonLoopSearchClause) {
          GivenClause = PotentialNonLoopSearchClause;
        }
      }
      else if((*Counter) % 5 == 1
         && TEMPORAL_MODE && !(clause_GetTemporalType(GivenClause) == LOOPSEARCH
                               || clause_GetTemporalType(GivenClause) == TERMINATING_LOOPSEARCH)) {
        CLAUSE PotentialLoopSearchClause = tl_FindUsableLoopSearchClause(Search);
        if(PotentialLoopSearchClause) {
          GivenClause = PotentialLoopSearchClause;
        }
      }
    }
  }

  if (*SplitClause == NULL && prfs_SplitCounter(Search) != 0) {
    /* Try to find the "optimal" literal for splitting the clause. */
    /* This makes sense for a clause that is the right part of a   */
    /* splitting step.                                             */
    LitIndex = top_GetOptimalSplitLiteralIndex(Search, GivenClause, FALSE);
    if (LitIndex >= 0) {
      SplitLits = list_List(clause_GetLiteral(GivenClause, LitIndex));
      *SplitClause = prfs_DoSplitting(Search, GivenClause, SplitLits);
      list_Delete(SplitLits);
    } else {
      /* Optimal splitting wasn't possible, so try the old-style splitting. */
      /* Here a split is done if a positive literal doesn't share variables */
      /* with another POSITIVE literal. */
      *SplitClause = prfs_PerformSplitting(Search, GivenClause);
    }
  }

  if(TEMPORAL_MODE && (clause_GetTemporalType(GivenClause) == TERMINATING_LOOPSEARCH
                          || clause_GetTemporalType(GivenClause) == LOOPSEARCH)
    && tl_ContainsExactlyOneLoopSearchMarker(GivenClause, &MarkerLiteral)) {
    if(flag_GetFlagValue(Flags, flag_SEQUENTIALLOOPSEARCH)
        || (*LoopClauseCounter % flag_GetFlagValue(Flags, flag_SEQUENTIALLOOPSEARCHITERATIONS) != 0)) {
      LIST SmallerClauses = tl_GetClausesWithSmallerLoopSearchIndex(MarkerLiteral, prfs_UsableSharingIndex(Search));
      if(!list_Empty(SmallerClauses)) {
        SmallerClauses = clause_ListSortWeighed(SmallerClauses);
        GivenClause = proof_SelectGivenClause(SmallerClauses, Flags, Counter);
        list_Delete(SmallerClauses);
      }
    }
    ++*LoopClauseCounter;
  }

  prfs_ExtractUsable(Search, GivenClause);
  clause_SelectLiteral(GivenClause, Flags);

  if (flag_GetFlagValue(Flags, flag_PGIVEN)) {
    fputs("\n\tGiven clause: ", stdout);
    clause_Print(GivenClause);
    fflush(stdout);
  }

  if(TEMPORAL_MODE && clause_GetTemporalType(GivenClause) == TERMINATING_LOOPSEARCH
                   && tl_ContainsExactlyOneLoopSearchMarker(GivenClause, &MarkerLiteral)) {

    if(flag_GetFlagValue(Flags, flag_PGIVEN)) {
      printf("\nTerminating loop search clause clause found!.");
    }
    if(!MarkerLiteral) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In top_FullReductionSelectGivenComputeDerivables: No loop search marker found.\n");
      misc_FinishErrorReport();
    }
    if(clause_Length(GivenClause) == 1) { /* GivenClause = s_i^L \implies \next false */
      if (flag_GetFlagValue(Flags, flag_PGIVEN)) {
        printf("\nFound empty loop search clause.");
      }
      CLAUSE EmptyClause = clause_Create(list_Nil(), list_Nil(), list_Nil(), Flags, Precedence);
      Derivables = list_Cons(EmptyClause, Derivables); /* add the empty clause */
    }
    else {
//         *terminatingStepSearchClauses = list_Cons(GivenClause, *terminatingStepSearchClauses);
      CLAUSE NewStepSearchClause = tl_CreateNextLoopSearchStepClause(GivenClause, MarkerLiteral, Flags, Precedence);
      if (flag_GetFlagValue(Flags, flag_PGIVEN)) {
        printf("\nCreating new loop search clause.");
        printf("\n");clause_Print(NewStepSearchClause);printf("\n");
      }
      Derivables = list_Cons(NewStepSearchClause, Derivables); /* add the new step search clause */
    }
    prfs_InsertWorkedOffClause(Search, GivenClause); /* don't forget this! */
  }
  else {
    if (*SplitClause != NULL)
      Derivables = list_List(*SplitClause);
    else {
      /* No splitting was applied */
      if (flag_GetFlagValue(Flags, flag_RTER) != flag_RTEROFF) {
        clock_StartCounter(clock_REDUCTION);
        TerminatorClause = red_Terminator(GivenClause,
            flag_GetFlagValue(Flags, flag_RTER),
            prfs_WorkedOffSharingIndex(Search),
            prfs_UsableSharingIndex(Search), Flags,
            Precedence);
        clock_StopAddPassedTime(clock_REDUCTION);

        if (TerminatorClause != NULL) {
    /* An empty clause was derived by the "terminator" rule */
    Derivables = list_List(TerminatorClause);
    prfs_InsertUsableClause(Search, GivenClause);
        }
      }
    }

    if (list_Empty(Derivables)) {
      /* No splitting was applied, no empty clause was found by terminator */
      /*clause_SetSpecialFlags(GivenClause,ana_SortDecreasing());*/
      prfs_InsertWorkedOffClause(Search, GivenClause);
      clock_StartCounter(clock_INFERENCE);
      Derivables = inf_DerivableClauses(Search, GivenClause);
      clock_StopAddPassedTime(clock_INFERENCE);
    }
  }

  prfs_IncDerivedClauses(Search, list_Length(Derivables));

  return Derivables;
}


static LIST top_LazyReductionSelectGivenComputeDerivables(PROOFSEARCH Search,
                CLAUSE *SplitClause,
                int *Counter)
/**************************************************************
  INPUT:   A proof search object, a pointer to a clause resulting from a
           previous splitting step, and a pointer to an integer counter.
  RETURNS: A list of derived clauses.
  EFFECT:  In this function a clause is selected from the set of
           "usable" clauses. After a clause was selected as "given clause",
     inferences between the given clause and the "worked off" clauses
     are made. Take a look at the description of the function
     top_FullReduction... for more details.
     This function is more complicated than the other function,
     since clauses in the set of usable clauses may be reducible.
     Because of this fact, the selection of the given clause
     has to be done in a loop. After picking a "candidate" clause
     the clause is inter-reduced with the "worked off" set.
     If the candidate still exists after the reduction it is
     selected as given clause, else another usable clause is picked
     as candidate.
***************************************************************/
{
  CLAUSE     GivenClause, TerminatorClause;
  LIST       Derivables;
  FLAGSTORE  Flags;
  PRECEDENCE Precedence;
  int        LitIndex;

  GivenClause      = (CLAUSE)NULL;
  TerminatorClause = (CLAUSE)NULL;
  Derivables       = list_Nil();
  Flags            = prfs_Store(Search);
  Precedence       = prfs_Precedence(Search);

  while (GivenClause == (CLAUSE)NULL &&
    !list_Empty(prfs_UsableClauses(Search))) {
    /* The selected clause may be redundant */

    if (*SplitClause != NULL &&
      list_PointerMember(prfs_UsableClauses(Search), *SplitClause))
      GivenClause = *SplitClause;

    *SplitClause  = NULL;

    /* Try selecting a clause that is optimal for splitting */
    if (GivenClause == NULL) {
      if (prfs_SplitCounter(Search) != 0) {
        GivenClause = top_GetPowerfulSplitClause(Search, FALSE, &LitIndex);
        /* The value of <LitIndex> isn't used here. */
      }

      if (GivenClause == NULL) {
        /* No optimal clause for splitting found */
        if ((*Counter) % flag_GetFlagValue(Flags, flag_WDRATIO) == 0)
          GivenClause = top_SelectClauseDepth(prfs_UsableClauses(Search), Flags);
        else {
        if (flag_GetFlagValue(Flags, flag_PREFCON) != flag_PREFCONUNCHANGED)
          GivenClause = top_SelectMinimalConWeightClause(prfs_UsableClauses(Search),
                Flags);
        else
          GivenClause = top_SelectMinimalWeightClause(prfs_UsableClauses(Search),
                Flags);
        }
        (*Counter)++;
      }
    }
    prfs_ExtractUsable(Search, GivenClause);

    /* Reduce the selected clause */
    clock_StartCounter(clock_REDUCTION);
    GivenClause = red_CompleteReductionOnDerivedClause(Search, GivenClause, 
                  red_WORKEDOFF);
    clock_StopAddPassedTime(clock_REDUCTION);
  }

  if (GivenClause == (CLAUSE)NULL)
    /* Set of usable clauses is empty */
    return list_Nil();


  if (clause_IsEmptyClause(GivenClause)) {
    Derivables = list_List(GivenClause);
    return Derivables;
  }
  else {
    /* Reduce Workedoff clauses with selected clause */
    clock_StartCounter(clock_REDUCTION);
    Derivables = red_BackReduction(Search, GivenClause, red_WORKEDOFF);
    clock_StopAddPassedTime(clock_REDUCTION);
  }

  clause_SelectLiteral(GivenClause, Flags);
  /* Print selected clause */
  if (flag_GetFlagValue(Flags, flag_PGIVEN)) {
    fputs("\n\tGiven clause: ", stdout);
    clause_Print(GivenClause); 
    fflush(stdout);
  }

  /* Try splitting */
  if (prfs_SplitCounter(Search) != 0) {
    /* First try "optimal" splitting on the selected clause */
    LitIndex = top_GetOptimalSplitLiteralIndex(Search, GivenClause, FALSE);

    if (LitIndex >= 0) {
      LIST SplitLits;

      SplitLits = list_List(clause_GetLiteral(GivenClause, LitIndex));
      *SplitClause = prfs_DoSplitting(Search, GivenClause, SplitLits);
      list_Delete(SplitLits);      
    } else {
      /* Try the old splitting that allows negative literals   */
      /* sharing variables with the selected positive literal. */
      *SplitClause = prfs_PerformSplitting(Search, GivenClause);
    }
  }

  if (*SplitClause != NULL) {
    Derivables = list_Cons(*SplitClause, Derivables);
  } else {
    /* Try terminator reduction only for a clause that wasn't splitted. */
    if (flag_GetFlagValue(Flags, flag_RTER) != flag_RTEROFF) {
      TerminatorClause = red_Terminator(GivenClause,
          flag_GetFlagValue(Flags, flag_RTER),
          prfs_WorkedOffSharingIndex(Search),
          prfs_UsableSharingIndex(Search),
          Flags, Precedence);
      if (TerminatorClause != NULL) {
        Derivables = list_Cons(TerminatorClause, Derivables);
        prfs_InsertUsableClause(Search, GivenClause);
      }
    }
    if (TerminatorClause == (CLAUSE)NULL) {   
      /* clause_SetSpecialFlags(GivenClause,ana_SortDecreasing());*/
      prfs_InsertWorkedOffClause(Search, GivenClause);
      clock_StartCounter(clock_INFERENCE);
      Derivables = list_Nconc(Derivables,
          inf_DerivableClauses(Search, GivenClause));
      clock_StopAddPassedTime(clock_INFERENCE);
    }
  }

  prfs_IncDerivedClauses(Search, list_Length(Derivables));

  return Derivables;
}

PROOFSEARCH proof_ProofSearch(PROOFSEARCH Search, LIST ProblemClauses,
          FLAGSTORE InputFlags, LIST UserPrecedence, 
                                   int *BoundApplied, BOOL NativeClauseInput)
/**************************************************************
  INPUT:   A proof search object, a list of clauses, a flag store
           containing the flags from the command line and from
           the input file, a list containing the precedence as
     specified by the user, a pointer to an integer, and a 
           boolean indicating if the input clauses need to be 
           treated specially.
  RETURNS: The same proof search object
  EFFECTS: 
***************************************************************/
{
  LIST       Scan,EmptyClauses,Derivables;
  LIST       UsedEmptyClauses;
  CLAUSE     SplitClause,HighestLevelEmptyClause;
  FLAGSTORE  Flags;
  PRECEDENCE Precedence;
  int        Counter, LoopClauseCounter, ActBound, BoundMode, BoundLoops;

  HighestLevelEmptyClause = (CLAUSE)NULL;
  UsedEmptyClauses        = list_Nil();
  EmptyClauses            = list_Nil();
  Derivables              = list_Nil();
  Flags                   = prfs_Store(Search);
  Precedence              = prfs_Precedence(Search);
  Counter                 = 1;
  LoopClauseCounter       = 1;

  clock_InitCounter(clock_REDUCTION);
  clock_InitCounter(clock_BACKTRACK);
  clock_InitCounter(clock_INFERENCE);

  /* Important ! Recomputes Weight ! */
  ana_AnalyzeProblem(Search, ProblemClauses);
  if (flag_GetFlagValue(Flags, flag_AUTO)) {
    prfs_InstallFiniteMonadicPredicates(Search, ProblemClauses, ana_FinMonPredList());
    ana_AutoConfiguration(ProblemClauses, Flags, Precedence);
    /* File and input flags have higher precedence */
    flag_TransferSetFlags(InputFlags, Flags);
  }

  /* Rearrange automatically determined precedence according to user's specification. */
  symbol_RearrangePrecedence(Precedence, UserPrecedence);

  if (NativeClauseInput) {
    CLAUSE Clause;
    for (Scan = ProblemClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      Clause = (CLAUSE)list_Car(Scan);
      clause_OrientEqualities(Clause, Flags, Precedence);
      clause_Normalize(Clause);
      clause_SetNativeMaxLitFlags(Clause, Flags, Precedence);
      clause_UpdateWeight(Clause, Flags);
      clause_UpdateMaxVar(Clause);
    }
  }
  else
    for (Scan = ProblemClauses; !list_Empty(Scan); Scan = list_Cdr(Scan))
      clause_OrientAndReInit(list_Car(Scan), Flags, Precedence);

  prfs_SetInputClauses(Search, list_Length(ProblemClauses));

  /* Must be called after ana_AnalyzeProblem and Reorientation */
  ana_AnalyzeSortStructure(ProblemClauses, Flags, Precedence);

  if (flag_GetFlagValue(Flags, flag_AUTO)) {
    ana_ExploitSortAnalysis(Flags);
    /* File and input flags have higher precedence */
    flag_TransferSetFlags(InputFlags, Flags);
  }
  prfs_SetSplitCounter(Search, flag_GetFlagValue(Flags, flag_SPLITS));

  ActBound       = flag_GetFlagValue(Flags, flag_BOUNDSTART);
  BoundMode      = flag_GetFlagValue(Flags, flag_BOUNDMODE);
  BoundLoops     = flag_GetFlagValue(Flags, flag_BOUNDLOOPS);
  *BoundApplied  = -1;

  if (flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    puts("");
    puts("--------------------------TSPASS-START-----------------------------");
    puts("Input Problem:");
    clause_ListPrint(ProblemClauses);
    ana_Print(Flags, Precedence);
  }

  if (!NativeClauseInput && flag_GetFlagValue(Flags, flag_SORTS) != flag_SORTSOFF) {
    BOOL Strong;
    Strong = (flag_GetFlagValue(Flags, flag_SORTS) == flag_SORTSMONADICALL);
    for (Scan = ProblemClauses; !list_Empty(Scan); Scan = list_Cdr(Scan))
      clause_SetSortConstraint((CLAUSE)list_Car(Scan),Strong,Flags, Precedence);
  }

  if (flag_GetFlagValue(Flags, flag_RINPUT)) {
    clock_StartCounter(clock_REDUCTION);
    EmptyClauses = red_ReduceInput(Search, ProblemClauses);
    clock_StopAddPassedTime(clock_REDUCTION);
    if (list_Empty(EmptyClauses) && flag_GetFlagValue(Flags, flag_SATINPUT))
      EmptyClauses = red_SatInput(Search);
  }
  else {
    for (Scan=ProblemClauses; !list_Empty(Scan); Scan=list_Cdr(Scan))
      if (red_ExplicitTautology(Search, list_Car(Scan),Flags,Precedence)) {
        clause_Delete(list_Car(Scan));
      }
      else
        prfs_InsertUsableClause(Search, list_Car(Scan));
  }
  Derivables = list_Nil();

  if (ana_SortRestrictions() ||
      (ana_UnsolvedSortRestrictions() &&
       flag_GetFlagValue(Flags,flag_SORTS) == flag_SORTSMONADICALL)) {
    if (flag_GetFlagValue(Flags, flag_RSST))
      prfs_SetStaticSortTheory(Search,sort_ApproxStaticSortTheory(prfs_UsableClauses(Search),Flags,Precedence));
    prfs_SetDynamicSortTheory(Search,sort_TheoryCreate());
  }

  /* Fix literal order in clauses in the usable set.
     Since they are shared, we have to extract them from
     the sharing before fixing them. Afterwards, we have to
     insert them in the sharing again.
  */ 
  for (Scan = prfs_UsableClauses(Search);
       !list_Empty(Scan);
       Scan = list_Cdr(Scan)) {
    CLAUSE clause;
    clause = list_Car(Scan);
    clause_MakeUnshared(clause,prfs_UsableSharingIndex(Search));
    clause_FixLiteralOrder(clause, Flags, Precedence);
    clause_InsertIntoSharing(clause, prfs_UsableSharingIndex(Search),
          prfs_Store(Search), prfs_Precedence(Search));
  }

  /* Calculate the frequency counts for the symbols in the usable set. */
  for (Scan = prfs_UsableClauses(Search);
       !list_Empty(Scan);
       Scan = list_Cdr(Scan)) {
    CLAUSE clause;
    clause = list_Car(Scan);

    clause_CountSymbols(clause);
  }

  /* Sort usable set. */
  prfs_SetUsableClauses(Search, 
    list_Sort(prfs_UsableClauses(Search), 
      (BOOL (*) (void *, void *)) clause_CompareAbstractLEQ));

  if (flag_GetFlagValue(Flags, flag_SOS)) {
    Derivables = list_Copy(prfs_UsableClauses(Search));
    for (Scan=Derivables;!list_Empty(Scan);Scan=list_Cdr(Scan))
      if (!clause_GetFlag(list_Car(Scan), CONCLAUSE))
        prfs_MoveUsableWorkedOff(Search,list_Car(Scan));
    list_Delete(Derivables);
  }

  if (flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    puts("\nProcessed Problem:");
    puts("\nWorked Off Clauses:");
    clause_ListPrint(prfs_WorkedOffClauses(Search));
    puts("\nUsable Clauses:");
    clause_ListPrint(prfs_UsableClauses(Search));
    puts("\nEventuality Clauses:");
    clause_ListPrint(prfs_EventualityClauses(Search));
  }

  while ((list_Empty(EmptyClauses) || !prfs_SplitStackEmpty(Search)) && 
    prfs_Loops(Search) != 0 &&
    ((*BoundApplied != -1) || !list_Empty(prfs_UsableClauses(Search))) &&
    (flag_GetFlagValue(Flags,flag_TIMELIMIT) == flag_TIMELIMITUNLIMITED ||
    flag_GetFlagValue(Flags,flag_TIMELIMIT) > clock_GetSeconds(clock_OVERALL))) {

    Derivables    = list_Nil();
    SplitClause   = (CLAUSE)NULL;
    *BoundApplied = -1;

    while ((list_Empty(EmptyClauses) || !prfs_SplitStackEmpty(Search)) && 
      prfs_Loops(Search) != 0 &&
      (!list_Empty(prfs_UsableClauses(Search)) || !list_Empty(EmptyClauses)) &&
      (flag_GetFlagValue(Flags,flag_TIMELIMIT) == flag_TIMELIMITUNLIMITED ||
        flag_GetFlagValue(Flags,flag_TIMELIMIT) > clock_GetSeconds(clock_OVERALL))) {

      if (!list_Empty(EmptyClauses)) {
        /* Backtracking */
        clock_StartCounter(clock_BACKTRACK);
        Derivables = split_Backtrack(Search, HighestLevelEmptyClause,
                  &SplitClause);
        clock_StopAddPassedTime(clock_BACKTRACK);
        prfs_IncBacktrackedClauses(Search, list_Length(Derivables));

        if (prfs_SplitStackEmpty(Search))
          Derivables = list_Nconc(EmptyClauses, Derivables);
        else {
          for ( ; !list_Empty(EmptyClauses); EmptyClauses = list_Pop(EmptyClauses))
            if (list_Car(EmptyClauses) != HighestLevelEmptyClause)
              clause_Delete(list_Car(EmptyClauses));
          prfs_InsertDocProofClause(Search, HighestLevelEmptyClause);
          /* Keep HighestLevelEmptyClause for finding the terms required */
          /* for the proof.                                              */
          if (flag_GetFlagValue(Flags, flag_DOCPROOF))
            UsedEmptyClauses = list_Cons(HighestLevelEmptyClause, UsedEmptyClauses);
          if (flag_GetFlagValue(Flags, flag_DOCSPLIT)) {
            printf("\n\t Split Backtracking level %d:",prfs_ValidLevel(Search));
            if (flag_GetFlagValue(Flags, flag_DOCSPLIT) == 2) {
              LIST Scon;
              printf("\n\t Backtracked clauses:");
              for(Scon=Derivables;!list_Empty(Scon);Scon=list_Cdr(Scon)) {
                fputs("\n\tBclause: ", stdout);
                clause_Print((CLAUSE)list_Car(Scon));
                fflush(stdout);
              }
              printf("\n\t End Backtracked clauses:");
            }
          }
        }
        EmptyClauses            = list_Nil();
        HighestLevelEmptyClause = (CLAUSE)NULL;
      }
      else {   /* no empty clause found */

#ifdef CHECK
      if (!prfs_Check(Search)) {
        misc_StartErrorReport();
        misc_ErrorReport("\n In top_ProofSearch: Illegal state of search in SPASS.\n");
        misc_FinishErrorReport();
      }
      if (!ana_Equations())
        red_CheckSplitSubsumptionCondition(Search);
#endif 

      if (flag_GetFlagValue(Flags, flag_FULLRED))
        Derivables = top_FullReductionSelectGivenComputeDerivables(Search, &SplitClause, &Counter, &LoopClauseCounter);
      else
        Derivables = top_LazyReductionSelectGivenComputeDerivables(Search, &SplitClause, &Counter);
      }

      /* Print the derived clauses, if required */
      if (flag_GetFlagValue(Flags, flag_PDER)) {
        for (Scan=Derivables; !list_Empty(Scan); Scan=list_Cdr(Scan)) {
          fputs("\nDerived: ", stdout); 
          clause_Print(list_Car(Scan));
        }
      }

      /* Partition the derived clauses into empty and non-empty clauses */
      Derivables = split_ExtractEmptyClauses(Derivables, &EmptyClauses);

      /* Apply reduction rules */
      clock_StartCounter(clock_REDUCTION);
      if (flag_GetFlagValue(Flags, flag_FULLRED)) {
        EmptyClauses = 
          list_Nconc(EmptyClauses,
              red_CompleteReductionOnDerivedClauses(Search, Derivables,
                      red_ALL, ActBound,
                      BoundMode,
                      BoundApplied));
      }
      else {
        EmptyClauses =
          list_Nconc(EmptyClauses,
              red_CompleteReductionOnDerivedClauses(Search, Derivables,
                      red_WORKEDOFF,
                      ActBound, BoundMode,
                      BoundApplied));
      }
      clock_StopAddPassedTime(clock_REDUCTION);

      Derivables = list_Nil();
/* !!!!!!!!!!!! Temporal Logic Stuff !!!!!!!!!!!!!!!!!!! */
      if(list_Empty(prfs_UsableClauses(Search))
         || prfs_LoopSearchIterations(Search) == flag_GetFlagValue(Flags, flag_LOOPSEARCHITERATIONS)) {


        if(!list_Empty(prfs_EventualityClauses(Search))) {
          if (flag_GetFlagValue(Flags, flag_PGIVEN)) {
            printf("\nPerforming loop search");
            if(list_Empty(prfs_UsableClauses(Search))) {
              printf(", due to an empty set of usable clauses");
            }
            printf("...");
          }
        }

        for(LIST list2 = prfs_EventualityClauses(Search); !list_Empty(list2); list2 = list_Cdr(list2)) {
          CLAUSE EventualityClause = list_Car(list2);
  
          Derivables = list_Nconc(tl_PerformLoopSearchTests(EventualityClause, Search), Derivables);
        }
  
        /* Print the derived clauses (again), if required */
        if (flag_GetFlagValue(Flags, flag_PDER)) {
          for (Scan=Derivables; !list_Empty(Scan); Scan=list_Cdr(Scan)) {
            fputs("\nDerived: ", stdout); 
            clause_Print(list_Car(Scan));
          }
        }

        prfs_IncDerivedClauses(Search, list_Length(Derivables));

        if(!list_Empty(Derivables)) {
          /* Apply reduction rules again */
          clock_StartCounter(clock_REDUCTION);
          if (flag_GetFlagValue(Flags, flag_FULLRED)) {
            EmptyClauses = 
              list_Nconc(EmptyClauses,
                  red_CompleteReductionOnDerivedClauses(Search, Derivables,
                          red_ALL, ActBound,
                          BoundMode,
                          BoundApplied));
          }
          else {
            EmptyClauses =
              list_Nconc(EmptyClauses,
                  red_CompleteReductionOnDerivedClauses(Search, Derivables,
                          red_WORKEDOFF,
                          ActBound, BoundMode,
                          BoundApplied));
          }
          clock_StopAddPassedTime(clock_REDUCTION);
        }
        prfs_ResetLoopSearchIterations(Search);
      }
      if (!list_Empty(EmptyClauses)) {
        HighestLevelEmptyClause = split_SmallestSplitLevelClause(EmptyClauses);
        if (flag_GetFlagValue(Flags, flag_PEMPTYCLAUSE)) {
          fputs("\nEmptyClause: ", stdout);
          clause_Print(HighestLevelEmptyClause);
        }
      }
      prfs_DecLoops(Search);
      prfs_IncreaseLoopSearchIterations(Search);
    }

    if (ActBound != flag_BOUNDSTARTUNLIMITED &&
        BoundMode != flag_BOUNDMODEUNLIMITED) {
      BoundLoops--;
      if (BoundLoops == flag_BOUNDLOOPSMIN)
        ActBound = flag_BOUNDSTARTUNLIMITED;
      else
        ActBound = *BoundApplied;
      if (*BoundApplied != -1) {
        prfs_SwapIndexes(Search);
      if  (flag_GetFlagValue(Flags,flag_PBINC))
        printf("\n\n\t ---- New Clause %s Bound: %2d ----\n",
        (BoundMode==flag_BOUNDMODERESTRICTEDBYDEPTH) ? "Term Depth" : "Weight",ActBound);
      }
    }
  }
  prfs_SetEmptyClauses(Search, EmptyClauses);
  prfs_SetUsedEmptyClauses(Search, UsedEmptyClauses);

  return Search;
}
 
