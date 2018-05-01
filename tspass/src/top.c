/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *              TOP MODULE OF SPASS                       * */
/* *                                                        * */
/* *  $Module:   TOP                                        * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000, 2001      * */
/* *  MPI fuer Informatik                                   * */
/* *                                                        * */
/* *  Copyright (C) 2008-2011                               * */
/* *  Michel Ludwig (michel.ludwig@gmail.com)               * */
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



/*** MAIN LOOP *************************************************/


/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "alarm.h"
#include "dfg.h"
#include "defs.h"
#include "ia.h"
// #include "rules-inf.h"
// #include "rules-sort.h"
// #include "rules-split.h"
// #include "terminator.h"
#include "rules-red.h"
#include "analyze.h"
#include "clock.h"
#include "strings.h"
#include "options.h"
#include "context.h"
#include "cnf.h"
#include "search.h"
#include "hasharray.h"
#include "closure.h"
#include "eml.h"
#include "tl.h"
#include "proof.h"
#include <errno.h>
#include <stdlib.h>


/**************************************************************/
/* Types and Variables                                        */
/**************************************************************/

static const char *top_InputFile;

static OPTID top_RemoveFileOptId;

typedef enum {top_PROOF, top_COMPLETION, top_RESOURCE} top_SEARCHRESULT;


/**************************************************************/
/* Catch Signals Section                                      */
/**************************************************************/

#ifdef SPASS_SIGNALS
#include <signal.h>

static PROOFSEARCH *top_PROOFSEARCH;

static void top_SigHandler(int Signal)
/**************************************************************
  INPUT:   
  RETURNS: 
  EFFECT:  
***************************************************************/
{
  if (Signal == SIGSEGV || Signal == SIGBUS) {
    puts("\n\n\tTSPASS is going to crash. This is probably caused by a");
    puts("\tbug in TSPASS.  Please send a copy of the input file(s) together");
    puts("\twith the used options to the author.\n");
    abort();
  }

  if (Signal == SIGINT || Signal == SIGTERM) {
    clock_StopPassedTime(clock_OVERALL);
    printf("\nTSPASS %s ", vrs_VERSION);
    puts("\nSPASS beiseite: Ran out of time. TSPASS was killed.");
    printf("Problem: %s ", 
      (top_InputFile != (char*)NULL ? top_InputFile : "Read from stdin."));
    printf("\nTSPASS derived %d clauses, backtracked %d clauses "
      "and kept %d clauses.",
      (*top_PROOFSEARCH == (PROOFSEARCH)NULL ? 0 : prfs_DerivedClauses(*top_PROOFSEARCH)),
      (*top_PROOFSEARCH == (PROOFSEARCH)NULL ? 0 : prfs_BacktrackedClauses(*top_PROOFSEARCH)),
      (*top_PROOFSEARCH == (PROOFSEARCH)NULL ? 0 : prfs_KeptClauses(*top_PROOFSEARCH)));
    printf("\nTSPASS allocated %lu KBytes.", memory_DemandedBytes()/1024);
    fputs("\nTSPASS spent\t", stdout);
    clock_PrintTime(clock_OVERALL);
    fputs(" on the problem.\n\t\t", stdout);
    clock_PrintTime(clock_INPUT);
    fputs(" for the input.\n\t\t", stdout);
    clock_PrintTime(clock_CNF);
    fputs(" for the FLOTTER CNF translation.\n\t\t", stdout);
    clock_PrintTime(clock_INFERENCE);
    fputs(" for inferences.\n\t\t", stdout);
    clock_PrintTime(clock_BACKTRACK);
    fputs(" for the backtracking.\n\t\t", stdout);
    clock_PrintTime(clock_REDUCTION);
    puts(" for the reduction.");
  }

  if (opts_IsSet(top_RemoveFileOptId))
    remove(top_InputFile);

  exit(EXIT_FAILURE);
}

#endif







static void top_Flotter(int argc, const char* argv[], LIST InputClauses, HASH ClauseToTermLabelList)
/**************************************************************
  INPUT:  
  RETURNS: Nothing.
  EFFECT:  
***************************************************************/
{
  FILE *Output;
  char *description;
  const char *creator = "\n\tCNF generated by FLOTTER " vrs_VERSION " *}";
  int  size;
  int  creator_size;

  if (argc < opts_Indicator()+2)
    Output = stdout;
  else
    Output = misc_OpenFile(argv[opts_Indicator()+1],"w");

  creator_size = (int)strlen(creator);
  size        = (int)strlen(dfg_ProblemDescription()) + creator_size;
  description = (char*)memory_Malloc(sizeof(char)*size);
  strncpy(description,dfg_ProblemDescription(),size-creator_size-3);
  strcpy(description+size-creator_size-3, creator);


  clause_FPrintCnfDFGProblem(Output, FALSE, dfg_ProblemName(), dfg_ProblemAuthor(), 
                      dfg_ProblemStatusString(), description, InputClauses, 
                      NULL, NULL, NULL, ClauseToTermLabelList, FALSE, TRUE);

  fputs("\nFLOTTER needed\t", stdout);
  clock_PrintTime(clock_INPUT);
  puts(" for the input.");
  fputs("\t\t", stdout);
  clock_PrintTime(clock_CNF);
  fputs(" for the  CNF translation.", stdout);
  

  if (Output != stdout)
    misc_CloseFile(Output,argv[opts_Indicator()+1]);
  memory_Free(description, sizeof(char)*size);
}

static BOOL top_CalledFlotter(FLAGSTORE Flags, const char* Call)
{ 
  int  length;
  BOOL result;
  length = strlen(Call);
  result = string_Equal((Call + (length > 7 ? length - 7 : 0)), "FLOTTER");
  if (result)
    flag_SetFlagValue(Flags, flag_FLOTTER, flag_FLOTTERON);
  return result;
}

static void top_EstablishClAxRelation(LIST ClAxRelation, LIST InputClauses, LIST* Labellist, HASH ClauseToTermLabellist, BOOL DocProof)
/**************************************************************
  INPUT:   A list of relations netween clause numbers and formula labels (strings) <ClAxRelation>
           a list of input clauses
           the list of used formula labels
           a hash array relating clauses to formula labels (strings)
           the doc proof flag
  RETURNS: Nothing.
  EFFECT:  If <DocProof> and the <ClAxRelation> is not empty, then the
           list representation of the clause to formula label relation is established
           in the hash array <ClauseToTermLabellist> and the labels are collected in  <Labellist>

           the <ClAxRelation> is eventually deleted
***************************************************************/
{
  LIST   Scan1, Scan2;
  CLAUSE Clause;

  if (!list_Empty(ClAxRelation)) {
    if (DocProof) {
      for (Scan1=ClAxRelation; !list_Empty(Scan1);Scan1=list_Cdr(Scan1)) {
        for (Scan2=InputClauses; 
            !list_Empty(Scan2) &&
              clause_Number((CLAUSE)list_Car(Scan2)) != (int)list_Car(list_Car(Scan1));
            Scan2=list_Cdr(Scan2));
        if (list_Empty(Scan2)) {
          misc_StartUserErrorReport();
          misc_UserErrorReport("\n For clause %d a formula relation was defined but the clause was not found in the input file!\n", 
                  (int)list_Car(list_Car(Scan1)));
          misc_FinishUserErrorReport();
        }
        Clause = (CLAUSE)list_Car(Scan2);
        for (Scan2=list_Cdr(list_Car(Scan1)); !list_Empty(Scan2); Scan2=list_Cdr(Scan2))
          *Labellist = list_Cons(list_Car(Scan2), *Labellist);
        hsh_PutList(ClauseToTermLabellist, Clause, list_Cdr(list_Car(Scan1)));
        list_Free(list_Car(Scan1));   
      }
      *Labellist = list_PointerDeleteDuplicates(*Labellist);
      for (Scan1=InputClauses; !list_Empty(Scan1);Scan1=list_Cdr(Scan1))
        if (hsh_Get(ClauseToTermLabellist, list_Car(Scan1)) == NULL) {
          misc_StartUserErrorReport();
          misc_UserErrorReport("\n The formula relation  for clause %d is missing!\n", 
                  clause_Number((CLAUSE)list_Car(Scan1)));
          misc_FinishUserErrorReport();
        }
    }
    else {
      for (Scan1=ClAxRelation;!list_Empty(Scan1);Scan1=list_Cdr(Scan1)) {
        for (Scan2=list_Cdr(list_Car(Scan1));!list_Empty(Scan2);Scan2=list_Cdr(Scan2))
          string_StringFree((char *)list_Car(Scan2));
        list_Delete(list_Car(Scan1));
      }
    }
    list_Delete(ClAxRelation);
  }
}



/**************************************************************/
/* Main Function                                              */
/**************************************************************/

int main(int argc, const char* argv[])
{
  LIST              InputClauses,Scan,Axioms,Conjectures, Sorts, QueryClauses, 
    LabelClauses, QueryPair, ProblemClauses, Labellist, Sortlabellist, 
    Symblist, UserPrecedence, UserSelection, ClAxRelation;
  LIST InitialClauses, UniversalClauses, StepClauses = list_Nil(), NewStepClauses = list_Nil(),
       EventualityClauses;
  LIST Constants = list_Nil(), NewConstants = list_Nil();
  LIST ListOfLeftHandSideSymbols = list_Nil();
  PROOFSEARCH       Search, FlotterSearch;
  /* <InputFlags> are the flags from the problem file and the command line. */
  FLAGSTORE         InputFlags, Flags;
  /* <InputPrecedence> is the precedence after reading the problem file. */
  PRECEDENCE        InputPrecedence, Precedence;
  FILE*             InputStream; 
  HASH              TermLabelToClauselist, ClauseToTermLabellist;
  top_SEARCHRESULT  Result;
  BOOL              NativeClauseInput;
  unsigned int      NumberOfEventualities = 0;

  Search = (PROOFSEARCH)NULL;
  NativeClauseInput = FALSE;
  
#ifdef SPASS_SIGNALS
  top_PROOFSEARCH = &Search;
  signal(SIGINT, top_SigHandler);
  signal(SIGTERM, top_SigHandler);
  signal(SIGSEGV, top_SigHandler);
  signal(SIGBUS, top_SigHandler);
#endif

  clock_Init();
  clock_StartCounter(clock_OVERALL);
  memory_Init(memory__UNLIMITED);
  atexit(memory_FreeAllMem);
  symbol_Init(TRUE);
  stack_Init();
  hash_Init();
  sort_Init();
  term_Init();

  InputPrecedence = symbol_CreatePrecedence();
  fol_Init(TRUE, InputPrecedence);
  eml_Init(InputPrecedence);
  tl_Init(InputPrecedence);
  cont_Init();
  unify_Init();
  flag_Init();
  subs_Init();
  clause_Init();
  red_Init();
  ren_Init();
  dp_Init();
  opts_Init();
  ana_Init();
  cc_Init();
  alarm_Init();

  /* Build proof search object to store definitions in */
  Search      = prfs_Create();
  InputFlags  = flag_CreateStore();

  /* declare all options */
  opts_DeclareSPASSFlagsAsOptions();
  top_RemoveFileOptId = opts_Declare("rf", opts_NOARGTYPE);

  if (!opts_Read(argc, argv)) 
    return EXIT_FAILURE;

   /* Check whether flag_STDIN is set in the command line */
  flag_InitStoreByDefaults(InputFlags);
  opts_SetFlags(InputFlags);

  if (argc < opts_Indicator()+1 && !flag_GetFlagValue(InputFlags,flag_STDIN)) {
    /* No input file, no stdin input */
    printf("\n\t          %s %s",argv[0],vrs_VERSION);
    if (top_CalledFlotter(InputFlags, argv[0]) ||
	flag_GetFlagValue(InputFlags, flag_FLOTTER))
      puts("\n\t       Usage: FLOTTER [options] [<input-file>] [<output-file>]\n");
    else
      puts("\n\t       Usage: TSPASS [options] [<input-file>] \n");
    puts("Possible options:\n");
    opts_PrintSPASSNames(); 
    return EXIT_FAILURE;
  }
  FlotterSearch = NULL;

  Axioms = Conjectures = EventualityClauses = Sorts = Labellist = Sortlabellist = UserPrecedence = UserSelection = ClAxRelation = list_Nil();
  
  if (flag_GetFlagValue(InputFlags, flag_STDIN)) {
    top_InputFile = (char*)NULL;
    InputStream   = stdin;
  } else {
    top_InputFile = argv[opts_Indicator()];
    InputStream = misc_OpenFile(top_InputFile, "r");
  }
  
  clock_StartCounter(clock_INPUT);
  flag_CleanStore(InputFlags);  /* Mark all flags as unset */

  /* Now add flags from file to InputFlags and set precedence */
  InputClauses = dfg_DFGParser(InputStream, InputFlags, InputPrecedence, &Axioms,
			       &Conjectures, &EventualityClauses, &Sorts, &UserPrecedence, &UserSelection, 
                               &ClAxRelation, &NativeClauseInput); 

  for(Scan=UserSelection;!list_Empty(Scan);Scan=list_Cdr(Scan))
    symbol_AddProperty((SYMBOL)list_Car(Scan), SELECTED);

  if(!list_Empty(Conjectures)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Conjecture formulae are not allowed!\n");
    misc_FinishUserErrorReport();  
  }

  InitialClauses = list_Nil();
  UniversalClauses = list_Nil();
  StepClauses = list_Nil();
  EventualityClauses = list_Nil();

  /* Add/overwrite with command line flags */
  opts_SetFlags(InputFlags);
  Flags      = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);
  /* The Flags were initialized with the default flag values.  */
  /* This values are now overwritten by command line flags and flags */
  /* from the input file. */
  flag_TransferSetFlags(InputFlags, Flags);
  /* From now on the input flags are not changed! */

  if (flag_GetFlagValue(Flags,flag_TIMELIMIT) != flag_TIMELIMITUNLIMITED) 
    alarm_SetAlarm(flag_GetFlagValue(Flags,flag_TIMELIMIT)+10); /* No race with main loop polling */
  
  /* Transfer input precedence to search object */
  symbol_TransferPrecedence(InputPrecedence, Precedence);


  /* Complain about missing input clauses/formulae when in */
  /* non-interactive mode */
  if (!flag_GetFlagValue(Flags, flag_INTERACTIVE) && list_Empty(Axioms) &&
      list_Empty(Conjectures) && list_Empty(InputClauses)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n No formulae and clauses found in input file!\n");
    misc_FinishUserErrorReport();
  }

  cnf_Init(Flags);  /* Depends on Strong Skolemization Flag */

  /* DocProof is required for interactive mode */
  if (flag_GetFlagValue(Flags, flag_INTERACTIVE)) {
    flag_SetFlagValue(Flags, flag_DOCPROOF, flag_DOCPROOFON);
  }

  if (flag_GetFlagValue(Flags, flag_DOCPROOF))
    prfs_AddDocProofSharingIndex(Search);

  /* Create necessary hasharrays */
  if (flag_GetFlagValue(Flags, flag_DOCPROOF)  || 
      top_CalledFlotter(Flags, argv[0]) || flag_GetFlagValue(Flags, flag_FLOTTER)) {
    TermLabelToClauselist = hsh_Create();
    ClauseToTermLabellist = hsh_Create();
  }
  else {
    TermLabelToClauselist = NULL;
    ClauseToTermLabellist = NULL;
  }

  /* Establish clause to term (formula) labels in case of doc proof */
  top_EstablishClAxRelation(ClAxRelation,InputClauses, &Labellist, ClauseToTermLabellist,flag_GetFlagValue(Flags, flag_DOCPROOF));
  
  /* Build conjecture formula and negate it: Conjectures are taken disjunctively!!*/
  for (Scan = Conjectures; !list_Empty(Scan); Scan = list_Cdr(Scan))
    list_Rplacd(list_Car(Scan), (LIST)term_Create(fol_Not(), 
						  list_List(list_PairSecond(list_Car(Scan)))));

  clock_StopPassedTime(clock_INPUT);

  if (top_InputFile) {
    misc_CloseFile(InputStream,top_InputFile);
    if (opts_IsSet(top_RemoveFileOptId))
      remove(top_InputFile);
  }

  clock_StartCounter(clock_CNF);

  if (list_Empty(InputClauses)) {
    NAT Termcount;

    Termcount  = 0;
    
    /* Create labels for formulae without them */
    for (Scan = Axioms; !list_Empty(Scan); Scan = list_Cdr(Scan), Termcount++) {
      if (list_PairFirst(list_Car(Scan)) == NULL) {
	char L[100];
	char* Label;
	sprintf(L, "axiom%d", Termcount);
	Label = string_StringCopy(L);
	list_Rplaca(list_Car(Scan), Label);
	if (flag_GetFlagValue(Flags, flag_DOCPROOF) &&
	    flag_GetFlagValue(Flags, flag_PLABELS)) {
	  printf("\nAdded label %s for axiom \n", Label);
	  fol_PrettyPrintDFG((TERM) list_PairSecond(list_Car(Scan)));
	}
      }
    }
    Termcount  = 0;
    for (Scan = Sorts; !list_Empty(Scan); Scan = list_Cdr(Scan), Termcount++) {
      char L[100];
      char* Label;
      sprintf(L, "declaration%d", Termcount);
      Label = string_StringCopy(L);
      list_Rplaca(list_Car(Scan), Label);
      if (flag_GetFlagValue(Flags, flag_DOCPROOF) &&
	  flag_GetFlagValue(Flags, flag_PLABELS)) {
	printf("\nAdded label %s for declaration \n", Label);
	fol_PrettyPrintDFG((TERM) list_PairSecond(list_Car(Scan)));
      }
      Sortlabellist = list_Cons(Label, Sortlabellist);
    }
    Axioms = list_Nconc(Axioms, Sorts);

    if (flag_GetFlagValue(Flags, flag_EML)) {
      clock_StartCounter(clock_TRANSL);

      /* Reduce EML special formulae to first-order logic */
      if (flag_GetFlagValue(Flags, flag_EML) ) {
        eml_TranslateToFolMain(&Axioms, &Conjectures, 
	        flag_GetFlagValue(Flags, flag_INTERACTIVE), Flags, Precedence);
      }

      clock_StopPassedTime(clock_TRANSL);
    }

    if (flag_GetFlagValue(Flags, flag_APPLYDEFS) != flag_APPLYDEFSOFF) {
      def_ExtractDefsFromTermlist(Search, Axioms, Conjectures); 
      Conjectures = def_ApplyDefinitionToTermList(prfs_Definitions(Search),
						  Conjectures, Flags,
						  Precedence);
    }

    /* We must keep the list of symbols because they can't be freed in cnf_Flotter */
    Symblist = list_Nil();

    /* Axioms is list of pairs, conjectures is list of terms */
    /* A ProofSearch object is only returned and the symbols kept in Symblist
       if flag_INTERACTIVE is set */
    BOOL predicateMap[symbol__MAXSIGNATURE];
    memset(predicateMap, symbol_Null(), sizeof(predicateMap));

    FlotterSearch = cnf_Flotter(Axioms, Conjectures, &Labellist,
                                &InitialClauses, &UniversalClauses,
                                &StepClauses, &EventualityClauses,
                                TermLabelToClauselist, ClauseToTermLabellist,
                                Flags, Precedence, &Symblist, predicateMap);

    tl_TranslateToFOL(InitialClauses, predicateMap, Flags, Precedence, FALSE);
    tl_TranslateToFOL(UniversalClauses, predicateMap, Flags, Precedence, TRUE);
    // copy the step clauses as they will still be needed later
    InputClauses = list_Nconc(list_Nconc(InitialClauses, UniversalClauses), list_Copy(StepClauses));

    InputClauses = clause_ListSortWeighed(InputClauses);
    clause_SetCounter(1);
    for (Scan = InputClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      clause_NewNumber(list_Car(Scan));
    }
  }
  else {
    dfg_DeleteFormulaPairList(Axioms);
    dfg_DeleteFormulaPairList(Sorts);
    dfg_DeleteFormulaPairList(Conjectures);
    if (flag_GetFlagValue(Flags, flag_APPLYDEFS) != flag_APPLYDEFSOFF) {
      /* Extract list of definitions */
      def_ExtractDefsFromClauselist(Search, InputClauses);
      def_FlattenDefinitionsDestructive(Search);
      for (Scan=prfs_Definitions(Search); !list_Empty(Scan); Scan=list_Cdr(Scan))
        InputClauses = def_ApplyDefToClauselist(Search, (DEF) list_Car(Scan),
                                                InputClauses, TRUE);
    }
  }

  clock_StopPassedTime(clock_CNF);

  if (top_CalledFlotter(Flags, argv[0]) || flag_GetFlagValue(Flags, flag_FLOTTER)) {
    top_Flotter(argc,argv,InputClauses, ClauseToTermLabellist);
    flag_SetFlagValue(Flags, flag_TIMELIMIT,   0);       /* Exit No Output */
    flag_SetFlagValue(Flags, flag_INTERACTIVE, flag_INTERACTIVEOFF);
    flag_SetFlagValue(Flags, flag_PPROBLEM,    flag_PPROBLEMOFF);
  }

  /* First of all, remove duplicate eventuality clauses */
  EventualityClauses = list_DeleteDuplicatesFree(EventualityClauses, (BOOL (*)(POINTER, POINTER))clause_Equal,
                                                                     (void (*)(POINTER))clause_Delete);
  Constants = tl_ListOfConstants(InputClauses);
  Constants = list_Nconc(Constants, tl_ListOfConstants(EventualityClauses));

  // we don't want Skolem constants
  for(LIST Scan = Constants; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    SYMBOL Constant = (SYMBOL) list_Car(Scan);
    if(!symbol_HasProperty(Constant, SKOLEM)) {
      NewConstants = list_Cons((POINTER) Constant, NewConstants);
    }
  }
  list_Delete(Constants);
  Constants = NewConstants;

  // duplicate elements might have been added again by the call to 'list_Nconc' above
  list_DeleteDuplicates(Constants, (BOOL (*)(POINTER, POINTER)) symbol_Equal);
  
  if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    printf("\nNon-Skolem constants contained in the problem: ");
    for(LIST Scan = Constants; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      SYMBOL Symbol = (SYMBOL) list_Car(Scan);
      symbol_Print(Symbol);
      if(!list_Empty(list_Cdr(Scan))) {
        printf(", ");
      }
    }
  }

  // after the next line, 'EventualityClauses' still doesn't contain any duplicate eventualities; 'tl_PerformConstantFlooding'
  // takes care of this
  EventualityClauses = list_Nconc(EventualityClauses, tl_PerformConstantFlooding(EventualityClauses, Constants, Flags));

  // perform constant flooding with the loop search constant if necessary
  // can't lead to duplicate entries in the list
  if(list_Length(EventualityClauses) > 0) {
    Constants = list_Cons((POINTER) tl_LoopSearchConstant(), Constants);
  }

  NewStepClauses = tl_PerformConstantFlooding(StepClauses, Constants, Flags);
  StepClauses = list_Nconc(StepClauses, list_Copy(NewStepClauses));
  InputClauses = list_Nconc(InputClauses, NewStepClauses);

  tl_ComputeTemporalOrdering(StepClauses, Flags);

  if (flag_GetFlagValue(Flags, flag_MODELCONSTRUCTION) != flag_MODELCONSTRUCTIONOFF) {
    ListOfLeftHandSideSymbols = tl_ListOfSymbolsFromLeftHandSides(StepClauses);
  }

  list_Delete(Constants);
  list_Delete(StepClauses);

  prfs_SetEventualityClauses(Search, EventualityClauses);
  tl_InitEventualityInformation(EventualityClauses, Precedence);
  prfs_IncInputClauses(Search, list_Length(EventualityClauses));
  NumberOfEventualities = list_Length(EventualityClauses);

  for(Scan = EventualityClauses; !list_Empty(Scan); Scan = list_Cdr(Scan))
  {
    CLAUSE Clause = list_Car(Scan);
    CLAUSE InitLoopSearchClause = NULL;

    clause_ReInit(Clause, Flags, Precedence);
    tl_CreateLoopSearchMarker(0, Clause, Precedence);
    InitLoopSearchClause = tl_CreateLoopSearchStepClause(0, Clause, list_Nil(), Flags, Precedence);
    if(InitLoopSearchClause) {
      InputClauses = list_Cons(InitLoopSearchClause, InputClauses);
    }
  }

  if(flag_GetFlagValue(Flags, flag_PPROBLEM)) {
    printf("\nStep clauses:");
  }

  TEMPORAL_MODE = TRUE;
  // re-initialise the clauses, especially to get the temporal type right
  for(Scan = InputClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE Clause = list_Car(Scan);
    clause_ReInit(Clause, Flags, Precedence);
    if(flag_GetFlagValue(Flags, flag_PPROBLEM)
     && (clause_GetTemporalType(Clause) == STEP || clause_GetTemporalType(Clause) == LOOPSEARCH)) {
      printf("\n"); clause_Print(Clause);
    }
  }
  
  tl_AttachProofSearch(Search);

  memory_Restrict(flag_GetFlagValue(Flags, flag_MEMORY));
  symbol_SeparateVariableSymbolNames();

  flag_SetFlagValue(Flags, flag_AUTO, flag_OFF);
  flag_SetFlagValue(Flags, flag_SELECT, flag_SELECTOFF);
  flag_SetFlagValue(Flags, flag_IORE, flag_ORDEREDRESOLUTIONNOEQUATIONS);
  flag_SetFlagValue(Flags, flag_IOFC, flag_FACTORINGONLYRIGHT);
  flag_SetFlagValue(Flags, flag_ROBV, flag_ROBVON);
  // comment the next three lines out if you want to control which type of redundancy elimination is performed
  flag_SetFlagValue(Flags, flag_RTAUT, flag_RTAUTSYNTACTIC);
  flag_SetFlagValue(Flags, flag_RFSUB, flag_RFSUBON);
  flag_SetFlagValue(Flags, flag_RBSUB, flag_RBSUBON);
  flag_SetFlagValue(Flags, flag_FULLRED, flag_FULLREDON);
  flag_SetFlagValue(Flags, flag_WDRATIO, 5);
  flag_SetFlagValue(Flags, flag_CNFOPTSKOLEM, flag_CNFOPTSKOLEMOFF);
  flag_SetFlagValue(Flags, flag_UNORDEREDFINEGRAINEDSTEPRESOLUTION, flag_UNORDEREDFINEGRAINEDSTEPRESOLUTIONOFF);

  do {
    LIST deflist;
    int  BoundApplied;
    ProblemClauses = list_Nil();
    LabelClauses   = list_Nil();
    Result         = top_RESOURCE;

    if (flag_GetFlagValue(Flags, flag_INTERACTIVE)) {
      QueryPair = ia_GetNextRequest(InputStream, Flags);
      /* A pair (<formula,labellist>) */
      /* Get list of clauses derivable from formulae with labels in labellist */
      if (list_Empty(QueryPair)) {
        break;
      }
      for (Scan=list_PairSecond(QueryPair);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
        LIST l;
        l = hsh_GetWithCompareFunc(TermLabelToClauselist, list_Car(Scan),
                                   (BOOL (*)(POINTER, POINTER)) cnf_LabelEqual,
                                   (unsigned long (*)(POINTER)) hsh_StringHashKey);

        l = list_PointerDeleteDuplicates(list_Copy(l));
        LabelClauses = list_Nconc(l, LabelClauses);
      }
      /* Get list of clauses derivable from sorts */
      for (Scan=Sortlabellist; !list_Empty(Scan); Scan=list_Cdr(Scan)) {
        LIST l;
        l = hsh_GetWithCompareFunc(TermLabelToClauselist, list_Car(Scan),
                                  (BOOL (*)(POINTER, POINTER)) cnf_LabelEqual,
                                  (unsigned long (*)(POINTER)) hsh_StringHashKey);

        l = list_PointerDeleteDuplicates(list_Copy(l));
        LabelClauses = list_Nconc(l, LabelClauses);
      }

      /* For labelclauses copies are introduced */
      /* So an update to the clause to term mapping is necessary */
      for (Scan=LabelClauses; !list_Empty(Scan); Scan=list_Cdr(Scan)) {
        CLAUSE C;
        LIST l;
        C = (CLAUSE) list_Car(Scan);
        l = list_Copy(hsh_Get(ClauseToTermLabellist, C));
        l = cnf_DeleteDuplicateLabelsFromList(l);
        list_Rplaca(Scan, clause_Copy(C));
        hsh_PutList(ClauseToTermLabellist, list_Car(Scan), l);
      }
      QueryClauses   = cnf_QueryFlotter(FlotterSearch, list_PairFirst(QueryPair),
                                                                        &Symblist, TRUE);
      ProblemClauses = list_Nconc(QueryClauses, LabelClauses);

      for (Scan=list_PairSecond(QueryPair); !list_Empty(Scan); Scan= list_Cdr(Scan)) {
        string_StringFree(list_Car(Scan)); /* Free the label strings */
      }
      list_Delete(list_PairSecond(QueryPair));
      list_PairFree(QueryPair);
      clock_InitCounter(clock_OVERALL);
      clock_StartCounter(clock_OVERALL);
    }
    else {
      ProblemClauses = InputClauses;
      InputClauses   = list_Nil();
    }

    prfs_SetSplitCounter(Search,flag_GetFlagValue(Flags, flag_SPLITS));
    prfs_SetLoops(Search,flag_GetFlagValue(Flags, flag_LOOPS));
    prfs_SetBacktrackedClauses(Search, 0);
    BoundApplied = -1;
    Search = proof_ProofSearch(Search, ProblemClauses, InputFlags, UserPrecedence, &BoundApplied, NativeClauseInput);

    if ((flag_GetFlagValue(Flags, flag_TIMELIMIT) == flag_TIMELIMITUNLIMITED ||
         flag_GetFlagValue(Flags, flag_TIMELIMIT) > clock_GetSeconds(clock_OVERALL)) &&
         prfs_Loops(Search) != 0 &&
        (BoundApplied == -1 || !list_Empty(prfs_EmptyClauses(Search)))) {
      if (list_Empty(prfs_EmptyClauses(Search)))
        Result = top_COMPLETION;
      else
        Result = top_PROOF;
      }
  
      if (flag_GetFlagValue(Flags, flag_TIMELIMIT) != 0) {
        /* Stop SPASS immediately */
        alarm_Off();
        printf("\nTSPASS %s ", vrs_VERSION);
        fputs("\nSPASS beiseite: ", stdout);
        switch (Result) {
          case top_RESOURCE:
            if (prfs_Loops(Search) != 0)
              fputs("Ran out of time.", stdout);
            else
              fputs("Maximal number of loops exceeded.", stdout);
            break;
          case top_PROOF:
            fputs("Unsatisfiable.", stdout);
            break;
          default:        /* Completion */
            fputs("Satisfiable.", stdout);
        }
        printf("\nProblem: %s ",
          (top_InputFile != (char*)NULL ? top_InputFile : "Read from stdin."));
        if (flag_GetFlagValue(Flags, flag_PSTATISTIC)) {
          clock_StopPassedTime(clock_OVERALL);
          printf("\nTSPASS derived %d clauses,", prfs_DerivedClauses(Search));
          printf(" backtracked %d clauses", prfs_BacktrackedClauses(Search));
          printf(" and kept %d clauses.", prfs_KeptClauses(Search));
          printf("\nNumber of input clauses: %i", prfs_InputClauses(Search));
          printf("\nNumber of eventualities: %i", list_Length(prfs_EventualityClauses(Search)));
          printf("\nTotal number of generated clauses: %i", prfs_InputClauses(Search) + prfs_DerivedClauses(Search));
          printf("\nNumber of forward-subsumed clauses: %i", prfs_ForwardSubsumedClauses(Search));
          printf("\nNumber of backward-subsumed clauses: %i", prfs_BackwardSubsumedClauses(Search));
          printf("\nTotal number of subsumed clauses: %i", prfs_ForwardSubsumedClauses(Search) + prfs_BackwardSubsumedClauses(Search));
          printf("\nNumber of tautology clauses: %i", prfs_TautologyClauses(Search));
          printf("\nNumber of clauses with different loop search markers: %i", prfs_DifferentMarkerClauses(Search));
          printf("\nNumber of usable clauses left: %i", list_Length(prfs_UsableClauses(Search)));
          printf("\nNumber of worked-off clauses left: %i", list_Length(prfs_WorkedOffClauses(Search)));
          printf("\nNumber of successful loop searches: %i", prfs_SuccessfulLoopSearches(Search));
          printf("\nTSPASS allocated %lu KBytes.", memory_DemandedBytes()/1024);
          fputs("\nTSPASS spent\t", stdout);
          clock_PrintTime(clock_OVERALL);
          fputs(" on the problem.\n\t\t", stdout);
          clock_PrintTime(clock_INPUT);
          fputs(" for the input.\n\t\t", stdout);
          clock_PrintTime(clock_CNF);
          fputs(" for the FLOTTER CNF translation", stdout);
          if(flag_GetFlagValue(Flags, flag_EML)) {
          fputs(", of which", stdout);
          fputs("\n\t\t", stdout); clock_PrintTime(clock_TRANSL);
          fprintf(stdout, " for the translation from %s to FOL", flag_Name(flag_EML));
        }
        printf(".");
        printf("\n\t\t"); clock_PrintTime(clock_INFERENCE);
        fputs(" for inferences.\n\t\t", stdout);
        clock_PrintTime(clock_BACKTRACK);
        fputs(" for the backtracking.\n\t\t", stdout);
        clock_PrintTime(clock_REDUCTION);
        puts(" for the reduction.");
      }
      if (Result != top_PROOF &&
          flag_GetFlagValue(Flags, flag_FPMODEL) != flag_FPMODELOFF) {
        FILE *Output;
        char name[100];
        const char * creator = "{*SPASS " vrs_VERSION " *}";
        BOOL PrintPotProductive;
    
        strcpy(name, (top_InputFile != (char*)NULL ? top_InputFile : "SPASS"));
        if (Result == top_COMPLETION)
          strcat(name, ".model");
        else
          strcat(name, ".clauses");
        Output = misc_OpenFile(name,"w");
        PrintPotProductive = (flag_GetFlagValue(Flags, flag_FPMODEL) ==
                                flag_FPMODELPOTENTIALLYPRODUCTIVECLAUSES);
        if (Result == top_COMPLETION)
          clause_FPrintCnfDFGProblem(Output, PrintPotProductive,
                "{*Completion_by_SPASS*}",
                creator, "satisfiable",
                dfg_ProblemDescription(),
                prfs_WorkedOffClauses(Search),
                list_Nil(), Flags, Precedence, NULL, TRUE, TRUE);
        else
          clause_FPrintCnfDFGProblem(Output, PrintPotProductive,
                "{*Clauses_generated_by_SPASS*}",
                creator, "unknown",
                dfg_ProblemDescription(),
                prfs_WorkedOffClauses(Search),
                prfs_UsableClauses(Search), Flags,
                Precedence, NULL, FALSE, TRUE);
                misc_CloseFile(Output, name);
        if (Result == top_COMPLETION)
          printf("\nCompletion printed to: %s\n", name);
        else
          printf("\nClauses printed to: %s\n", name);
      }
  
      if (flag_GetFlagValue(Flags, flag_DOCPROOF) && Result != top_RESOURCE) {
        if (Result == top_COMPLETION) {
          puts("\n\n The saturated set of worked-off clauses is :");
          clause_ListPrint(prfs_WorkedOffClauses(Search));
        }
        else {
          LIST UsedClauses, UsedTerms;
          if (!top_InputFile)
            top_InputFile = "SPASS";
          UsedClauses = dp_PrintProof(Search, prfs_EmptyClauses(Search),
                                      top_InputFile);
          /* Find terms required for proof */
          UsedTerms = list_Nil();
      
          for (Scan = UsedClauses; !list_Empty(Scan); Scan = list_Cdr(Scan))
            if (clause_IsFromInput((CLAUSE) list_Car(Scan))) {
              LIST L;
              L = hsh_Get(ClauseToTermLabellist, list_Car(Scan));
              L = list_Copy(L);
              L = cnf_DeleteDuplicateLabelsFromList(L);
              UsedTerms = list_Nconc(UsedTerms, L);
            }
          list_Delete(UsedClauses);
          UsedTerms = cnf_DeleteDuplicateLabelsFromList(UsedTerms);
          fputs("\nFormulae used in the proof :", stdout);
          for (Scan = UsedTerms; !list_Empty(Scan); Scan = list_Cdr(Scan)) 
            if (!(strncmp((char*) list_Car(Scan), "_SORT_", 6) == 0))
              printf(" %s", (char*) list_Car(Scan));
          putchar('\n');
          list_Delete(UsedTerms);
        }
      }
    }

    if (flag_GetFlagValue(Flags, flag_MODELCONSTRUCTION) != flag_MODELCONSTRUCTIONOFF
        && Result != top_PROOF && Result != top_RESOURCE) {
      tl_ConstructModel(Search, Flags, ListOfLeftHandSideSymbols);
    }

    /* Delete mapping for the clause copies of the labelclauses */
    for (Scan = LabelClauses; !list_Empty(Scan); Scan=list_Cdr(Scan))
      hsh_DelItem(ClauseToTermLabellist, list_Car(Scan));
  
    list_Delete(ProblemClauses);
  
    fflush(stdout);
    
    /* Keep definitions */
    deflist = prfs_Definitions(Search);
    prfs_SetDefinitions(Search, list_Nil());
    prfs_Clean(Search);
    prfs_SetDefinitions(Search, deflist);
    
    symbol_TransferPrecedence(InputPrecedence, Precedence);
    if (flag_GetFlagValue(Flags, flag_PPROBLEM))
      fputs("\n--------------------------TSPASS-STOP------------------------------", stdout);
  }
  while (flag_GetFlagValue(Flags, flag_INTERACTIVE) &&
        (flag_GetFlagValue(Flags, flag_TIMELIMIT) != 0));

  for (Scan = InputClauses; !list_Empty(Scan); Scan=list_Cdr(Scan))
    clause_OrientAndReInit(list_Car(Scan), Flags, Precedence);

  /* Cleanup Flotter data structures */
  if (flag_GetFlagValue(Flags, flag_INTERACTIVE)) {
    if (flag_GetFlagValue(Flags, flag_DOCPROOF))
      list_Delete(Symblist);
    else 
      symbol_DeleteSymbolList(Symblist);
    /*  symbol_ResetSkolemIndex(); */
    if (FlotterSearch != NULL) 
      prfs_Delete(FlotterSearch);
  }
  if (flag_GetFlagValue(Flags, flag_PFLAGS)) {
    putchar('\n');
    flag_Print(Flags);
  }
  if (TermLabelToClauselist != (HASH)NULL) {
    hsh_Delete(TermLabelToClauselist);
    hsh_Delete(ClauseToTermLabellist);
  }
  for (Scan = Labellist; !list_Empty(Scan); Scan = list_Cdr(Scan))
    string_StringFree(list_Car(Scan));
  list_Delete(Labellist);
  list_Delete(Sortlabellist);
  list_Delete(UserPrecedence);
  list_Delete(UserSelection);

  cnf_Free(Flags);
  eml_Free();
  tl_Free();

  list_Delete(ListOfLeftHandSideSymbols);
  prfs_Delete(Search);
  clause_DeleteClauseList(InputClauses);
  clause_DeleteClauseList(EventualityClauses); /* FIXME: this should be moved into prfs_delete */
  tl_DeleteEventualityInformation(NumberOfEventualities);

  flag_DeleteStore(InputFlags);
  symbol_DeletePrecedence(InputPrecedence);

  cc_Free();
  ana_Free();
  sort_Free();
  subs_Free();
  unify_Free();
  cont_Free();
  fol_Free();
  symbol_FreeAllSymbols();
  dfg_Free();
  opts_Free();
#ifdef CHECK
  memory_Print();
  memory_PrintLeaks();
#endif
  putchar('\n');
  return 0;
}
