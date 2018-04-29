/************************************************************
 *    Copyright (C) 2008-2011                               *
 *    Michel Ludwig (michel.ludwig@liverpool.ac.uk)         *
 *    University of Liverpool                               *
 *                                                          *
 *    This program is free software; you can redistribute   *
 *    it and/or modify it under the terms of the GNU        *
 *    General Public License as published by the Free       *
 *    Software Foundation; either version 3 of the License, *
 *    or (at your option) any later version.                *
 *                                                          *
 *    This program is distributed in the hope that it will  *
 *    be useful, but WITHOUT ANY WARRANTY; without even     *
 *    the implied warranty of MERCHANTABILITY or FITNESS    *
 *    FOR A PARTICULAR PURPOSE.  See the GNU General Public *
 *    License for more details.                             *
 *                                                          *
 *    You should have received a copy of the GNU General    *
 *    Public License along with this program; if not, see   *
 *    <http://www.gnu.org/licenses/>.                       *
 ************************************************************/

#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/resource.h>

#include <iostream>

#include "formula.h"
#include "logic.h"
#include "helpers.h"
#include "misc.h"
#include "output.h"
#include "outputstream.h"
#include "parser.h"

#define ONE_MILLION       1000000

extern "C"
{
	extern FILE *yyin;
	void yyerror(const char *error);
}

extern struct list *formula_list;

extern int yyparse(void);

static struct timeval add_timeval(const struct timeval& t1, const struct timeval& t2)
{
	struct timeval result;
	result.tv_sec = t1.tv_sec + t2.tv_sec;
	result.tv_usec = t1.tv_usec + t2.tv_usec;
	if(result.tv_usec >= ONE_MILLION) {
		result.tv_sec += result.tv_usec / ONE_MILLION;
		result.tv_usec %= ONE_MILLION;
	}
	return result;
}

void yyerror(const char *error)
{
	std::cerr << "Error: " << error << std::endl;
	abort();
}

static void printUsage()
{
	std::cout << "First-Order Temporal Logic Translation Tool v 0.17" << std::endl;
	std::cout << "Usage: fotl-translate [--help | -h] [--debug | -d] [--extendedstepclauses] [--regroupnext] [--singleeventuality] [--measuretime] [<input file>]" << std::endl;
}

int main(int argc, char** argv)
{
	DSNFTransformationOptions transformationOptions;
	int debugOutput = false;
	bool measureTransformationTime = false;

	while(true) {
		static struct option long_options[] =
		{
			{"debug", no_argument, NULL, 'd'},
			{"extendedstepclauses", no_argument, NULL, 'e'},
			{"regroupnext", no_argument, NULL, 'n'},
			{"singleeventuality", no_argument, NULL, 's'},
			{"measuretime", no_argument, NULL, 't'},
			{"help", no_argument, NULL, '?'},
			// {"add", no_argument, 0, 'a'},
			{0, 0, 0, 0}
		};
		int option_index = 0;

		int c = getopt_long (argc, argv, "dh", long_options, &option_index);

		if (c == -1) {
			break;
		}

		switch(c) {
			case 0:
				/* If this option set a flag, do nothing else now. */
				if (long_options[option_index].flag != 0) {
                 			break;
				}
				break;

			case 'd':
				debugOutput = true;
				break;

			case 'e':
				transformationOptions.extendedStepClauses = true;
				break;

			case 'n':
				transformationOptions.regroupConjunctiveDisjunctiveNextFormulae = true;
				break;

			case 's':
				transformationOptions.singleEventuality = true;
				break;

			case 't':
				measureTransformationTime = true;
				break;

			case 'h': // fall through
			case '?':
				printUsage();
				return -1;
				break;

			default:
				abort();
		}
	}

	setOutputEnabled(debugOutput);

	if(optind < argc) {
		stdoutput() << "Using input file: " << argv[optind] << std::endl;
		yyin = fopen(argv[optind], "r");
		if(!yyin) {
			perror("Input file");
			exit(1);
		}
	}
	else {
		stdoutput() << "Using standard input." << std::endl;
		yyin = stdin;
	}

	yyparse();

	std::list<TreeNode*> formulaList;

	for(struct list *it = formula_list; !list_IsEmpty(it); it = list_Tail(it)) {
		tree* t = (tree*)list_Element(it);
		stdoutput() << "found formula ";
		tree_Print(t);
		stdoutput() << std::endl;
		if(t) {
			formulaList.push_back(transformToDeBruijnTree((tree*)list_Element(it)));
		}
		tree_Delete(t);
	}
	list_Delete(formula_list);

	stdoutput() << "Input formulae:" << std::endl;
	for(std::list<TreeNode*>::iterator i = formulaList.begin(); i != formulaList.end(); ++i) {
		stdoutput() << *i << std::endl;
	}
	RenamingInformation renamingInformation;
	std::list<TreeNode*> dsnfList = toDSNF(formulaList, transformationOptions, renamingInformation);
	stdoutput() << std::endl << "Formulae in DSNF:" << std::endl;
	printFormulaList(dsnfList);

	if(transformationOptions.singleEventuality) {
		if(isPropositional(dsnfList)) {
			stdoutput() << std::endl;
			TreeNodeListPair p = transformPropositionalProblemToSingleEventuality(dsnfList);
			stdoutput() << std::endl << "New Formulae:" << std::endl;
			printFormulaList(p.second);
			dsnfList = p.first;
			append(dsnfList, p.second);
			dsnfList = toDSNF(dsnfList, transformationOptions, renamingInformation);
			stdoutput() << std::endl << "Formulae in DSNF:" << std::endl;
			printFormulaList(dsnfList);
		}
		else {
			std::cerr << "Transformation to a single-eventuality problem requested, but the input problem is not propositional!" << std::endl;
		}
	}

	DFGOutputWriter dfgOutputWriter;
	std::string output = dfgOutputWriter.write(dsnfList);
	resultoutput() << output;

	for(TreeNodeList::iterator i = dsnfList.begin(); i != dsnfList.end(); ++i) {
		delete(*i);
	}
	// clean up renaming information
	for(TreeNodePairList::iterator it = renamingInformation.renamedFormulae.begin();
	    it != renamingInformation.renamedFormulae.end(); ++it) {
		delete((*it).first);
		delete((*it).second);
	}
	for(TreeNodePairList::iterator it = renamingInformation.renamedEventualityFormulae.begin();
	    it != renamingInformation.renamedEventualityFormulae.end(); ++it) {
		delete((*it).first);
		delete((*it).second);
	}
 
	// now measure the time that we took (if required)
	if(measureTransformationTime) {
		struct rusage rus;
	      
		if(getrusage(RUSAGE_SELF, &rus) < 0) {
			return 0;
		}
		struct timeval timeUsed = add_timeval(rus.ru_utime, rus.ru_stime);
		std::cerr << "Time needed for the transformation: " << (timeUsed.tv_sec + static_cast<double>(timeUsed.tv_usec) / ONE_MILLION) << std::endl;
	}

	return 0;
}
