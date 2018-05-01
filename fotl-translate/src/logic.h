/************************************************************
 *    Copyright (C) 2008-2009                               *
 *    Michel Ludwig (michel.ludwig@gmail.com)               *
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
 
#ifndef LOGIC_H
#define LOGIC_H

#include <list>

#include "formula.h"

class DSNFTransformationOptions
{
	public:
		DSNFTransformationOptions();

		bool regroupConjunctiveDisjunctiveNextFormulae;
		// Step clauses in DSNF can contain more than one literal on each side
		bool extendedStepClauses;
		// Reduce several eventualities into a single one (only works in the propositional case)
		bool singleEventuality;
};

class RenamingInformation
{
	public:
		RenamingInformation();

		unsigned int lastTemporalRenamingIndex;
		unsigned int lastComplexFirstOrderRenamingIndex;
		unsigned int lastAlwaysRenamingIndex;
		unsigned int lastUntilRenamingIndex;
		unsigned int lastUnlessRenamingIndex;
		unsigned int lastSometimeRenamingIndex;
		unsigned int lastComplexEventualitySubformulaRenamingIndex;
		unsigned int lastUntilUnlessRenamingIndex;
		unsigned int lastEventualityRenamingIndex;
		// the first element of the pair contains the formula renamed, and the
		// second one the new symbol for it
		TreeNodePairList renamedFormulae;
		TreeNodePairList renamedEventualityFormulae;
};

std::list<TreeNode*> toDSNF(const std::list<TreeNode*>& formulae, const DSNFTransformationOptions& options,
                                                                  RenamingInformation& renamingInformation);

TreeNodeListPair transformPropositionalProblemToSingleEventuality(const TreeNodeList& list);

#endif

