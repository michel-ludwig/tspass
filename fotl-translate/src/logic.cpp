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
 
/**
 * DESIGN DECISION:
 * In DSNF, eventualities must be at most monadic, but the literals
 * in step clauses can be of arbitrary arity as long they contain
 * at most one free variable.
 **/

#include "logic.h"

#include <assert.h>
#include <string.h>

#include <typeinfo>

#include "formula.h"
#include "misc.h"
#include "parser.h"
#include "outputstream.h"

// AND OR NOT ALWAYS NEXT EVENTUALLY FORALL EXISTS UNLESS UNTIL IMPLICATION

#define MAX(a,b) ((a) >= (b) ? (a) : (b))

DSNFTransformationOptions::DSNFTransformationOptions()
: regroupConjunctiveDisjunctiveNextFormulae(false), extendedStepClauses(false), singleEventuality(false)
{
}


RenamingInformation::RenamingInformation()
:
lastTemporalRenamingIndex(0),
lastComplexFirstOrderRenamingIndex(0),
lastAlwaysRenamingIndex(0),
lastUntilRenamingIndex(0),
lastUnlessRenamingIndex(0),
lastSometimeRenamingIndex(0),
lastComplexEventualitySubformulaRenamingIndex(0),
lastUntilUnlessRenamingIndex(0),
lastEventualityRenamingIndex(0)
{
}

// forward declarations
std::pair<TreeNode*, TreeNodeList> toNNF(TreeNode* n, RenamingInformation& renamingInformation);

static bool containsTemporalOperator(TreeNode *n)
{
	if(isOperator(n)) {
		int op = static_cast<Operator*>(n)->getOperator();
		if(op == ALWAYS || op == NEXT || op == SOMETIME || op == UNLESS || op == UNTIL) {
			return true;
		}
	}
	TreeNodeList children = n->children();
	for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
		if(containsTemporalOperator(*i)) {
			return true;
		}
	}
	return false;
}

static int getFirstFreeVariable(TreeNode *n, int freeIndex)
{
	if(typeid(*n) == typeid(Variable) && static_cast<Variable*>(n)->getVariable() >= freeIndex) {
		return static_cast<Variable*>(n)->getVariable() - freeIndex;
	}
	else {
		if(isQuantifier(n)) {
			++freeIndex;
		}
		TreeNodeList children = n->children();
		for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
			int v = getFirstFreeVariable(*i, freeIndex);
			if(v >= 0) {
				return v;
			}
		}
		return -1;
	}
}

static int getFirstFreeVariable(TreeNode *n)
{
	return getFirstFreeVariable(n, 0);
}

static bool isDisjunctionOfLiterals(TreeNode *n)
{
	if(isLiteral(n)) {
		return true;
	}
	if(!isOr(n)) {
		return false;
	}
	TreeNodeList children = n->children();
	for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
		TreeNode *child = *i;
		if(isOr(child)) {
			if(!isDisjunctionOfLiterals(child)) {
				return false;
			}
		}
		else if(!isLiteral(child)) {
			return false;
		}
	}
	return true;
}

static bool isConjunctionOfPositiveLiterals(TreeNode *n)
{
	if(isPositiveLiteral(n)) {
		return true;
	}
	if(!isAnd(n)) {
		return false;
	}
	TreeNodeList children = n->children();
	for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
		TreeNode *child = *i;
		if(isAnd(child)) {
			if(!isConjunctionOfPositiveLiterals(child)) {
				return false;
			}
		}
		else if(!isPositiveLiteral(child)) {
			return false;
		}
	}
	return true;
}

static bool isEventuality(TreeNode *n)
{
	bool quantified = false;
	// check whether 'n' is an initial clause
	if(!containsTemporalOperator(n)) {
		return false;
	}
	// 'n' must start with an operator now
	Operator *op = static_cast<Operator*>(n);
	if(op->getOperator() != ALWAYS) {
		return false;
	}
	assert(op->childrenCount() == 1);
	TreeNode *n2 = op->firstChild();
	if(!isOperator(n2)) {
		return false;
	}
	// 'n2' must start with an operator now
	Operator *op2 = static_cast<Operator*>(n2);
	TreeNode *n3 = NULL;
	if(op2->getOperator() == FORALL) {
		assert(op2->childrenCount() == 2);
		n3 = op2->secondChild();
		quantified = true;
	}
	else {
		n3 = n2;
	}

	// 'n3' must start with an operator now
	Operator *op3 = static_cast<Operator*>(n3);
	if(op3->getOperator() == SOMETIME) {
		TreeNode *child = op3->firstChild();
		if(!isLiteral(child) || child->childrenCount() > 1) {
			return false;
		}
		unsigned int numFreeVariables = freeVariableCount(child);
		if(!quantified && numFreeVariables > 0) {
			return false;
		}
		if(numFreeVariables >= 2) {
			return false;
		}
		if(numFreeVariables == 1 && (getFirstFreeVariable(child) > 0)) {
			return false;
		}
		return true;
	}
	else {
		return false;
	}
}

static bool isInDSNF(TreeNode *n, const DSNFTransformationOptions& options)
{
	bool quantified = false;
	// check whether 'n' is an initial clause
	if(!containsTemporalOperator(n)) {
		return true;
	}
	// 'n' must start with an operator now
	Operator *op = static_cast<Operator*>(n);
	if(op->getOperator() != ALWAYS) {
		return false;
	}
	assert(op->childrenCount() == 1);
	TreeNode *n2 = op->firstChild();
	if(!containsTemporalOperator(n2)) { //universal formula
		return true;
	}
	// 'n2' must start with an operator now
	Operator *op2 = static_cast<Operator*>(n2);
	TreeNode *n3 = NULL;
	if(op2->getOperator() == FORALL) {
		assert(op2->childrenCount() == 2);
		n3 = op2->secondChild();
		quantified = true;
	}
	else {
		n3 = n2;
	}

	// 'n3' must start with an operator now
	Operator *op3 = static_cast<Operator*>(n3);
	if(op3->getOperator() == IMPLICATION) {
		assert(op3->childrenCount() == 2);
		TreeNode *n4 = op3->secondChild();
		if(!isNext(n4)) {
			return false;
		}
		assert(n4->childrenCount() == 1);
		TreeNode *leftNode = op3->firstChild();
		TreeNode *rightNode = n4->firstChild();
		if(options.extendedStepClauses) {
			if(!(isConjunctionOfPositiveLiterals(leftNode)
			&& isDisjunctionOfLiterals(rightNode))) {
				return false;
			}
		}
		else {
			if(!(isPositiveLiteral(leftNode)
			     && isLiteral(rightNode))) {
				return false;
			}
		}
		unsigned numLeftVariables = freeVariableCount(leftNode);
		unsigned numRightVariables = freeVariableCount(rightNode);
		if(!quantified && (numLeftVariables > 0 || numRightVariables > 0)) {
			return false;
		}
		if(numLeftVariables >= 2 || numRightVariables >= 2) {
			return false;
		}
		if((numLeftVariables == 1 && (getFirstFreeVariable(leftNode) != 0))
		    || (numRightVariables == 1 && (getFirstFreeVariable(rightNode) != 0))) {
			return false;
		}
		return true;
	}
	else if(op3->getOperator() == SOMETIME) {
		TreeNode *child = op3->firstChild();
		if(!isLiteral(child) || child->childrenCount() > 1) {
			return false;
		}
		unsigned int numFreeVariables = freeVariableCount(child);
		if(!quantified && numFreeVariables > 0) {
			return false;
		}
		if(numFreeVariables >= 2) {
			return false;
		}
		if(numFreeVariables == 1 && (getFirstFreeVariable(child) > 0)) {
			return false;
		}
		return true;
	}
	else {
		return false;
	}
}

/**
 * Checks whether the clause is a pre-step clause, i.e. of the form
 * \always \forall(x, \implies(P(x), <op>\phi(x))) or
 * \always \implies(p, <op> phi), where <op> is a temporal operator and such
 * that \phi(x) does not contain a temporal operator.
 **/
static bool isPreStepClause(TreeNode *n)
{
	// check whether 'n' is an initial clause
	if(!containsTemporalOperator(n)) {
		return false;
	}
	// 'n' must start with an operator now
	Operator *op = static_cast<Operator*>(n);
	if(op->getOperator() != ALWAYS) {
		return false;
	}
	assert(op->childrenCount() == 1);
	TreeNode *n2 = op->firstChild();
	if(!containsTemporalOperator(n2)) {
		return false;
	}
	// 'n2' must start with an operator now
	Operator *op2 = static_cast<Operator*>(n2);
	TreeNode *n3 = NULL;
	if(op2->getOperator() == FORALL) {
		assert(op2->childrenCount() == 2);
		n3 = op2->secondChild();
	}
	else {
		n3 = n2;
	}
	// 'n3' must start with an operator now
	Operator *op3 = static_cast<Operator*>(n3);
	if(op3->getOperator() != IMPLICATION) {
		return false;
	}
	assert(op3->childrenCount() == 2);
	TreeNode *leftNode = op3->firstChild();
	if(!isPositiveLiteral(leftNode)) {
		return false;
	}
	unsigned numLeftVariables = freeVariableCount(leftNode);
	TreeNode *n4 = op3->secondChild();
	if(!isOperator(n4)) {
		return false;
	}
	int temporalOperator = static_cast<Operator*>(n4)->getOperator();
	if(temporalOperator == NEXT || temporalOperator == ALWAYS || temporalOperator == SOMETIME) {
		assert(n4->childrenCount() == 1);
		TreeNode *rightNode = n4->firstChild();
		unsigned numRightVariables = freeVariableCount(rightNode);
		if(containsTemporalOperator(rightNode)) {
			return false;
		}
		if(numLeftVariables >= 2 || numRightVariables >= 2) {
			return false;
		}
		if((numLeftVariables == 1 && (getFirstFreeVariable(leftNode) != 0))
		   || (numRightVariables == 1 && (getFirstFreeVariable(rightNode) != 0))) {
			return false;
		}
	}
	else if(temporalOperator == UNTIL || temporalOperator == UNLESS) {
		assert(n4->childrenCount() == 2);
		TreeNode *rightNode1 = n4->firstChild();
		TreeNode *rightNode2 = n4->secondChild();
		unsigned numRightVariables1 = freeVariableCount(rightNode1);
		unsigned numRightVariables2 = freeVariableCount(rightNode2);
		if(containsTemporalOperator(rightNode1) || containsTemporalOperator(rightNode2)) {
			return false;
		}
		if(numLeftVariables >= 2 || numRightVariables1 >= 2 || numRightVariables2 >= 2) {
			return false;
		}
		if((numLeftVariables == 1 && (getFirstFreeVariable(leftNode) != 0))
		    || (numRightVariables1 == 1 && (getFirstFreeVariable(rightNode1) != 0))
		    || (numRightVariables2 == 1 && (getFirstFreeVariable(rightNode2) != 0))) {
			return false;
		}
	}
	else {
		return false;
	}
	return true;

}

static std::pair<TreeNodeList, TreeNodeList> extractDSNFFormulae(const TreeNodeList& list,
                                                                 const DSNFTransformationOptions& options)
{
	TreeNodeList nonDSNFFormulae, dsnfFormulae;;
	for(TreeNodeList::const_iterator i = list.begin(); i != list.end(); ++i) {
		if(!*i) {
			continue;
		}
		if(!isInDSNF(*i, options)) {
			nonDSNFFormulae.push_back(*i);
		}
		else {
			dsnfFormulae.push_back(*i);
		}
	}
	return std::pair<TreeNodeList, TreeNodeList>(nonDSNFFormulae, dsnfFormulae);
}

static std::map<int, int> increaseVariableMappings(const std::map<int, int>& mapping)
{
	std::map<int, int> toReturn;

	for(std::map<int, int>::const_iterator it = mapping.begin(); it != mapping.end(); ++it) {
		toReturn[it->first + 1] = it->second + 1;
	}

	return toReturn;
}

static int findFreeIndex(const std::map<int, int>& renamingMap, int quantifierThreshold)
{
	std::map<int, bool> takenMap;

	for(std::map<int, int>::const_iterator it = renamingMap.begin(); it != renamingMap.end(); ++it) {
		takenMap[(*it).first] = true;
	}

	for(int i = quantifierThreshold; true; ++i) {
		if(takenMap.find(i) == takenMap.end()) {
			return i;
		}
	}
	return -1;
}

static TreeNode* normaliseFreeVariables(TreeNode *n, const std::map<int, int>& renamingMap = std::map<int, int>(), int quantifierThreshold = 0)
{
	std::map<int, int> newRenamingMap = renamingMap;
	int newQuantifierThreshold = quantifierThreshold;
	Operator *op = dynamic_cast<Operator*>(n);

	if(typeid(*n) == typeid(Variable)) {
		Variable *variable = static_cast<Variable*>(n);
		int index = variable->getVariable();
		if(index >= quantifierThreshold) {
			std::map<int, int>::const_iterator it = renamingMap.find(index);
			if(it == renamingMap.end()) {
				int newIndex = findFreeIndex(renamingMap, quantifierThreshold);
				newRenamingMap[index] = newIndex;
				variable->setVariable(newIndex);
			}
			else {
				variable->setVariable((*it).second);
			}
		}
	}
	else if(op && (op->getOperator() == FORALL || op->getOperator() == EXISTS)) {
		newRenamingMap = increaseVariableMappings(renamingMap);
		++newQuantifierThreshold;
	}

	TreeNodeList children = n->children();
	for(TreeNodeList::const_iterator it = children.begin(); it != children.end(); ++it) {
		normaliseFreeVariables(*it, newRenamingMap, newQuantifierThreshold);
	}
	return n;
}

static TreeNode* hasBeenRenamed(TreeNode *n, const TreeNodePairList& list)
{
	TreeNode* toReturn = NULL;
	TreeNode *copied = copy(n);
	normaliseFreeVariables(copied);
	for(TreeNodePairList::const_iterator it = list.begin(); it != list.end(); ++it) {
		TreeNode* formula = (*it).first;
		if(*copied == formula) {
			toReturn = (*it).second;
			break;
		}
	}
	delete(copied);

	return toReturn;
}

static TreeNode* hasBeenRenamed(TreeNode *n, const RenamingInformation& renamingInformation)
{
	return hasBeenRenamed(n, renamingInformation.renamedFormulae);
}

/**
 * CAUTION: 'n' will be deleted when it has already been renamed.
 **/
static TreeNodePair renameSubformula(TreeNode *n, const std::string& symbol, unsigned int& counter,
                                                 RenamingInformation& renamingInformation)
{
	unsigned int numberOfFreeVariables = freeVariableCount(n);
	assert(numberOfFreeVariables <= 1);
	int variable = -1;
	if(numberOfFreeVariables == 1) {
		variable = getFirstFreeVariable(n);
		assert(variable >= 0);
	}
	TreeNode* alreadyRenamedSymbol = hasBeenRenamed(n, renamingInformation);
	if(alreadyRenamedSymbol) {
		TreeNode* toReturn = copy(alreadyRenamedSymbol);
		if(numberOfFreeVariables > 0) {
			substituteFreeVariable(toReturn, 0, variable);
		}
		delete(n);
		return TreeNodePair(toReturn, NULL);
	}

	TreeNode *newSymbol = new Identifier((counter == 0) ? symbol : symbol + toString(counter));
	if(numberOfFreeVariables == 1) {
		newSymbol->addChild(new Variable(0));
		substituteFreeVariable(n, variable, 0);
	}

	TreeNode *newFormula = NULL;
	if(numberOfFreeVariables == 0) {
		newFormula = Always(Implication(newSymbol, n));
	}
	else {
		newFormula = Always(Forall(Implication(newSymbol, n)));
	}

	renamingInformation.renamedFormulae.push_back(TreeNodePair(normaliseFreeVariables(copy(n)), copy(newSymbol)));

	++counter;
	TreeNode *newSymbolForOld = copy(newSymbol);
	if(numberOfFreeVariables == 1) {
		substituteFreeVariable(newSymbolForOld, 0, variable);
	}
	return std::pair<TreeNode*, TreeNode*>(newSymbolForOld, newFormula);
}


/**
 * Returns the temporal subformula of a pre step clause.
 **/
static Operator* temporalSubformulaOfPreStepClause(TreeNode *n, int op = -1)
{
	if(!isAlways(n)) {
		return NULL;
	}
	TreeNode *n2 = n->firstChild(), *n3;
	if(isImplication(n2)) {
		n3 = n2;
	}
	else if(isForall(n2) && isImplication(quantifierSubFormula(n2))) {
		n3 = quantifierSubFormula(n2);
	}
	else {
		return NULL;
	}
	TreeNode *f1 = n3->firstChild(), *n4 = n3->secondChild();
	if(!isPositiveLiteral(f1)) {
		return NULL;
	}
	if(!isOperator(n4)) {
		return NULL;
	}
	Operator *opNode = static_cast<Operator*>(n4);
	int opNodeOp = opNode->getOperator();
	if(!(op >= 0 && opNodeOp == op)
	   && !(op < 0 && isTemporalOperator(opNodeOp))) {
		return NULL;
	}
	return opNode;
}

/**
 * Returns the \next operator at which the complex formula is located.
 **/
static TreeNode* complexFirstOrderSubformulaeInPreStepClause(TreeNode *n)
{
	TreeNode *f = temporalSubformulaOfPreStepClause(n, NEXT);
	if(!f) {
		return NULL;
	}
	TreeNode *f2 = f->firstChild();
	if(isLiteral(f2) || containsTemporalOperator(f2)) {
		return NULL;
	}

	return f;
}

/**
 * Returns the \sometime operator at which the complex formula is located.
 **/
static TreeNode* complexEventualitySubformulaeInPreStepClause(TreeNode *n)
{
	TreeNode *f = temporalSubformulaOfPreStepClause(n, SOMETIME);
	if(!f) {
		return NULL;
	}
	TreeNode *f2 = f->firstChild();
	if(isPositiveLiteral(f2) || containsTemporalOperator(f2)) {
		return NULL;
	}

	return f;
}

static TreeNodeList transformAlwaysPreStepClause(TreeNode *n, TreeNode *tempOp, RenamingInformation &renamingInformation)
{
	TreeNodeList toReturn;
	toReturn.push_back(n);
	TreeNode *newSymbol = new Identifier("_R" + ((renamingInformation.lastAlwaysRenamingIndex == 0) ? "" : toString(renamingInformation.lastAlwaysRenamingIndex)));
	++renamingInformation.lastAlwaysRenamingIndex;
	unsigned int numberOfFreeVariables = freeVariableCount(tempOp);
	assert(numberOfFreeVariables <= 1);
	if(numberOfFreeVariables == 1) {
		newSymbol->addChild(new Variable(0));
	}
	TreeNode *phi = tempOp->firstChild();

	replaceInnerNode(tempOp, newSymbol);
	if(numberOfFreeVariables == 1) {
		toReturn.push_back(Always(Forall(Implication(copy(newSymbol), Next(copy(newSymbol))))));
		toReturn.push_back(Always(Forall(Implication(copy(newSymbol), phi))));
	}
	else {
		toReturn.push_back(Always(Implication(copy(newSymbol), Next(copy(newSymbol)))));
		toReturn.push_back(Always(Implication(copy(newSymbol), phi)));
	}
	delete tempOp;
	return toReturn;
}

static TreeNodeList transformUntilPreStepClause(TreeNode *n, TreeNode *tempOp, RenamingInformation &renamingInformation)
{
	TreeNodeList toReturn;
	TreeNode *impNode = tempOp->getParent();
	assert(impNode);
	TreeNode* pNode = impNode->firstChild();
	assert(pNode);
	TreeNode *newSymbol = new Identifier("_S" + ((renamingInformation.lastUntilRenamingIndex == 0) ? "" : toString(renamingInformation.lastUntilRenamingIndex)));
	++renamingInformation.lastUntilRenamingIndex;
	unsigned int numberOfFreeVariables = MAX(freeVariableCount(pNode), freeVariableCount(tempOp));
	assert(numberOfFreeVariables <= 1);
	if(numberOfFreeVariables == 1) {
		newSymbol->addChild(new Variable(0));
	}

	// copy them first before they are deleted
	pNode = copy(pNode);
	assert(tempOp->childrenCount() == 2);
	TreeNode *phiNode = copy(tempOp->firstChild());
	TreeNode *psiNode = copy(tempOp->secondChild());
	delete(n);

	if(numberOfFreeVariables == 1) {
		toReturn.push_back(Always(Forall(Implication(pNode, Or(phiNode, psiNode)))));
		toReturn.push_back(Always(Forall(Implication(copy(pNode), Sometime(copy(psiNode))))));
		toReturn.push_back(Always(Forall(Implication(copy(pNode), Or(newSymbol, copy(psiNode))))));
		toReturn.push_back(Always(Forall(Implication(copy(newSymbol), Next(Or(copy(phiNode), copy(psiNode)))))));
		toReturn.push_back(Always(Forall(Implication(copy(newSymbol), Next(Or(copy(newSymbol), copy(psiNode)))))));
	}
	else {
		toReturn.push_back(Always(Implication(pNode, Or(phiNode, psiNode))));
		toReturn.push_back(Always(Implication(copy(pNode), Sometime(copy(psiNode)))));
		toReturn.push_back(Always(Implication(copy(pNode), Or(newSymbol, copy(psiNode)))));
		toReturn.push_back(Always(Implication(copy(newSymbol), Next(Or(copy(phiNode), copy(psiNode))))));
		toReturn.push_back(Always(Implication(copy(newSymbol), Next(Or(copy(newSymbol), copy(psiNode))))));
	}
	return toReturn;
}

static TreeNodeList transformUnlessPreStepClause(TreeNode *n, TreeNode *tempOp, RenamingInformation &renamingInformation)
{
	TreeNodeList toReturn;
	TreeNode *impNode = tempOp->getParent();
	assert(impNode);
	TreeNode* pNode = impNode->firstChild();
	assert(pNode);
	TreeNode *newSymbol = new Identifier("_W" + ((renamingInformation.lastUnlessRenamingIndex == 0) ? "" : toString(renamingInformation.lastUnlessRenamingIndex)));
	++renamingInformation.lastUnlessRenamingIndex;
	unsigned int numberOfFreeVariables = MAX(freeVariableCount(pNode), freeVariableCount(tempOp));
	assert(numberOfFreeVariables <= 1);
	if(numberOfFreeVariables == 1) {
		newSymbol->addChild(new Variable(0));
	}

	// copy them first before they are deleted
	pNode = copy(pNode);
	assert(tempOp->childrenCount() == 2);
	TreeNode *phiNode = copy(tempOp->firstChild());
	TreeNode *psiNode = copy(tempOp->secondChild());
	delete(n);

	if(numberOfFreeVariables == 1) {
		toReturn.push_back(Always(Forall(Implication(pNode, Or(phiNode, psiNode)))));
		toReturn.push_back(Always(Forall(Implication(copy(pNode), Or(newSymbol, copy(psiNode))))));
		toReturn.push_back(Always(Forall(Implication(copy(newSymbol), Next(Or(copy(phiNode), copy(psiNode)))))));
		toReturn.push_back(Always(Forall(Implication(copy(newSymbol), Next(Or(copy(newSymbol), copy(psiNode)))))));
	}
	else {
		toReturn.push_back(Always(Implication(pNode, Or(phiNode, psiNode))));
		toReturn.push_back(Always(Implication(copy(pNode), Or(newSymbol, copy(psiNode)))));
		toReturn.push_back(Always(Implication(copy(newSymbol), Next(Or(copy(phiNode), copy(psiNode))))));
		toReturn.push_back(Always(Implication(copy(newSymbol), Next(Or(copy(newSymbol), copy(psiNode))))));
	}
	return toReturn;
}

static TreeNodeList transformSometimePreStepClause(TreeNode *n, Operator *tempOp, RenamingInformation &renamingInformation)
{
	TreeNodeList toReturn;
	Identifier *eventualityNode = dynamic_cast<Identifier*>(tempOp->firstChild());
	assert(tempOp->getParent());
	TreeNode* pNode = tempOp->getParent()->firstChild();
	assert(pNode);
	assert(eventualityNode);
	unsigned int numberOfFreeVariables = MAX(freeVariableCount(pNode), freeVariableCount(tempOp));
	assert(numberOfFreeVariables <= 1);
	TreeNode *newSymbol = hasBeenRenamed(eventualityNode, renamingInformation.renamedEventualityFormulae);
	bool newSymbolIntroduced = false;
	if(!newSymbol) {
		std::string suffix = (renamingInformation.lastEventualityRenamingIndex == 0 ? "" : "_" + toString(renamingInformation.lastEventualityRenamingIndex));
		++renamingInformation.lastEventualityRenamingIndex;
		newSymbol = new Identifier("_waitfor" + eventualityNode->getIdentifier() + suffix);
		renamingInformation.renamedEventualityFormulae.push_back(TreeNodePair(normaliseFreeVariables(copy(eventualityNode)), copy(newSymbol)));
		newSymbolIntroduced = true;
	}
	else {
		newSymbol = copy(newSymbol);
	}
	
	if(numberOfFreeVariables == 1) {
		newSymbol->addChild(new Variable(0));
	}

	// copy them first before they are deleted
	pNode = copy(pNode);
	eventualityNode = static_cast<Identifier*>(copy(eventualityNode));
	delete(n);

	if(numberOfFreeVariables == 1) {
		toReturn.push_back(Always(Forall(Implication(And(pNode, Not(eventualityNode)), newSymbol))));
		if(newSymbolIntroduced) {
			toReturn.push_back(Always(Forall(Implication(copy(newSymbol), Next(Or(copy(newSymbol), copy(eventualityNode)))))));
			toReturn.push_back(Always(Forall(Sometime(Not(copy(newSymbol))))));
		}
	}
	else {
		toReturn.push_back(Always(Implication(And(pNode, Not(eventualityNode)), newSymbol)));
		if(newSymbolIntroduced) {
			toReturn.push_back(Always(Implication(copy(newSymbol), Next(Or(copy(newSymbol), copy(eventualityNode))))));
			toReturn.push_back(Always(Sometime(Not(copy(newSymbol)))));
		}
	}
	return toReturn;
}


static TreeNodeList eliminateTemporalSubformulaeInPreStepClauses(TreeNode* n, RenamingInformation &renamingInformation, bool handleEventualities = false)
{
	TreeNodeList toReturn;
	Operator *temporalOperator = temporalSubformulaOfPreStepClause(n);
	if(temporalOperator) {
		int op = temporalOperator->getOperator();
		if(handleEventualities && op == SOMETIME) {
			return transformSometimePreStepClause(n, temporalOperator, renamingInformation);
		}
		else if(!handleEventualities) {
			switch(op) {
				case ALWAYS:
					return transformAlwaysPreStepClause(n, temporalOperator, renamingInformation);
				break;
				case UNTIL:
					return transformUntilPreStepClause(n, temporalOperator, renamingInformation);
				break;
				case UNLESS:
					return transformUnlessPreStepClause(n, temporalOperator, renamingInformation);
				break;
				default:
					// do nothing
				break;
			}
		}
	}
	toReturn.push_back(n);
	return toReturn;
}

static TreeNodeList eliminateEventualitySubformulaeInPreStepClauses(const TreeNodeList& list, RenamingInformation &renamingInformation)
{
	TreeNodeList newFormulaList, toBeTransformed;
	for(std::list<TreeNode*>::const_iterator i = list.begin(); i != list.end(); ++i) {
		TreeNodeList l = eliminateTemporalSubformulaeInPreStepClauses(*i, renamingInformation, true);
		append(newFormulaList, l);
	}
	return newFormulaList;
}

static TreeNodeList eliminateTemporalSubformulaeInPreStepClauses(const TreeNodeList& list, RenamingInformation &renamingInformation)
{
	TreeNodeList newFormulaList, toBeTransformed;
	for(std::list<TreeNode*>::const_iterator i = list.begin(); i != list.end(); ++i) {
		TreeNodeList l = eliminateTemporalSubformulaeInPreStepClauses(*i, renamingInformation);
		append(newFormulaList, l);
	}
	return newFormulaList;
}

static TreeNodePair renameComplexEventualitySubformulaeInPreStepClauses(TreeNode *n, RenamingInformation &renamingInformation)
{
	TreeNode *impNode = complexEventualitySubformulaeInPreStepClause(n);
	if(!impNode) {
		return TreeNodePair(n, NULL);
	}
	TreeNodePair p = renameSubformula(impNode->firstChild(), "_L", renamingInformation.lastComplexEventualitySubformulaRenamingIndex,
	                                                               renamingInformation);
	impNode->clearChildren();
	impNode->addChild(p.first);
	return TreeNodePair(n, p.second);
}

static std::pair<TreeNodeList, TreeNodeList> renameComplexEventualitySubformulaeInPreStepClauses(const TreeNodeList& list, RenamingInformation &renamingInformation)
{
	TreeNodeList oldFormulaList, newFormulaList;
	for(std::list<TreeNode*>::const_iterator i = list.begin(); i != list.end(); ++i) {
		TreeNodePair p = renameComplexEventualitySubformulaeInPreStepClauses(*i, renamingInformation);
		oldFormulaList.push_back(p.first);
		if(p.second) {
			newFormulaList.push_back(p.second);
		}
	}
	return std::pair<TreeNodeList, TreeNodeList>(oldFormulaList, newFormulaList);
}

static TreeNodePair renameComplexFirstOrderSubformulaeInStepPreStepClauses(TreeNode *n, RenamingInformation &renamingInformation)
{
	TreeNode *impNode = complexFirstOrderSubformulaeInPreStepClause(n);
	if(!impNode) {
		return TreeNodePair(n, NULL);
	}
	TreeNodePair p = renameSubformula(impNode->firstChild(), "_U", renamingInformation.lastComplexFirstOrderRenamingIndex,
	                                                               renamingInformation);
	impNode->clearChildren();
	impNode->addChild(p.first);
	return TreeNodePair(n, p.second);
}

static std::pair<TreeNodeList, TreeNodeList> renameComplexFirstOrderSubformulaeInStepPreStepClauses(const TreeNodeList& list, RenamingInformation &renamingInformation)
{
	TreeNodeList oldFormulaList, newFormulaList;
	for(std::list<TreeNode*>::const_iterator i = list.begin(); i != list.end(); ++i) {
		TreeNodePair p = renameComplexFirstOrderSubformulaeInStepPreStepClauses(*i, renamingInformation);
		oldFormulaList.push_back(p.first);
		if(p.second) {
			newFormulaList.push_back(p.second);
		}
	}
	return std::pair<TreeNodeList, TreeNodeList>(oldFormulaList, newFormulaList);
}

static std::pair<TreeNode*, TreeNodeList> renameInnermostTemporalSubformulae(TreeNode *n,
                                                                             RenamingInformation &renamingInformation,
                                                                             const DSNFTransformationOptions& options)
{
	TreeNode *toReturn = n;
	TreeNodeList newFormulaList;
	TreeNodeList newChildrenList;

	if(isTopLevelFormula(n) && isPreStepClause(n)) {
		return FormulaListPair(toReturn, newFormulaList);
	}
	TreeNodeList children = n->children();
	for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
		std::pair<TreeNode*, TreeNodeList> p = renameInnermostTemporalSubformulae(*i, renamingInformation, options);
		append(newFormulaList, p.second);
		newChildrenList.push_back(p.first);
	}
	n->setChildren(newChildrenList);

	if((isTopLevelFormula(n) && isPreStepClause(n))
	|| (isTopLevelFormula(n) && isInDSNF(n, options))) {
		return FormulaListPair(toReturn, newFormulaList);
	}

	if(isOperator(n)) {
		Operator *op = static_cast<Operator*>(n);
		int opType = op->getOperator();
		if(opType == ALWAYS || opType == NEXT || opType == SOMETIME || opType == UNTIL || opType == UNLESS) {
			assert(op->childrenCount() >= 1);
			std::pair<TreeNode*, TreeNode*> p = renameSubformula(n, "_P", renamingInformation.lastTemporalRenamingIndex,
			                                                              renamingInformation);
			toReturn = p.first;
			if(p.second) {
				newFormulaList.push_back(p.second);
			}
		}
	}

	return FormulaListPair(toReturn, newFormulaList);
}

static std::pair<TreeNodeList, TreeNodeList> renameInnermostTemporalSubformulae(const TreeNodeList& list,
                                                                                RenamingInformation &renamingInformation,
                                                                                const DSNFTransformationOptions& options)
{
	TreeNodeList oldFormulaList, newFormulaList;
	for(std::list<TreeNode*>::const_iterator i = list.begin(); i != list.end(); ++i) {
		std::pair<TreeNode*, TreeNodeList> p = renameInnermostTemporalSubformulae(*i, renamingInformation, options);
		oldFormulaList.push_back(p.first);
		append(newFormulaList, p.second);
	}
	return TreeNodeListPair(oldFormulaList, newFormulaList);
}

/**
 * Returns 'true' if and ony if
 *      n == (\not)* A
 * where A is an atom
 **/
static bool isAtomWithNegations(TreeNode *n)
{
	while(isNot(n)) {
		n = n->firstChild();
	}
	return isIdentifier(n);
}

static void ensureStepAndPreStepClausesUseImplications(TreeNode* n)
{
	Operator *op = dynamic_cast<Operator*>(n);
	if(!op || op->getOperator() != ALWAYS) {
		return;
	}
	TreeNode *n2 = op->firstChild();
	Operator *op2 = dynamic_cast<Operator*>(n2);
	TreeNode *n3 = NULL;
	if(!op2) {
		return;
	}
	if(op2->getOperator() == FORALL) {
		n3 = op2->secondChild();
	}
	else {
		n3 = n2;
	}

	Operator *op3 = dynamic_cast<Operator*>(n3);
	if(!op3 || op3->getOperator() != OR) {
		return;
	}
	TreeNode *leftNode = op3->firstChild();
	TreeNode *rightNode = op3->secondChild();
	Operator *rightOperator = dynamic_cast<Operator*>(rightNode);
	if(!rightOperator) {
		return;
	}

	if(!(isNegativeLiteral(leftNode) && isTemporalOperator(rightOperator->getOperator()))) {
		return;
	}
	unsigned numLeftVariables = freeVariableCount(leftNode);
	unsigned numRightVariables = freeVariableCount(rightOperator);
	if(numLeftVariables != numRightVariables || numLeftVariables >= 2) {
		return;
	}
	if(numLeftVariables > 0 && (getFirstFreeVariable(leftNode) != 0 || getFirstFreeVariable(rightOperator) != 0)) {
		return;
	}
	op3->setOperator(IMPLICATION);
	TreeNode *positiveLiteral = leftNode->firstChild();
	leftNode->removeChild(positiveLiteral);
	op3->replaceChild(leftNode, positiveLiteral);
	delete(leftNode);
}

static void ensureStepAndPreStepClausesUseImplications(const std::list<TreeNode*>& formulae)
{
	for(std::list<TreeNode*>::const_iterator i = formulae.begin(); i != formulae.end(); ++i) {
		ensureStepAndPreStepClausesUseImplications(*i);
	}
}

static void ensureDegeneratedPreStepClausesUseImplications(TreeNode *n)
{
	if(!isTopLevelFormula(n) || !isAlways(n)) {
		return;
	}
	TreeNode *parentFormula = n;
	TreeNode *potentialTemporalFormula = n->firstChild();
	if(isForall(potentialTemporalFormula)) {
		parentFormula = potentialTemporalFormula;
		potentialTemporalFormula = potentialTemporalFormula->secondChild();
	}
	Operator *potentialTemporalOperator = dynamic_cast<Operator*>(potentialTemporalFormula);
	if(!potentialTemporalOperator) {
		return;
	}
	if(!isTemporalOperator(potentialTemporalOperator->getOperator())) {
		return;
	}
	parentFormula->removeChild(potentialTemporalOperator);
	parentFormula->addChild(Implication(new Identifier(true), potentialTemporalOperator));
}

static void ensureDegeneratedPreStepClausesUseImplications(const std::list<TreeNode*>& formulae)
{
	for(std::list<TreeNode*>::const_iterator i = formulae.begin(); i != formulae.end(); ++i) {
		ensureDegeneratedPreStepClausesUseImplications(*i);
	}
}

static void removeTwoConsecutiveAlwaysOperators(TreeNode *n)
{
	TreeNodeList children = n->children();
	for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
		removeTwoConsecutiveAlwaysOperators(*i);
	}
	if(isAlways(n)) {
		TreeNode *child = n->firstChild();
		if(isAlways(child)) {
			TreeNode *grandChild = child->firstChild();
			child->removeChild(grandChild);
			n->removeChild(child);
			delete(child);
			n->addChild(grandChild);
		}
	}
}

static void removeTwoConsecutiveAlwaysOperators(const std::list<TreeNode*>& formulae)
{
	for(std::list<TreeNode*>::const_iterator i = formulae.begin(); i != formulae.end(); ++i) {
		removeTwoConsecutiveAlwaysOperators(*i);
	}
}

static void regroupConjunctiveDisjunctiveNextFormulae(TreeNode* n)
{
	if(isIdentifier(n) || isVariable(n)) {
		return;
	}
	if(isOr(n) || isAnd(n)) {
		Operator *op = static_cast<Operator*>(n);
		TreeNode *child1 = op->firstChild();
		TreeNode *child2 = op->secondChild();
		regroupConjunctiveDisjunctiveNextFormulae(child1);
		regroupConjunctiveDisjunctiveNextFormulae(child2);
		if(isNext(child1) && isNext(child2)) {
			op->removeChild(child1);
			op->removeChild(child2);
			TreeNode *phi = child1->firstChild();
			child1->removeChild(phi);
			delete(child1);
			TreeNode *psi = child2->firstChild();
			child2->removeChild(psi);
			delete(child2);
			Operator *newOperator = new Operator(op->getOperator());
			op->setOperator(NEXT);
			op->addChild(newOperator);
			newOperator->addChild(phi);
			newOperator->addChild(psi);
		}
	}
	else {
		TreeNodeList children = n->children();
		for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
			regroupConjunctiveDisjunctiveNextFormulae(*i);
		}
	}
}

static void regroupConjunctiveDisjunctiveNextFormulae(const std::list<TreeNode*>& formulae)
{
	for(std::list<TreeNode*>::const_iterator i = formulae.begin(); i != formulae.end(); ++i) {
		regroupConjunctiveDisjunctiveNextFormulae(*i);
	}
}

static TreeNodeList splitTopLevelConjunctions(TreeNode* n)
{
	TreeNodeList toReturn;
	if(!isAnd(n)) {
		toReturn.push_back(n);
		return toReturn;
	}
	assert(n->childrenCount() == 2);
	TreeNode *firstChild = n->firstChild();
	TreeNode *secondChild = n->secondChild();
	n->removeChild(firstChild);
	n->removeChild(secondChild);
	delete(n);
	TreeNodeList l = splitTopLevelConjunctions(firstChild);
	append(toReturn, l);
	l = splitTopLevelConjunctions(secondChild);
	append(toReturn, l);
	return toReturn;
}

static TreeNodeList splitTopLevelConjunctions(const std::list<TreeNode*>& formulae)
{
	TreeNodeList toReturn;
	for(std::list<TreeNode*>::const_iterator i = formulae.begin(); i != formulae.end(); ++i) {
		TreeNodeList l = splitTopLevelConjunctions(*i);
		append(toReturn, l);
	}
	return toReturn;
}

static TreeNodeListPair childrenToNNF(TreeNode *n, RenamingInformation &renamingInformation, bool negateFormula = false)
{
	TreeNodeList newChildren, newFormulae;

	TreeNodeList children = n->children();
	for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
		TreeNode* newTerm = (negateFormula ? Not(*i) : *i);
		std::pair<TreeNode*, TreeNodeList> p = toNNF(newTerm, renamingInformation);
		newChildren.push_back(p.first);
		append(newFormulae, p.second);
	}
	return TreeNodeListPair(newChildren, newFormulae);
}

std::pair<TreeNode*, TreeNodeList> toNNF(TreeNode* n, RenamingInformation &renamingInformation)
{
	TreeNodeList newFormulaList;
	if(isOperator(n)) {
		Operator *op = static_cast<Operator*>(n);
		if(op->getOperator() == NOT) {
			assert(op->childrenCount() == 1);
			TreeNode *n2 = op->firstChild();
			if(isOperator(n2)) {
				Operator *op2 = static_cast<Operator*>(n2);
				int op2Type = op2->getOperator();
				
				if(op2Type == AND) {
					op2->setOperator(OR);
					TreeNodeListPair p = childrenToNNF(n2, renamingInformation, true);
					op2->setChildren(p.first);
					append(newFormulaList, p.second);
				}
				else if(op2Type == OR) {
					op2->setOperator(AND);
					TreeNodeListPair p = childrenToNNF(n2, renamingInformation, true);
					op2->setChildren(p.first);
					append(newFormulaList, p.second);
				}
				else if(op2Type == NOT) {
					assert(op2->childrenCount() == 1);
					TreeNode *child = op2->firstChild();
					n2->removeChild(child);
					delete n2;
					delete n; // n2 will be deleted as well through this
					std::pair<TreeNode*, TreeNodeList> p = toNNF(child, renamingInformation);
					append(newFormulaList, p.second);
					return std::pair<TreeNode*, TreeNodeList>(p.first, newFormulaList);
				}
				else if(op2Type == ALWAYS) {
					op2->setOperator(SOMETIME);
					TreeNodeListPair p = childrenToNNF(n2, renamingInformation, true);
					op2->setChildren(p.first);
					append(newFormulaList, p.second);
				}
				else if(op2Type == NEXT) {
					TreeNodeListPair p = childrenToNNF(n2, renamingInformation, true);
					op2->setChildren(p.first);
					append(newFormulaList, p.second);
				}
				else if(op2Type == SOMETIME) {
					op2->setOperator(ALWAYS);
					TreeNodeListPair p = childrenToNNF(n2, renamingInformation, true);
					op2->setChildren(p.first);
					append(newFormulaList, p.second);
				}
				else if(op2Type == FORALL) {
					op2->setOperator(EXISTS);
					TreeNodeList newChildren;
					TreeNode *firstChild = op2->firstChild();
					TreeNode *secondChild = op2->secondChild();
					newChildren.push_back(firstChild);
					std::pair<TreeNode*, TreeNodeList> p = toNNF(Not(secondChild), renamingInformation);
					newChildren.push_back(p.first);
					append(newFormulaList, p.second);
					op2->setChildren(newChildren);
				}
				else if(op2Type == EXISTS) {
					op2->setOperator(FORALL);
					std::list<TreeNode*> newChildren;
					TreeNode *firstChild = op2->firstChild();
					TreeNode *secondChild = op2->secondChild();
					newChildren.push_back(firstChild);
					std::pair<TreeNode*, TreeNodeList> p = toNNF(Not(secondChild), renamingInformation);
					newChildren.push_back(p.first);
					append(newFormulaList, p.second);
					op2->setChildren(newChildren);
				}
				else if(op2Type == UNLESS || op2Type == UNTIL) {
					assert(op2->childrenCount() == 2);
					op2->setOperator((op2Type == UNLESS) ? UNTIL : UNLESS);
					TreeNode *firstChild = op2->firstChild();
					TreeNode *secondChild = op2->secondChild();
					TreeNode *negFirstChild = Not(firstChild);
					std::pair<TreeNode*, TreeNodeList> p2;

					std::pair<TreeNode*, TreeNodeList> p1 = toNNF(negFirstChild, renamingInformation);
					append(newFormulaList, p1.second);

					if(!isAtomWithNegations(secondChild)) {
						TreeNode *formulaToBeRenamed = Not(secondChild);

						TreeNodePair p = renameSubformula(formulaToBeRenamed, "_N", renamingInformation.lastUntilUnlessRenamingIndex,
						                                                            renamingInformation);
						TreeNodeList list;
						if(p.second) {
							std::pair<TreeNode*, TreeNodeList> p3 = toNNF(p.second, renamingInformation);
							list.push_back(p3.first);
							append(list, p3.second);
						}
						p2 = std::pair<TreeNode*, TreeNodeList>(p.first, list);
					}
					else {
						p2 = toNNF(Not(secondChild), renamingInformation);
					}
					append(newFormulaList, p2.second);

					TreeNodeList newChildren;
					newChildren.push_back(p2.first);
					newChildren.push_back(And(p1.first, copy(p2.first)));
					op2->setChildren(newChildren);
				}
				else if(op2Type == IMPLICATION) {
					TreeNode *firstChild = op2->firstChild();
					TreeNode *secondChild = op2->secondChild();
					op2->removeChild(firstChild);
					op2->removeChild(secondChild);
					op2->setOperator(AND);
					std::list<TreeNode*> newChildren;
					std::pair<TreeNode*, TreeNodeList> p = toNNF(firstChild, renamingInformation);
					newChildren.push_back(p.first);
					append(newFormulaList, p.second);
					p = toNNF(Not(secondChild), renamingInformation);
					newChildren.push_back(p.first);
					append(newFormulaList, p.second);
					op2->setChildren(newChildren);
				}
				else if(op2Type == EQUIVALENCE) {
					// should not occur!
					assert(false);
				}
				n->removeChild(n2);
				delete n;
				return std::pair<TreeNode*, TreeNodeList>(n2, newFormulaList);
			}
		}
		else {
			TreeNodeListPair p = childrenToNNF(n, renamingInformation);
			n->setChildren(p.first);
			append(newFormulaList, p.second);
		}
	}
	return std::pair<TreeNode*, TreeNodeList>(n, newFormulaList);
}

static TreeNodeListPair toNNF(const std::list<TreeNode*>& formulae, RenamingInformation &renamingInformation)
{
	TreeNodeList oldFormulaList, newFormulaList;
	std::list<TreeNode*> toReturn;
	for(std::list<TreeNode*>::const_iterator i = formulae.begin(); i != formulae.end(); ++i) {
		std::pair<TreeNode*, TreeNodeList> p = toNNF(*i, renamingInformation);
		oldFormulaList.push_back(p.first);
		append(newFormulaList, p.second);
	}
	return TreeNodeListPair(oldFormulaList, newFormulaList);
}

static TreeNode* eliminateEquivalencesAndImplications(TreeNode* n)
{
	if(isOperator(n)) {
		if(static_cast<Operator*>(n)->getOperator() == EQUIVALENCE) {
			TreeNode *firstChild = n->firstChild();
			TreeNode *secondChild = n->secondChild();
			n->removeChild(firstChild);
			n->removeChild(secondChild);
			delete n;

			TreeNode *r1 = eliminateEquivalencesAndImplications(firstChild);
			TreeNode *r2 = eliminateEquivalencesAndImplications(secondChild);

			return And(Or(Not(r1), r2), Or(Not(copy(r2)), copy(r1)));
		}
		else if(static_cast<Operator*>(n)->getOperator() == IMPLICATION) {
			TreeNode *firstChild = n->firstChild();
			TreeNode *secondChild = n->secondChild();
			n->removeChild(firstChild);
			n->removeChild(secondChild);
			delete n;

			TreeNode *r1 = eliminateEquivalencesAndImplications(firstChild);
			TreeNode *r2 = eliminateEquivalencesAndImplications(secondChild);

			return Or(Not(r1), r2);
		}
		else {
			TreeNodeList oldChildren = n->children();
			TreeNodeList newChildren;
			for(std::list<TreeNode*>::const_iterator i = oldChildren.begin(); i != oldChildren.end(); ++i) {
				newChildren.push_back(eliminateEquivalencesAndImplications(*i));
			}
			n->setChildren(newChildren);
			return n;
		}
	}
	else {
		return n;
	}
}

static std::list<TreeNode*> eliminateEquivalencesAndImplications(const std::list<TreeNode*>& formulae)
{
	std::list<TreeNode*> toReturn;
	for(std::list<TreeNode*>::const_iterator i = formulae.begin(); i != formulae.end(); ++i) {
		toReturn.push_back(eliminateEquivalencesAndImplications(*i));
	}
	return toReturn;
}

static void extractDSNFFormulae(TreeNodeList& usableList, TreeNodeList& workedOffList,
                                                   const DSNFTransformationOptions& options)
{
	TreeNodeListPair p = extractDSNFFormulae(usableList, options);
	append(workedOffList, p.second);
	usableList = p.first;

	stdoutput() << "Formulae in DSNF now: " << std::endl;
	printFormulaList(workedOffList);
	stdoutput() << "Formulae remaining to be transformed: " << std::endl;
	printFormulaList(usableList);
}

TreeNodeList toDSNF(const std::list<TreeNode*>& formulae, const DSNFTransformationOptions& options,
                                                          RenamingInformation& renamingInformation)
{
	TreeNodeList newFormulaList;
	TreeNodeList toReturn, toBeTransformed = formulae;

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Removing equivalences, implications and computing the negation normal form: " << std::endl;
	toBeTransformed = eliminateEquivalencesAndImplications(toBeTransformed);
	TreeNodeListPair p = toNNF(toBeTransformed, renamingInformation);
	toBeTransformed = p.first;
	append(toBeTransformed, p.second);

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Splitting top-level conjunctions: " << std::endl;
	toBeTransformed = splitTopLevelConjunctions(toBeTransformed);

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Remove consecutive always operators: " << std::endl;
	removeTwoConsecutiveAlwaysOperators(toBeTransformed);

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	if(options.regroupConjunctiveDisjunctiveNextFormulae) {
		stdoutput() << std::endl << "Regrouping conjunctive or disjunctive next formulae: " << std::endl;
		regroupConjunctiveDisjunctiveNextFormulae(toBeTransformed);
		
		extractDSNFFormulae(toBeTransformed, toReturn, options);
	}

	stdoutput() << std::endl << "Ensure degenerated pre-step clauses use implications: " << std::endl;
	ensureDegeneratedPreStepClausesUseImplications(toBeTransformed);

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Ensuring step and pre-step clauses use implications: " << std::endl;
	ensureStepAndPreStepClausesUseImplications(toBeTransformed);

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Renaming innermost temporal subformulae: " << std::endl;
	p = renameInnermostTemporalSubformulae(toBeTransformed, renamingInformation, options);
	stdoutput() << "New formulae obtained: " << std::endl;
	printFormulaList(p.second);
	toBeTransformed = p.first;
	append(toBeTransformed, p.second);

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Renaming complex first-order subformulae in step pre-step clauses: " << std::endl;
	p = renameComplexFirstOrderSubformulaeInStepPreStepClauses(toBeTransformed, renamingInformation);
	stdoutput() << "New formulae obtained: " << std::endl;
	printFormulaList(p.second);
	toBeTransformed = p.first;
	append(toBeTransformed, p.second);

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Renaming remaining temporal subformulae in pre-step clauses: " << std::endl;
	newFormulaList = eliminateTemporalSubformulaeInPreStepClauses(toBeTransformed, renamingInformation);
	stdoutput() << "New formulae obtained: " << std::endl;
	printFormulaList(newFormulaList);
	toBeTransformed = newFormulaList;

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Renaming complex eventuality subformulae in pre-step clauses: " << std::endl;
	p = renameComplexEventualitySubformulaeInPreStepClauses(toBeTransformed, renamingInformation);
	stdoutput() << "New formulae obtained: " << std::endl;
	printFormulaList(p.second);
	toBeTransformed = p.first;
	append(toBeTransformed, p.second);

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Renaming eventuality temporal subformulae in pre-step clauses: " << std::endl;
	newFormulaList = eliminateEventualitySubformulaeInPreStepClauses(toBeTransformed, renamingInformation);
	stdoutput() << "New formulae obtained: " << std::endl;
	printFormulaList(newFormulaList);
	toBeTransformed = newFormulaList;

	extractDSNFFormulae(toBeTransformed, toReturn, options);

	stdoutput() << std::endl << "Renaming complex first-order subformulae in step pre-step clauses: " << std::endl;
	p = renameComplexFirstOrderSubformulaeInStepPreStepClauses(toBeTransformed, renamingInformation);
	stdoutput() << "New formulae obtained: " << std::endl;
	printFormulaList(p.second);
	toBeTransformed = p.first;
	append(toBeTransformed, p.second);

	p = extractDSNFFormulae(toBeTransformed, options);
	append(toReturn, p.second);
	toBeTransformed = p.first;
	assert(toBeTransformed.size() == 0);

	stdoutput() << std::endl << "Transformation finished!" << std::endl;
	return toReturn;
}

static TreeNodeListPair extractEventualities(const TreeNodeList& list)
{
	TreeNodeList nonEventualityList, eventualityList;
	for(TreeNodeList::const_iterator it = list.begin(); it != list.end(); ++it) {
		TreeNode *n = *it;
		if(isEventuality(n)) {
			eventualityList.push_back(n);
		}
		else {
			nonEventualityList.push_back(n);
		}
	}
	return TreeNodeListPair(nonEventualityList, eventualityList);
}

inline std::string eventualityName(TreeNode *n)
{
	assert(isAlways(n));
	TreeNode *n2 = n->firstChild();
	if(isForall(n2)) {
		n2 = n2->secondChild();
	}
	assert(isSometime(n2));
	TreeNode *n3 = n2->firstChild();
	if(isNot(n3)) {
		n3 = n3->firstChild();
	}
	Identifier *id = static_cast<Identifier*>(n3);
	return id->getIdentifier();
}

inline TreeNode* eventualityFromDSNF(TreeNode *n)
{
	assert(isAlways(n));
	TreeNode *n2 = n->firstChild();
	if(isForall(n2)) {
		n2 = n2->secondChild();
	}
	assert(isSometime(n2));
	TreeNode *toReturn = n2->firstChild();
	n2->removeChild(toReturn);
	return toReturn;
}

TreeNodeListPair transformPropositionalProblemToSingleEventuality(const TreeNodeList& list)
{
	TreeNodeListPair formulaeListPair = extractEventualities(list);
	TreeNodeList newFormulae;
	stdoutput() << std::endl << "Eventualities:" << std::endl;
	printFormulaList(formulaeListPair.second);
	if(formulaeListPair.second.size() <= 1) {
		append(formulaeListPair.first, formulaeListPair.second);
		return TreeNodeListPair(formulaeListPair.first, TreeNodeList());
	}
	Identifier *l = new Identifier(std::string("_l")); // necessary otherwise "_l" will be interpreted as a constant
	TreeNodeList newSPredicates;
	for(TreeNodeList::iterator it = formulaeListPair.second.begin(); it != formulaeListPair.second.end(); ++it) {
		std::string name = eventualityName(*it);
		TreeNode *eventuality = eventualityFromDSNF(*it);
		Identifier *s = new Identifier("_since" + name);
		newSPredicates.push_back(s);
		newFormulae.push_back(Not(copy(s)));
		newFormulae.push_back(Always(Implication(Or(eventuality, And(Not(copy(l)), copy(s))), Next(copy(s)))));
		newFormulae.push_back(Always(Implication(Not(Or(copy(eventuality), And(Not(copy(l)), copy(s)))), Next(Not(copy(s))))));
		delete(*it);
	}
	newFormulae.push_back(l);
	newFormulae.push_back(Always(Implication(copy(l), Sometime(Next(And(And(newSPredicates), copy(l)))))));
	return TreeNodeListPair(formulaeListPair.first, newFormulae); 
}
