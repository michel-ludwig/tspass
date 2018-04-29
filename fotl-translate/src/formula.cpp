/************************************************************
 *    Copyright (C) 2008-2009                               *
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

#include "formula.h"

#include <assert.h>

#include <map>

#include "misc.h"
#include "parser.h"

TreeNode::TreeNode(const TreeNodeList& children)
: m_parent(NULL), m_children(children)
{
}

TreeNode::TreeNode(const TreeNode& n)
: m_parent(NULL)
{
	TreeNodeList nChildren = n.m_children;
	for(TreeNodeList::const_iterator i = nChildren.begin(); i != nChildren.end(); ++i) {
		addChild((*i)->clone());
	}
}

TreeNode::~TreeNode()
{
	if(m_parent) {
		m_parent->removeChild(this);
	}
	TreeNodeList childrenList = m_children;
	for(TreeNodeList::iterator i = childrenList.begin(); i != childrenList.end(); ++i) {
		delete(*i);
	}
}

void TreeNode::addChild(TreeNode *n)
{
	assert(n);
	if(n->m_parent) {
		n->m_parent->removeChild(n);
	}
	m_children.push_back(n);
	n->m_parent = this;
}

const TreeNodeList& TreeNode::children() const
{
	return m_children;
}

void TreeNode::setChildren(const std::list<TreeNode*>& children)
{
	m_children = children;
	for(TreeNodeList::iterator i = m_children.begin(); i != m_children.end(); ++i) {
		assert(*i);
		(*i)->m_parent = this;
	}
}

void TreeNode::clearChildren()
{
	for(TreeNodeList::iterator i = m_children.begin(); i != m_children.end(); ++i) {
		(*i)->m_parent = NULL;
	}
	m_children.clear();
}

unsigned int TreeNode::childrenCount() const
{
	return m_children.size();
}

TreeNode* TreeNode::firstChild()
{
	return *(m_children.begin());
}

TreeNode* TreeNode::secondChild()
{
	return *(++m_children.begin());
}

TreeNode* TreeNode::getParent()
{
	return m_parent;
}

void TreeNode::replaceChild(TreeNode *n1, TreeNode *n2)
{
	for(std::list<TreeNode*>::iterator i = m_children.begin(); i != m_children.end(); ++i) {
		if(*i == n1) {
			(*i)->m_parent = NULL;
			*i = n2;
			n2->m_parent = this;
		}
	}
}

void TreeNode::removeChild(TreeNode *n)
{
	m_children.remove(n);
	n->m_parent = NULL;
}

void TreeNode::output(std::string &output, const std::map<int, std::string>& variableIdMap, unsigned int variableCounter)
{
	// does nothing
}

bool TreeNode::childrenEqual(const TreeNode* n2)
{
	const TreeNodeList& children = m_children;
	TreeNodeList children2 = n2->children();

	if(m_children.size() != children2.size()) {
		return false;
	}
	TreeNodeList::const_iterator it = children.begin();
	TreeNodeList::const_iterator it2 = children2.begin();
	while(it != children.end() && it2 != children2.end()) {
		if(!(*(*it) == *it2)) {
			return false;
		}
		++it;
		++it2;
	}

	return true;
}

Variable::Variable(int index, const std::list<TreeNode*>& children)
: TreeNode(children), m_index(index)
{
}

Variable::~Variable()
{
}

void Variable::output(std::string &output, const std::map<int, std::string>& variableIdMap, unsigned int variableCounter)
{
	std::map<int, std::string>::const_iterator it = variableIdMap.find(m_index);
	if(it == variableIdMap.end()) {
		output += "<unspecified variable (" + toString(m_index) + ")>";
	}
	else {
		output += it->second;
	}
}

int Variable::getVariable() const
{
	return m_index;
}

void Variable::setVariable(int index)
{
	m_index = index;
}

TreeNode* Variable::clone()
{
	return new Variable(*this);
}

bool Variable::operator==(const TreeNode* n2)
{
	const Variable *variable2 = dynamic_cast<const Variable*>(n2);
	if(!variable2) {
		return false;
	}
	return (m_index == variable2->m_index);
}

Identifier::Identifier(bool trueFalseConstant)
: TreeNode(), m_trueFalseConstant(trueFalseConstant)
{
}

Identifier::Identifier(const std::string& id, const std::list<TreeNode*>& children)
: TreeNode(children), m_id(id)
{
}

Identifier::~Identifier()
{
}

void Identifier::output(std::string &output, const std::map<int, std::string>& variableIdMap, unsigned int variableCounter)
{
	if(m_id.length() == 0) {
		if(m_trueFalseConstant) {
			output += "TRUE";
		}
		else {
			output += "FALSE";
		}
		return;
	}
	output += m_id;
	if(m_children.size() > 0) {
		output += "(";
	}
	for(std::list<TreeNode*>::iterator i = m_children.begin(); i != m_children.end(); ++i) {
		if(i != m_children.begin()) {
			output += ",";
		}
		(*i)->output(output, variableIdMap, variableCounter);
	}
	if(m_children.size() > 0) {
		output += ")";
	}
}

TreeNode* Identifier::clone()
{
	return new Identifier(*this);
}

bool Identifier::isTrue() const
{
	return (m_id.length() == 0 && m_trueFalseConstant);
}

bool Identifier::isFalse() const
{
	return (m_id.length() == 0 && !m_trueFalseConstant);
}

const std::string& Identifier::getIdentifier() const
{
	return m_id;
}

bool Identifier::operator==(const TreeNode* n2)
{
	const Identifier *identifier2 = dynamic_cast<const Identifier*>(n2);
	if(!identifier2) {
		return false;
	}

	if(m_id.length() != identifier2->m_id.length()) {
		return false;
	}

	if(m_id.length() == 0) {
		if(m_trueFalseConstant != identifier2->m_trueFalseConstant) {
			return false;
		}
		else {
			return true;
		}
	}

	if(m_id.compare(identifier2->m_id) != 0) {
		return false;
	}
	return childrenEqual(n2);
}

Operator::Operator(int type, const std::list<TreeNode*>& children)
: TreeNode(children), m_type(type)
{
}

Operator::~Operator()
{
}

TreeNode* Operator::clone()
{
	return new Operator(*this);
}

bool Operator::operator==(const TreeNode* n2)
{
	const Operator *operator2 = dynamic_cast<const Operator*>(n2);
	if(!operator2) {
		return false;
	}

	if(m_type != operator2->m_type) {
		return false;
	}
	return childrenEqual(n2);
}

TreeNode* Not(TreeNode* n)
{
	TreeNode *toReturn = new Operator(NOT);
	toReturn->addChild(n);
	return toReturn;
}

TreeNode* And(TreeNode* n1, TreeNode *n2)
{
	TreeNode *toReturn = new Operator(AND);
	toReturn->addChild(n1);
	toReturn->addChild(n2);
	return toReturn;
}

TreeNode* And(const TreeNodeList& list)
{
	if(list.empty()) {
		return NULL;
	}
	TreeNode *toReturn = NULL;
	TreeNode *previous = *(list.begin());
	if(list.size() == 1) {
		return previous;
	}
	for(TreeNodeList::const_iterator it = ++list.begin(); it != list.end(); ++it) {
		toReturn = And(*it, previous);
		previous = toReturn;
	}
	return toReturn;
}

TreeNode* Or(TreeNode* n1, TreeNode *n2)
{
	TreeNode *toReturn = new Operator(OR);
	toReturn->addChild(n1);
	toReturn->addChild(n2);
	return toReturn;
}

TreeNode* Implication(TreeNode* n1, TreeNode *n2)
{
	TreeNode *toReturn = new Operator(IMPLICATION);
	toReturn->addChild(n1);
	toReturn->addChild(n2);
	return toReturn;
}

TreeNode* Forall(TreeNode *n)
{
	TreeNode *toReturn = new Operator(FORALL);
	toReturn->addChild(new Variable(0));
	toReturn->addChild(n);
	return toReturn;
}

TreeNode* Always(TreeNode *n)
{
	TreeNode *toReturn = new Operator(ALWAYS);
	toReturn->addChild(n);
	return toReturn;
}

TreeNode* Next(TreeNode *n)
{
	TreeNode *toReturn = new Operator(NEXT);
	toReturn->addChild(n);
	return toReturn;
}

TreeNode* Sometime(TreeNode *n)
{
	TreeNode *toReturn = new Operator(SOMETIME);
	toReturn->addChild(n);
	return toReturn;
}

std::string getNewVariableName(unsigned int variableCounter)
{
	switch(variableCounter) {
		case 0:
			return "x";
		case 1:
			return "y";
		case 2:
			return "z";
		default:
			return "x" + toString(variableCounter - 2);
	}
}

std::map<int, std::string> updateVariableMap(const std::map<int, std::string>& variableIdMap, unsigned int variableCounter)
{
	std::map<int, std::string> toReturn;
	std::string newVariableName;
	for(std::map<int, std::string>::const_iterator it = variableIdMap.begin(); it != variableIdMap.end(); ++it) {
		toReturn[it->first + 1] = it->second;
	}
	toReturn[0] = getNewVariableName(variableCounter);
	return toReturn;
}

std::string operatorToString(int op)
{
	switch(op) {
		case AND:
			return "AND";
		break;
		case OR:
			return "OR";
		break;
		case NOT:
			return "NOT";
		break;
		case ALWAYS:
			return "ALWAYS";
		break;
		case NEXT:
			return "NEXT";
		break;
		case SOMETIME:
			return "SOMETIME";
		break;
		case FORALL:
			return "FORALL";
		break;
		case EXISTS:
			return "EXISTS";
		break;
		case UNTIL:
			return "UNTIL";
		break;
		case UNLESS:
			return "UNLESS";
		break;
		case IMPLICATION:
			return "IMPLICATION";
		break;
		case EQUIVALENCE:
			return "EQUIVALENCE";
		break;
	}
	return "";
}

void Operator::output(std::string &output, const std::map<int, std::string>& variableIdMap, unsigned int variableCounter)
{
	output += operatorToString(m_type);
	output += "(";
	std::map<int, std::string> newVariableIdMap = variableIdMap;
	if(m_type == FORALL || m_type == EXISTS) {
		newVariableIdMap = updateVariableMap(variableIdMap, variableCounter);
		++variableCounter;
	}
	for(std::list<TreeNode*>::iterator i = m_children.begin(); i != m_children.end(); ++i) {
		if(i != m_children.begin()) {
			output += ",";
		}
		(*i)->output(output, newVariableIdMap, variableCounter);
	}
	output += ")";
}

int Operator::getOperator() const
{
	return m_type;
}

void Operator::setOperator(int op)
{
	m_type = op;
}

void substituteFreeVariable(TreeNode *n, int varIndex, int varIndex2)
{
	if(isVariable(n)) {
		Variable *v = static_cast<Variable*>(n);
		if(v->getVariable() == varIndex) {
			v->setVariable(varIndex2);
		}
	}
	else {
		if(isQuantifier(n)) {
			++varIndex;
			++varIndex2;
		}
		TreeNodeList children = n->children();
		for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
			substituteFreeVariable(*i, varIndex, varIndex2);
		}
	}
}

std::ostream& operator<<(std::ostream &os, TreeNode* n)
{
	if(!n) {
		os << "(null)";
	}
	else {
		std::string output;
		n->output(output, std::map<int, std::string>(), 0);
		os << output;
	}
	return os;
}

std::map<std::string, int> increaseVariableIndexes(const std::map<std::string, int>& variableIndexMap)
{
	std::map<std::string, int> m = variableIndexMap;

	for(std::map<std::string, int>::iterator i = m.begin(); i != m.end(); ++i) {
		++(i->second);
	}
	return m;
}

TreeNode* transformToDeBruijnTree(tree *t, const std::map<std::string, int>& variableIndexMap)
{
	TreeNode *toReturn = NULL;
	list *children = tree_Children(t);

	if(tree_Op(t)) {
		std::map<std::string, int> newVariableIndexMap = variableIndexMap;
		int op = tree_Op(t);
		if(op == TRUE || op == FALSE) {
			return new Identifier(op == TRUE);
		}
		else {
			toReturn = new Operator(tree_Op(t));
			if(op == EXISTS || op == FORALL) {
				assert(tree_ChildrenCount(t) >= 2);
				std::string variable = tree_Id(static_cast<tree*>(list_FirstElement(children)));
				newVariableIndexMap = increaseVariableIndexes(variableIndexMap);
				newVariableIndexMap[variable] = 0;
			}
			for(list *it = children; !list_IsEmpty(it); it = list_Tail(it)) {
				toReturn->addChild(transformToDeBruijnTree(static_cast<tree*>(list_Element(it)), newVariableIndexMap));
			}
		}
	}
	else {
		std::string id = tree_Id(t);
		std::map<std::string, int>::const_iterator it = variableIndexMap.find(id);
		if(it == variableIndexMap.end()) {
			toReturn = new Identifier(id);
		}
		else {
			toReturn = new Variable(it->second);
		}
		for(list *it = children; !list_IsEmpty(it); it = list_Tail(it)) {
			toReturn->addChild(transformToDeBruijnTree(static_cast<tree*>(list_Element(it)), variableIndexMap));
		}
	}
	return toReturn;
}

TreeNode* transformToDeBruijnTree(tree *t)
{
	return transformToDeBruijnTree(t, std::map<std::string, int>());
}

TreeNode* copy(TreeNode *n)
{
	TreeNode *toReturn = n->clone();
	toReturn->m_parent = NULL;

	return toReturn;
}

std::list<int> freeVariables(TreeNode *n, int freeVariableIndex)
{
	std::list<int> toReturn;
	if(isVariable(n)) {
		Variable *v = static_cast<Variable*>(n);
		int variable = v->getVariable();
		if(variable >= freeVariableIndex) {
			toReturn.push_back(variable - freeVariableIndex);
		}
	}
	else {
		if(isQuantifier(n)) {
			++freeVariableIndex;
		}
		TreeNodeList children = n->children();
		for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
			std::list<int> freeVariablesInSub = freeVariables(*i, freeVariableIndex);
			toReturn.merge(freeVariablesInSub);
		}
	}
	toReturn.sort();
	toReturn.unique();
	return toReturn;
}

std::list<int> freeVariables(TreeNode *n)
{
	return freeVariables(n, 0);
}

unsigned int freeVariableCount(TreeNode *n)
{
	return freeVariables(n).size();
}

void mapPredicatesAndFunctionSymbols(TreeNode *n, IdentifierArityMap& functionMap,
                                     IdentifierArityMap& predicateMap, bool predicateAlreadyFound = false)
{
	if(isIdentifier(n)) {
		Identifier *identifier = static_cast<Identifier*>(n);
		if(identifier->isTrue() || identifier->isFalse()) {
			return;
		}
		IdentifierArityMap& map = (predicateAlreadyFound ? functionMap : predicateMap);
		IdentifierArityMap::iterator it = map.find(identifier->getIdentifier());
		if(it == map.end()) {
			map[identifier->getIdentifier()] = identifier->childrenCount();
		}
		else {
			if(identifier->childrenCount() != it->second) {
				std::cerr << "wrong arities for the symbol " << identifier->getIdentifier()
				          << " (supposed to have " << it->second << ", got "
				          << identifier->childrenCount() << ")." << std::endl;
				assert(false);
			}
		}
		predicateAlreadyFound = true;
	}

	TreeNodeList children = n->children();
	for(std::list<TreeNode*>::const_iterator i = children.begin(); i != children.end(); ++i) {
		mapPredicatesAndFunctionSymbols(*i, functionMap, predicateMap, predicateAlreadyFound);
	}

}

std::pair<IdentifierArityMap, IdentifierArityMap> extractPredicatesAndFunctionSymbols(const std::list<TreeNode*>& list)
{
	IdentifierArityMap functionMap, predicateMap;
	for(std::list<TreeNode*>::const_iterator i = list.begin(); i != list.end(); ++i) {
		mapPredicatesAndFunctionSymbols(*i, functionMap, predicateMap);
	}

	return std::pair<IdentifierArityMap, IdentifierArityMap>(functionMap, predicateMap);
}

void removeDuplicateTreeNode(TreeNodeList& list, TreeNodeList::iterator& start)
{
	TreeNodeList::iterator it = start;
	++it;
	for(; it != list.end(); ) {
		if(*(*it) == *start) {
			delete(*it);
			it = list.erase(it);
		}
		else {
			++it;
		}
	}
}

void removeDuplicates(TreeNodeList& list)
{
	if(list.empty()) {
		return;
	}
	for(TreeNodeList::iterator it = list.begin(); it != list.end(); ++it) {
		removeDuplicateTreeNode(list, it);
	}
}
