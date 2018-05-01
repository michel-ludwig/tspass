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
 
#ifndef _FORMULA_H
#define _FORMULA_H

#ifdef __cplusplus

#include <assert.h>

#include <iostream>
#include <list>
#include <map>
#include <string>
#include <typeinfo>

#include "helpers.h"
#include "parser.h"

//forward declaration
class TreeNode;

typedef std::list<TreeNode*> TreeNodeList;
typedef std::pair<TreeNode*, TreeNode*> TreeNodePair;
typedef std::list<TreeNodePair> TreeNodePairList;
typedef std::pair<TreeNodeList, TreeNodeList> TreeNodeListPair;
typedef std::pair<TreeNode*, TreeNodeList> FormulaListPair;

TreeNode* copy(TreeNode *n);

class TreeNode {
	friend TreeNode* copy(TreeNode *n);

	public:
		TreeNode(const TreeNodeList& children = TreeNodeList());
		TreeNode(const TreeNode& n);
		virtual ~TreeNode();

		void addChild(TreeNode *n);
		const TreeNodeList& children() const;
		void setChildren(const std::list<TreeNode*>& children);
		void clearChildren();

		unsigned int childrenCount() const;
		TreeNode* firstChild();
		TreeNode* secondChild();

		TreeNode* getParent();

		void removeChild(TreeNode *n);
		void replaceChild(TreeNode *n1, TreeNode *n2);

		/**
		 * The values '0', '1', '2' for 'variableCounter' are reserved for the variables 'x', 'y' and 'z', respectively.
		 */
		virtual void output(std::string &output, const std::map<int, std::string>& variableIdMap, unsigned int variableCounter);

		virtual TreeNode* clone() = 0;

		virtual bool operator==(const TreeNode* n2) = 0;

	protected:
		TreeNode* m_parent;
		std::list<TreeNode*> m_children;

		bool childrenEqual(const TreeNode* n2);
};

class Variable : public TreeNode
{
	public:
		Variable(int index, const std::list<TreeNode*>& children = std::list<TreeNode*>());
		virtual ~Variable();

		virtual void output(std::string &output, const std::map<int, std::string>& variableIdMap, unsigned int variableCounter);
		int getVariable() const;
		void setVariable(int index);

		virtual TreeNode* clone();

		virtual bool operator==(const TreeNode* n2);

	protected:
		int m_index;

};


class Identifier : public TreeNode
{
	public:
		Identifier(bool trueFalseConstant);
		Identifier(const std::string& id, const std::list<TreeNode*>& children = std::list<TreeNode*>());
		virtual ~Identifier();

		virtual void output(std::string &output, const std::map<int, std::string>& variableIdMap, unsigned int variableCounter);

		virtual TreeNode* clone();
		const std::string& getIdentifier() const;

		bool isTrue() const;
		bool isFalse() const;

		virtual bool operator==(const TreeNode* n2);

	protected:
		std::string m_id;
		bool m_trueFalseConstant;
};


class Operator : public TreeNode
{
	public:
		Operator(int type, const std::list<TreeNode*>& children = std::list<TreeNode*>());
		virtual ~Operator();

		virtual void output(std::string &output, const std::map<int, std::string>& variableIdMap, unsigned int variableCounter);
		int getOperator() const;
		void setOperator(int op);

		virtual TreeNode* clone();

		virtual bool operator==(const TreeNode* n2);

	protected:
		int m_type;
};

inline bool isVariable(TreeNode *n)
{
	return (typeid(*n) == typeid(Variable));
}

inline bool isIdentifier(TreeNode *n)
{
	return (typeid(*n) == typeid(Identifier));
}

inline bool isOperator(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator));
}

inline bool isQuantifier(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator)) && (static_cast<Operator*>(n)->getOperator() == FORALL
	                                         || static_cast<Operator*>(n)->getOperator() == EXISTS);
}

inline bool isAnd(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator) && static_cast<Operator*>(n)->getOperator() == AND);
}

inline bool isOr(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator) && static_cast<Operator*>(n)->getOperator() == OR);
}

inline bool isNot(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator) && static_cast<Operator*>(n)->getOperator() == NOT);
}

inline bool isAlways(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator) && static_cast<Operator*>(n)->getOperator() == ALWAYS);
}

inline bool isImplication(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator) && static_cast<Operator*>(n)->getOperator() == IMPLICATION);
}

inline bool isForall(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator) && static_cast<Operator*>(n)->getOperator() == FORALL);
}

inline bool isNext(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator) && static_cast<Operator*>(n)->getOperator() == NEXT);
}

inline bool isSometime(TreeNode *n)
{
	return (typeid(*n) == typeid(Operator) && static_cast<Operator*>(n)->getOperator() == SOMETIME);
}

inline bool isTemporalOperator(int op)
{
	return (op == ALWAYS || op == NEXT || op == UNTIL || op == UNLESS || op == ALWAYS
	                                                                  || op == SOMETIME);
}

TreeNode* Not(TreeNode* n);
TreeNode* And(TreeNode* n1, TreeNode *n2);
TreeNode* And(const TreeNodeList& list);
TreeNode* Or(TreeNode* n1, TreeNode *n2);
TreeNode* Implication(TreeNode* n1, TreeNode *n2);
TreeNode* Forall(TreeNode *n);
TreeNode* Always(TreeNode *n);
TreeNode* Next(TreeNode *n);
TreeNode* Sometime(TreeNode *n);

inline TreeNode* quantifierSubFormula(TreeNode *n)
{
	assert(isQuantifier(n));
	return n->secondChild();
}

inline bool isTopLevelFormula(TreeNode *n)
{
	return (n->getParent() == NULL);
}

inline void replaceInnerNode(TreeNode *n1, TreeNode *n2)
{
	assert(n1->getParent() != NULL);
	n1->getParent()->replaceChild(n1, n2);
}

/**
 * Capture-free replacement of every free occurrence of the variable 'varIndex' by 'varIndex2'.
 **/
void substituteFreeVariable(TreeNode *n, int varIndex, int varIndex2);

std::ostream& operator<<(std::ostream &os, TreeNode* n);

TreeNode* transformToDeBruijnTree(tree *t);

/**
 * The parent of 'n' is not copied over to the returned node!
 **/
TreeNode* copy(TreeNode *n);

std::list<int> freeVariables(TreeNode *n);

unsigned int freeVariableCount(TreeNode *n);

std::map<int, std::string> updateVariableMap(const std::map<int, std::string>& variableIdMap, unsigned int variableCounter);

typedef std::map<std::string, unsigned int> IdentifierArityMap;
std::pair<IdentifierArityMap, IdentifierArityMap> extractPredicatesAndFunctionSymbols(const std::list<TreeNode*>& list);

inline bool isLiteral(TreeNode *n)
{
	// works for 'true' and 'false'
	return (isIdentifier(n) || (isNot(n) && isIdentifier(n->firstChild())));
}

inline bool isPositiveLiteral(TreeNode *n)
{
	// works for 'true' and 'false'
	return isIdentifier(n);
}

inline bool isNegativeLiteral(TreeNode *n)
{
	// works for 'true' and 'false'
	return (isNot(n) && isIdentifier(n->firstChild()));
}

void removeDuplicates(TreeNodeList& list);

inline bool isPropositional(TreeNode *n)
{
	if(isVariable(n)) {
		return false;
	}
	if(isIdentifier(n)) {
		return (n->childrenCount() == 0);
	}
	if(isQuantifier(n)) {
		return false;
	}
	const TreeNodeList& children = n->children();
	for(TreeNodeList::const_iterator i = children.begin(); i != children.end(); ++i) {
		if(!isPropositional(*i)) {
			return false;
		}
	}
	return true;
}

inline bool isPropositional(const TreeNodeList& list)
{
	for(TreeNodeList::const_iterator i = list.begin(); i != list.end(); ++i) {
		if(!isPropositional(*i)) {
			return false;
		}
	}
	return true;
}

#endif

#endif
