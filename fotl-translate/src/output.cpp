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
 
#include "output.h"

#include <cstdlib>

#include "misc.h"
#include "outputstream.h"

OutputWriter::~OutputWriter()
{
}

DFGOutputWriter::~DFGOutputWriter()
{
}

void printDFGHeader(std::string& output)
{
	output += "begin_problem(TranslatedInput).\n";


	output += "list_of_descriptions.\n";
	output += "name({*Translated Input*}).\n";
	output += "author({**}).\n";
	output += "status(unknown).\n";
	output += "description({**}).\n";
	output += "end_of_list.\n";
	output += "\n";
}

void printDFGFooter(std::string& output)
{
	output += "end_problem.\n";
}

void printDFGSymbols(std::string& output, const std::pair<IdentifierArityMap, IdentifierArityMap>& mapPair)
{
	IdentifierArityMap functionMap = mapPair.first;
	IdentifierArityMap predicateMap = mapPair.second;

	if(functionMap.empty() && predicateMap.empty()) {
		return;
	}

	output += "list_of_symbols.\n";

	if(!functionMap.empty()) {
		output += "functions[";
		for(IdentifierArityMap::const_iterator it = functionMap.begin(); it != functionMap.end(); ++it) {
			if(it != functionMap.begin()) {
				output += ",";
			}
			output += "(" + (*it).first + "," + toString((*it).second) + ")";
		}
		output += "].\n";
	}

	if(!predicateMap.empty()) {
		output += "predicates[";
		for(IdentifierArityMap::const_iterator it = predicateMap.begin(); it != predicateMap.end(); ++it) {
			if(it != predicateMap.begin()) {
				output += ",";
			}
			output += "(" + (*it).first + "," + toString((*it).second) + ")";
		}
		output += "].\n";
	}

	output += "end_of_list.\n";
	output += "\n";
}

static std::string operatorToString(int op)
{
	switch(op) {
		case AND:
			return "and";
		break;
		case OR:
			return "or";
		break;
		case NOT:
			return "not";
		break;
		case ALWAYS:
			return "always";
		break;
		case NEXT:
			return "next";
		break;
		case SOMETIME:
			return "sometime";
		break;
		case FORALL:
			return "forall";
		break;
		case EXISTS:
			return "exists";
		break;
		case IMPLICATION:
			return "implies";
		break;
		case EQUIVALENCE:
			return "equiv";
		break;
		default:
			std::cerr << "Operator should not occur: " << op << std::endl;
			abort();
	}
	return "";
}

std::string treeNodeToDFG(TreeNode *n, const std::map<int, std::string>& variableIdMap = std::map<int, std::string>(),
                                      unsigned int variableCounter = 0)
{
	std::string toReturn;
	const TreeNodeList& children = n->children();

	if(typeid(*n) == typeid(Variable)) {
		int variable = static_cast<Variable*>(n)->getVariable();
		std::map<int, std::string>::const_iterator it = variableIdMap.find(variable);
		if(it == variableIdMap.end()) {
			return "<unspecified variable (" + toString(variable) + ")>";
		}
		else {
			return "_" + it->second;
		}
	}
	else if(typeid(*n) == typeid(Identifier)) {
		Identifier *identifier = static_cast<Identifier*>(n);
		if(identifier->isTrue()) {
			toReturn += "true";
		}
		else if(identifier->isFalse()) {
			toReturn += "false";
		}
		else {
			toReturn += identifier->getIdentifier();
			if(children.size() > 0) {
				toReturn += "(";
			}
			for(TreeNodeList::const_iterator i = children.begin(); i != children.end(); ++i) {
				if(i != children.begin()) {
					toReturn += ",";
				}
				toReturn += treeNodeToDFG(*i, variableIdMap, variableCounter);
			}
			if(children.size() > 0) {
				toReturn += ")";
			}
		}
	}
	else if(typeid(*n) == typeid(Operator)) {
		int operatorType = static_cast<Operator*>(n)->getOperator();
		toReturn += operatorToString(operatorType);
		toReturn += "(";
		std::map<int, std::string> newVariableIdMap = variableIdMap;
		if(operatorType == FORALL || operatorType == EXISTS) {
			newVariableIdMap = updateVariableMap(variableIdMap, variableCounter);
			++variableCounter;
		}
		for(TreeNodeList::const_iterator i = children.begin(); i != children.end(); ++i) {
			bool outputBrackets = false;
			if(i != children.begin()) {
				toReturn += ",";
			}
			if((operatorType == FORALL || operatorType == EXISTS)
			   && i == children.begin()) {
				outputBrackets = true;
			}
			toReturn += (outputBrackets ? "[" : "") + treeNodeToDFG(*i, newVariableIdMap, variableCounter)
			            + (outputBrackets ? "]" : "");
		}
		toReturn += ")";
	}

	return toReturn;
}

void printDFGFormulae(std::string& output, const std::list<TreeNode*>& formulaList)
{
	if(formulaList.empty()) {
		return;
	}

	output += "list_of_formulae(axioms).\n";

	for(std::list<TreeNode*>::const_iterator it = formulaList.begin(); it != formulaList.end(); ++it) {
		output += "formula(" + treeNodeToDFG(*it) + ").\n";
	}

	output += "end_of_list.\n";
	output += "\n";
}

std::string DFGOutputWriter::write(const std::list<TreeNode*>& formulaList)
{
	std::string toReturn;

	std::pair<IdentifierArityMap, IdentifierArityMap> mapPair = extractPredicatesAndFunctionSymbols(formulaList);
	printDFGHeader(toReturn);
	printDFGSymbols(toReturn, mapPair);
	printDFGFormulae(toReturn, formulaList);

	printDFGFooter(toReturn);

	return toReturn;
}
