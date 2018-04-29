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
 
%{

#include <iostream>

#include "formula.h"
#include "helpers.h"

extern "C"
{
	void yyerror(char*);
        int yylex(void);
}

extern list *formula_list;

// forward declaration
tree* buildTreeFromAtLeastTwoList(int op, list *l);

%}

%error-verbose

%token ID AND AND_TEXT OR OR_TEXT NOT ALWAYS NEXT SOMETIME FORALL EXISTS LEFT_BRACKET RIGHT_BRACKET COMMA UNLESS UNTIL IMPLICATION EQUIVALENCE LEFT_SQUARE_BRACKET RIGHT_SQUARE_BRACKET FALSE TRUE

%union {
 char* cstring;
 struct tree* ctree;
 struct list* clist;
}

%type <ctree> formula term predicate quantified_formula unary_formula binary_formula
%type <cstring> ID AND OR NOT ALWAYS NEXT SOMETIME FORALL EXISTS LEFT_BRACKET RIGHT_BRACKET UNLESS UNTIL
%type <clist> termlist formulae variablelist formula_list_at_least_two

%right UNLESS UNTIL IMPLICATION EQUIVALENCE
%right OR AND OR_TEXT AND_TEXT
%right ALWAYS NEXT SOMETIME
%right EXISTS FORALL
%right NOT
%right LEFT_BRACKET RIGHT_BRACKET
%right QUANTIFIED_FORMULA_PREC

%%

formulae:
		{
			$$ = list_New();
		}
	| formulae formula
		{
			$$ = list_PushBack($1, $2);
			formula_list = $$;
		};

term:	ID
		{
			$$ = tree_TreeId($1);
		}
	| ID LEFT_BRACKET termlist RIGHT_BRACKET
		{
			tree *t = tree_TreeId($1);
			tree_SetChildren(t, $3);
			$$ = t;
		};

termlist: term
		{
			$$ = list_List($1);
		}
        | termlist COMMA term
		{
			$$ = list_PushBack($1, $3);
		};

predicate: ID LEFT_BRACKET termlist RIGHT_BRACKET
		{
			tree *t = tree_TreeId($1);
			tree_SetChildren(t, $3);
			$$ = t;
		}
	| ID
		{
			$$ = tree_TreeId($1);
		};

formula:
	LEFT_BRACKET formula RIGHT_BRACKET
		{
			$$ = $2;
		}
	| unary_formula
		{
			$$ = $1;
		}
	| binary_formula
		{
			$$ = $1;
		}
	| AND_TEXT LEFT_BRACKET LEFT_SQUARE_BRACKET formula_list_at_least_two RIGHT_SQUARE_BRACKET RIGHT_BRACKET
		{
			$$ = buildTreeFromAtLeastTwoList(AND, $4);
		}
	| OR_TEXT LEFT_BRACKET LEFT_SQUARE_BRACKET formula_list_at_least_two RIGHT_SQUARE_BRACKET RIGHT_BRACKET
		{
			$$ = buildTreeFromAtLeastTwoList(OR, $4);
		}
	| AND_TEXT LEFT_BRACKET LEFT_SQUARE_BRACKET formula RIGHT_SQUARE_BRACKET RIGHT_BRACKET
		{
			$$ = $4;
		}
	| OR_TEXT LEFT_BRACKET LEFT_SQUARE_BRACKET formula RIGHT_SQUARE_BRACKET RIGHT_BRACKET
		{
			$$ = $4;
		};


formula_list_at_least_two:
	formula COMMA formula
		{
			$$ = list_PushBack(list_List($1), $3);
		}
	| formula_list_at_least_two COMMA formula
		{
			$$ = list_PushBack($1, $3);
		};

binary_formula:
	formula AND formula
		{
			tree *t = tree_TreeOp(AND);
			tree_SetChildren(t, list_PushBack(list_List($1), $3));
			$$ = t;
		}
	| formula OR formula
		{
			tree *t = tree_TreeOp(OR);
			tree_SetChildren(t, list_PushBack(list_List($1), $3));
			$$ = t;
		}

	| formula UNTIL formula
		{
			tree *t = tree_TreeOp(UNTIL);
			tree_SetChildren(t, list_PushBack(list_List($1), $3));
			$$ = t;
		}
	| formula UNLESS formula
		{
			tree *t = tree_TreeOp(UNLESS);
			tree_SetChildren(t, list_PushBack(list_List($1), $3));
			$$ = t;
		}
	| formula IMPLICATION formula 
		{
			tree *t = tree_TreeOp(IMPLICATION);
			tree_SetChildren(t, list_PushBack(list_List($1), $3));
			$$ = t;
		}
	| formula EQUIVALENCE formula
		{
			tree *t = tree_TreeOp(EQUIVALENCE);
			tree_SetChildren(t, list_PushBack(list_List($1), $3));
			$$ = t;
		};

unary_formula:
	TRUE
		{
			$$ = tree_TreeOp(TRUE);
		}
	| FALSE
		{
			$$ = tree_TreeOp(FALSE);
		}
	| predicate
		{
			$$ = $1;
		}
	| NOT formula
		{
			tree *t = tree_TreeOp(NOT);
			tree_SetChildren(t, list_List($2));
			$$ = t;
		}
	| ALWAYS formula
		{
			tree *t = tree_TreeOp(ALWAYS);
			tree_SetChildren(t, list_List($2));
			$$ = t;
		}
	| NEXT formula
		{
			tree *t = tree_TreeOp(NEXT);
			tree_SetChildren(t, list_List($2));
			$$ = t;
		}
	| SOMETIME formula
		{
			tree *t = tree_TreeOp(SOMETIME);
			tree_SetChildren(t, list_List($2));
			$$ = t;
		}
	| FORALL LEFT_SQUARE_BRACKET variablelist RIGHT_SQUARE_BRACKET quantified_formula %prec QUANTIFIED_FORMULA_PREC
		{
			$$ = tree_Quantifier(FORALL, $3, $5);
		}
	| EXISTS LEFT_SQUARE_BRACKET variablelist RIGHT_SQUARE_BRACKET quantified_formula %prec QUANTIFIED_FORMULA_PREC
		{
			$$ = tree_Quantifier(EXISTS, $3, $5);
		};

quantified_formula:
	unary_formula
	{
		$$ = $1;
	}
	| LEFT_BRACKET formula RIGHT_BRACKET
	{
		$$ = $2;
	};

variablelist:
	variablelist COMMA ID
	{
		$$ = list_PushBack($1, tree_TreeId($3));
	}
	| ID
	{
		$$ = list_List(tree_TreeId($1));
	}

%%

tree* buildTreeFromAtLeastTwoList(int op, list *l)
{
	tree *toReturn = tree_TreeOp(op);
	tree_AddChild(toReturn, (tree*) list_FirstElement(l));
	tree *actualTree = toReturn;
	for(list *Scan = list_Tail(l); !list_IsEmpty(Scan); Scan = list_Tail(Scan)) {
		if(list_IsEmpty(list_Tail(Scan))) {
			tree_AddChild(actualTree, (tree*) list_Element(Scan));
		}
		else {
			tree *newTree = tree_TreeOp(op);
			tree_AddChild(newTree, (tree*) list_Element(Scan));
			tree_AddChild(actualTree, newTree);
			actualTree = newTree;
		}
	}
	list_Delete(l);
	return toReturn;
}

list *formula_list = NULL;
