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
 
#include "helpers.h"

#include <stdlib.h>

#include <iostream>

#include "outputstream.h"

list* list_New()
{
	list* l = new list;
	l->element = NULL;
	l->next = NULL;
	return l;
}

bool list_IsEmpty(list *l)
{
	return (l == NULL);
}

void* list_Element(list *l)
{
	return l->element;
}

list* list_Tail(list *l)
{
	return l->next;
}

list* list_PushBack(list *l, void *element)
{
	list *last = NULL;
	/* find the last list element */
	for(list *it = l; !list_IsEmpty(it); it = list_Tail(it)) {
		last = it;
	}
	list *newListElement = list_New();
	newListElement->element = element;
	if(last) {
		last->next = newListElement;
		return l;
	}
	else {
		return newListElement;
	}
}

list* list_List(void *element)
{
	return list_PushBack(NULL, element);
}

void list_Delete(list *l)
{
	if(list_IsEmpty(l)) {
		return;
	}
	for(list *it = list_Tail(l); !list_IsEmpty(it);) {
		list *l2 = list_Tail(it);
		delete it;
		it = l2;
	}
	delete l;
}

void list_DeleteWith(list *l, void (*elementDelete)(void*))
{
	if(list_IsEmpty(l)) {
		return;
	}
	for(list *it = list_Tail(l); !list_IsEmpty(it); ) {
		elementDelete(list_Element(it));
		list *l2 = list_Tail(it);
		delete it;
		it = l2;
	}
	elementDelete(list_Element(l));
	delete l;
}

unsigned int list_Length(list *l)
{
	if(list_IsEmpty(l)) {
		return 0;
	}
	else {
		return 1 + list_Length(list_Tail(l));
	}
}

void* list_FirstElement(list *l)
{
	return list_Element(l);
}

void* list_SecondElement(list *l)
{
	return list_Element(list_Tail(l));
}

tree* tree_New()
{
	tree *t = new tree;
	t->id = NULL;
	t->op = 0;
	t->children = NULL;
	t->parent = NULL;
	return t;
}

void tree_Free(tree *t)
{
	if(!t) {
		return;
	}

	free(t->id);
	list_Delete(t->children);
	delete t;
}

void tree_Delete(tree *t)
{
	if(!t) {
		return;
	}

	for(list *it = tree_Children(t); !list_IsEmpty(it); it = list_Tail(it)) {
		tree_Delete((tree*) list_Element(it));
	}
	tree_Free(t);
}

tree* tree_TreeId(char *id)
{
	tree *t = tree_New();
	t->id = id;
	return t;
}

tree* tree_TreeOp(int op)
{
	tree *t = tree_New();
	t->op = op;
	return t;
}

tree* tree_Quantifier(int quant, list* variables, tree* formula)
{
	tree *toReturn = tree_TreeOp(quant);
	tree *parent = toReturn;

	for(list *it = variables; !list_IsEmpty(it); it = list_Tail(it)) {
		tree* variableId = (tree*)list_Element(it);
		tree_AddChild(parent, variableId);

		if(!list_IsEmpty(list_Tail(it))) {
			tree *newParent = tree_TreeOp(quant);
			tree_AddChild(parent, newParent);
			parent = newParent;
		}
	}
	tree_AddChild(parent, formula);
	list_Delete(variables);
	return toReturn;
}

char* tree_Id(tree *t)
{
	return t->id;
}

int tree_Op(tree *t)
{
	return t->op;
}

tree* tree_Parent(tree *t)
{
	return t->parent;
}

void tree_SetParent(tree *t, tree *parent)
{
	t->parent = parent;
}

void tree_AddIdChild(tree *t, char* id)
{
	tree *newNode = tree_New();
	newNode->id = id;
	newNode->parent = t;
	t->children = list_PushBack(t->children, newNode);
}

void tree_SetChildren(tree *t, list *children)
{
	t->children = children;
	for(list *it = children; !list_IsEmpty(it); it = list_Tail(it)) {
		tree_SetParent((tree*)list_Element(it), t);
	}
}

void tree_Print(tree *t)
{
	if(!t) {
		stdoutput() << "(null)";
		return;
	}
	if(tree_Id(t)) {
		stdoutput() << (char*)tree_Id(t);
	}
	else {
		stdoutput() << tree_Op(t);
	}

	if(!list_IsEmpty(tree_Children(t))) {
		stdoutput() << "(";
		for(list *it = tree_Children(t); !list_IsEmpty(it); it = list_Tail(it)) {
			tree_Print((tree*)list_Element(it));
			if(!list_IsEmpty(list_Tail(it))) {
				stdoutput() << ",";
			}
		}
		stdoutput() << ")";
	}
}
 
unsigned int tree_ChildrenCount(tree *t)
{
	return list_Length(tree_Children(t));
}
