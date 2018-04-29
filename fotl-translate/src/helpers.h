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
 
#ifndef HELPERS_H
#define HELPERS_H

/* singly linked list */
/* the empty list is represted by the null pointer */
struct list {
	void *element;
	list *next;
};

/* string tree */
struct tree {
	char* id;
	int op;
	list* children;
	tree* parent;
};

void* list_Element(list *l);
bool list_IsEmpty(list *l);
list* list_New();
void list_Delete(list *l);
list* list_PushBack(list *l, void *element);
list* list_List(void *element);
list* list_Tail(list *l);
unsigned int list_Length(list *l);
void* list_FirstElement(list *l);
void* list_SecondElement(list *l);

static __inline__ list* tree_Children(tree *t)
{
	return t->children;
}

void tree_Free(tree *t);
void tree_Delete(tree *t);
char* tree_Id(tree *t);
int tree_Op(tree *t);
tree* tree_TreeId(char *id);
tree* tree_TreeOp(int op);
tree* tree_Quantifier(int quant, list* variables, tree* formula);
list* tree_Children(tree *t);
void tree_SetChildren(tree *t, list *l);

static __inline__ void tree_AddChild(tree *t, tree *child)
{
	tree_SetChildren(t, list_PushBack(tree_Children(t), child));
}

void tree_Print(tree *t);
unsigned int tree_ChildrenCount(tree *t);

#endif

