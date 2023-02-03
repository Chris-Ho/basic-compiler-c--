/*
 * Adapted from 
 * CM20029 Coursework Assignment 1
 * Tom Crick
 * cs1tc@bath.ac.uk
 * 30 Apr 2003
 *
 * symbol_table.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "token.h"
#include "C.tab.h"

typedef struct value
{
  int type;
  union
  {
    int integer;
    int boolean;
    char *string;
    void *function;
  } v;
} VALUE;

// typedef struct memory{ //linked list nodes for memory locations for address descriptor
//   char* reg_name;
//   struct memory* next; //if more than one register/memory location that contains this identifier
// }MEMORY;

// typedef struct my_symbol_table{ //node for symbol table entry for an identifier
//   TOKEN* name;
//   struct memory* address_desc; //address descriptor
//   struct my_symbol_table* next; //points to next symbol table in linked list
// }SYMB_ENTRY;



static TOKEN** symbtable;
// static SYMB_ENTRY** my_symbol_table;
#define HASH_SIZE (1000)
#define MAX_PROC_SIZE (100) //maximum number of procedures

TOKEN *int_token, *void_token, *function_token;

void init_symbtable(void)
{
    symbtable = (TOKEN**)calloc(HASH_SIZE, sizeof(TOKEN*));
    int_token = new_token(INT);
    int_token->lexeme = "int";
    function_token = new_token(FUNCTION);
    function_token->lexeme = "function";
    void_token = new_token(VOID);
    void_token->lexeme = "void";
}

int hash(char *s)
{
    int h = 0;
    while (*s != '\0') {
      h = (h<<4) ^ *s++;
    }
    return (0x7fffffff&h) % HASH_SIZE;
}

//change this lookup to include specific symbol table it's checking
TOKEN* lookup_token(char *s)
{
    int	h = hash(s);
    TOKEN *a = symbtable[h];
    TOKEN *ans;
/*     printf("\nLookup: %s\n", s); */
    while (a!=NULL) {
      if (strcmp(a->lexeme, s)==0) return a;
      a = a->next;
    }
    ans = new_token(IDENTIFIER);
    ans->lexeme = (char*)malloc(1+strlen(s));
    strcpy(ans->lexeme, s);
    ans->next = symbtable[h];
    symbtable[h] = ans;
/*     printf(" stored at %p\n", ans); */
    return ans;
}

//change this lookup to include specific symbol table it's checking
// SYMB_ENTRY* my_lookup_table(char *s)
// {
//     int	h = hash(s);
//     SYMB_ENTRY* a = my_symbol_table[h];
//     TOKEN *ans;
//     while (a!=NULL) {
//       if (strcmp(a->name->lexeme, s)==0) return a;
//       a = a->next;
//     }
//     ans = new_token(IDENTIFIER);
//     ans->lexeme = (char*)malloc(1+strlen(s));
//     strcpy(ans->lexeme, s);
//     my_symbol_table[h]->name = ans;
//     return ans;
// }

TOKEN*** mktable(TOKEN** previous){
    TOKEN** newTable = (TOKEN***)calloc(HASH_SIZE, sizeof(TOKEN**));
    
}