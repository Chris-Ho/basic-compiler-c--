#ifndef __TOKEN_H
#define __TOKEN_H

#define TRUE 1
#define FALSE 0
#define TEST_MODE 0

struct SYMBOLTABLE;
struct TOKEN;

typedef struct ar{
  char* fp;
  struct ar* access_link; //link to caller
  int pc; //caller's pc - needed?
  int nested_depth;
}AR;

struct SYMB_ENTRY;

typedef struct symbol_table{
  int size;
  struct ar* ar; //activation record for what stored 
  struct SYMB_ENTRY** symbtable; 
  struct SYMBOLTABLE* static_link; 
}SYMBOLTABLE;

typedef struct TOKEN
{
  int           type;
  char          *lexeme;
  int           value;
  struct TOKEN  *next;
  SYMBOLTABLE* symbtable; 
} TOKEN;

typedef struct memory{ //linked list nodes for memory locations for address descriptor
  char* reg_name;
  struct memory* next; //if more than one register/memory location that contains this identifier
}MEMORY;

typedef struct symbol_table_entry{ //node for symbol table entry for an identifier
  TOKEN* name;
  int offset;
  struct memory* address_desc; //address descriptor
  struct symbol_table_entry* next; //points to next symbol table-entry in linked list
  struct ar ar;
  struct tac* next_use; //POINTER to TAC statement for next use of this particular variable
}SYMB_ENTRY;

extern TOKEN* new_token(int);



#endif
