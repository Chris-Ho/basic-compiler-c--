#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include "nodes.h"
#include "C.tab.h"
#include <string.h>
//#include "symbol_table.c"

#define HASH_SIZE (1000)


#define DECLARATION 126  //~
#define FUNCTIONDEC 100  //d
#define FUNCTIONDEF 68   //D
#define FUNCTIONPARAM 70 //F
#define EQUALS 61        //=
#define PLUS 43          //+ 
#define MINUS 45         //-
#define DIVIDE 47
#define MULTIPLY 42 
#define MOD 37        //%
#define GE_OP 262 // >=
#define LE_OP 261 // <=
#define EQ_OP 263 // ==
#define NE_OP 264 // != 
#define SEQUENCE 59      //;
#define LESSTHAN 60 //<
#define GREATERTHAN 62 //>
#define LISTING 44 // '

#define TYPE 271 //INT or VOID




//global variable offset for TAC generation
int offset = 0;

int uniqueCountForTemporaries = 1;
int uniqueCountForLabels = 1;


enum tac_op
  {
   tac_plus = 1
  };

struct CLOSURE;

typedef struct value
{
  int type;
  union
  {
    int integer;
    int boolean;
    char *string;
    void *function;
    struct CLOSURE* c;
  } v;
} VALUE;

typedef struct binding
{
  TOKEN *name;
  VALUE *val;
  struct binding *next;
} BINDING;

typedef struct frame
{
  BINDING *bindings;
  struct frame *next;
} FRAME;

typedef struct closure{
  FRAME* env;
  NODE* code;
} CLOSURE;



// typedef struct symbol_table {
// 	int env_size;
// 	struct value **values;
// 	struct symbol_table *static_link;
// 	int nested_level;
// } symbol_table;


enum op {plus,minus,multiply,divide,ge_op,le_op,ne_op, eq_op,less_than,greater_than,
       retrn, load, store, none, assignment, proc, endproc,label,go_to, if_then};   


typedef struct tac { //MIGHT HAVE TO CHANGE THIS TO MAKE IT MORE EFFICIENT FOR OTHER FORMS OF TAC
  enum op op;
  TOKEN* src1;
  TOKEN* src2;
  TOKEN* dst;
  struct tac* src1_next_use; //next uses in block (useful for register allocation later)
  struct tac* src2_next_use;
  struct tac* dst_next_use; 
  struct tac* next;
  struct tac* prev; //useful in calculating next-uses (for register allocation later)
} TAC;


typedef struct bb{
  TAC* leader;
  struct bb* next_bb; //points to next basic block in basic block sequence
  // struct bb* prev_bb; //used for computing next-uses of variables later
}BB;

typedef struct mc {
  char* insn;
  struct mc* next;
} MC;

typedef struct reg_entry{
  char* reg_name;
  TOKEN* name;
  struct reg_entry* next;
}REGISTER;


// struct SYMBOLTABLE;

// typedef struct ar{
//   struct symbol_table* access_link; 
//   int pc; //caller's pc - needed?
//   int nested_depth;
// }AR;

// typedef struct symbol_table_entry{ //node for symbol table entry for an identifier
//   TOKEN* name;
//   int offset;
//   struct memory* address_desc; //address descriptor
//   struct symbol_table_entry* next; //points to next symbol table-entry in linked list
//   struct ar ar;
//   struct tac* next_use; //POINTER to TAC statement for next use of this particular variable
// }SYMB_ENTRY;

// typedef struct symbol_table{
//   struct ar* ar;
//   struct SYMB_ENTRY** symbtable; 
// }SYMBOLTABLE;

//get symbol table entry for given identifier
SYMB_ENTRY* my_lookup_table(char *s, SYMBOLTABLE* symbol_table)
{
    int	h = hash(s);
    SYMB_ENTRY* a = symbol_table->symbtable[h];
    TOKEN *ans;
    while (a!=NULL) {
      if(a->name!=NULL){
        if (strcmp(a->name->lexeme, s)==0) return a;
      }
      a = a->next;
    }
    symbol_table->symbtable[h] = malloc(sizeof(SYMB_ENTRY));
    a = symbol_table->symbtable[h];
    ans = new_token(IDENTIFIER);
    ans->lexeme = (char*)malloc(1+strlen(s));
    strcpy(ans->lexeme, s);
    a->name = ans;
    a->offset = offset+4; //incrementing offset for memory location.
    offset+=4;
    return a;
}

TAC* icg_output; 

VALUE *interpret(NODE *tree, FRAME *e);
MC* new_mci(char* s);
TAC* mmc_icg(NODE* tree, SYMBOLTABLE* symbtable);
BINDING* init_global_env(NODE* tree);
void print_bindings(BINDING* bind);
NODE* get_args(NODE* param);


char *named(int t)
{
  static char b[100];
  if (isgraph(t) || t == ' ')
  {
    sprintf(b, "%c", t);
    return b;
  }
  switch (t)
  {
  default:
    return "???";
  case IDENTIFIER:
    return "id";
  case CONSTANT:
    return "constant";
  case STRING_LITERAL:
    return "string";
  case LE_OP:
    return "<=";
  case GE_OP:
    return ">=";
  case EQ_OP:
    return "==";
  case NE_OP:
    return "!=";
  case EXTERN:
    return "extern";
  case AUTO:
    return "auto";
  case INT:
    return "int";
  case VOID:
    return "void";
  case APPLY:
    return "apply";
  case LEAF:
    return "leaf";
  case IF:
    return "if";
  case ELSE:
    return "else";
  case WHILE:
    return "while";
  case CONTINUE:
    return "continue";
  case BREAK:
    return "break";
  case RETURN:
    return "return";
  }
}

void print_leaf(NODE *tree, int level)
{
  TOKEN *t = (TOKEN *)tree;
  int i;
  for (i = 0; i < level; i++)
    putchar(' ');
  if (t->type == CONSTANT)
    printf("%d\n", t->value);
  else if (t->type == STRING_LITERAL)
    printf("\"%s\"\n", t->lexeme);
  else if (t)
    puts(t->lexeme);
}

void print_tree0(NODE *tree, int level)
{
  int i;
  if (tree == NULL)
    return;
  if (tree->type == LEAF)
  {
    print_leaf(tree->left, level);
  }
  else
  {
    for (i = 0; i < level; i++)
      putchar(' ');
    printf("%s\n", named(tree->type));   
    /*       if (tree->type=='~') { */
    /*         for(i=0; i<level+2; i++) putchar(' '); */
    /*         printf("%p\n", tree->left); */
    /*       } */
    /*       else */
    print_tree0(tree->left, level + 2);
    print_tree0(tree->right, level + 2);
  }
}

void print_tree(NODE *tree)
{
  print_tree0(tree, 0);
}

char* tac_ops[] = {"plus","minus","multiply","divide","ge_op","le_op","ne_op","eq_op","less_than", "greater_than",
                   "retrn", "load", "store", "none", "assignment", "proc", "endproc", "label","go_to", "if_then"};

//print intermediate code. (tac)
void mmc_print_ic(TAC* i)
{
  for(;i!=NULL;i=i->next)
    if(i->src1){
    printf("%s %s %d %d %d %s %s \n",
	   tac_ops[i->op], // need to range check!
     i->dst->lexeme,
     i->dst->value,
     i->src1->value,
     i->src2->value,
     i->src1->lexeme,
     i->src2->lexeme);}
}

extern int yydebug;
extern NODE *yyparse(void);
extern NODE *ans;
extern void init_symbtable(void);


//function to generate new tac
TAC* new_tac(enum op op, TOKEN* src1, TOKEN* src2, TOKEN* dst)
{
  TAC* ans = (TAC*)malloc(sizeof(TAC));
  if (ans==NULL) {
    printf("Error! memory not allocated.");
    exit(0);
  }
  ans->op = op;
  ans->src1 = src1;
  ans->src2 = src2;
  ans->dst = dst;
  return ans;
}

TAC* empty_tac(){
  TAC* tac = malloc(sizeof(TAC));
  return tac;
}

char* new_temp_name(){
  char* t = malloc(6*sizeof(char));
  char number[5];
  sprintf(number, "%d", uniqueCountForTemporaries);
  snprintf(t, sizeof(t), "t%s", number);
  uniqueCountForTemporaries++;
  return t;
}

TOKEN* new_label(){
  TOKEN* label = malloc(sizeof(TOKEN));
  label->value = 0;
  char* t = malloc(6*sizeof(char));
  char number[5];
  sprintf(number, "%d", uniqueCountForLabels);
  snprintf(t, sizeof(t), "_L%s", number);
  uniqueCountForLabels++;
  label->lexeme = t;
  return label;
}

TOKEN* new_temp(NODE* tree, SYMBOLTABLE* symbtable){
  TOKEN* new_temporary = malloc(sizeof(TOKEN));
  new_temporary->lexeme = new_temp_name();
  new_temporary->value=0;
  new_temporary->next = NULL;
  if((tree)){
    new_temporary->value = ((TOKEN*)(tree->left))->value;
  }
  my_lookup_table(new_temporary, symbtable); //adds temporary to symbol table
  new_temporary->symbtable = symbtable; 
  return new_temporary;
}

TOKEN* new_var(NODE* tree, SYMBOLTABLE* symbtable){
  TOKEN* new_var = malloc(sizeof(TOKEN));
  new_var = (TOKEN*)tree;
  new_var->symbtable = symbtable;
  return new_var;
}

TOKEN* new_empty(){ //temporary empty token to allow for printing of TAC
  TOKEN* new_temporary = malloc(sizeof(TOKEN));
  new_temporary->lexeme = "empty";
  new_temporary->value=0;
  new_temporary->next = NULL;
  return new_temporary;
}



//generate TAC for each instruction
TAC* mmc_ic_instr(NODE* tree, enum op operator, SYMBOLTABLE* symbtable){ 
  TAC* result = malloc(sizeof(TAC));
  TAC* left = (TAC*)malloc(sizeof(TAC));
  TAC* right = (TAC*)malloc(sizeof(TAC));
  if (right==NULL || left==NULL) {
    printf("Error! memory not allocated.");
    exit(0);
  }    
  right = mmc_icg(tree->right, symbtable);
  left = mmc_icg(tree->left, symbtable);
  TAC* i=right;
  for(;i!=NULL;i=i->next){
    if(!i->next){
      i->next = left;
      break;
    }
  }
  TAC* j = left;
  for(;j!=NULL;j=j->next){
    if(!j->next){
      break;
    }
  }
  result = new_tac(operator, j->dst, i->dst, new_temp(NULL, symbtable));
  j->next = result;
  return right;
}

int count_args(NODE* tree){
  NODE* i = tree;
  int count = 0;
  for(;i!=NULL;i=i->right){
    if(i->type!= TYPE){
      count++;
    }
    if(!i->right){
      break;
    }
  }
  return count;
}

//generate TAC for function - OP is proc, DST is the name of the function 
//SRC 1 value is number of formal parameters
TAC* mmc_ic_proc(NODE* tree, SYMBOLTABLE* symbol_table){
  TAC* result = malloc(sizeof(TAC));
  result->op = proc;
  result->dst = malloc(sizeof(TOKEN));
  result->src1 = malloc(sizeof(TOKEN));
  result->src2 =  malloc(sizeof(TOKEN));

  result->dst->value = 0;
  result->src1->value = count_args(get_args(tree->left->right->right));
  result->src2->value = 0;
  result->dst->lexeme = ((TOKEN*)tree->left->right->left->left)->lexeme;
  my_lookup_table(result->dst, symbol_table); //add ptr to this proc's symbol table
  result->dst->symbtable = symbol_table;
  result->src1->lexeme = "n";
  result->src2->lexeme = "empty";
  return result;
}

//generate TAC for end of function
TAC* mmc_ic_endproc(NODE* tree, SYMB_ENTRY* symbtable){
  TAC* result = malloc(sizeof(TAC));
  result->op = endproc;
  result->dst = malloc(sizeof(TOKEN));
  result->src1 = malloc(sizeof(TOKEN));
  result->src2 =  malloc(sizeof(TOKEN));

  result->dst->value = 0;
  result->src1->value = 0;
  result->src2->value = 0;
  result->dst->lexeme = ((TOKEN*)tree->left->right->left->left)->lexeme;
  result->src1->lexeme = "empty";
  result->src2->lexeme = "empty";
  return result;
}
//make condition temporary
//make if tac
//make label for jump if condition true
//make label for jump if condition not true (if else exists)

TAC* mmc_ic_makeif(NODE* tree, SYMBOLTABLE* symbtable){
  //condition TAC
  TAC* condition = malloc(sizeof(TAC));

  switch(tree->left->type){
    case LESSTHAN:
      condition->op = less_than;
      break;
    case GREATERTHAN:
      condition->op = greater_than;
      break;
    case GE_OP:
      condition->op = ge_op;
      break;
    case LE_OP:
      condition->op = le_op;
      break;
    case EQ_OP:
      condition->op = eq_op;
      break;
    case NE_OP:
      condition->op = ne_op;
      break;
  }

  condition->dst = new_temp(NULL, symbtable);
  condition->src1 = new_empty();
  condition->src2 = new_empty();
  //IF tac
  TAC* result = malloc(sizeof(TAC));
  result->src1 = condition->dst; 
  result->src2 = condition->dst;

  //Deals with end of both if_then statement and if_then_else statements
  TAC* conditional_end = malloc(sizeof(TAC)); //LABEL that marks start of rest of code/end of the true part of if statement
  conditional_end->op = label;
  conditional_end->dst = new_label();
  conditional_end->src1 = new_empty();
  conditional_end->src2 = new_empty();
  TAC* end_jump = malloc(sizeof(TAC)); //JUMP that jumps to label that marks the resst of code/end of true part/start of false part
  end_jump->op = go_to;
  end_jump->dst = conditional_end->dst;
  end_jump->src1 = new_empty();
  end_jump->src2 = new_empty();
  //JUMP if true
  TAC* jump_true = malloc(sizeof(TAC));
  jump_true->op = label;
  jump_true->dst = new_label();
  jump_true->src1 = new_empty();
  jump_true->src2 = new_empty();
  
  if(tree->right->type == ELSE){
    result->op = if_then;
    //TRUE part of conditional statement
    jump_true->next = mmc_icg(tree->right->left, symbtable);
    TAC* jump_i = jump_true; //END of true jump for condition should go to conditional_end.
    for(;jump_i!=NULL;jump_i = jump_i->next){
      if(!jump_i->next){
        jump_i->next = conditional_end; //connects TAC. Marks end of true part of if_then_.
        break;
      }
    }
    end_jump->next = jump_true; //PUTS TRUE section of condition AFTER end JUMP, which is executed at the END of ELSE section.
    //FALSE part of conditional statement
    TAC* jump_false = malloc(sizeof(TAC));
    jump_false = mmc_icg(tree->right->right, symbtable);
    TAC* jump_j = jump_false; //END of true jump for condition should go to conditional_end.
    for(;jump_j!=NULL;jump_j = jump_j->next){
      if(!jump_j->next){
        jump_j->next = end_jump; //ADDS a JUMP to the end of the else part of tac. SO if ELSE part is run, TRUE part won't be run.
        break;
      }
    }
    result->next = jump_false; //next TAC is else part of statement. Won't be run if true, as there will be a jump to JUMP_TRUE label.
    result->dst = jump_true->dst;
  }
  else{ //if_then
    result->op = if_then;
    jump_true->next = mmc_icg(tree->right, symbtable); //if-then {'backpatch(E.truelist, M.quad)}
    TAC* jump_i = jump_true; //END of true jump for condition should go to conditional_end.
    for(;jump_i!=NULL;jump_i = jump_i->next){
      if(!jump_i->next){
        jump_i->next = conditional_end;
        break;
      }
    }
    end_jump->next = jump_true; //connects TAC in one sequence.
    result->dst = jump_true->dst; //E.truelist
    result->next = end_jump; //IF the condition isn't true, then the following TAC is a jump that skips the TAC for the true part of statement
  }
  condition->next = result;
  return condition;
}


// void append_tac(TAC* tac){
//   TAC* i = icg_output;
//   if(i!=NULL){
//     for(;i!=NULL;i=i->next){
//       if(!i->next){
//         i->next = tac;
//         break;
//       }
//     }
//   }
//   else{
//     icg_output = tac;
//   }

// }

//when you find an interior node for tree
//generate a temporary name - make function called newtemp that does this
//enter temporary name into symbol table as it is created
TAC* mmc_icg(NODE* tree, SYMBOLTABLE* symbtable)
{
  switch (tree->type) {
    case SEQUENCE:
    ;
      TAC* ans = (TAC*)malloc(sizeof(TAC));
      if (ans==NULL) {
        printf("Error! memory not allocated.");
        exit(0);
      }    
      ans = mmc_icg(tree->left, symbtable);
      TAC* i = ans;
      for(;i!=NULL;i=i->next){
        if(!i->next){
          i->next = mmc_icg(tree->right, symbtable);
          break;
        }
      }
      return ans;
      break;
    //numerical and comparison operators
   case PLUS:
      return (mmc_ic_instr(tree, plus, symbtable));
      break;
    case MINUS:
      return (mmc_ic_instr(tree, minus, symbtable));
      break;
    case DIVIDE:
      return (mmc_ic_instr(tree, divide, symbtable));
      break;
    case MULTIPLY:
      return (mmc_ic_instr(tree, multiply, symbtable));
      break;
    case NE_OP:
      return (mmc_ic_instr(tree, ne_op, symbtable));
      break;
    case EQ_OP:
      return (mmc_ic_instr(tree, eq_op, symbtable));
      break;
    case LE_OP:
      return (mmc_ic_instr(tree, le_op, symbtable));
      break;
    case GE_OP:
      return (mmc_ic_instr(tree, ge_op, symbtable));
      break;
    case LESSTHAN:
      return (mmc_ic_instr(tree, less_than, symbtable));
      break;
    case GREATERTHAN:
      return (mmc_ic_instr(tree, greater_than, symbtable));
      break;
    
    //conditionals
    case IF:
    ; 
      TAC* condition = malloc(sizeof(TAC));
      condition = mmc_ic_makeif(tree, symbtable);
      return condition;
      //return (make_if(tree));

    //assignments
    case EQUALS:
      ;
      TAC* value = (TAC*)malloc(sizeof(TAC));
      TAC* identifier = (TAC*)malloc(sizeof(TAC));
      if (value==NULL || identifier==NULL) {
        printf("Error! memory not allocated.");
        exit(0);
      }    

      value = mmc_icg(tree->right, symbtable);
      identifier = mmc_icg(tree->left, symbtable);
      TAC* j = value;
      for(;j!=NULL;j=j->next){
        if(!j->next){
          identifier->src1 = j->dst;
          j->next = identifier;
          break;
        }
      }
      return value;
      break;

    //unconditional jump - APPLYING FUNCTION
    case APPLY:
      break;

    case RETURN:
      ;
      TAC* ic_ret = (TAC*)malloc(sizeof(TAC));
      ic_ret->op = retrn;
      ic_ret->dst = new_empty();
      ic_ret->src1 = new_empty();
      ic_ret->src2 = new_empty();
      return ic_ret;
    
    //leafs
    case LEAF:
      if(tree->left->type == IDENTIFIER){
        SYMB_ENTRY* table_entry = my_lookup_table((TOKEN*) tree->left, symbtable); //makes a new symbol table entry for the identifier    
        table_entry->next_use = NULL; 
        return new_tac(assignment, new_empty(), new_empty(), new_var(tree->left, symbtable));
      } 
      // if(tree->left->type == MINUS){ //UMINUS doesn't exist in this language.
      //   return new_tac(uminus, NULL, NULL, new_temp((TOKEN*) tree->left));
      // }
      else{
        return new_tac(none, new_empty(), new_empty(), new_temp(tree, symbtable));
      }
      break;
    //declaration of variable
    case DECLARATION:
      ;
      if(tree->left->type == TYPE){
        return mmc_icg(tree->right, symbtable);
      }
      else{
        TAC* new_tac = empty_tac();
        new_tac = mmc_icg(tree->left, symbtable);
        TAC* k = new_tac;
        TAC* new_tac2 = empty_tac();
        new_tac2 = mmc_icg(tree->right,symbtable);
        for(;k!=NULL;k=k->next){
          if(!k->next){
            k->next = new_tac2; 
            break;
          }
        }
        return new_tac;
      }
      break;
    case FUNCTIONDEF:
    ;
      int previous_offset = offset;
      offset = 0; //ensure offset set to 0 for all names found in procedure
      SYMBOLTABLE* new_symbtable = malloc(sizeof(SYMBOLTABLE));
      new_symbtable->symbtable = (SYMB_ENTRY**)calloc(HASH_SIZE, sizeof(SYMB_ENTRY*)); //make a new symbol table for 
      new_symbtable->ar = malloc(sizeof(AR));
      new_symbtable->ar->access_link = symbtable->ar; //where the function was called from : changes later?
      new_symbtable->ar->nested_depth = symbtable->ar->nested_depth+1; //nested depth
      TAC* proc = malloc(sizeof(TAC));
      proc = mmc_ic_proc(tree, new_symbtable);
      if(tree->right){
        proc->next = mmc_icg(tree->right, new_symbtable); //pass in symbol table for lookup token
      }
      TAC* proc_i = proc;
      for(;proc_i!=NULL;proc_i=proc_i->next){
        if(proc_i->next == NULL){
          proc_i->next = mmc_ic_endproc(tree, new_symbtable);
          break;
        }
      }
      new_symbtable->size = offset;
      offset = previous_offset; //restoring offset for calling function.
      return proc; 
      break;
    case FUNCTIONDEC: //LEFT CHILD IS RETURN TYPE //RIGHT CHILD IS FUNCTION DEFINITION

    case FUNCTIONPARAM:


  default:
    printf("unknown type code %d (%p) in mmc_icg\n",tree->type,tree);
    return NULL;
  }
};

void bb_print(BB* bb){
  BB* b = bb;
  for(;b!=NULL;b=b->next_bb){
    printf("\nStart block\n");
    mmc_print_ic(b->leader);
    printf("\nend block\n");
    // if(bb->next_bb == NULL){
    //   break;
    // }
  }
}
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! NEED TO UPDATE FOR FUNCTION CALLS AS WELL !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
BB* bb_gen(TAC* tac){
  int flag = 1;
  TAC* i = tac;
  BB* bb_start = malloc(sizeof(BB));
  BB* cur_bb = bb_start;
  TAC* prev = NULL;
  while(i != NULL){
      TAC* j = i;
      while(j){
        if(j->next){
          if(j->next->op == label || j->next->op == proc){ //if statement is target of jump then it's a leader --> don't need flag, as this is a new leader either way.
            compute_next_uses(j); //if statement following j is a label, then j is the last TAC statement of the block.
            cur_bb->next_bb = malloc(sizeof(BB));
            TAC* new_leader = malloc(sizeof(TAC));
            new_leader = j->next; //new leader of next basic block
            j->next = NULL; //break off rest of TAC that isn't in this BB
            cur_bb->leader = i; //set this BB leader
            cur_bb = cur_bb->next_bb; //set cur pointer to next BB in BB sequence
            i = new_leader; //set i to start from new BB leader.
            flag = 0;
            break;
          }
          else if((j->op == if_then || j->op == go_to ||j->op == APPLY || j->op == endproc) && flag == 1){ //any statement that follows a goto or conditional goto is a leader
            compute_next_uses(j); //if j is a jump, then j is the last TAC statement of the block, so pass in compute next uses function
            cur_bb->next_bb = malloc(sizeof(BB));
            TAC* new_leader = malloc(sizeof(TAC));
            new_leader = j->next;
            j->next = NULL;
            cur_bb->leader = i;
            cur_bb = cur_bb->next_bb;
            i = new_leader;
            flag = 0; //flag ensures that the leader of the current block is not marked as the leader of the next block in an infinite loop.
            break;
          }
        }
        j->prev = prev;
        prev = j;
        j = j->next;
        if(j == NULL){
          flag = 3; //loop reached end of tac sequence without finding another bb
        }
      }
      if(flag == 3){ //need to exit while loop
        cur_bb->leader = i;
        compute_next_uses(prev);
        break;
      }
    flag = 1; //mark flag as one if the leader of current block is skipped.
  }
  return bb_start;
}

//function to compute the next uses of each identifier in each basic block
//based on the algorithm described by AHO, SETHI, ULLMAN - SECTION 9.5
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!MIGHT NEED TO BE CALLED FROM MCG, AS SYMBTABLE MAY BE OVERWRITTEN BY FOLLOWING TAC IN OTHER BLOCKS
void compute_next_uses(TAC* tac){
  TAC* i = tac; //i should be the last TAC of a basic block passed in from the bb_gen function
  for(;i!=NULL;i=i->prev){
    if(i->op <=14){ //if tac is of form x = y op z
      SYMB_ENTRY* dst_lookup = my_lookup_table(i->dst, i->dst->symbtable);
      i->dst_next_use = dst_lookup->next_use;
      dst_lookup->next_use = NULL; //set x to no next use
      if(i->src1 && i->src1->lexeme!="empty"){
        SYMB_ENTRY* src1_lookup = my_lookup_table(i->src1, i->dst->symbtable);
        i->src1_next_use = src1_lookup->next_use;
        src1_lookup->next_use = i; //set next uses of y to i
      }
      if(i->src2 && i->src2->lexeme!="empty"){
        SYMB_ENTRY* src2_lookup = my_lookup_table(i->src2, i->dst->symbtable);
        i->src2_next_use = src2_lookup->next_use; 
        src2_lookup->next_use = i; //set next uses of z to i
      }
    }
  }
}

//______________________________Machine Code Generator_____________________________________________

REGISTER reg_desc[27]; //register descriptor as a table of linked lists
//only 27, as I ignore reserved registers

char* get_reg_name(int x){
  switch(x){
    case 0:
      return "$v0";
      break;
    case 1:
      return "$v1";
      break;
    case 2:
      return "$a0";
      break;
    case 3:
      return "$a1";
      break;
    case 4:
      return "$a2";
      break;
    case 5:
      return "$a3";
      break;
    case 6:
      return "$t0";
      break;
    case 7:
      return "$t1";
      break;
    case 8:
      return "$t2";
      break;
    case 9:
      return "$t3";
      break;
    case 10:
      return "$t4";
      break;
    case 11:
      return "$t5";
      break;
    case 12:
      return "$t6";
      break;
    case 13:
      return "$t7";
      break;
    case 14:
      return "$s0";
      break;
    case 15:
      return "$s1";
      break;
    case 16:
      return "$s2";
      break;
    case 17:
      return "$s3";
      break;
    case 18:
      return "$s4";
      break;
    case 19:
      return "$s5";
      break;
    case 20:
      return "$s6";
      break;
    case 21:
      return "$s7";
      break;
    case 22:
      return "$t8";
      break;
    case 23:
      return "$t9";
      break;
    case 24:
      return "$gp";
      break;
    case 25:
      return "$sp";
      break;
    case 26:
      return "$fp";
      break;
    case 27:
      return "$ra";
      break;
  }
}

REGISTER* register_search(char* reg_name){ //NEED TO CHANGE THIS
  if(strstr(reg_name, "$v") != NULL){
    return &reg_desc[reg_name[2] - '0'];
  }
  else if(strstr(reg_name, "$a") != NULL){
    return &reg_desc[reg_name[2] - '0' + 2];
  }
  else if(strstr(reg_name, "$t") != NULL 
  && strstr(reg_name, "8") == NULL
  && strstr(reg_name, "9") == NULL){
    return &reg_desc[reg_name[2] - '0' + 6];
  }
  else if(strstr(reg_name, "$sp") != NULL){ //stack pointer
    return &reg_desc[25];
  }
  else if(strstr(reg_name, "$s") != NULL){
    return &reg_desc[reg_name[2] - '0' + 14];
  }
  else if(strstr(reg_name, "$t") != NULL){
    return &reg_desc[reg_name[2] - '0' + 22];
  }
  else if(strstr(reg_name, "$gp") != NULL){ 
    return &reg_desc[24];
  }
  else if(strstr(reg_name, "$fp") != NULL){ 
    return &reg_desc[26];
  }
  else if(strstr(reg_name, "$ra") != NULL){ 
    return &reg_desc[27];
  }
}

char* search_free_reg(){
  for(int i =6;i<13;i++){  //first set of t reg
    if(reg_desc[i].name == NULL){
      return(i);
    }
  }
  for(int i =22;i<23;i++){ //second set of t reg
    if(reg_desc[i].name == NULL){
      return(i);
    }
  }
  for(int i =14;i<21;i++){ //set of s reg
    if(reg_desc[i].name == NULL){
      return(i);
    }
  }
  return NULL;
}

char* search_free_for_frame(){
  for(int i =14;i<21;i++){ //set of s reg
    if(reg_desc[i].name == NULL){
      return(get_reg_name(i));
    }
  }
  return NULL;
}

//returns name of occupied register with the least number of names in
char* get_occupied_reg(){
  int min = 100;
  int index;

  for(int i =6;i<13;i++){ 
    int counter = 0;
    REGISTER* reg = reg_desc[i].next;
    if(reg == NULL){
      return get_reg_name(i);
    }
    else{
      for(;reg!=NULL;reg=reg->next){
        counter++;
      }
      if(counter<min){
        min = counter;
        index = i;
      }
    }

  }
  for(int i =22;i<23;i++){
    int counter = 0;
    REGISTER* reg = reg_desc[i].next;
    if(reg == NULL){
      return get_reg_name(i);
    }
    else{
      for(;reg!=NULL;reg=reg->next){
        counter++;
      }
      if(counter<min){
        min = counter;
        index = i;
      }
    }
  }
  return get_reg_name(index);
}

//struct needed because we may need to generate code to store data from register to memory
typedef struct getreg_out{
  char* reg;
  int flag;
}getreg_out;

//remove location from address desc for a given entry in symbol table
void add_address_desc_entry(SYMB_ENTRY* entry, char* location){
  MEMORY* i = entry->address_desc;
  for(;i!=NULL;i=i->next){
    if(i->next == NULL){
      MEMORY* t = malloc(sizeof(MEMORY));
      t->reg_name = location;
      i->next = t;
      break;
    }
  }
}

//remove location from address desc for a given entry in symbol table
void remove_address_desc_entry(SYMB_ENTRY* entry, char* location){
  MEMORY* i = entry->address_desc;
  for(;i!=NULL;i=i->next){
    if(i->reg_name == location){
      while(i->next->reg_name){ //removes location frmo register desc
        i->reg_name = i->next->reg_name; //shifts everything on the right of removed left.
        i=i->next;
      }
      break;
    }
  }
}


getreg_out* getreg(TAC* tac){
  getreg_out* reg_out = malloc(sizeof(getreg_out));
  char* x = tac->dst->lexeme;
  char* y = tac->src1->lexeme;
  SYMB_ENTRY* table_y = my_lookup_table(y, tac->src1->symbtable);
  MEMORY* address_y = table_y->address_desc;
  //condition 1 of getreg from AHO, SETHI, ULMAN algorithm
  if(address_y && strstr(address_y->reg_name, "$") != NULL){ //if y is in an address, and address is a register
    if(register_search(address_y->reg_name)->next == NULL){ //if address containing y contains no other variables
      if(tac->src1_next_use == NULL){ //if y has no next use
      printf("c");
        remove_address_desc_entry(table_y, address_y->reg_name);
        reg_out->reg = address_y->reg_name;
        reg_out->flag = 0;
        return reg_out;
      }
    }
  }
  //condition 2 of getreg from AHO, SETHI, ULMAN
  else if(search_free_reg() !=NULL){
    reg_out->reg = get_reg_name(search_free_reg());
    reg_out->flag = 0;
    return reg_out;
  }
  //condition 3 
  else if(my_lookup_table(x, tac->dst->symbtable)->next_use != NULL){
    printf("a");
    char* reg = get_occupied_reg(); 
    reg_out->reg = reg;
    reg_out->flag = 1; //need to store whatever is in this location.
    return reg_out;
  }
  else{
    SYMB_ENTRY* table_x = my_lookup_table(x, tac->dst->symbtable);
    reg_out->reg = table_x->offset = '0';
    reg_out->flag = 2; //flag indicates offset is being returned (Memory location of x)
    return reg_out;
  }

}



void add_reg_desc_entry(REGISTER* reg, TOKEN* name){
    REGISTER* i = reg;
  for(;i!=NULL;i=i->next){
    if(i->next == NULL){
      REGISTER* t = malloc(sizeof(REGISTER));
      t->name = name;
      t->reg_name = reg->reg_name;
      i->next = t;
      break;
    }
  }
}

//remove a token from a register in the register desc
void remove_reg_desc_entry(REGISTER* reg, TOKEN* name){
  REGISTER* i = reg;
  for(;i!=NULL;i=i->next){
    if(i->name == name){
      while(i->next){
        if(i->next->name){
          i = i->next->name;
        }
        i = i->next;
      }
      break;
    }
  }
}

//returns free $s register
char* get_free_reg_for_frame(){
  for(int i = 14; i<21;i++){
    if(reg_desc[i].name == NULL){
      return get_reg_name(i);
    }
  }
}

//finds MEMORY location for a given token. 
//(Assumes that all variables that are nonlocal that are being used have been assigned some address already and this has been logged in the address descriptor)
char* search_address_desc(TOKEN* name){
  SYMB_ENTRY* entry = my_lookup_table(name->lexeme, name->symbtable);
  MEMORY* cur_address = entry->address_desc;
  while(strstr(cur_address->reg_name, "$") != NULL){ //find something that isnt a register
    cur_address = cur_address->next;
  }
  return cur_address->reg_name;
}

//symbol_table is the symbol table for the current call.
//hence if nested depth is different, then the variable is a variable from the enclosing proc or beyond.
//stores all names held in a register in their correct memory locations.
MC* store_from_reg(REGISTER* reg, SYMBOLTABLE* symbol_table){
  REGISTER* i = reg;
  MC* mc_instr_head = malloc(sizeof(MC));
  MC* mc_instr_tail = mc_instr_head;
  for(;i!=NULL;i=i->next){
    MC* mc_instr = malloc(sizeof(MC));
    char* instr;
    if(i->name->symbtable->ar->nested_depth != symbol_table->ar->nested_depth){ //non-local
      instr = ("sw %s, %d($sp)", i->reg_name, -4*(i->name->symbtable->ar->nested_depth-symbol_table->ar->nested_depth)); //decrement stack pointer to find correct frame
    }
    else{
      SYMB_ENTRY* entry = my_lookup_table(i->name->lexeme, i->name->symbtable);
      instr = ("sw %s, %d($fp)", i->reg_name, entry->offset);
    }
    mc_instr = new_mci(instr);
    mc_instr_tail = mc_instr;
    if(i->next){
      mc_instr_tail->next = malloc(sizeof(MC));
      mc_instr_tail = mc_instr_tail->next;
    }
  }
  return mc_instr_head;
}


void mmc_print_mc(MC* i)
{
  for(;i!=NULL;i=i->next){
    if(i->next == NULL){
      printf("%s\n", i->insn);
      break;
    }
    printf("%s\n", i->insn);
  }
}

//save whatever is in fp in some register
MC* save_and_store_frame(SYMBOLTABLE* symbol_table){
  MC* allocate_frame = new_mci("li $v0, 9"); //load dynamic allocation syscall
  char* frameinstr1 = malloc(15 * sizeof(char));
  sprintf(frameinstr1, "li $a0, %d", symbol_table->size + 4);
  MC* allocate_frame2 = new_mci(frameinstr1); //allocate bytes equal to nested depth
  MC* allocate_frame3 = new_mci("syscall"); //syscall to allocate memory
  //allocated heap is now in v0
  MC* store_frame1 = new_mci("sw $v0, $fp"); //save frame pointer to newly allocate memory located in $v0
  char* fp = search_free_for_frame();
  char* frameinstr2 = malloc(15 * sizeof(char));
  char* ra = malloc(15 * sizeof(char));
  sprintf(ra, "la $ra, %s", fp);
  MC* load_ra = new_mci(ra);
  sprintf(frameinstr2, "move $v0, %s", fp);
  MC* store_frame2 = new_mci(frameinstr2); //move address stored in $v0 to some free registers
  symbol_table->ar->fp = fp; //stores register holding address holding fp of old frame in AR 
  store_frame2->next = load_ra; //puts address of caller in $ra
  store_frame1->next = store_frame2;
  allocate_frame3->next = store_frame1;
  allocate_frame2->next = allocate_frame3;
  allocate_frame->next = allocate_frame2;

  return allocate_frame;
}

MC* allocate_new_frame(SYMBOLTABLE* symbol_table){
  MC* allocate_frame = new_mci("li $v0, 9"); //load dynamic allocation syscall
  char* framinstr1 = malloc(15 * sizeof(char));
  sprintf(framinstr1, "li $a0, %d", symbol_table->size + 4);
  MC* allocate_frame2 = new_mci(framinstr1); //allocate bytes equal to size of variables in proc
  MC* allocate_frame3 = new_mci("syscall"); //syscall to allocate memory

  //store allocated address in frame pointer. i.e., update frame pointer to point to base of address
  MC* allocate_frame4 = new_mci("move $v0, $fp");
  allocate_frame->next = allocate_frame2;
  allocate_frame2->next = allocate_frame3;
  allocate_frame3->next = allocate_frame4;
  return allocate_frame;
}

//attaches instructions b to end of a
MC* join_instructions(MC* a, MC* b){
  MC* i = a;
  if(b == NULL){
    return a;
  }
  else if(a == NULL){
    return b;
  }
  for(;i!=NULL;i=i->next){
    if(!i->next){
      break;
    }
  }
  i->next = b;
  return a;
}

MC* mmc_mc_plus(TAC* i, SYMBOLTABLE* symbol_table){
  getreg_out* r_out= getreg(i);
  char * L = r_out->reg;
  char* add = malloc(15*sizeof(char));

  char* load1 = malloc(15* sizeof(char));
  SYMB_ENTRY* op1 = my_lookup_table(i->src1->lexeme, i->src1->symbtable);
  sprintf(load1, "lw %s, %d(%s)", i->src1->lexeme, op1->offset,i->src1->symbtable->ar->fp);
  char* load2 = malloc(15* sizeof(char));
  MC* load_op1 = new_mci(load1);
  SYMB_ENTRY* op2 = my_lookup_table(i->src2->lexeme, i->src2->symbtable);
  sprintf(load2, "lw %s, %d(%s)", i->src2->lexeme, op2->offset,i->src2->symbtable->ar->fp);
  MC* load_op2 = new_mci(load2);

  //add instruction

  sprintf(add, "add %s, %s, %s", L, i->src1->lexeme, i->src2->lexeme);
  MC* addinstr = new_mci(add);

  load_op2->next = addinstr;
  load_op1->next = load_op2;


  if(r_out->flag == 1){ //need to save whatever is in L in correct memory location
    char* save_reg_instr = malloc(sizeof(char));
    SYMB_ENTRY* entry = my_lookup_table(i->dst->lexeme, i->dst->symbtable);
    sprintf(save_reg_instr, "sw %s, %d(%s)", L, entry->offset, entry->ar.fp); 
    MC* save_reg = new_mci(save_reg_instr);
    save_reg->next = load_op1;
    return save_reg;
  }
  return load_op1;
}

MC* mmc_mc_minus(TAC* i, SYMBOLTABLE* symbol_table){
  getreg_out* r_out= getreg(i);
  char * L = r_out->reg;
  char* add = malloc(15*sizeof(char));

  char* load1 = malloc(15* sizeof(char));
  SYMB_ENTRY* op1 = my_lookup_table(i->src1->lexeme, i->src1->symbtable);
  sprintf(load1, "lw %s, %d(%s)", i->src1->lexeme, op1->offset,i->src1->symbtable->ar->fp);
  char* load2 = malloc(15* sizeof(char));
  MC* load_op1 = new_mci(load1);
  SYMB_ENTRY* op2 = my_lookup_table(i->src2->lexeme, i->src2->symbtable);
  sprintf(load2, "lw %s, %d(%s)", i->src2->lexeme, op2->offset,i->src2->symbtable->ar->fp);
  MC* load_op2 = new_mci(load2);

  //add instruction

  sprintf(add, "sub %s, %s, %s", L, i->src1->lexeme, i->src2->lexeme);
  MC* addinstr = new_mci(add);

  load_op2->next = addinstr;
  load_op1->next = load_op2;


  if(r_out->flag == 1){ //need to save whatever is in L in correct memory location
    char* save_reg_instr = malloc(sizeof(char));
    SYMB_ENTRY* entry = my_lookup_table(i->dst->lexeme, i->dst->symbtable);
    sprintf(save_reg_instr, "sw %s, %d(%s)", L, entry->offset, entry->ar.fp); 
    MC* save_reg = new_mci(save_reg_instr);
    save_reg->next = load_op1;
    return save_reg;
  }
  return load_op1;
}

MC* mmc_mc_divide(TAC* i, SYMBOLTABLE* symbol_table){
  getreg_out* r_out= getreg(i);
  char * L = r_out->reg;
  char* add = malloc(15*sizeof(char));

  char* load1 = malloc(15* sizeof(char));
  SYMB_ENTRY* op1 = my_lookup_table(i->src1->lexeme, i->src1->symbtable);
  sprintf(load1, "lw %s, %d(%s)", i->src1->lexeme, op1->offset,i->src1->symbtable->ar->fp);
  char* load2 = malloc(15* sizeof(char));
  MC* load_op1 = new_mci(load1);
  SYMB_ENTRY* op2 = my_lookup_table(i->src2->lexeme, i->src2->symbtable);
  sprintf(load2, "lw %s, %d(%s)", i->src2->lexeme, op2->offset,i->src2->symbtable->ar->fp);
  MC* load_op2 = new_mci(load2);

  //add instruction

  sprintf(add, "div %s, %s, %s", L, i->src1->lexeme, i->src2->lexeme);
  MC* addinstr = new_mci(add);

  load_op2->next = addinstr;
  load_op1->next = load_op2;


  if(r_out->flag == 1){ //need to save whatever is in L in correct memory location
    char* save_reg_instr = malloc(sizeof(char));
    SYMB_ENTRY* entry = my_lookup_table(i->dst->lexeme, i->dst->symbtable);
    sprintf(save_reg_instr, "sw %s, %d(%s)", L, entry->offset, entry->ar.fp); 
    MC* save_reg = new_mci(save_reg_instr);
    save_reg->next = load_op1;
    return save_reg;
  }
  return load_op1;
}

MC* mmc_mc_multiply(TAC* i, SYMBOLTABLE* symbol_table){
  getreg_out* r_out= getreg(i);
  char * L = r_out->reg;
  char* add = malloc(15*sizeof(char));

  char* load1 = malloc(15* sizeof(char));
  SYMB_ENTRY* op1 = my_lookup_table(i->src1->lexeme, i->src1->symbtable);
  sprintf(load1, "lw %s, %d(%s)", i->src1->lexeme, op1->offset,i->src1->symbtable->ar->fp);
  char* load2 = malloc(15* sizeof(char));
  MC* load_op1 = new_mci(load1);
  SYMB_ENTRY* op2 = my_lookup_table(i->src2->lexeme, i->src2->symbtable);
  sprintf(load2, "lw %s, %d(%s)", i->src2->lexeme, op2->offset,i->src2->symbtable->ar->fp);
  MC* load_op2 = new_mci(load2);

  //multiply instruction

  sprintf(add, "mult %s, %s", i->src1->lexeme, i->src2->lexeme);
  char* load_result = malloc(15*sizeof(char));
  char* load_result2 = malloc(15*sizeof(char));
  MC* addinstr = new_mci(add);


  //load result from floating point registers
  sprintf(load_result, "mfhi %s", i->src1->lexeme);
  sprintf(load_result2, "mflo %s", i->src2->lexeme);
  MC* lr1 = new_mci(load_result);
  MC* lr2 = new_mci(load_result2);

  lr1->next = lr2;
  addinstr->next = lr1;
  load_op2->next = addinstr;
  load_op1->next = load_op2;
  
  //update symbol table
  SYMB_ENTRY* entry = my_lookup_table(i->dst->lexeme, i->dst->symbtable);
  add_address_desc_entry(entry, i->src1->lexeme);
  add_address_desc_entry(entry, i->src2->lexeme);

  if(r_out->flag == 1){ //need to save whatever is in L in correct memory location
    char* save_reg_instr = malloc(sizeof(char));
    sprintf(save_reg_instr, "sw %s, %d(%s)", L, entry->offset, entry->ar.fp); 
    MC* save_reg = new_mci(save_reg_instr);
    save_reg->next = load_op1;
    return save_reg;
  }
  return load_op1;
}

MC* mmc_mc_assign(TAC* i, SYMBOLTABLE* symbol_table){
  char* assignment = malloc(15* sizeof(char));
  SYMB_ENTRY* entry = malloc(sizeof(SYMB_ENTRY));
  entry = my_lookup_table(i->dst->lexeme, i->dst->symbtable);
  if(strcmp(i->src1->lexeme,"empty")!= 0){
    sprintf(assignment, "move %d(%s), $%s",entry->offset ,i->dst->symbtable->ar->fp, i->src1->lexeme);
    // sprintf(assignment, "move %s, $%s",i->dst->symbtable->ar->fp, i->src1->lexeme);
    MC* instr = new_mci(assignment);
    return instr;
  }
  else{
    return NULL;
  }
}

MC* mmc_mc_load(TAC* i, SYMBOLTABLE* symbol_table){
  char* load = malloc(15*sizeof(char));
  sprintf(load, "li $%s, %d", i->dst->lexeme, i->dst->value);
  MC* none = new_mci(load);
  return none;
}

//mips machine code machine code generator
MC* mmc_mcg(TAC* i, SYMBOLTABLE* symbol_table)
{
  int n1 = 0;
  if (i==NULL) return NULL;
  switch (i->op) {
    case proc:
    ;
      char* proc_label = malloc(15*sizeof(char));
      sprintf(proc_label, "%s:", i->dst->lexeme);
      MC* proc_begin = malloc(sizeof(MC));
      proc_begin = new_mci(proc_label);
      //save and store old frame and update the symbol_table for this frame
      proc_begin->next = save_and_store_frame(symbol_table);
      
      //Make a new activation record for current frame and point to activation record of caller
      AR* new_ar = malloc(sizeof(AR));
      new_ar->access_link = symbol_table->ar;
      new_ar->nested_depth = symbol_table->ar->nested_depth+1;
      new_ar->fp = "$fp";

      i->dst->symbtable->ar = new_ar; //sets the activation record of the symbol table of the function to be this new ar
      
      // //allocate new space for this new frame
      MC* new_frame = allocate_new_frame(i->dst->symbtable);

      return join_instructions(join_instructions(proc_begin, new_frame), mmc_mcg(i->next, i->dst->symbtable));
      break;
    case endproc:
    ;
      //endproc
      //need to save all of the important registers
      MC* end_proc = malloc(sizeof(MC));
      end_proc = new_mci(("jr $ra")); //return to previous function call.
      return join_instructions(end_proc, mmc_mcg(i->next, i->dst->symbtable));
      break;
    ;

    case none:
      //need to update reg desc and address desc
      return join_instructions(mmc_mc_load(i, symbol_table), mmc_mcg(i->next, i->dst->symbtable));
      break;
    ;
      
    case plus: //form x = y op z
    ;
      return join_instructions(mmc_mc_plus(i, symbol_table), mmc_mcg(i->next, i->dst->symbtable));
      break;
    case multiply:
    ; 
      return join_instructions(mmc_mc_multiply(i, symbol_table), mmc_mcg(i->next, i->dst->symbtable));
      break;
    case assignment:
    ; 
      return join_instructions(mmc_mc_assign(i, symbol_table), mmc_mcg(i->next, i->dst->symbtable));
      break;
      //return join_instructions(mmc_mc_assign(i, symbol_table, mmc_mcg(i->next, i->dst->symbtable)));
  default:
    printf("unknown type code %d (%p) in mmc_mcg\n",i->op,i);
    return NULL;
  }
}

//creates new machine code instruction
MC* new_mci(char* s)
{
  MC* ans = (MC*)malloc(sizeof(MC));
  if (ans==NULL) {
    printf("Error! memory not allocated.");
    exit(0);
  }
  ans->insn = s;
  ans->next = NULL;
  return ans;
}


// ________________________________________________________________
//Interpeter


FRAME* make_frame(BINDING* binding, FRAME* next){
  FRAME* newFrame = malloc(sizeof(FRAME));
  newFrame->bindings = binding;
  newFrame->next = next;
  return newFrame;
}

//
BINDING* make_binding(NODE* formalParam, VALUE* arg, BINDING* bindings){
  BINDING* newBinding = malloc(sizeof(BINDING));
  newBinding->name = (TOKEN*)formalParam;
  newBinding->val = arg;
  newBinding->next = bindings;
  return newBinding; 
}

//when you call a function extend frame
FRAME* extend_frame ( FRAME* env ,NODE* ids , NODE* args ) {
  FRAME* newenv = make_frame (NULL , NULL); // note env = NULL
  BINDING * bindings = NULL ;
  NODE* ip;
  NODE* ap;
  for (ip = ids, ap = args ;( ip != NULL ) && (ap != NULL ); ip=ip->right , ap=ap->right ) {
    bindings = make_binding (ip ,interpret (ap , env), bindings );
  }
  newenv -> bindings = bindings;
  return newenv ;
}

//finds closure associated with function called and returns it
CLOSURE* name_method(TOKEN* name, FRAME* env){
  CLOSURE* newClosure = malloc(sizeof(CLOSURE));
  BINDING* i=env->bindings;
  for(;i!=NULL;i=i->next){
    if(i->name == name && i->val->v.c){ //checks for correct name in bindings and that the binding is the function (has a closure)
      newClosure = i->val->v.c;
      break;
    }
    if(!i->next){
      env = env->next;
      i = env->bindings;
    }
  }
  return newClosure;
}

NODE* get_args(NODE* param){
  if(param == NULL){
    return NULL;
  }
  switch(param->type){
    case LISTING:
    ;
      NODE* node_l = malloc(sizeof(NODE));
      node_l = get_args(param->left); 
      NODE* node_r = malloc(sizeof(NODE));
      node_r = get_args(param->right);
      node_r->right = node_l;
      // NODE* i = node_l;
      // for(;i!=NULL;i=i->right){
      //   if(!i->right){
      //     i->right = node_r;
      //     break;
      //   }
      // }
      return node_r;
    case DECLARATION:
    ;
      NODE* node = malloc(sizeof(NODE));
      node = param->right->left;
      return node;
      break;
    case LEAF:
    ;
      return param;
  }
}


NODE* formals(CLOSURE* f){
  NODE* param = f->code; //starts from D
  NODE* formal_param = malloc(sizeof(NODE));
  param = param->left->right->right; //now at first parameter
  formal_param = get_args(param);
  return formal_param;
}

VALUE* lexical_call_method(TOKEN* name, NODE* args, FRAME* env){
  CLOSURE* f = name_method(name,env); //finds closure associated with function called
  FRAME* newenv = extend_frame(env, formals(f), args); //extends frame of called function by zipping formal params and args
  newenv->next = f->env; //attach old env to extended env -> lexical call will return 'latest' version of variables
  return interpret(f->code->right, newenv); //interpret the function called
}


VALUE *add_method(NODE *l, NODE *r, FRAME *e)
{
  VALUE *op1 = interpret(l, e);
  VALUE *op2 = interpret(r, e);
  op1->v.integer = op1->v.integer + op2->v.integer;
  return (op1);
}

VALUE *sub_method(NODE *l, NODE *r, FRAME *e)
{
  VALUE *op1 = interpret(l, e);
  VALUE *op2 = interpret(r, e);
  op1->v.integer = op1->v.integer - op2->v.integer;
  return (op1);
}

VALUE *multiply_method(NODE *l, NODE *r, FRAME *e)
{
  VALUE *op1 = interpret(l, e);
  VALUE *op2 = interpret(r, e);
  op1->v.integer = op1->v.integer * op2->v.integer;
  return (op1);
}

VALUE *divide_method(NODE *l, NODE *r, FRAME *e)
{
  VALUE *op1 = interpret(l, e);
  VALUE *op2 = interpret(r, e);
  op1->v.integer = op1->v.integer / op2->v.integer;
  return (op1);
}

//creates new binding
VALUE* declare_binding(TOKEN* t, FRAME* e){
  BINDING* bindings = e->bindings;
  BINDING* new = malloc(sizeof(BINDING));
  if (new!=0){
    new->name = t;
    new->val = (VALUE*)0;
    new->next = bindings;
    e->bindings = new;
    return (VALUE*)0;
  }
  perror("binding allocation failed");
}

//finds some binding of a token t in a frame
VALUE* find_binding(TOKEN* t, FRAME* frame){
  BINDING* bindings= malloc(sizeof(BINDING));
  while(frame!=NULL){
    bindings = frame->bindings;
    while(bindings!=NULL){
      if(strcmp(bindings->name->lexeme,t->lexeme)==0){
        return bindings->val;
      }
      bindings = bindings->next;
    }
    frame = frame->next;
  }
  perror("unbound variable in binding");
}

//binds some value to a variable in a frame
VALUE* add_binding(TOKEN* t, FRAME* frame, VALUE* value){
  while(frame!=NULL){
    BINDING* bindings = frame->bindings;
    while(bindings!=NULL){
      if(bindings->name ==t){
        bindings->val = value;
        return value;
      }
      bindings = bindings->next;
    }
    frame = frame->next;
  }
  perror("unbound variable in frame");
}

//Bindings for all global variables
BINDING* init_global_var(NODE* tree){
  if(!tree){
    return NULL;
  }
  else{
    switch(tree->type){
      case LISTING:
        ; 
          BINDING* new_binding = malloc(sizeof(BINDING));
          new_binding = init_global_var(tree->left);
          new_binding->next = init_global_var(tree->right);
          return new_binding;
          break;
      case EQUALS:
        ;
          BINDING* new_binding1 = malloc(sizeof(BINDING));
          new_binding1->name = (TOKEN*) tree->left->left;
          new_binding1->val = interpret(tree->right, NULL);
          return new_binding1;
      case LEAF:
        ;
          BINDING* new_binding2 = malloc(sizeof(BINDING));
          new_binding2->name = (TOKEN*)tree->left;
          VALUE* val1 = malloc(sizeof(VALUE));
          new_binding2->val = val1;
          new_binding2->val->v.integer = 0; //TEMPORARY !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
          return (new_binding2);
    }
  }
}

BINDING* init_global_env(NODE* tree){
  if (!tree)
  {
    return NULL;
  }
  else
  {
    //printf("%d", tree->type);
    switch (tree->type)
    {
    case FUNCTIONDEF: //D
    ;
        VALUE* new_env = malloc(sizeof(VALUE));
        CLOSURE* new_closure = malloc(sizeof(CLOSURE));
        BINDING* new_binding = malloc(sizeof(BINDING));
        new_closure->code = tree;
        new_closure->env= NULL;
        new_env->v.c = new_closure; 
        //bindings to add to the global environment
        new_binding->val = new_env;
        new_binding->name = (TOKEN*)tree->left->right->left->left;
        return new_binding; 
    case DECLARATION: //~
    ;
      if(tree->left->type != TYPE){
        BINDING* new_binding1 = malloc(sizeof(BINDING));
        BINDING* new_binding2 = malloc(sizeof(BINDING));
        new_binding1 = init_global_env(tree->left);
        new_binding2 = init_global_env(tree->right);
        BINDING* i=new_binding1;
        for(;i!=NULL;i=i->next){
          if(!i->next){
            i->next = new_binding2;
            break;
          }
        }
          return new_binding1;
        }
      else{
        BINDING* new_binding1 = malloc(sizeof(BINDING));
        new_binding1 = init_global_var(tree->right);
        return(new_binding1);
      }
      break;
  }
}
}

//testing purposes - prints all bindings of some binding
void print_bindings(BINDING* bind){
  BINDING* i=bind;
  for(;i!=NULL;i=i->next){
    printf("%s", i->name->lexeme);
    printf("%d", i->val->v.integer);
    if(!i->next){
      break;
    }
  }
}

CLOSURE* find_main(FRAME* env){
  BINDING* i=env->bindings;
  for(;i!=NULL;i=i->next){
    if(strcmp(i->name->lexeme, "main") == 0){
        return i->val->v.c;
    }
    if(!i->next){
      printf("No main function found");
      perror("No main function");
      break;
    }
  }
}

VALUE* setup_interpreter(NODE* tree){
  BINDING* global_env_bindings = malloc(sizeof(BINDING));
  global_env_bindings = init_global_env(tree);
  FRAME* global_env = malloc(sizeof(FRAME));
  global_env->bindings = global_env_bindings;
  // print_bindings(global_env_bindings);
  CLOSURE* main_closure = find_main(global_env);
  NODE* main_fn = malloc(sizeof(NODE));
  main_fn = main_closure->code->right; //code starts from D.
  return interpret(main_fn, global_env);
}


//INTERPRETER: Interprets recursively
VALUE *interpret(NODE *tree, FRAME *e)
{
  if (!tree)
  {
    return NULL;
  }
  else
  {
    //printf("%d", tree->type);
    switch (tree->type)
    {
    case SEQUENCE: //;
      interpret(tree->left, e);
      interpret(tree->right, e);
      break;
    case FUNCTIONDEF: //D
    ;
      // BINDING* new_binding = malloc(sizeof(BINDING));
      // new_binding = init_global_env(tree);
      // //add binding to end of frame
      // BINDING* i=e->bindings;
      // for(;i!=NULL;i=i->next){
      //   if(!i->next){
      //     print_bindings(i);
      //     i->next = new_binding;
      //     break;
      //   }
      // }

        VALUE* new_env = malloc(sizeof(VALUE));
        CLOSURE* new_closure = malloc(sizeof(CLOSURE));
        BINDING* new_binding = malloc(sizeof(BINDING));
        new_closure->code = tree;
        new_closure->env= e;
        new_env->v.c = new_closure; 
        //bindings to add to the global environment
        new_binding->val = new_env;
        new_binding->name = (TOKEN*)tree->left->right->left->left;

        BINDING* i=e->bindings;
        for(;i!=NULL;i=i->next){
          if(!i->next){
            i->next = new_binding;
            break;
          }
        }
      break;
    case FUNCTIONDEC: //d
      interpret(tree->right, e);
      break;
    case DECLARATION: //~
      if(tree->left){
        if(tree->right->type == EQUALS){
          declare_binding((TOKEN*)(tree->right->left->left), e);
        }
        else{
          declare_binding((TOKEN*)(tree->right->left), e);
        }
      }
      interpret(tree->right, e);
      break;
    case FUNCTIONPARAM: //F
      interpret(tree->right, e);
    case APPLY: //calling a function : applying some function to some arguments
      ;
      NODE* actual_args = get_args(tree->right);
      return lexical_call_method((TOKEN*) tree->left->left, actual_args, e);
      break;
    case RETURN:
      return (interpret(tree->left, e));
      break;
    case FUNCTION:
      return NULL;
      break;
    case PLUS:
      return add_method(tree->left, tree->right, e);
      break;
    case MINUS:
      return sub_method(tree->left, tree->right, e);
      break;
    case MULTIPLY:
      return multiply_method(tree->left, tree->right, e);
      break;
    case DIVIDE:
      return divide_method(tree->left, tree->right, e);
      break;
    case EQUALS:
      add_binding((TOKEN*)tree->left->left, e, interpret(tree->right, e));
      break;
    case IF:
      if(tree->right->type == ELSE){
        if(interpret(tree->left, e)->v.boolean == TRUE){
          interpret(tree->right->left, e);
        }
        else{
          interpret(tree->right->right, e);
        }
      }
      else if(interpret(tree->left, e)->v.boolean == TRUE){
        interpret(tree->right, e);
      }
      break;
    case LESSTHAN:
    ;
      VALUE *lessThanCondition = malloc(sizeof(VALUE));
      if(lessThanCondition == NULL){
        exit(EXIT_FAILURE);
      }
      if(interpret(tree->left, e)->v.integer < interpret(tree->right, e)->v.integer){
        lessThanCondition->v.boolean = TRUE;
      }
      else{
        lessThanCondition->v.boolean = FALSE;
      }
      return lessThanCondition;
      break;
    case GREATERTHAN:
    ;
      VALUE *greaterThanCondition = malloc(sizeof(VALUE));
      if(greaterThanCondition == NULL){
        exit(EXIT_FAILURE);
      }
      if(interpret(tree->left, e)->v.integer > interpret(tree->right, e)->v.integer){
        greaterThanCondition->v.boolean = TRUE;
      }
      else{
        greaterThanCondition->v.boolean = FALSE;
      }
      return greaterThanCondition;
      break;
    case GE_OP:
    ;
      VALUE *GECondition = malloc(sizeof(VALUE));
      if(GECondition == NULL){
        exit(EXIT_FAILURE);
      }
      if(interpret(tree->left, e)->v.integer >= interpret(tree->right, e)->v.integer){
        GECondition->v.boolean = TRUE;
      }
      else{
        GECondition->v.boolean = FALSE;
      }
      return GECondition;
      break;
    case LE_OP:
    ;
      VALUE *LECondition = malloc(sizeof(VALUE));
      if(LECondition == NULL){
        exit(EXIT_FAILURE);
      }
      if(interpret(tree->left, e)->v.integer <= interpret(tree->right, e)->v.integer){
        LECondition->v.boolean = TRUE;
      }
      else{
        LECondition->v.boolean = FALSE;
      }
      return LECondition;
      break;
    case EQ_OP:
    ;
      VALUE *EQCondition = malloc(sizeof(VALUE));
      if(EQCondition == NULL){
        exit(EXIT_FAILURE);
      }
      if(interpret(tree->left, e)->v.integer == interpret(tree->right, e)->v.integer){
        EQCondition->v.boolean = TRUE;
      }
      else{
        EQCondition->v.boolean = FALSE;
      }
      return EQCondition;
      break;

    case NE_OP:
    ;
      VALUE *NECondition = malloc(sizeof(VALUE));
      if(NECondition == NULL){
        exit(EXIT_FAILURE);
      }
      if(interpret(tree->left, e)->v.integer != interpret(tree->right, e)->v.integer){
        NECondition->v.boolean = TRUE;
      }
      else{
        NECondition->v.boolean = FALSE;
      }
      return NECondition;
      break;
    
    case LEAF:;
      TOKEN *t = (TOKEN *)(tree->left);
      VALUE *val = malloc(sizeof(VALUE));
      if (t->type == IDENTIFIER){
        val = find_binding((TOKEN*)tree->left, e);
        if (val == NULL)
        {
          exit(EXIT_FAILURE);
        }
      }
      else{
        val->v.integer = t->value;
      }
      val->type = LEAF; //might change?
      return val;
      break;
    }
  }
}


int main(int argc, char **argv)
{
  NODE *tree;
  VALUE *result;
  FRAME* e;
  if (argc > 1 && strcmp(argv[1], "-d") == 0)
    yydebug = 1;
  init_symbtable();
  SYMBOLTABLE* global_symboltable = malloc(sizeof(SYMBOLTABLE));
  global_symboltable->symbtable = (SYMB_ENTRY**)calloc(HASH_SIZE, sizeof(SYMB_ENTRY*)); //Make SYMB_table
  global_symboltable->ar = malloc(sizeof(AR));
  global_symboltable->ar->access_link = NULL;
  global_symboltable->ar->nested_depth = 0;
  printf("--C COMPILER\n");
  yyparse();
  tree = ans;
  printf("parse finished with %p\n", tree);
  // print_tree(tree);

  // result = setup_interpreter(tree);
  // printf("\n%d\n", result->v.integer);
  // VALUE* test = setup_interpreter(tree);
  // if(test == NULL){
  //   printf("yes");
  // }
  TAC* t = mmc_icg(tree, global_symboltable);
  // mmc_print_ic(t);
  // BB* bb_seq = bb_gen(t);
  // printf("done");
  // bb_print(bb_seq);
  MC* m = mmc_mcg(t, global_symboltable);
  mmc_print_mc(m);
  return 0;
}
