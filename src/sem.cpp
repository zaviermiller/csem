#include <stdio.h>
#include <string.h>

extern "C" {
    #include "cc.h"
    #include "scan.h"
    #include "semutil.h"
    #include "sem.h"
    #include "sym.h"
}

#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include <utility>
#include <cstdlib>
#include <memory>
#include <cctype>
#include <cstdio>
#include <string>
#include <vector>
#include <list>
#include <map>

# define MAXLOOPNEST 50
# define MAXLABELS 50
# define MAXGOTOS 50

using std::map;
using std::string;
using std::vector;
using llvm::outs;
using llvm::Type;
using llvm::Value;
using llvm::Module;
using llvm::Function;
using llvm::Constant;
using llvm::IRBuilder;
using llvm::ArrayType;
using llvm::BasicBlock;
using llvm::AllocaInst;
using llvm::BranchInst;
using llvm::Instruction;
using llvm::LLVMContext;
using llvm::ConstantInt;
using llvm::ConstantFP;
using llvm::GlobalValue;
using llvm::IntegerType;
using llvm::PointerType;
using llvm::FunctionType;
using llvm::GlobalVariable;
using llvm::ConstantAggregateZero;

extern int formalnum;                         /* number of formal arguments */
extern struct id_entry* formalvars[MAXLOCS];  /* entries for parameters */
extern int localnum;                          /* number of local variables  */
extern struct id_entry* localvars[MAXLOCS];   /* entries for local variables */

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

template<typename T, typename... Args>
std::unique_ptr<T> make_unique(Args&&... args) {
  return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
}

static int label_index = 0;
int relexpr = 0;

struct loopscope {
  struct sem_rec* breaks;
  struct sem_rec* conts;
} lscopes[MAXLOOPNEST];

static int looplevel = 0;
struct loopscope *looptop = (struct loopscope *) NULL;

struct labelnode {
   const char *id;    /* label string    */
   BasicBlock *bb;    /* basic block for label */
} labels[MAXLABELS];

struct gotonode {
   const char *id;     /* label string in goto statement */
   BranchInst *branch; /* branch to temporary label */
} gotos[MAXGOTOS];     /* list of gotos to be backpatched */

int numgotos = 0;    /* number of gotos to be backpatched */
int numlabelids = 0; /* total label ids in function */

string type_string(int t) {
  string s;
  if (t & T_INT) s += "INT,";
  if (t & T_STR) s += "STRING,";
  if (t & T_DOUBLE) s += "DOUBLE,";
  if (t & T_PROC) s += "FUNCTION,";
  if (t & T_ARRAY) s += "ARRAY,";
  if (t & T_ADDR) s += "ADDRESS,";
  if (t & T_LBL) s += "LABEL,";

  if (s == "") s = "NOT SET,";

  s.pop_back();

  return s;
}


int get_link_length(struct sem_rec *s) {
  int total = 0;
  for (; s->s_link; s = s->s_link) {
    total += 1;
  }

  return total;
}

// assumes that the sem_recs s_value is a ConstantInt
int extract_int_from_sem_rec(struct sem_rec *s) {
  ConstantInt *ci = llvm::dyn_cast<ConstantInt>((Value *)s->s_value);
  return ci->getValue().getSExtValue();
}

std::string new_label()
{
  return ("L" + std::to_string(label_index++));
}

BasicBlock*
create_tmp_label()
{
  return BasicBlock::Create(TheContext);
}

BasicBlock*
create_named_label(std::string label)
{
  Function *curr_func = Builder.GetInsertBlock()->getParent();
  BasicBlock *new_block = BasicBlock::Create(TheContext, label, curr_func);
  return new_block;
}

/*
 * convert an internal csem type (s_type or i_type) to an LLVM Type*
 */
Type *get_llvm_type(int type){
  switch( type &~(T_ARRAY|T_ADDR) ){
  case T_INT:
    return Type::getInt32Ty(TheContext);
    break;
  case T_DOUBLE:
    return Type::getDoubleTy(TheContext);
    break;
  default:
    fprintf(stderr,"get_llvm_type: invalid type %x\n", type);
    exit(1);
    break;
  }
}

/*
 * startloopscope - start the scope for a loop
 */
void
startloopscope()
{
   looptop = &lscopes[looplevel++];
   if (looptop > lscopes+MAXLOOPNEST) {
      fprintf(stderr, "loop nest too great\n");
      exit(1);
   }
   looptop->breaks = (struct sem_rec *) NULL;
   looptop->conts = (struct sem_rec *) NULL;
}

/*
 * endloopscope - end the scope for a loop
 */
void
endloopscope()
{
  looplevel--;
  looptop--;
}


/*
 * Global allocations. Globals are initialized to 0.
 */
void
global_alloc (struct id_entry *p, int width)
{
  string name(p->i_name);
  GlobalVariable *var;
  Type *type;
  Constant *init;

  if (p->i_type & T_ARRAY) {
    type = ArrayType::get(get_llvm_type(p->i_type), width);
    init = ConstantAggregateZero::get(type);
  }
  else {
    type = get_llvm_type(p->i_type);
    init = ConstantInt::get(get_llvm_type(T_INT), 0);
  }

  TheModule->getOrInsertGlobal(name, type);
  var = TheModule->getNamedGlobal(name);
  var->setInitializer(init);
  p->i_value = (void*) var;
}


/*
 * backpatch - set temporary labels in the sem_rec to real labels
 *
 * LLVM API calls:
 *
 * llvm::dyn_cast<BranchInst>(Value*)
 * BranchInst::getNumSuccessors()
 * BranchInst::getSuccessor(unsigned)
 * BranchInst::setSuccessor(unsigned, BasicBlock*)
 */
void backpatch(struct sem_rec *rec, void *bb)
{
  unsigned i;
  BranchInst *br_inst;

  // loop through each record in the list
  for (; rec; rec = rec->s_link) {
    if ((br_inst = llvm::dyn_cast<BranchInst>((Value *) rec->s_value))) {
      for (i = 0; i < br_inst->getNumSuccessors(); i++) {
        if (br_inst->getSuccessor(i) == ((BasicBlock *) rec->s_bb)) {
          br_inst->setSuccessor(i, (BasicBlock *)bb);
        }
      }
    } else {
      fprintf(stderr, "sem: backpatch with non-branch instruction\n");
      exit(1);
    }
  }
}

/*
 * backpatch_conts - backpatch all continue statements
 */
void backpatch_conts(void *bb) {
  struct sem_rec *rec;
  for(rec = looptop->conts; rec; rec = rec->s_link) {
    backpatch(rec, bb);
  }
}

/*
 * backpatch_breaks - backpatch all break statements
 */
void backpatch_breaks(void *bb) {
  struct sem_rec *rec;
  for(rec = looptop->breaks; rec; rec = rec->s_link) {
    backpatch(rec, bb);
  }
}


/*
 * create_binary_op - uses the LLVM API to create binary operations according to the passed operator
 *
 * The method uses the following API calls:
 * IRBuilder::CreateAdd(Value *, Value *)
 * IRBuilder::CreateFAdd(Value *, Value *)
 * IRBuilder::CreateSub(Value *, Value *)
 * IRBuilder::CreateFSub(Value *, Value *)
 * IRBuilder::CreateMul(Value *, Value *)
 * IRBuilder::CreateFMul(Value *, Value *)
 * IRBuilder::CreateSDiv(Value *, Value *)
 * IRBuilder::CreateFDiv(Value *, Value *)
 * IRBuilder::CreateSRem(Value *, Value *)
 * IRBuilder::CreateAnd(Value *, Value *)
 * IRBuilder::CreateOr(Value *, Value *)
 * IRBuilder::CreateXOr(Value *, Value *)
 * IRBuilder::CreateShl(Value *, Value *)
 * IRBuilder::CreateAShr(Value *, Value *)
 */

struct sem_rec *create_binary_op(string op, struct sem_rec *a, struct sem_rec *b) {
  Value *a_val, *b_val, *val;

  // cast a or b to double if one is a double and one is an int
  if (a->s_type & T_INT && b->s_type & T_DOUBLE) {
    a = cast(a, T_DOUBLE);
  } else if (a->s_type & T_DOUBLE && b->s_type & T_INT) {
    b = cast(b, T_DOUBLE);
  }

  a_val = (Value *)a->s_value;
  b_val = (Value *)b->s_value;

  if (a->s_type & T_INT && b->s_type & T_INT) {
    // int only operations
    if (op == "+")
      val = Builder.CreateAdd(a_val, b_val);
    else if (op == "-")
      val = Builder.CreateSub(a_val, b_val);
    else if (op == "*")
      val = Builder.CreateMul(a_val, b_val);
    else if (op == "/")
      val = Builder.CreateSDiv(a_val, b_val);
    else if (op == "%")
      val = Builder.CreateSRem(a_val, b_val);
    else if (op == "&")
      val = Builder.CreateAnd(a_val, b_val);
    else if (op == "|")
      val = Builder.CreateOr(a_val, b_val);
    else if (op == "^")
      val = Builder.CreateXor(a_val, b_val);
    else if (op == "<<")
      val = Builder.CreateShl(a_val, b_val);
    else if (op == ">>")
      val = Builder.CreateAShr(a_val, b_val);
    else {
      // didn't recognize the operation
      fprintf(stderr, "sem: invalid int operator '%s'\n", op.c_str());
      exit(1);
    }
    return s_node(val, a->s_type);
  } else if (a->s_type & T_DOUBLE && b->s_type & T_DOUBLE) {
    if (op == "+")
      val = Builder.CreateFAdd(a_val, b_val);
    else if (op == "-")
      val = Builder.CreateFSub(a_val, b_val);
    else if (op == "*")
      val = Builder.CreateFMul(a_val, b_val);
    else if (op == "/")
      val = Builder.CreateFDiv(a_val, b_val);
    else {
      fprintf(stderr, "sem: invalid double operator '%s'\n", op.c_str());
      exit(1);
    }
    return s_node(val, a->s_type);
  }

  fprintf(stderr, "sem: invalid types for binary operation (%s) & (%s)\n", type_string(a->s_type).c_str(), type_string(b->s_type).c_str());
  exit(1);
}


/*
 * call - procedure invocation
 *
 * Grammar:
 * lval -> ID '(' ')'            { $$ = call($1, (struct sem_rec *) NULL); }
 * lval -> ID '(' exprs ')'      { $$ = call($1, $3); }
 *
 * LLVM API calls:
 * makeArrayRef(vector<Value*>)
 * IRBuilder::CreateCall(Function *, ArrayRef<Value*>)
 */
struct sem_rec*
call(char *f, struct sem_rec *args)
{
  vector<Value *> vals;
  struct sem_rec *arg = args;
  Value *val;
  struct id_entry *entry;

  // put all args into a vector
  while (arg != NULL) {
    vals.insert(vals.begin(), (Value *)arg->s_value);
    arg = arg->s_link;
  }

  // lookup the function we are calling
  entry = lookup(f, 0);

  if (entry == NULL) {
    fprintf(stderr, "sem: function '%s' not defined\n", f);
    exit(1);
  }


  val = Builder.CreateCall((Function *)entry->i_value, makeArrayRef(vals));

  return s_node(val, T_PROC);
}


/*
 * ccand - logical and
 *
 * Grammar:
 * cexpr -> cexpr AND m cexpr     { $$ = ccand($1, $3, $4); }
 *
 * LLVM API calls:
 * None
 */
struct sem_rec*
ccand(struct sem_rec *e1, void *m, struct sem_rec *e2)
{
  backpatch(e1->s_true, m);

  return node(
          (void *)NULL,
          (void *)NULL,
          0,
          (struct sem_rec *)NULL,
          e2->s_true,
          merge(e1->s_false, e2->s_false)
         );
}

/*
 * ccexpr - convert arithmetic expression to logical expression
 *
 * Grammar:
 * cexpr -> expr                  { $$ = ccexpr($1); }
 *
 * LLVM API calls:
 *
 * IRBuilder::CreateICmpNE(Value *, Value *)
 * IRBuilder::CreateFCmpONE(Value *, Value *)
 * IRBuilder::CreateCondBr(Value *, BasicBlock *, BasicBlock *)
 */
struct sem_rec*
ccexpr(struct sem_rec *e)
{
  BasicBlock *tmp_true, *tmp_false;
  Value *val;

  tmp_true = create_tmp_label();
  tmp_false = create_tmp_label();
  val = Builder.CreateCondBr((Value *)e->s_value, tmp_true, tmp_false);

  return (node((void *)NULL, (void *)NULL, 0, (struct sem_rec *)NULL,
            (node(
              val, tmp_true, 0, (struct sem_rec *)NULL,
              (struct sem_rec *)NULL, (struct sem_rec *)NULL)),
            (node(
              val, tmp_false, 0, (struct sem_rec *)NULL,
              (struct sem_rec *)NULL, (struct sem_rec *)NULL))
         ));
}

/*
 * ccnot - logical not
 *
 * Grammar:
 * cexpr -> NOT cexpr             { $$ = ccnot($2); }
 *
 * LLVM API calls:
 * None
 */
struct sem_rec*
ccnot(struct sem_rec *e)
{
  return node((void *)NULL, (void *)NULL, 0, (struct sem_rec *)NULL, e->s_false, e->s_true);
}

/*
 * ccor - logical or
 *
 * Grammar:
 * cexpr -> cexpr OR m cexpr      { $$ = ccor($1, $3, $4); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
struct sem_rec*
ccor(struct sem_rec *e1, void *m, struct sem_rec *e2)
{
  backpatch(e1->s_false, m);

  return node(
          (void *)NULL,
          (void *)NULL,
          0,
          (struct sem_rec *)NULL,
          merge(e1->s_true, e2->s_true),
          e2->s_false
         );
}

/*
 * con - constant reference in an expression
 *
 * Grammar:
 * expr -> CON                   { $$ = con($1); }
 *
 * LLVM API calls:
 * ConstantInt::get(Type*, int)
 */
struct sem_rec*
con(const char *x)
{
  struct id_entry *entry;

  if ((entry = lookup(x, 0)) == NULL) {
    entry = install (x, 0);
    entry->i_type = T_INT;
    entry->i_scope = GLOBAL;
    entry->i_defined = 1;
  }

  entry->i_value = (void *) ConstantInt::get(get_llvm_type(T_INT), std::stoi(x));

  return (s_node((void *)entry->i_value, entry->i_type));
}

/*
 * dobreak - break statement
 *
 * Grammar:
 * stmt -> BREAK ';'                { dobreak(); }
 *
 * LLVM API calls:
 * None -- but uses n
 */
void
dobreak()
{
  struct sem_rec *n_rec;

  n_rec = n();
  looptop->breaks = merge(looptop->breaks, n_rec);
}

/*
 * docontinue - continue statement
 *
 * Grammar:
 * stmt -> CONTINUE ';'              { docontinue(); }
 *
 * LLVM API calls:
 * None -- but uses n
 */
void
docontinue()
{
  struct sem_rec *n_rec;

  n_rec = n();
  looptop->conts = merge(looptop->conts, n_rec);
}

/*
 * dodo - do statement
 *
 * Grammar:
 * stmt -> DO m s lblstmt WHILE '(' m cexpr ')' ';' m
 *                { dodo($2, $7, $8, $11); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void
dodo(void *loop_body, void *cond_stmt, struct sem_rec *cond, void *exit)
{
  backpatch(cond->s_true, loop_body);
  backpatch(cond->s_false, exit);
  backpatch_breaks(exit);
  backpatch_conts(cond_stmt);
}

/*
 * dofor - for statement
 *
 * Grammar:
 * stmt -> FOR '(' expro ';' m cexpro ';' m expro n ')' m s lblstmt n m
 *               { dofor($5, $6, $8, $10, $12, $15, $16); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void
dofor(void *cond_stmt, struct sem_rec *cond, void *iter_stmt, struct sem_rec *n1, void *loop_body,
  struct sem_rec *n2, void *exit)
{
  backpatch(cond->s_true, loop_body);
  backpatch(cond->s_false, exit);
  backpatch(n2, iter_stmt);
  backpatch(n1, cond_stmt);
  backpatch_breaks(exit);
  backpatch_conts(cond_stmt);
}

/*
 * dogoto - goto statement
 *
 * Grammar:
 * stmt -> GOTO ID ';'              { dogoto($2); }
 *
 * LLVM API calls:
 * IRBuilder::CreateBr(BasicBlock *)
 */
void
dogoto(char *id)
{
  BasicBlock *lbl;
  struct gotonode *g;

  lbl = create_tmp_label();

  g = &gotos[numgotos++];
  g->id = (char *)malloc(strlen(id) + 1); // do i need to malloc here?
  strcpy((char *)g->id, id);
  g->branch = Builder.CreateBr(lbl);
}

/*
 * doif - one-arm if statement
 *
 * Grammar:
 * stmt -> IF '(' cexpr ')' m lblstmt m
 *         { doif($3, $5, $7); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void
doif(struct sem_rec *cond, void *m1, void *m2)
{
  backpatch(cond->s_true, m1);
  backpatch(cond->s_false, m2);
}

/*
 * doifelse - if then else statement
 *
 * Grammar:
 * stmt -> IF '(' cexpr ')' m lblstmt ELSE n m lblstmt m
 *                { doifelse($3, $5, $8, $9, $11); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void
doifelse(struct sem_rec *cond, void *true_body, struct sem_rec *n,
  void *false_body, void *exit)
{
  backpatch(cond->s_true, true_body);
  backpatch(cond->s_false, false_body);
  backpatch(n, exit);
}

/*
 * doret - return statement
 *
 * Grammar:
 * stmt -> RETURN ';'            { doret((struct sem_rec *) NULL); }
 * stmt -> RETURN expr ';'       { doret($2); }
 *
 * LLVM API calls:
 * IRBuilder::CreateRetVoid();
 * IRBuilder::CreateRet(Value *);
 */
void
doret(struct sem_rec *e)
{
  if (!e) {
    Builder.CreateRetVoid();
    return;
  }

  Builder.CreateRet((Value *)e->s_value);
}

/*
 * dowhile - while statement
 *
 * Grammar:
 * stmt -> WHILE '(' m cexpr ')' m s lblstmt n m
 *                { dowhile($3, $4, $6, $9, $10); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void
dowhile(void *cond_stmt, struct sem_rec *cond, void *loop_body,
  struct sem_rec *n, void *exit)
{
  backpatch(cond->s_true, loop_body);
  backpatch(cond->s_false, exit);
  backpatch(n, cond_stmt);
  backpatch_breaks(exit);
  backpatch_conts(cond_stmt);
}

/*
 * exprs - form a list of expressions
 *
 * Grammar:
 * exprs -> exprs ',' expr        { $$ = exprs($1, $3); }
 *
 * LLVM API calls:
 * None
 */
struct sem_rec*
exprs(struct sem_rec *l, struct sem_rec *e)
{
  e->s_link = l;
  return e;
}

/*
 * fhead - beginning of function body
 *
 * Grammar:
 * fhead -> fname fargs '{' dcls  { fhead($1); }
 */
void
fhead(struct id_entry *p)
{
  Type *func_type, *var_type;
  Value *arr_size;
  vector<Type*> func_args;
  GlobalValue::LinkageTypes linkage;
  FunctionType *FT;
  Function *F;
  BasicBlock *B;
  int i;
  struct id_entry *v;

  /* get function return type */
  func_type = get_llvm_type(p->i_type);

  /* get function argument types */
  for (i = 0; i < formalnum; i++) {
    func_args.push_back(get_llvm_type(formalvars[i]->i_type));
  }

  FT = FunctionType::get(func_type, makeArrayRef(func_args), false);

  /* linkage is external if function is main */
  linkage = (strcmp(p->i_name, "main") == 0) ?
            Function::ExternalLinkage :
            Function::InternalLinkage ;

  F = Function::Create(FT, linkage, p->i_name, TheModule.get());
  p->i_value = (void*) F;


  B = BasicBlock::Create(TheContext, "", F);
  Builder.SetInsertPoint(B);

  /*
   * Allocate instances of each parameter and local so they can be referenced
   * and mutated.
   */
  i = 0;
  for (auto &arg : F->args()) {

    v = formalvars[i++];
    arg.setName(v->i_name);
    var_type = get_llvm_type(v->i_type);
    arr_size = (v->i_width > 1) ?
               (ConstantInt::get(get_llvm_type(T_INT), v->i_width)) :
               NULL;

    v->i_value = Builder.CreateAlloca(var_type, arr_size, arg.getName());
    Builder.CreateStore(&arg, (Value*)v->i_value);
  }

  /* Create the instance of stack memory for each local variable */
  for (i = 0; i < localnum; i++) {
    v = localvars[i];
    var_type = get_llvm_type(v->i_type);
    arr_size = (v->i_width > 1) ?
               (ConstantInt::get(get_llvm_type(T_INT), v->i_width)) :
               NULL;

    v->i_value = Builder.CreateAlloca(var_type, arr_size, std::string(v->i_name));
  }
}

/*
 * fname - function declaration
 *
 * Grammar:
 * fname -> type ID               { $$ = fname($1, $2); }
 * fname -> ID                    { $$ = fname(T_INT, $1); }
 */
struct id_entry*
fname(int t, char *id)
{
  struct id_entry *entry = lookup(id, 0);

  // add function to hash table if it doesn't exist
  if (!entry) {
    entry = install(id, 0);
  }

  // cannot have two functions of the same name
  if (entry->i_defined) {
    yyerror("cannot declare function more than once");
  }

  entry->i_type = t;
  entry->i_scope = GLOBAL;
  entry->i_defined = true;

  // need to enter the block to let hash table do internal work
  enterblock();
  // then need to reset argument count variables

  formalnum = 0;
  localnum = 0;

  return entry;
}

struct labelnode *get_label_node(const char *id) {
  struct labelnode l;
  int i;

  for (i = 0; i < numlabelids; i++) {
    l = labels[i];
    if (strcmp(id, l.id) == 0) {
      return &labels[i];
    }
  }
  return NULL;
}

/*
 * ftail - end of function body
 *
 * Grammar:
 * func -> fhead stmts '}'       { ftail(); }
 */
void
ftail()
{
  int i;
  struct gotonode g;
  struct labelnode *l;

  // backpatch goto statements
  for (i = 0; i < numgotos; i++) {
    g = gotos[i];
    l = get_label_node(g.id);
    if (l == NULL) {
      return;
    }
    // backpatch(g.branch, l->bb);
    g.branch->setSuccessor(0, l->bb);
  }

  // do clean up
  numgotos = 0;
  numlabelids = 0;
  leaveblock();
}

/*
 * id - variable reference
 *
 * Grammar:
 * lval -> ID                    { $$ = id($1); }
 * lval -> ID '[' expr ']'       { $$ = indx(id($1), $3); }
 *
 * LLVM API calls:
 * None
 */
struct sem_rec*
id(char *x)
{
  struct id_entry *entry;

  if ((entry = lookup(x, 0)) == NULL) {
    yyerror("undeclared identifier");
    entry = install(x, -1);
    entry->i_type = T_INT;
    entry->i_scope = LOCAL;
    entry->i_defined = 1;
  }

  return s_node((void *)entry->i_value, entry->i_type | T_ADDR);
}

/*
 * indx - subscript
 *
 * Grammar:
 * lval -> ID '[' expr ']'       { $$ = indx(id($1), $3); }
 *
 * LLVM API calls:
 * makeArrayRef(vector<Value*>)
 * IRBuilder::CreateGEP(Type, Value *, ArrayRef<Value*>)
 */
struct sem_rec*
indx(struct sem_rec *x, struct sem_rec *i)
{
  vector<Value *> indices;
  indices.push_back((Value *)i->s_value);

  Value *val = Builder.CreateGEP(get_llvm_type(x->s_type), (Value *)x->s_value, makeArrayRef(indices));

  return s_node(val, (x->s_type &(~T_ARRAY)));
}

/*
 * labeldcl - process a label declaration
 *
 * Grammar:
 * labels -> ID ':'                { labeldcl($1); }
 * labels -> labels ID ':'         { labeldcl($2); }
 *
 * NOTE: All blocks in LLVM must have a terminating instruction (i.e., branch
 * or return statement -- fall-throughs are not allowed). This code must
 * ensure that each block ends with a terminating instruction.
 *
 * LLVM API calls:
 * IRBuilder::GetInsertBlock()
 * BasicBlock::getTerminator()
 * IRBuilder::CreateBr(BasicBlock*)
 * IRBuilder::SetInsertPoint(BasicBlock*)
 * BranchInst::setSuccessor(unsigned, BasicBlock*)
 */
void
labeldcl(const char *id)
{
  BasicBlock *bb;
  BranchInst *bi;
  struct labelnode *l;
  string id_str = string(id);

  id_str = "userlbl_" + id_str;

  bb = create_named_label(id_str);

  if (Builder.GetInsertBlock()->getTerminator() == NULL) {
    bi = Builder.CreateBr(bb);
    bi->setSuccessor(0, bb);
  }

  Builder.SetInsertPoint(bb);

  // create record in labels list
  l = &labels[numlabelids++];
  l->bb = bb;
  l->id = (char *)malloc(strlen(id) + 1);
  strcpy((char *)l->id, id);
}

/*
 * m - generate label and return next temporary number
 *
 * NOTE: All blocks in LLVM must have a terminating instruction (i.e., branch
 * or return statement -- fall-throughs are not allowed). This code must
 * ensure that each block ends with a terminating instruction.
 *
 * LLVM API calls:
 * IRBuilder::GetInsertBlock()
 * BasicBlock::getTerminator()
 * IRBuilder::CreateBr(BasicBlock*)
 * IRBuilder::SetInsertPoint(BasicBlock*)
 */
void*
m ()
{
  BasicBlock *bb;
  string label = new_label();
  bb = create_named_label(label);

  if (Builder.GetInsertBlock()->getTerminator() == NULL) {
    Builder.CreateBr(bb);
  }

  Builder.SetInsertPoint(bb);
  return (void *)bb;
}

/*
 * n - generate goto and return backpatch pointer
 *
 * LLVM API calls:
 * IRBuilder::CreateBr(BasicBlock *)
 */
struct sem_rec *n()
{
  BasicBlock *bb;
  Value *val;
  bb = create_tmp_label();

  val = Builder.CreateBr(bb);

  return node((void *)val, (void *)bb, 0, (struct sem_rec *)NULL, (struct sem_rec *)NULL, (struct sem_rec *)NULL);
}

/*
 * op1 - unary operators
 *
 * LLVM API calls:
 * IRBuilder::CreateLoad(Type, Value *)
 * IRBuilder::CreateNot(Value *)
 * IRBuilder::CreateNeg(Value *)
 * IRBuilder::CreateFNeg(Value *)
 */
struct sem_rec*
op1(const char *op, struct sem_rec *y)
{
  struct sem_rec *rec;
  if (*op == '@') {
    if (!(y->s_type & T_ARRAY)) {
      y->s_type &= ~T_ADDR;
      rec = s_node(Builder.CreateLoad(get_llvm_type(y->s_type), (Value *)y->s_value), y->s_type);
    }
  } else if (*op == '~') {
    rec = s_node(Builder.CreateNot((Value *)y->s_value), y->s_type);
  } else if (*op == '-') {
    if (y->s_type & T_DOUBLE) {
      rec = s_node(Builder.CreateFNeg((Value *)y->s_value), y->s_type);
    } else if (y->s_type & T_INT) {
      rec = s_node(Builder.CreateNeg((Value *)y->s_value), y->s_type);
    }
  } else {
    yyerror("invalid unary operatory");
  }

  return rec;
}

/*
 * op2 - arithmetic operators
 *
 * No LLVM API calls, but most functionality is abstracted to a separate
 * method used by op2, opb, and set.
 */
struct sem_rec*
op2(const char *op, struct sem_rec *x, struct sem_rec *y)
{
  return create_binary_op(op, x, y);
}

/*
 * opb - bitwise operators
 *
 * No LLVM API calls, but most functionality is abstracted to a separate
 * method used by op2, opb, and set. The comment above op2 lists the LLVM API
 * calls for this method.
 */
struct sem_rec*
opb(const char *op, struct sem_rec *x, struct sem_rec *y)
{
  return create_binary_op(op, x, y);
}

/*
 * rel - relational operators
 *
 * Grammar:
 * cexpr -> expr EQ expr          { $$ = rel((char*) "==", $1, $3); }
 * cexpr -> expr NE expr          { $$ = rel((char*) "!=", $1, $3); }
 * cexpr -> expr LE expr          { $$ = rel((char*) "<=", $1, $3); }
 * cexpr -> expr GE expr          { $$ = rel((char*) ">=", $1, $3); }
 * cexpr -> expr LT expr          { $$ = rel((char*) "<",  $1, $3); }
 * cexpr -> expr GT expr          { $$ = rel((char*) ">",  $1, $3); }
 *
 * LLVM API calls:
 * IRBuilder::CreateICmpEq(Value *, Value *)
 * IRBuilder::CreateFCmpOEq(Value *, Value *)
 * IRBuilder::CreateICmpNE(Value *, Value *)
 * IRBuilder::CreateFCmpONE(Value *, Value *)
 * IRBuilder::CreateICmpSLT(Value *, Value *)
 * IRBuilder::CreateFCmpOLT(Value *, Value *)
 * IRBuilder::CreateICmpSLE(Value *, Value *)
 * IRBuilder::CreateFCmpOLE(Value *, Value *)
 * IRBuilder::CreateICmpSGT(Value *, Value *)
 * IRBuilder::CreateFCmpOGT(Value *, Value *)
 * IRBuilder::CreateICmpSGE(Value *, Value *)
 * IRBuilder::CreateFCmpOGE(Value *, Value *)
 */
struct sem_rec*
rel(const char *op, struct sem_rec *x, struct sem_rec *y)
{
  Value *val = NULL;

  // cast as needed
  if (x->s_type == T_INT && y->s_type == T_DOUBLE) {
    x = cast(x, T_DOUBLE);
  } else if (x->s_type == T_DOUBLE && y->s_type == T_INT) {
    y = cast(y, T_DOUBLE);
  }

  if (*op == '<') {
    if (x->s_type == T_INT && y->s_type == T_INT) {
      val = Builder.CreateICmpSLT((Value *)x->s_value, (Value *)y->s_value);
    } else if (x->s_type == T_DOUBLE && y->s_type == T_DOUBLE) {
      val = Builder.CreateFCmpOLT((Value *)x->s_value, (Value *)y->s_value);
    }
  } else if (*op == '>') {
    if (x->s_type == T_INT && y->s_type == T_INT) {
      val = Builder.CreateICmpSGT((Value *)x->s_value, (Value *)y->s_value);
    } else if (x->s_type == T_DOUBLE && y->s_type == T_DOUBLE) {
      val = Builder.CreateFCmpOGT((Value *)x->s_value, (Value *)y->s_value);
    }
  } else if (strncmp(op, "==", 2) == 0) {
    if (x->s_type == T_INT && y->s_type == T_INT) {
      val = Builder.CreateICmpEQ((Value *)x->s_value, (Value *)y->s_value);
    } else if (x->s_type == T_DOUBLE && y->s_type == T_DOUBLE) {
      val = Builder.CreateFCmpOEQ((Value *)x->s_value, (Value *)y->s_value);
    }
  } else if (strncmp(op, "!=", 2) == 0) {
    if (x->s_type == T_INT && y->s_type == T_INT) {
      val = Builder.CreateICmpNE((Value *)x->s_value, (Value *)y->s_value);
    } else if (x->s_type == T_DOUBLE && y->s_type == T_DOUBLE) {
      val = Builder.CreateFCmpONE((Value *)x->s_value, (Value *)y->s_value);
    }
  } else if (strncmp(op, "<=", 2) == 0) {
    if (x->s_type == T_INT && y->s_type == T_INT) {
      val = Builder.CreateICmpSLE((Value *)x->s_value, (Value *)y->s_value);
    } else if (x->s_type == T_DOUBLE && y->s_type == T_DOUBLE) {
      val = Builder.CreateFCmpOLE((Value *)x->s_value, (Value *)y->s_value);
    }
  } else if (strncmp(op, ">=", 2) == 0) {
    if (x->s_type == T_INT && y->s_type == T_INT) {
      val = Builder.CreateICmpSGE((Value *)x->s_value, (Value *)y->s_value);
    } else if (x->s_type == T_DOUBLE && y->s_type == T_DOUBLE) {
      val = Builder.CreateFCmpOGE((Value *)x->s_value, (Value *)y->s_value);
    }
  }

  return ccexpr(s_node((void *)val, T_INT));
}

/*
 * cast - cast value to a different type
 *
 * LLVM API calls:
 * IRBuilder::CreateSIToFP(Value *, Type *)
 * IRBuilder::CreateFPToSI(Value *, Type *)
 */
struct sem_rec*
cast (struct sem_rec *y, int t)
{
  Value *val;

  if (y->s_type == t) return y;

  if (y->s_type & T_INT && t & T_DOUBLE) {
    val = Builder.CreateSIToFP((Value *)y->s_value, get_llvm_type(T_DOUBLE));
    t |= y->s_type;
    t &= ~T_INT;
  } else if (y->s_type & T_DOUBLE && t & T_INT) {
    val = Builder.CreateFPToSI((Value *)y->s_value, get_llvm_type(T_INT));
    t |= y->s_type;
    t &= ~T_DOUBLE;
  } else {
    fprintf(stderr, "sem: invalid type cast (%s -> %s)\n", type_string(y->s_type).c_str(), type_string(t).c_str());
    exit(1);
  }
  return s_node((void *)val, t);
}

/*
 * set - assignment operators
 *
 * Grammar:
 * expr -> lval SET expr         { $$ = set((char*) "",   $1, $3); }
 * expr -> lval SETOR expr       { $$ = set((char*) "|",  $1, $3); }
 * expr -> lval SETXOR expr      { $$ = set((char*) "^",  $1, $3); }
 * expr -> lval SETAND expr      { $$ = set((char*) "&",  $1, $3); }
 * expr -> lval SETLSH expr      { $$ = set((char*) "<<", $1, $3); }
 * expr -> lval SETRSH expr      { $$ = set((char*) ">>", $1, $3); }
 * expr -> lval SETADD expr      { $$ = set((char*) "+",  $1, $3); }
 * expr -> lval SETSUB expr      { $$ = set((char*) "-",  $1, $3); }
 * expr -> lval SETMUL expr      { $$ = set((char*) "*",  $1, $3); }
 * expr -> lval SETDIV expr      { $$ = set((char*) "/",  $1, $3); }
 * expr -> lval SETMOD expr      { $$ = set((char*) "%",  $1, $3); }
 *
 * Much of the functionality in this method is abstracted to a separate method
 * used by op2, opb, and set. The comment above op2 lists the LLVM API calls
 * for this method.
 *
 * Additional LLVM API calls:
 * IRBuilder::CreateLoad(Type, Value *)
 * IRBuilder::CreateStore(Value *, Value *)
 */
struct sem_rec*
set(const char *op, struct sem_rec *x, struct sem_rec *y)
{
  Value *val, *double_val, *load_var;
  ConstantInt *ci;
  struct sem_rec *op_result, *casted_rec;

  if (*op == (char)0) {
    if (x->s_type & T_INT) {
      val = Builder.CreateStore((Value *)y->s_value, (Value *)x->s_value);
      return s_node(val, T_ADDR | T_INT);
    } else if (x->s_type & T_DOUBLE && y->s_type & T_INT) {
      if ((ci = llvm::dyn_cast<ConstantInt>((Value *)y->s_value))) {
        double_val = ConstantFP::get(get_llvm_type(T_DOUBLE), ci->getValue().getSExtValue());
        val = Builder.CreateStore(double_val, (Value *)x->s_value);
        return s_node(val, T_ADDR | T_DOUBLE);
      } else {
        casted_rec = cast(y, T_DOUBLE);
        val = Builder.CreateStore((Value *)casted_rec->s_value, (Value *)x->s_value);
        return s_node(val, T_ADDR | T_DOUBLE);
      }
    } else {
      val = Builder.CreateStore((Value *)y->s_value, (Value *)x->s_value);
      return s_node(val, T_ADDR | T_DOUBLE);
    }
  } else {
    load_var = Builder.CreateLoad(get_llvm_type(x->s_type), (Value *)x->s_value);
    op_result = create_binary_op(string(op), s_node(load_var, x->s_type), y);
    val = Builder.CreateStore((Value *)op_result->s_value, (Value *)x->s_value);
    return s_node(val, T_ADDR | op_result->s_type);
  }
}

/*
 * genstring - generate code for a string
 *
 * Grammar:
 * expr ->  STR                   { $$ = genstring($1); }
 *
 * Use parse_escape_chars (in semutil.c) to handle escape characters
 *
 * LLVM API calls:
 * IRBuilder::CreateGlobalStringPtr(char *)
 */
struct sem_rec*
genstring(char *s)
{
  char *parsed_s = parse_escape_chars(s);
  Value *val = Builder.CreateGlobalStringPtr(parsed_s);

  return s_node((void *)val, T_ADDR | T_STR);
}

void
declare_print ()
{
  struct id_entry *entry;
  FunctionType *var_arg;
  Value *F;
  std::string fname = "print";

  /* Add print to our internal data structure */
  var_arg = FunctionType::get(IntegerType::getInt32Ty(TheContext),
                              PointerType::get(Type::getInt8Ty(TheContext), 0), true);
  F = TheModule->getOrInsertFunction(fname, var_arg).getCallee();

  entry = install( slookup(fname.c_str()), 0 );
  entry->i_type = T_INT | T_PROC;
  entry->i_value = (void*) F;
}

void
init_IR ()
{
  TheModule = make_unique<Module>("<stdin>", TheContext);
  declare_print();
}


void
emit_IR ()
{
  TheModule->print(outs(), nullptr);
}
