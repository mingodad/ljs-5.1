/*
** $Id: lparser.c,v 2.42.1.4 2011/10/21 19:31:42 roberto Exp $
** Lua Parser
** See Copyright Notice in lua.h
*/


#include <string.h>

#define lparser_c
#define LUA_CORE

#include "lua.h"

#include "lcode.h"
#include "ldebug.h"
#include "ldo.h"
#include "lfunc.h"
#include "llex.h"
#include "lmem.h"
#include "lobject.h"
#include "lopcodes.h"
#include "lparser.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"



#define hasmultret(k)		((k) == VCALL || (k) == VVARARG)

#define getlocvar(fs, i)	((fs)->f->locvars[(fs)->actvar[i]])

#define luaY_checklimit(fs,v,l,m)	if ((v)>(l)) errorlimit(fs,l,m)


/*
** nodes for block list (list of active blocks)
*/
typedef struct BlockCnt {
  struct BlockCnt *previous;  /* chain */
  int breaklist;  /* list of jumps out of this loop */
  int continuelist;  /* list of jumps to the loop's test */
  lu_byte nactvar;  /* # active locals outside the breakable structure */
  lu_byte upval;  /* true if some variable in the block is an upvalue */
  lu_byte isbreakable;  /* true if `block' is a loop */
} BlockCnt;



/*
** prototypes for recursive non-terminal functions
*/
static int statement (LexState *ls);
static void chunk (LexState *ls);
static void expr (LexState *ls, expdesc *v);


static void anchor_token (LexState *ls) {
  if (ls->t.token == TK_NAME || ls->t.token == TK_STRING) {
    TString *ts = ls->t.seminfo.ts;
    luaX_newstring(ls, getstr(ts), ts->tsv.len);
  }
}


static void error_expected (LexState *ls, int token) {
  luaX_syntaxerror(ls,
      luaO_pushfstring(ls->L, LUA_QS " expected", luaX_token2str(ls, token)));
}


static void errorlimit (FuncState *fs, int limit, const char *what) {
  const char *msg = (fs->f->linedefined == 0) ?
    luaO_pushfstring(fs->L, "main function has more than %d %s", limit, what) :
    luaO_pushfstring(fs->L, "function at line %d has more than %d %s",
                            fs->f->linedefined, limit, what);
  luaX_lexerror(fs->ls, msg, 0);
}


static int testnext (LexState *ls, int c) {
  if (ls->t.token == c) {
    luaX_next(ls);
    return 1;
  }
  else return 0;
}


static void check (LexState *ls, int c) {
  if (ls->t.token != c)
    error_expected(ls, c);
}

static void checknext (LexState *ls, int c) {
  check(ls, c);
  luaX_next(ls);
}


#define check_condition(ls,c,msg)	{ if (!(c)) luaX_syntaxerror(ls, msg); }



static void check_match (LexState *ls, int what, int who, int where) {
  if (!testnext(ls, what)) {
    if (where == ls->linenumber)
      error_expected(ls, what);
    else {
      luaX_syntaxerror(ls, luaO_pushfstring(ls->L,
             LUA_QS " expected (to close " LUA_QS " at line %d)",
              luaX_token2str(ls, what), luaX_token2str(ls, who), where));
    }
  }
}


static TString *str_checkname (LexState *ls) {
  TString *ts;
  check(ls, TK_NAME);
  ts = ls->t.seminfo.ts;
  luaX_next(ls);
  return ts;
}


static void init_exp (expdesc *e, expkind k, int i) {
  e->f = e->t = NO_JUMP;
  e->k = k;
  e->u.s.info = i;
}


static void codestring (LexState *ls, expdesc *e, TString *s) {
  init_exp(e, VK, luaK_stringK(ls->fs, s));
}


static void checkname(LexState *ls, expdesc *e) {
  codestring(ls, e, str_checkname(ls));
}


static int registerlocalvar (LexState *ls, TString *varname) {
  FuncState *fs = ls->fs;
  Proto *f = fs->f;
  int oldsize = f->sizelocvars;
  luaM_growvector(ls->L, f->locvars, fs->nlocvars, f->sizelocvars,
                  LocVar, SHRT_MAX, "too many local variables");
  while (oldsize < f->sizelocvars) f->locvars[oldsize++].varname = NULL;
  f->locvars[fs->nlocvars].varname = varname;
  luaC_objbarrier(ls->L, f, varname);
  return fs->nlocvars++;
}


#define new_localvarliteral(ls,v,n) \
  new_localvar(ls, luaX_newstring(ls, "" v, (sizeof(v)/sizeof(char))-1), n)


static void new_localvar (LexState *ls, TString *name, int n) {
  FuncState *fs = ls->fs;
  int vidx, nactvar_n;
  vidx = fs->bl ? fs->bl->nactvar : 0;
  nactvar_n = fs->nactvar+n;
  for (; vidx < nactvar_n; ++vidx) {
    if (name == getlocvar(fs, vidx).varname)
      luaX_syntaxerror(ls, luaO_pushfstring(ls->L,
             "Name [%s] already declared", getstr(name)));
  }
  luaY_checklimit(fs, nactvar_n+1, LUAI_MAXVARS, "local variables");
  fs->actvar[nactvar_n] = cast(unsigned short, registerlocalvar(ls, name));
}


static void adjustlocalvars (LexState *ls, int nvars) {
  FuncState *fs = ls->fs;
  fs->nactvar = cast_byte(fs->nactvar + nvars);
  for (; nvars; nvars--) {
    getlocvar(fs, fs->nactvar - nvars).startpc = fs->pc;
  }
}


static void removevars (LexState *ls, int tolevel) {
  FuncState *fs = ls->fs;
  while (fs->nactvar > tolevel)
    getlocvar(fs, --fs->nactvar).endpc = fs->pc;
}


static int indexupvalue (FuncState *fs, TString *name, expdesc *v) {
  int i;
  Proto *f = fs->f;
  int oldsize = f->sizeupvalues;
  for (i=0; i<f->nups; i++) {
    if (fs->upvalues[i].k == v->k && fs->upvalues[i].info == v->u.s.info) {
      lua_assert(f->upvalues[i] == name);
      return i;
    }
  }
  /* new one */
  luaY_checklimit(fs, f->nups + 1, LUAI_MAXUPVALUES, "upvalues");
  luaM_growvector(fs->L, f->upvalues, f->nups, f->sizeupvalues,
                  TString *, MAX_INT, "");
  while (oldsize < f->sizeupvalues) f->upvalues[oldsize++] = NULL;
  f->upvalues[f->nups] = name;
  luaC_objbarrier(fs->L, f, name);
  lua_assert(v->k == VLOCAL || v->k == VUPVAL);
  fs->upvalues[f->nups].k = cast_byte(v->k);
  fs->upvalues[f->nups].info = cast_byte(v->u.s.info);
  return f->nups++;
}


static int searchvar (FuncState *fs, TString *n) {
  int i;
  for (i=fs->nactvar-1; i >= 0; i--) {
    if (n == getlocvar(fs, i).varname)
      return i;
  }
  return -1;  /* not found */
}


static void markupval (FuncState *fs, int level) {
  BlockCnt *bl = fs->bl;
  while (bl && bl->nactvar > level) bl = bl->previous;
  if (bl) bl->upval = 1;
}


static int singlevaraux (FuncState *fs, TString *n, expdesc *var, int base) {
  if (fs == NULL) {  /* no more levels? */
    init_exp(var, VGLOBAL, NO_REG);  /* default is global variable */
    return VGLOBAL;
  }
  else {
    int v = searchvar(fs, n);  /* look up at current level */
    if (v >= 0) {
      init_exp(var, VLOCAL, v);
      if (!base)
        markupval(fs, v);  /* local will be used as an upval */
      return VLOCAL;
    }
    else {  /* not found at current level; try upper one */
      if (singlevaraux(fs->prev, n, var, 0) == VGLOBAL)
        return VGLOBAL;
      var->u.s.info = indexupvalue(fs, n, var);  /* else was LOCAL or UPVAL */
      var->k = VUPVAL;  /* upvalue in this level */
      return VUPVAL;
    }
  }
}


static void singlevar (LexState *ls, expdesc *var) {
  TString *varname = str_checkname(ls);
  FuncState *fs = ls->fs;
  if (singlevaraux(fs, varname, var, 1) == VGLOBAL)
    var->u.s.info = luaK_stringK(fs, varname);  /* info points to global name */
}


static void adjust_assign (LexState *ls, int nvars, int nexps, expdesc *e) {
  FuncState *fs = ls->fs;
  int extra = nvars - nexps;
  if (hasmultret(e->k)) {
    extra++;  /* includes call itself */
    if (extra < 0) extra = 0;
    luaK_setreturns(fs, e, extra);  /* last exp. provides the difference */
    if (extra > 1) luaK_reserveregs(fs, extra-1);
  }
  else {
    if (e->k != VVOID) luaK_exp2nextreg(fs, e);  /* close last expression */
    if (extra > 0) {
      int reg = fs->freereg;
      luaK_reserveregs(fs, extra);
      luaK_nil(fs, reg, extra);
    }
  }
}


static void enterlevel (LexState *ls) {
  if (++ls->L->nCcalls > LUAI_MAXCCALLS)
	luaX_lexerror(ls, "chunk has too many syntax levels", 0);
}


#define leavelevel(ls)	((ls)->L->nCcalls--)


static void enterblock (FuncState *fs, BlockCnt *bl, lu_byte isbreakable) {
  bl->breaklist = NO_JUMP;
  bl->continuelist = NO_JUMP;
  bl->isbreakable = isbreakable;
  bl->nactvar = fs->nactvar;
  bl->upval = 0;
  bl->previous = fs->bl;
  fs->bl = bl;
  lua_assert(fs->freereg == fs->nactvar);
}

static void continuestat (LexState *ls) {
  FuncState *fs = ls->fs;
  BlockCnt *bl = fs->bl;
  int upval = 0;
  while (bl && !bl->isbreakable) {
    upval |= bl->upval;
    bl = bl->previous;
  }
  if (!bl)
    luaX_syntaxerror(ls, "no loop to continue");
  if (upval)
    luaK_codeABC(fs, OP_CLOSE, bl->nactvar, 0, 0);
  luaK_concat(fs, &bl->continuelist, luaK_jump(fs));
}

static void leaveblock (FuncState *fs) {
  BlockCnt *bl = fs->bl;
  fs->bl = bl->previous;
  removevars(fs->ls, bl->nactvar);
  if (bl->upval)
    luaK_codeABC(fs, OP_CLOSE, bl->nactvar, 0, 0);
  /* a block either controls scope or breaks (never both) */
  lua_assert(!bl->isbreakable || !bl->upval);
  lua_assert(bl->nactvar == fs->nactvar);
  fs->freereg = fs->nactvar;  /* free registers */
  luaK_patchtohere(fs, bl->breaklist);
}


static void pushclosure (LexState *ls, FuncState *func, expdesc *v) {
  FuncState *fs = ls->fs;
  Proto *f = fs->f;
  int oldsize = f->sizep;
  int i;
  luaM_growvector(ls->L, f->p, fs->np, f->sizep, Proto *,
                  MAXARG_Bx, "constant table overflow");
  while (oldsize < f->sizep) f->p[oldsize++] = NULL;
  f->p[fs->np++] = func->f;
  luaC_objbarrier(ls->L, f, func->f);
  init_exp(v, VRELOCABLE, luaK_codeABx(fs, OP_CLOSURE, 0, fs->np-1));
  for (i=0; i<func->f->nups; i++) {
    OpCode o = (func->upvalues[i].k == VLOCAL) ? OP_MOVE : OP_GETUPVAL;
    luaK_codeABC(fs, o, 0, func->upvalues[i].info, 0);
  }
}


static void open_func (LexState *ls, FuncState *fs) {
  lua_State *L = ls->L;
  Proto *f = luaF_newproto(L);
  fs->f = f;
  fs->prev = ls->fs;  /* linked list of funcstates */
  fs->ls = ls;
  fs->L = L;
  ls->fs = fs;
  fs->pc = 0;
  fs->lasttarget = -1;
  fs->jpc = NO_JUMP;
  fs->freereg = 0;
  fs->nk = 0;
  fs->np = 0;
  fs->nlocvars = 0;
  fs->nactvar = 0;
  fs->bl = NULL;
  f->source = ls->source;
  f->maxstacksize = 2;  /* registers 0/1 are always valid */
  fs->h = luaH_new(L, 0, 0);
  /* anchor table of constants and prototype (to avoid being collected) */
  sethvalue2s(L, L->top, fs->h);
  incr_top(L);
  setptvalue2s(L, L->top, f);
  incr_top(L);
}


static void close_func (LexState *ls) {
  lua_State *L = ls->L;
  FuncState *fs = ls->fs;
  Proto *f = fs->f;
  removevars(ls, 0);
  luaK_ret(fs, 0, 0);  /* final return */
  luaM_reallocvector(L, f->code, f->sizecode, fs->pc, Instruction);
  f->sizecode = fs->pc;
  luaM_reallocvector(L, f->lineinfo, f->sizelineinfo, fs->pc, int);
  f->sizelineinfo = fs->pc;
  luaM_reallocvector(L, f->k, f->sizek, fs->nk, TValue);
  f->sizek = fs->nk;
  luaM_reallocvector(L, f->p, f->sizep, fs->np, Proto *);
  f->sizep = fs->np;
  luaM_reallocvector(L, f->locvars, f->sizelocvars, fs->nlocvars, LocVar);
  f->sizelocvars = fs->nlocvars;
  luaM_reallocvector(L, f->upvalues, f->sizeupvalues, f->nups, TString *);
  f->sizeupvalues = f->nups;
  lua_assert(luaG_checkcode(f));
  lua_assert(fs->bl == NULL);
  ls->fs = fs->prev;
  /* last token read was anchored in defunct function; must reanchor it */
  if (fs) anchor_token(ls);
  L->top -= 2;  /* remove table and prototype from the stack */
}


Proto *luaY_parser (lua_State *L, ZIO *z, Mbuffer *buff, const char *name) {
  struct LexState lexstate;
  struct FuncState funcstate;
  lexstate.buff = buff;
  luaX_setinput(L, &lexstate, z, luaS_new(L, name));
  open_func(&lexstate, &funcstate);
  funcstate.f->is_vararg = VARARG_ISVARARG;  /* main func. is always vararg */
  luaX_next(&lexstate);  /* read first token */
  chunk(&lexstate);
  check(&lexstate, TK_EOS);
  close_func(&lexstate);
  lua_assert(funcstate.prev == NULL);
  lua_assert(funcstate.f->nups == 0);
  lua_assert(lexstate.fs == NULL);
  return funcstate.f;
}



/*============================================================*/
/* GRAMMAR RULES */
/*============================================================*/


static void field (LexState *ls, expdesc *v) {
  /* field -> ['.' | ':'] NAME */
  FuncState *fs = ls->fs;
  expdesc key;
  luaK_exp2anyreg(fs, v);
  luaX_next(ls);  /* skip the dot or colon */
  checkname(ls, &key);
  luaK_indexed(fs, v, &key);
}


static void yindex (LexState *ls, expdesc *v) {
  /* index -> '[' expr ']' */
  luaX_next(ls);  /* skip the '[' */
  expr(ls, v);
  luaK_exp2val(ls->fs, v);
  checknext(ls, ']');
}

static void sindex (LexState *ls, expdesc *v) {
  /* index -> string */
  expr(ls, v);
  luaK_exp2val(ls->fs, v);
}


/*
** {======================================================================
** Rules for Constructors
** =======================================================================
*/


struct ConsControl {
  expdesc v;  /* last list item read */
  expdesc *t;  /* table descriptor */
  int nh;  /* total number of `record' elements */
  int na;  /* total number of array elements */
  int tostore;  /* number of array elements pending to be stored */
};


static void recfield (LexState *ls, struct ConsControl *cc) {
  /* recfield -> (NAME | `['exp1`]') = exp1 */
  FuncState *fs = ls->fs;
  int reg = ls->fs->freereg;
  expdesc key, val;
  int rkkey;
  if (ls->t.token == TK_NAME) {
    luaY_checklimit(fs, cc->nh, MAX_INT, "items in a constructor");
    checkname(ls, &key);
  }
  else if (ls->t.token == TK_STRING) {
    sindex(ls, &key);
  }
  else  /* ls->t.token == '[' */
    yindex(ls, &key);
  cc->nh++;
  if(!(testnext(ls, '=') || testnext(ls, ':')))
     luaX_syntaxerror(ls, "expect '=' or ':' as key value delimiter");
  rkkey = luaK_exp2RK(fs, &key);
  expr(ls, &val);
  luaK_codeABC(fs, OP_SETTABLE, cc->t->u.s.info, rkkey, luaK_exp2RK(fs, &val));
  fs->freereg = reg;  /* free registers */
}


static void closelistfield (FuncState *fs, struct ConsControl *cc) {
  if (cc->v.k == VVOID) return;  /* there is no list item */
  luaK_exp2nextreg(fs, &cc->v);
  cc->v.k = VVOID;
  if (cc->tostore == LFIELDS_PER_FLUSH) {
    luaK_setlist(fs, cc->t->u.s.info, cc->na, cc->tostore);  /* flush */
    cc->tostore = 0;  /* no more items pending */
  }
}


static void lastlistfield (FuncState *fs, struct ConsControl *cc) {
  if (cc->tostore == 0) return;
  if (hasmultret(cc->v.k)) {
    luaK_setmultret(fs, &cc->v);
    luaK_setlist(fs, cc->t->u.s.info, cc->na, LUA_MULTRET);
    cc->na--;  /* do not count last expression (unknown number of elements) */
  }
  else {
    if (cc->v.k != VVOID)
      luaK_exp2nextreg(fs, &cc->v);
    luaK_setlist(fs, cc->t->u.s.info, cc->na, cc->tostore);
  }
}


static void listfield (LexState *ls, struct ConsControl *cc) {
  expr(ls, &cc->v);
  luaY_checklimit(ls->fs, cc->na, MAX_INT, "items in a constructor");
  cc->na++;
  cc->tostore++;
}


static void table_field (LexState *ls, struct ConsControl *cc) {
  /* field -> listfield | recfield */
  switch(ls->t.token) {
    case TK_STRING:
    case TK_NAME: {  /* may be 'listfield' or 'recfield' */
      luaX_lookahead(ls);
      if (!((ls->lookahead.token == '=') || (ls->lookahead.token == ':')))  /* expression? */
        listfield(ls, cc);
      else
        recfield(ls, cc);
      break;
    }
    case '[': {
      recfield(ls, cc);
      break;
    }
    default: {
      listfield(ls, cc);
      break;
    }
  }
}
static void constructor_base (LexState *ls, expdesc *t, int openTk, int closeTk) {
  /* constructor -> '{' [ field { sep field } [sep] ] '}'
     sep -> ',' | ';' */
  FuncState *fs = ls->fs;
  int line = ls->linenumber;
  int pc = luaK_codeABC(fs, OP_NEWTABLE, 0, 0, 0);
  struct ConsControl cc;
  cc.na = cc.nh = cc.tostore = 0;
  cc.t = t;
  init_exp(t, VRELOCABLE, pc);
  init_exp(&cc.v, VVOID, 0);  /* no value (yet) */
  luaK_exp2nextreg(ls->fs, t);  /* fix it at stack top (for gc) */
  checknext(ls, openTk);
  do {
    lua_assert(cc.v.k == VVOID || cc.tostore > 0);
    if (ls->t.token == closeTk) break;
    closelistfield(fs, &cc);
    if(openTk == '{') table_field(ls, &cc);
    else listfield(ls, &cc);
  } while (testnext(ls, ',') || testnext(ls, ';'));
  check_match(ls, closeTk, openTk, line);
  lastlistfield(fs, &cc);
  SETARG_B(fs->f->code[pc], luaO_int2fb(cc.na)); /* set initial array size */
  SETARG_C(fs->f->code[pc], luaO_int2fb(cc.nh));  /* set initial table size */
}

static void constructor (LexState *ls, expdesc *t) {
  /* constructor -> '{' [ field { sep field } [sep] ] '}'
     sep -> ',' | ';' */
  constructor_base(ls, t, '{', '}');
}

static void constructor_array (LexState *ls, expdesc *t) {
  /* constructor -> '[' [ field { sep field } [sep] ] ']'
     sep -> ',' | ';' */
  constructor_base(ls, t, '[', ']');
}
/* }====================================================================== */



static void parlist (LexState *ls) {
  /* parlist -> [ param { `,' param } ] */
  FuncState *fs = ls->fs;
  Proto *f = fs->f;
  int nparams = 0;
  f->is_vararg = 0;
  if (ls->t.token != ')') {  /* is `parlist' not empty? */
    do {
      switch (ls->t.token) {
        case TK_NAME: {  /* param -> NAME */
          new_localvar(ls, str_checkname(ls), nparams++);
          break;
        }
        case TK_DOTS: {  /* param -> `...' */
          luaX_next(ls);
#if defined(LUA_COMPAT_VARARG)
          /* use `arg' as default name */
          new_localvarliteral(ls, "arg", nparams++);
          f->is_vararg = VARARG_HASARG | VARARG_NEEDSARG;
#endif
          f->is_vararg |= VARARG_ISVARARG;
          break;
        }
        default: luaX_syntaxerror(ls, "<name> or " LUA_QL("...") " expected");
      }
      if(testnext(ls, ':')) { /*optional parameter type*/
        checknext(ls, TK_NAME); /*for now do nothing, discard*/
      }
    } while (!f->is_vararg && testnext(ls, ','));
  }
  adjustlocalvars(ls, nparams);
  f->numparams = cast_byte(fs->nactvar - (f->is_vararg & VARARG_HASARG));
  luaK_reserveregs(fs, fs->nactvar);  /* reserve register for parameters */
}


static void body (LexState *ls, expdesc *e, int needthis, int line) {
  /* body ->  `(' parlist `)' chunk END */
  FuncState new_fs;
  open_func(ls, &new_fs);
  new_fs.f->linedefined = line;
  checknext(ls, '(');
  if (needthis) {
    new_localvarliteral(ls, "this", 0);
    adjustlocalvars(ls, 1);
  }
  parlist(ls);
  checknext(ls, ')');
  if(testnext(ls, ':')) { /*optional function return type*/
      checknext(ls, TK_NAME); /*for now do nothing, discard*/
  }
  checknext(ls, '{');
  chunk(ls);
  new_fs.f->lastlinedefined = ls->linenumber;
  check_match(ls, '}', TK_FUNCTION, line);
  close_func(ls);
  pushclosure(ls, &new_fs, e);
}


static int explist1 (LexState *ls, expdesc *v) {
  /* explist1 -> expr { `,' expr } */
  int n = 1;  /* at least one expression */
  expr(ls, v);
  while (testnext(ls, ',')) {
    luaK_exp2nextreg(ls->fs, v);
    expr(ls, v);
    n++;
  }
  return n;
}


static void funcargs (LexState *ls, expdesc *f) {
  FuncState *fs = ls->fs;
  expdesc args;
  int base, nparams;
  int line = ls->linenumber;
  switch (ls->t.token) {
    case '(': {  /* funcargs -> `(' [ explist1 ] `)' */
      if (line != ls->lastline)
        luaX_syntaxerror(ls,"ambiguous syntax (function call x new statement)");
      luaX_next(ls);
      if (ls->t.token == ')')  /* arg list is empty? */
        args.k = VVOID;
      else {
        explist1(ls, &args);
        luaK_setmultret(fs, &args);
      }
      check_match(ls, ')', '(', line);
      break;
    }
    default: {
      luaX_syntaxerror(ls, "function arguments expected");
      return;
    }
  }
  lua_assert(f->k == VNONRELOC);
  base = f->u.s.info;  /* base register for call */
  if (hasmultret(args.k))
    nparams = LUA_MULTRET;  /* open call */
  else {
    if (args.k != VVOID)
      luaK_exp2nextreg(fs, &args);  /* close last argument */
    nparams = fs->freereg - (base+1);
  }
  init_exp(f, VCALL, luaK_codeABC(fs, OP_CALL, base, nparams+1, 2));
  luaK_fixline(fs, line);
  fs->freereg = base+1;  /* call remove function and arguments and leaves
                            (unless changed) one result */
}




/*
** {======================================================================
** Expression parsing
** =======================================================================
*/

//static void changevalue (LexState *ls, int op, expdesc *v);
static void inc_dec_op (LexState *ls, OpCode op, expdesc *v, int isPost);

static void prefixexp (LexState *ls, expdesc *v) {
  /* prefixexp -> NAME | '(' expr ')' */
  switch (ls->t.token) {
    case '(': {
      int line = ls->linenumber;
      luaX_next(ls);
      expr(ls, v);
      check_match(ls, ')', '(', line);
      if (testnext(ls, '?')) {
        int condexit;
        int escapelist = NO_JUMP;
        int reg;
        FuncState *fs = ls->fs;
        if (v->k == VNIL) v->k = VFALSE;  /* 'falses' are all equal here */
        luaK_goiftrue(ls->fs, v);  /* skip over block if condition is false */
        condexit = v->f;
        expr(ls, v);  /* eval part for true conditional */
        reg = luaK_exp2anyreg(fs, v);  /* set result to reg. */
        luaK_concat(fs, &escapelist, luaK_jump(fs));  /* must jump over it */
        luaK_patchtohere(fs, condexit);
        checknext(ls, ':');
        expr(ls, v);  /* eval part for false conditional */
        luaK_exp2reg(fs, v, reg);  /* set result to reg. */
        luaK_patchtohere(fs, escapelist);  /* patch escape list to conditional end */
        return;
      }
      luaK_dischargevars(ls->fs, v);
      return;
    }
    case TK_NAME: {
      singlevar(ls, v);
      return;
    }
#if 0
    case TK_INC: {  /* added 0.5.2.*/
      luaX_next(ls);
      changevalue(ls, OP_ADD, v);
      return;
    }
    case TK_DEC: {  /* added 0.5.2.*/
      luaX_next(ls);
      changevalue(ls, OP_SUB, v);
      return;
    }
#endif
    case TK_PLUSPLUS: {
      luaX_next(ls);
      inc_dec_op(ls, OP_ADD, v, 0);
      return;
    }
    case TK_MINUSMINUS: {
      luaX_next(ls);
      inc_dec_op(ls, OP_SUB, v, 0);
      return;
    }
    default: {
      luaX_syntaxerror(ls, "unexpected symbol");
      return;
    }
  }
}

static void primaryexp (LexState *ls, expdesc *v) {
  /* primaryexp ->
        prefixexp { `.' NAME | `[' exp `]' | `:' NAME funcargs | funcargs } */
  FuncState *fs = ls->fs;
  prefixexp(ls, v);
  for (;;) {
    switch (ls->t.token) {
      case '.': {  /* field */
        field(ls, v);
        break;
      }
      case '[': {  /* `[' exp1 `]' */
        expdesc key;
        luaK_exp2anyreg(fs, v);
        yindex(ls, &key);
        luaK_indexed(fs, v, &key);
        break;
      }
      case TK_ARROW: {  /* ':' NAME funcargs */
        expdesc key;
        luaX_next(ls);
        checkname(ls, &key);
        luaK_self(fs, v, &key);
        funcargs(ls, v);
        break;
      }
      case '(': {  /* funcargs */
        luaK_exp2nextreg(fs, v);
        funcargs(ls, v);
        break;
      }
      case TK_PLUSPLUS: {
        luaX_next(ls);
        inc_dec_op(ls, OP_ADD, v, 1);
        break;
      }
      case TK_MINUSMINUS: {
        luaX_next(ls);
        inc_dec_op(ls, OP_SUB, v, 1);
        break;
      }
      default: return;
    }
  }
}


static void simpleexp (LexState *ls, expdesc *v) {
  /* simpleexp -> NUMBER | STRING | NIL | true | false | ... |
                  constructor | FUNCTION body | primaryexp */
  switch (ls->t.token) {
    case TK_NUMBER: {
      init_exp(v, VKNUM, 0);
      v->u.nval = ls->t.seminfo.r;
      break;
    }
    case TK_STRING: {
      codestring(ls, v, ls->t.seminfo.ts);
      break;
    }
    case TK_NIL: {
      init_exp(v, VNIL, 0);
      break;
    }
    case TK_TRUE: {
      init_exp(v, VTRUE, 0);
      break;
    }
    case TK_FALSE: {
      init_exp(v, VFALSE, 0);
      break;
    }
    case TK_DOTS: {  /* vararg */
      FuncState *fs = ls->fs;
      check_condition(ls, fs->f->is_vararg,
                      "cannot use " LUA_QL("...") " outside a vararg function");
      fs->f->is_vararg &= ~VARARG_NEEDSARG;  /* don't need 'arg' */
      init_exp(v, VVARARG, luaK_codeABC(fs, OP_VARARG, 0, 1, 0));
      break;
    }
    case '{': {  /* constructor */
      constructor(ls, v);
      return;
    }
    case '[': {  /* array */
      constructor_array(ls, v);
      return;
    }
    case TK_FUNCTION: {
      luaX_next(ls);
      body(ls, v, 0, ls->linenumber);
      return;
    }
    case TK___LINE__: {
      init_exp(v, VKNUM, 0);
      v->u.nval = ls->linenumber;
      break;
    }
    case TK___FILE__: {
      codestring(ls, v, ls->source);
      break;
    }
#if 0
    case TK_INC: {  /* added 0.5.2.*/
      luaX_next(ls);
      changevalue(ls, OP_ADD, v);
      return;
    }
    case TK_DEC: {  /* added 0.5.2.*/
      luaX_next(ls);
      changevalue(ls, OP_SUB, v);
      return;
    }
#endif
    case TK_PLUSPLUS: {
      luaX_next(ls);
      inc_dec_op(ls, OP_ADD, v, 0);
      return;
    }
    case TK_MINUSMINUS: {
      luaX_next(ls);
      inc_dec_op(ls, OP_SUB, v, 0);
      return;
    }
    default: {
      primaryexp(ls, v);
      return;
    }
  }
  luaX_next(ls);
}


static UnOpr getunopr (int op) {
  switch (op) {
    case TK_NOT: return OPR_NOT;
    case '-': return OPR_MINUS;
    case '!': return OPR_BNOT;
    case '#': return OPR_LEN;
    //case TK_PLUSPLUS: return OPR_PLUSPLUS;
    //case TK_MINUSMINUS: return OPR_MINUSMINUS;
    default: return OPR_NOUNOPR;
  }
}


static BinOpr getbinopr (int op) {
  switch (op) {
    /*
    * if we change the number/order of elments here
    * we should also change in the priority struct bellow
    * and on lcode.h enum BinOpr
    */
    case '+': return OPR_ADD;
    case '-': return OPR_SUB;
    case '*': return OPR_MUL;
    case '%': return OPR_MOD;
    case TK_POW: return OPR_POW;
    case '/': return OPR_DIV;
    case '&': return OPR_BAND;
    case '|': return OPR_BOR;
    case '^': return OPR_BXOR;
    case TK_SHL: return OPR_SHL;
    case TK_SHR: return OPR_SHR;
    case TK_CONCAT: return OPR_CONCAT;
    case TK_NE: return OPR_NE;
    case TK_EQ: return OPR_EQ;
    case '<': return OPR_LT;
    case TK_LE: return OPR_LE;
    case '>': return OPR_GT;
    case TK_GE: return OPR_GE;
    case TK_AND: return OPR_AND;
    case TK_OR: return OPR_OR;
    default: return OPR_NOBINOPR;
  }
}


static const struct {
  lu_byte left;  /* left priority for each binary operator */
  lu_byte right; /* right priority */
} priority[] = {  /* ORDER OPR */
   {10, 10}, {10, 10},           /* '+' '-' */
   {11, 11}, {11, 11},           /* '*' '%' */
   {14, 13},                  /* '**' (right associative) */
   {11, 11},                 /* '/' */
   {6, 6}, {4, 4}, {5, 5},   /* '&' '|' '~' */
   {7, 7}, {7, 7},           /* '<<' '>>' */
   {9, 8},                   /* '..' (right associative) */
   {3, 3}, {3, 3}, {3, 3},   /* ==, <, <= */
   {3, 3}, {3, 3}, {3, 3},   /* !=, >, >= */
   {2, 2}, {1, 1}            /* and, or */
};

#define UNARY_PRIORITY	12  /* priority for unary operators */


/*
** subexpr -> (simpleexp | unop subexpr) { binop subexpr }
** where `binop' is any binary operator with a priority higher than `limit'
*/
static BinOpr subexpr (LexState *ls, expdesc *v, unsigned int limit) {
  BinOpr op;
  UnOpr uop;
  enterlevel(ls);
  uop = getunopr(ls->t.token);
  if (uop != OPR_NOUNOPR) {
    luaX_next(ls);
    subexpr(ls, v, UNARY_PRIORITY);
    luaK_prefix(ls->fs, uop, v);
  }
  else simpleexp(ls, v);
  /* expand while operators have priorities higher than `limit' */
  op = getbinopr(ls->t.token);
  while (op != OPR_NOBINOPR && priority[op].left > limit) {
    expdesc v2;
    BinOpr nextop;
    luaX_next(ls);
    luaK_infix(ls->fs, op, v);
    /* read sub-expression with higher priority */
    nextop = subexpr(ls, &v2, priority[op].right);
    luaK_posfix(ls->fs, op, v, &v2);
    op = nextop;
  }
  leavelevel(ls);
  return op;  /* return first untreated operator */
}


static void expr (LexState *ls, expdesc *v) {
  subexpr(ls, v, 0);
}

/* }==================================================================== */



/*
** {======================================================================
** Rules for Statements
** =======================================================================
*/


static int block_follow (int token) {
  switch (token) {
    case '}':
    case TK_ELSE:
	case TK_EOS:
      return 1;
    default: return 0;
  }
}


static void block (LexState *ls) {
  /* block -> [stat | statlist] */
  int line = ls->linenumber;
  FuncState *fs = ls->fs;
  BlockCnt bl;
  enterblock(fs, &bl, 0);
  if(testnext(ls, '{'))
  {
	  chunk(ls);
	  lua_assert(bl.breaklist == NO_JUMP);
	  check_match(ls, '}', '{', line);
  }
  else
  {
	  statement(ls);
	  while(testnext(ls, ';'));//skip all ; after statement it breaks else/elseif
  }
  leaveblock(fs);
}


/*
** structure to chain all variables in the left-hand side of an
** assignment
*/
struct LHS_assign {
  struct LHS_assign *prev;
  expdesc v;  /* variable (global, local, upvalue, or indexed) */
};


/*
** check whether, in an assignment to a local variable, the local variable
** is needed in a previous assignment (to a table). If so, save original
** local value in a safe place and use this safe copy in the previous
** assignment.
*/
static void check_conflict (LexState *ls, struct LHS_assign *lh, expdesc *v) {
  FuncState *fs = ls->fs;
  int extra = fs->freereg;  /* eventual position to save local variable */
  int conflict = 0;
  for (; lh; lh = lh->prev) {
    if (lh->v.k == VINDEXED) {
      if (lh->v.u.s.info == v->u.s.info) {  /* conflict? */
        conflict = 1;
        lh->v.u.s.info = extra;  /* previous assignment will use safe copy */
      }
      if (lh->v.u.s.aux == v->u.s.info) {  /* conflict? */
        conflict = 1;
        lh->v.u.s.aux = extra;  /* previous assignment will use safe copy */
      }
    }
  }
  if (conflict) {
    luaK_codeABC(fs, OP_MOVE, fs->freereg, v->u.s.info, 0);  /* make copy */
    luaK_reserveregs(fs, 1);
  }
}

static void assignment (LexState *ls, struct LHS_assign *lh, int nvars) {
  expdesc e;
  check_condition(ls, vkisvar(lh->v.k), "syntax error");
  if (testnext(ls, ',')) {  /* assignment -> `,' primaryexp assignment */
    struct LHS_assign nv;
    nv.prev = lh;
    primaryexp(ls, &nv.v);
    if (nv.v.k == VLOCAL)
      check_conflict(ls, lh, &nv.v);
    luaY_checklimit(ls->fs, nvars, LUAI_MAXCCALLS - ls->L->nCcalls,
                    "variables in assignment");
    assignment(ls, &nv, nvars+1);
  }
  else {  /* assignment -> `=' explist1 */
    int nexps;
    checknext(ls, '=');
    nexps = explist1(ls, &e);
    if (nexps != nvars) {
      adjust_assign(ls, nvars, nexps, &e);
      if (nexps > nvars)
        ls->fs->freereg -= nexps - nvars;  /* remove extra values */
    }
    else {
      luaK_setoneret(ls->fs, &e);  /* close last expression */
      luaK_storevar(ls->fs, &lh->v, &e);
      return;  /* avoid default */
    }
  }
  init_exp(&e, VNONRELOC, ls->fs->freereg-1);  /* default assignment */
  luaK_storevar(ls->fs, &lh->v, &e);
}


static void assign_compound (LexState *ls, struct LHS_assign *lh, int opType) {

  FuncState * fs=ls->fs;
  expdesc lhv, infix, rh;
  int nexps;
  BinOpr op;
  /*store expression before grounding */
  lhv = lh->v;

  check_condition(ls, vkisvar(lh->v.k),
                      "syntax error in left hand expression in compound assignment");

  /* parse Compound operation. */
  switch (opType) {
      case TK_CADD: op = OPR_ADD; break;
      case TK_CSUB: op = OPR_SUB; break;
      case TK_CMUL: op = OPR_MUL; break;
      case TK_CDIV: op = OPR_DIV; break;
      case TK_CMOD: op = OPR_MOD; break;
  };
  luaX_next(ls);

  /* store compound results in a new register (needed for nested tables) */
  if(lh->v.k == VINDEXED) luaK_reserveregs(fs, 1);

  /* ground the lhs expresion */
  luaK_exp2nextreg(fs, &lh->v);

  /* parse right-hand expression */
  nexps = explist1(ls, &rh);
  check_condition(ls, nexps == 1, "syntax error in right hand expression in compound assignment");

  infix = lh->v;
  luaK_infix(fs,op,&infix);

  luaK_posfix(fs, op, &infix, &rh);
  /* use the lhs before grounding to store */
  luaK_storevar(fs, &lhv, &infix);
}


static int cond (LexState *ls) {
  /* cond -> exp */
  expdesc v;
  expr(ls, &v);  /* read condition */
  if (v.k == VNIL) v.k = VFALSE;  /* `falses' are all equal here */
  luaK_goiftrue(ls->fs, &v);
  return v.f;
}


static int nocond (LexState *ls) {
  /* cond -> exp */
  expdesc v;
  expr(ls, &v);  /* read condition */
  if (v.k == VNIL) v.k = VFALSE;  /* 'falses' are all equal here */
  luaK_goiffalse(ls->fs, &v);
  return v.t;
}


static void breakstat (LexState *ls) {
  FuncState *fs = ls->fs;
  BlockCnt *bl = fs->bl;
  int upval = 0;
  while (bl && !bl->isbreakable) {
    upval |= bl->upval;
    bl = bl->previous;
  }
  if (!bl)
    luaX_syntaxerror(ls, "no loop to break");
  if (upval)
    luaK_codeABC(fs, OP_CLOSE, bl->nactvar, 0, 0);
  luaK_concat(fs, &bl->breaklist, luaK_jump(fs));
}

static void labelstat (LexState *ls, TString *label, int line) {
#if 0
  /* label -> '::' NAME '::' */
  FuncState *fs = ls->fs;
  Labellist *ll = &ls->dyd->label;
  int l;  /* index of new label being created */
  checkrepeated(fs, ll, label);  /* check for repeated labels */
  checknext(ls, ':');  /* skip colon */
  /* create new entry for this label */
  l = newlabelentry(ls, ll, label, line, fs->pc);
  skipnoopstat(ls);  /* skip other no-op statements */
  if (block_follow(ls, 0)) {  /* label is last no-op statement in the block? */
    /* assume that locals are already out of scope */
    ll->arr[l].nactvar = fs->bl->nactvar;
  }
  findgotos(ls, &ll->arr[l]);
#endif
}

static void whilestat (LexState *ls, int line) {
  /* whilestat -> WHILE ( cond ) block */
  FuncState *fs = ls->fs;
  int whileinit;
  int condexit;
  BlockCnt bl;
  luaX_next(ls);  /* skip WHILE */
  checknext(ls, '(');
  whileinit = luaK_getlabel(fs);
  condexit = cond(ls);
  checknext(ls, ')');
  enterblock(fs, &bl, 1);
  block(ls);
  luaK_patchlist(fs, bl.continuelist, whileinit);  /* continue goes to start, too */
  luaK_patchlist(fs, luaK_jump(fs), whileinit);
  leaveblock(fs);
  luaK_patchtohere(fs, condexit);  /* false conditions finish the loop */
}


static void dowhilestat (LexState *ls, int line) {
  /* dowhilestat -> DO block WHILE ( cond ) */
  int condexit;
  FuncState *fs = ls->fs;
  int dowhile_init = luaK_getlabel(fs);
  BlockCnt bl1, bl2;
  enterblock(fs, &bl1, 1);  /* loop block */
  enterblock(fs, &bl2, 0);  /* scope block */
  luaX_next(ls);  /* skip DO */
  checknext(ls, '{');
  chunk(ls);
  luaK_patchtohere(fs, bl1.continuelist);
  check_match(ls, '}', TK_DO, line);
  check_match(ls, TK_WHILE, TK_DO, line);
  line = ls->linenumber;
  checknext(ls, '(');
  condexit = nocond(ls);  /* read condition (inside scope block) */
  check_match(ls, ')', TK_WHILE, line);
  if (!bl2.upval) {  /* no upvalues? */
    leaveblock(fs);  /* finish scope */
    luaK_patchlist(ls->fs, condexit, dowhile_init);  /* close the loop */
  }
  else {  /* complete semantics when there are upvalues */
    breakstat(ls);  /* if condition then break */
    luaK_patchtohere(ls->fs, condexit);  /* else... */
    leaveblock(fs);  /* finish scope... */
    luaK_patchlist(ls->fs, luaK_jump(fs), dowhile_init);  /* and repeat */
  }
  leaveblock(fs);  /* finish loop */
}


static int exp1 (LexState *ls) {
  expdesc e;
  int k;
  expr(ls, &e);
  k = e.k;
  luaK_exp2nextreg(ls->fs, &e);
  return k;
}


static void forbody (LexState *ls, int base, int line, int nvars, int isnum) {
  /* forbody -> DO block */
  BlockCnt bl;
  FuncState *fs = ls->fs;
  int prep, endfor;
  adjustlocalvars(ls, 3);  /* control variables */
  prep = isnum ? luaK_codeAsBx(fs, OP_FORPREP, base, NO_JUMP) : luaK_jump(fs);
  enterblock(fs, &bl, 0);  /* scope for declared variables */
  adjustlocalvars(ls, nvars);
  luaK_reserveregs(fs, nvars);
  block(ls);
  leaveblock(fs);  /* end of scope for declared variables */
  luaK_patchtohere(fs, prep);
  luaK_patchtohere(fs, bl.previous->continuelist);	/* continue, if any, jumps to here */
  endfor = (isnum) ? luaK_codeAsBx(fs, OP_FORLOOP, base, NO_JUMP) :
                     luaK_codeABC(fs, OP_TFORLOOP, base, 0, nvars);
  luaK_fixline(fs, line);  /* pretend that `OP_FOR' starts the loop */
  luaK_patchlist(fs, (isnum ? endfor : luaK_jump(fs)), prep + 1);
}


static void fornum (LexState *ls, TString *varname, int line) {
  /* fornum -> NAME = exp1,exp1[,exp1] forbody */
  FuncState *fs = ls->fs;
  int base = fs->freereg;
  new_localvarliteral(ls, "(for index)", 0);
  new_localvarliteral(ls, "(for limit)", 1);
  new_localvarliteral(ls, "(for step)", 2);
  new_localvar(ls, varname, 3);
  checknext(ls, '=');
  exp1(ls);  /* initial value */
  checknext(ls, ',');
  exp1(ls);  /* limit */
  if (testnext(ls, ','))
    exp1(ls);  /* optional step */
  else {  /* default step = 1 */
    luaK_codeABx(fs, OP_LOADK, fs->freereg, luaK_numberK(fs, 1));
    luaK_reserveregs(fs, 1);
  }
  checknext(ls, ')');
  forbody(ls, base, line, 1, 1);
}


static void forlist (LexState *ls, TString *indexname) {
  /* forlist -> NAME {,NAME} IN explist1 forbody */
  FuncState *fs = ls->fs;
  expdesc e;
  int nvars = 0;
  int line;
  int base = fs->freereg;
  /* create control variables */
  new_localvarliteral(ls, "(for generator)", nvars++);
  new_localvarliteral(ls, "(for state)", nvars++);
  new_localvarliteral(ls, "(for control)", nvars++);
  /* create declared variables */
  new_localvar(ls, indexname, nvars++);
  while (testnext(ls, ','))
    new_localvar(ls, str_checkname(ls), nvars++);
  checknext(ls, TK_IN);
  line = ls->linenumber;
  adjust_assign(ls, 3, explist1(ls, &e), &e);
  luaK_checkstack(fs, 3);  /* extra space to call generator */
  checknext(ls, ')');
  forbody(ls, base, line, nvars - 3, 0);
}


static void forstat (LexState *ls, int line) {
  /* forstat -> FOR (fornum | forlist) END */
  FuncState *fs = ls->fs;
  TString *varname;
  BlockCnt bl;
  enterblock(fs, &bl, 1);  /* scope for loop and control variables */
  luaX_next(ls);  /* skip 'for' */
  checknext(ls, '(');
  varname = str_checkname(ls);  /* first variable name */
  switch (ls->t.token) {
    case '=': fornum(ls, varname, line); break;
    case ',': case TK_IN: forlist(ls, varname); break;
    default: luaX_syntaxerror(ls, LUA_QL("=") " or " LUA_QL("in") " expected");
  }
  leaveblock(fs);  /* loop scope (`break' jumps to this point) */
}


static int test_then_block (LexState *ls) {
  /* test_then_block -> [IF | ELSEIF] cond THEN block */
  int condexit;
  luaX_next(ls);  /* skip IF or ELSEIF */
  checknext(ls, '(');
  condexit = cond(ls);
  checknext(ls, ')');
  block(ls);  /* `then' part */
  return condexit;
}


static void ifstat (LexState *ls, int line) {
  /* ifstat -> IF ( cond ) block {ELSE IF ( cond ) block} [ELSE block] */
  FuncState *fs = ls->fs;
  int flist;
  int escapelist = NO_JUMP;  /* exit list for finished parts */
  flist = test_then_block(ls);  /* IF ( cond ) block */
check_else:
  if(testnext(ls, TK_ELSE)) {
    luaK_concat(fs, &escapelist, luaK_jump(fs));
    luaK_patchtohere(fs, flist);
    if (ls->t.token == TK_IF) {
      flist = test_then_block(ls);  /* ELSE IF cond THEN block */
      goto check_else; /* try again nested ELSE IF */
    }
    block(ls);  /* 'else' part */
  }
  else
    luaK_concat(fs, &escapelist, flist);
  luaK_patchtohere(fs, escapelist);  /* patch escape list to 'if' end */
}


static void localfunc (LexState *ls) {
  expdesc v, b;
  FuncState *fs = ls->fs;
  new_localvar(ls, str_checkname(ls), 0);
  init_exp(&v, VLOCAL, fs->freereg);
  luaK_reserveregs(fs, 1);
  adjustlocalvars(ls, 1);
  body(ls, &b, 0, ls->linenumber);
  luaK_storevar(fs, &v, &b);
  /* debug information will only see the variable after this point! */
  getlocvar(fs, fs->nactvar - 1).startpc = fs->pc;
}


static void localstat (LexState *ls) {
  /* stat -> LOCAL NAME {`,' NAME} [`=' explist1] */
  int nvars = 0;
  int nexps;
  expdesc e;
  do {
    new_localvar(ls, str_checkname(ls), nvars++);
    if(testnext(ls, ':')) { /*optional parameter type*/
      checknext(ls, TK_NAME); /*for now do nothing, discard*/
    }
  } while (testnext(ls, ','));
  if (testnext(ls, '='))
    nexps = explist1(ls, &e);
  else {
    e.k = VVOID;
    nexps = 0;
  }
  adjust_assign(ls, nvars, nexps, &e);
  adjustlocalvars(ls, nvars);
}


static int funcname (LexState *ls, expdesc *v) {
  /* funcname -> NAME {field} [`:' NAME] */
  int needself = 0;
  singlevar(ls, v);
  while (ls->t.token == '.')
    field(ls, v);
  if (ls->t.token == TK_DBCOLON) {
    needself = 1;
    field(ls, v);
  }
  return needself;
}


static void funcstat (LexState *ls, int line) {
  /* funcstat -> FUNCTION funcname body */
  int needself;
  expdesc v, b;
  luaX_next(ls);  /* skip FUNCTION */
  needself = funcname(ls, &v);
  body(ls, &b, needself, line);
  luaK_storevar(ls->fs, &v, &b);
  luaK_fixline(ls->fs, line);  /* definition `happens' in the first line */
}


static void exprstat (LexState *ls) {
  /* stat -> func | compound | assignment */
  FuncState *fs = ls->fs;
  struct LHS_assign v;
  primaryexp(ls, &v.v);
  if (v.v.k == VCALL)  /* stat -> func */
    SETARG_C(getcode(fs, &v.v), 1);  /* call statement uses no results */
  else {  /* stat -> assignment */
    v.prev = NULL;
    switch(ls->t.token) {
      case TK_CADD: case TK_CSUB: case TK_CMUL:
      case TK_CDIV: case TK_CMOD:
        assign_compound(ls, &v, ls->t.token);
        break;
      case ',': case '=': //case TK_CCONCAT:
        assignment(ls, &v, 1);
        break;
      case ';':
        /* TK_PLUSPLUS, TK_MINUMINUS should be already managed */
        break;
      default:
        luaX_syntaxerror(ls, lua_pushfstring(ls->L,
                         "'++', '--', +=', '-=', '*=', '/=', '%%=', '..=' or '=' expected"));
        break;
    }
  }
}


static void retstat (LexState *ls) {
  /* stat -> RETURN [explist] [';'] */
  FuncState *fs = ls->fs;
  expdesc e;
  int first, nret;  /* registers with returned values */
  luaX_next(ls);  /* skip RETURN */
  if (block_follow(ls->t.token) || ls->t.token == ';')
    first = nret = 0;  /* return no values */
  else {
    nret = explist1(ls, &e);  /* optional return values */
    if (hasmultret(e.k)) {
      luaK_setmultret(fs, &e);
      if (e.k == VCALL && nret == 1) {  /* tail call? */
        SET_OPCODE(getcode(fs,&e), OP_TAILCALL);
        lua_assert(GETARG_A(getcode(fs,&e)) == fs->nactvar);
      }
      first = fs->nactvar;
      nret = LUA_MULTRET;  /* return all values */
    }
    else {
      if (nret == 1)  /* only one single value? */
        first = luaK_exp2anyreg(fs, &e);
      else {
        luaK_exp2nextreg(fs, &e);  /* values must go to the `stack' */
        first = fs->nactvar;  /* return all `active' values */
        lua_assert(nret == fs->freereg - first);
      }
    }
  }
  luaK_ret(fs, first, nret);
}

#if 0
/* written by Andreas Falkenhahn and posted to lua.bazar2.conectiva.com.br on 01 Sep 2004
   changed to process multiple values in 0.6.0, November 10, 2007; patched 0.29.1, December 13, 2009 */

void codecompcase (FuncState *fs, int base, int nargs, expdesc *e) {
  //luaK_codeABC(fs, OP_CMD, base, nargs, CMD_CASE);  /* nargs: all registers set before including instr# */
  e->u.s.info = luaK_jump(fs);
  e->k = VJMP;
}

static void casestat (LexState *ls, expdesc *v) {
  FuncState *fs = ls->fs;
  expdesc v2;
  int nargs, base;
  checknext(ls, TK_CASE);
  /* do not set base to 0 for if case is used in (local) loops, it does not work properly */
  base = fs->freereg;
  luaK_exp2nextreg(fs, v);
  nargs = explist1(ls, &v2); /* put every value into a register */
  if (!(v2.k == VK || v2.k == VKNUM)) luaX_syntaxerror(ls, "case expressions must be constants");
  luaK_exp2nextreg(fs, &v2);
  codecompcase(fs, base, nargs+1, v);
  fs->freereg -= nargs+1;  /* free all registers */
  if (v->k == VNIL) v->k = VFALSE;
  luaK_goiftrue(fs, v);
  luaK_patchtohere(fs, v->t);
  checknext(ls, ':');
  block(ls);
}

/* written by Andreas Falkenhahn and posted to lua.bazar2.conectiva.com.br on 01 Sep 2004 */

static void switchstat (LexState *ls, int line) {
  /* switchstat -> switch (val1) {case val2: block [case valx: block [default: block]] } */
  FuncState *fs = ls->fs;
  BlockCnt bl;
  int escapelist = NO_JUMP;
  expdesc v;
  luaX_next(ls);  /* skip 'switch' */
  checknext(ls, '(');
  enterblock(fs, &bl, 0);  /* block to control variable scope */
  expr(ls, &v);
  checknext(ls, ')');
  checknext(ls, '{');
  int isFirst = 1;
  while (ls->t.token == TK_CASE) {
    if(!isFirst) {
      luaK_concat(fs, &escapelist, luaK_jump(fs));
      luaK_patchtohere(fs, v.f);
    }
    casestat(ls, &v);  /* case val : block */
    isFirst = 0;
  }
  if (ls->t.token == TK_DEFAULT) {
    luaK_concat(fs, &escapelist, luaK_jump(fs));
    luaK_patchtohere(fs, v.f);
    luaX_next(ls);  /* skip default */
    checknext(ls, ':');
    block(ls);  /* default part */
  } else {
    luaK_concat(fs, &escapelist, v.f);
  }
  luaK_patchtohere(fs, escapelist);
  check_match(ls, '}', TK_SWITCH, line);
  leaveblock(fs);
}

void codecompcase (FuncState *fs, int base, int nargs, expdesc *e) {
  //luaK_codeABC(fs, OP_CMD, base, nargs, CMD_CASE);  /* nargs: all registers set before including instr# */
  e->u.s.info = luaK_jump(fs);
  e->k = VJMP;
}

static void casestat (LexState *ls, expdesc *v) {
  FuncState *fs = ls->fs;
  expdesc v2;
  int nargs, base;
  checknext(ls, TK_CASE);
  /* do not set base to 0 for if case is used in (local) loops, it does not work properly */
  base = fs->freereg;
  luaK_exp2nextreg(fs, v);
  nargs = explist1(ls, &v2); /* put every value into a register */
  luaK_exp2nextreg(fs, &v2);
  codecompcase(fs, base, nargs+1, v);
  fs->freereg -= nargs+1;  /* free all registers */
  if (v->k == VNIL) v->k = VFALSE;
  luaK_goiftrue(fs, v);
  luaK_patchtohere(fs, v->t);
  checknext(ls, ':');
  block(ls);
}

/* written by Andreas Falkenhahn and posted to lua.bazar2.conectiva.com.br on 01 Sep 2004 */

static void switchstat (LexState *ls, int line) {
  /* switchstat -> switch (val1) {case val2: block [case valx: block [default: block]] } */
  FuncState *fs = ls->fs;
  BlockCnt bl;
  int escapelist = NO_JUMP;
  expdesc v;
  luaX_next(ls);  /* skip 'switch' */
  checknext(ls, '(');
  enterblock(fs, &bl, 0);  /* block to control variable scope */
  expr(ls, &v);
  checknext(ls, ')');
  checknext(ls, '{');
  casestat(ls, &v);  /* case val : block */
  while (ls->t.token == TK_CASE) {
    luaK_concat(fs, &escapelist, luaK_jump(fs));
    luaK_patchtohere(fs, v.f);
    casestat(ls, &v);  /* case val : block */
  }
  if (ls->t.token == TK_DEFAULT) {
    luaK_concat(fs, &escapelist, luaK_jump(fs));
    luaK_patchtohere(fs, v.f);
    luaX_next(ls);  /* skip default */
    checknext(ls, ':');
    block(ls);  /* default part */
  } else {
    luaK_concat(fs, &escapelist, v.f);
  }
  luaK_patchtohere(fs, escapelist);
  check_match(ls, '}', TK_SWITCH, line);
  leaveblock(fs);
}

/* Used by INC and DEC statements
   added 0.5.2, June 08, 2007; extended November 04, 2007; patched May 10, 2010 */

static void changevalue (LexState *ls, int op, expdesc *v) {
  FuncState *fs = ls->fs;
  expdesc lv, e1, e2;
  if(!v) v = &lv;
  int indices;
  testnext(ls, '(');
  indices = fs->freereg;
  primaryexp(ls, v);
  e1 = *v;
  if (v->k == VINDEXED)
    luaK_reserveregs(fs, fs->freereg - indices);  /* 1.0.1 patch: increase stack by the number of indices */
  if (testnext(ls, ',')) {
    luaK_exp2nextreg(fs, &e1);  /* <- this call solved the problem with indexed values, 0.32.0 */
    expr(ls, &e2);
  } else {  /* using special opcodes is not faster */
    init_exp(&e2, VKNUM, 0);
    e2.u.nval = (lua_Integer)1;
  }
  testnext(ls, ')');
  luaK_codearith(fs, (OpCode)op, &e1, &e2);
  luaK_setoneret(fs, &e1);  /* close last expression */
  luaK_storevar(fs, v, &e1);
  if(v != &lv) luaK_exp2nextreg(fs, v);
}
#endif

static void inc_dec_op (LexState *ls, OpCode op, expdesc *v, int isPost) {
  FuncState *fs = ls->fs;
  expdesc lv, e1, e2;
  int indices;
  if(!v) v = &lv;
  indices = fs->freereg;
  init_exp(&e2, VKNUM, 0);
  e2.u.nval = (lua_Integer)1;
  if(isPost) {
    check_condition(ls, vkisvar(v->k),
                      "syntax error expression not assignable");
    lv = e1 = *v;
    if (v->k == VINDEXED)
      luaK_reserveregs(fs, 1);
    luaK_exp2nextreg(fs, v);
    luaK_reserveregs(fs, 1); //copy again to operate on it
    luaK_codearith(fs, op, &e1, &e2);
    luaK_storevar(fs, &lv, &e1);
    --fs->freereg; //remove extra copy register
    return;
  }
  primaryexp(ls, v);
  check_condition(ls, vkisvar(v->k),
                      "syntax error expression not assignable");
  e1 = *v;
  if (v->k == VINDEXED)
    luaK_reserveregs(fs, fs->freereg - indices);
  luaK_codearith(fs, op, &e1, &e2);
  luaK_storevar(fs, v, &e1);
  if(v != &lv) luaK_exp2nextreg(fs, v);
}


static int statement (LexState *ls) {
  int line = ls->linenumber;  /* may be needed for error messages */
  switch (ls->t.token) {
    case TK_IF: {  /* stat -> ifstat */
      ifstat(ls, line);
      return 0;
    }
    case TK_WHILE: {  /* stat -> whilestat */
      whilestat(ls, line);
      return 0;
    }
    case '{': {  /* stat -> DO block END */
      block(ls);
      return 0;
    }
    case TK_FOR: {  /* stat -> forstat */
      forstat(ls, line);
      return 0;
    }
    case TK_DO: {  /* stat -> dowhilestat */
      dowhilestat(ls, line);
      return 0;
    }
    case TK_FUNCTION: {
      funcstat(ls, line);  /* stat -> funcstat */
      return 0;
    }
    case TK_LOCAL: {  /* stat -> localstat */
      luaX_next(ls);  /* skip LOCAL */
      if (testnext(ls, TK_FUNCTION))  /* local function? */
        localfunc(ls);
      else
        localstat(ls);
      return 0;
    }
    case TK_RETURN: {  /* stat -> retstat */
      retstat(ls);
      return 1;  /* must be last statement */
    }
    case TK_BREAK: {  /* stat -> breakstat */
      luaX_next(ls);  /* skip BREAK */
      breakstat(ls);
      return 1;  /* must be last statement */
    }
    case TK_CONTINUE: {  /* stat -> continuestat */
      luaX_next(ls);  /* skip CONTINUE */
      continuestat(ls);
      return 1;	  /* must be last statement */
    }
#if 0
    case TK_SWITCH: {  /* stat -> switchstat */
      switchstat(ls, line);
      return 0;
    }
    case TK_INC: {  /* added 0.5.2.*/
      luaX_next(ls);
      changevalue(ls, OP_ADD, NULL);
      return 0;
    }
    case TK_DEC: {  /* added 0.5.2.*/
      luaX_next(ls);
      changevalue(ls, OP_SUB, NULL);
      return 0;
    }
#endif
    case TK_PLUSPLUS: {
      luaX_next(ls);
      inc_dec_op(ls, OP_ADD, NULL, 0);
      return 0;
    }
    case TK_MINUSMINUS: {
      luaX_next(ls);
      inc_dec_op(ls, OP_SUB, NULL, 0);
      return 0;
    }
    case TK_NAME: {
      if (ls->current == ':') {/* stat -> label */
        labelstat(ls, str_checkname(ls), line);
        return 0;
      }
    }
    default: {
      exprstat(ls);
      return 0;  /* to avoid warnings */
    }
  }
}


static void chunk (LexState *ls) {
  /* chunk -> { stat [`;'] } */
  int islast = 0;
  enterlevel(ls);
  while (!islast && !block_follow(ls->t.token)) {
    islast = statement(ls);
    testnext(ls, ';');
    lua_assert(ls->fs->f->maxstacksize >= ls->fs->freereg &&
               ls->fs->freereg >= ls->fs->nactvar);
    ls->fs->freereg = ls->fs->nactvar;  /* free registers */
  }
  leavelevel(ls);
}

/* }====================================================================== */
