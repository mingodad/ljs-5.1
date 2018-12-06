#define LUA_LIB

#include "lua.h"

#include "lauxlib.h"
#include "lualib.h"

#ifdef _MSC_VER
typedef unsigned __int64 U64;
#else
typedef unsigned long long U64;
#endif

typedef unsigned int UB;
static UB barg(lua_State *L,int idx){
	union{
		lua_Number n;
		U64 b;
	}bn;
	bn.n=lua_tonumber(L,idx)+6755399441055744.0;
	if (bn.n==0.0&&!lua_isnumber(L,idx))luaL_typerror(L,idx,"number");
	return(UB)bn.b;
}
#define BRET(b) lua_pushnumber(L,(lua_Number)(int)(b));return 1;
static int tobit(lua_State *L){BRET(barg(L,1))}
static int bnot(lua_State *L){BRET(~barg(L,1))}
static int band(lua_State *L){
	int i;
	UB b=barg(L,1);
	for(i=lua_gettop(L);i>1;i--)b&=barg(L,i);
	BRET(b)
}
static int bor(lua_State *L){
	int i;
	UB b=barg(L,1);
	for(i=lua_gettop(L);i>1;i--)b|=barg(L,i);
	BRET(b)
}
static int bxor(lua_State *L){
	int i;
	UB b=barg(L,1);
	for(i=lua_gettop(L);i>1;i--)b^=barg(L,i);
	BRET(b)
}
static int lshift(lua_State *L){UB b=barg(L,1),n=barg(L,2)&31;BRET(b<<n)}
static int rshift(lua_State *L){UB b=barg(L,1),n=barg(L,2)&31;BRET(b>>n)}
static int arshift(lua_State *L){UB b=barg(L,1),n=barg(L,2)&31;BRET((int)b>>n)}
static int rol(lua_State *L){UB b=barg(L,1),n=barg(L,2)&31;BRET((b<<n)|(b>>(32-n)))}
static int ror(lua_State *L){UB b=barg(L,1),n=barg(L,2)&31;BRET((b>>n)|(b<<(32-n)))}
static int bswap(lua_State *L){UB b=barg(L,1);b=(b>>24)|((b>>8)&0xff00)|((b&0xff00)<<8)|(b<<24);BRET(b)}
static int tohex(lua_State *L){
	UB b=barg(L,1);
	int n=lua_isnone(L,2)?8:(int)barg(L,2);
	const char *hexdigits="0123456789abcdef";
	char buf[8];
	int i;
	if(n<0){n=-n;hexdigits="0123456789ABCDEF";}
	if(n>8)n=8;
	for(i=(int)n;--i>=0;){buf[i]=hexdigits[b&15];b>>=4;}
	lua_pushlstring(L,buf,(size_t)n);
	return 1;
}
static const struct luaL_Reg bitlib[] = {
	{"tobit",tobit},
	{"bnot",bnot},
	{"band",band},
	{"bor",bor},
	{"bxor",bxor},
	{"lshift",lshift},
	{"rshift",rshift},
	{"arshift",arshift},
	{"rol",rol},
	{"ror",ror},
	{"bswap",bswap},
	{"tohex",tohex},
	{NULL,NULL}
};

LUALIB_API int luaopen_bit (lua_State *L) {
  luaL_register(L, LUA_BITNAME, bitlib);
  return 1;
}
