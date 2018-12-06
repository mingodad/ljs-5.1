// fibonacci function with cache

local N;
// very inefficient fibonacci function
local function fib(n)
{
	//N=N+1
	++N;
	if( n<2 )
		return n;
	else
		return fib(n-1)+fib(n-2);
}

// a general-purpose value cache
local function cache(f)
{
	local c={};
	local trget=table_rawget;
	return function (x) {
		local y=trget(c, x, null);
		if (! y) {
			y=f(x);
			c[x] <- y;
		}
		return y;
	}
}

local n;
// run and time it
local function test(s,f)
{
	N=0;
	local c=os.clock();
	local v=f(n);
	local t=os.clock()-c;
	print(s,n,v,format("%0.6f",t),N);
}

n = (vargv.len() > 1) ? vargv[1] : 24;		// for other values, do lua fib.lua XX
n=n.tointeger();
print("","n","value","time","evals");
test("plain",fib);
fib = cache(fib);
test("cached",fib);
