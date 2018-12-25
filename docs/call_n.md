# How to make sure that function will be called n times (in ATS)

Suppose, we need to have a function `iterateN(n,func)` that must call `func(0)`, `func(1)`, ..., `func(n-1)` consecutively.

In ATS, is it possible somehow formally specify that `func` actually will be called n times, starting from `func(0)` then `func(1)` and so on? (Ideally, without any overhead)

What types `func` and `iterateN` then should have?

The answer is - it is possible!

## First Try

First naive idea is to use `dataprop` like this:

```ats
dataprop CALL (int, int) =
  | {n: pos}
	CALLbas(n, 0)
  | {n, i: pos | i <= n}
	CALLind(n, i) of (CALL(n,i-1))
	
	
fn func
  {n, i: nat | i < n}
  ( pf : CALL(n,i)
  | i  : int i)
  :<fun1> (CALL(n,i+1) | void)
= let 
  val     _ = println! ("func(", i+1, ")")
  prval pf2 = CALLind(pf)
in (pf2 | ()) end


typedef func_type = 
  {n, i: nat | i < n} 
  (CALL(n,i) | int i) 
  -<fun1> (CALL(n,i+1) | void)
  

fn iterateN
  {n: pos}
  ( pf0 : CALL(n,0)
  | n   : int n 
  , f   : func_type )
  : (CALL(n,n) | void)
= let
  fun loop
	{n, i: nat | i <= n}
	.<n - i>.
	( pfi : CALL(n,i)
	| n   : int n 
	, i   : int i
	, f   : func_type )
	: (CALL(n,n) | void)
  = if i >= n // i == n
	then (pfi | ())
	else let
		val (pfi1 | _) = f{n,i}(pfi | i)
		// prval pfi1 = CALLind(pfi)             <<<===--- (*)
	  in loop{n, i+1}(pfi1 | n, i+1, f) end
  //
in loop{n,0}(pf0 | n, 0, f) end

// ...

val _ = iterateN(CALLbas | 10, func)

// ...
```

But nothing is preventing us to write (see `(*)`):

    prval pfi1 = CALLind(pfi)

instead of:

    val (pfi1 | _) = f{n,i}(pfi | i)

So, is it possible?

## The Answer

The solution is to parameterize `CALL` (see `(1)`):

```ats
dataprop CALL (int, int) =
  | {n: nat}
    CALLbas(n, 0)
  | {n, i: nat | i <= n}
    CALLind(n, i) of (CALL(n,i-1))
    
    
fn func
  {n, i: nat | i < n}
  ( pf : CALL(n,i)
  | i  : int i)
  :<fun1> (CALL(n,i+1) | void)
= let 
  val     _ = println! ("func(", i+1, ")")
  prval pf2 = CALLind(pf)
in (pf2 | ()) end


typedef func_type (p: (int, int) -> prop) =     // <<==-- (1)
  {n, i: nat | i < n} 
  (p(n,i) | int i) 
  -<fun1> (p(n,i+1) | void)
  

fn iterateN
  {p: (int, int) -> prop}                       // <<==-- (1)
  {n: nat}
  ( pf0 : p(n,0)
  | n   : int n 
  , f   : func_type(p) )                        // <<==-- (1)
  : (p(n,n) | void)                             // <<==-- (1)
= let
  fun loop
    {p: (int, int) -> prop}                     // <<==-- (1)
    {n, i: nat | i <= n}
    .<n - i>.
    ( pfi : p(n,i)
    | n   : int n 
    , i   : int i
    , f   : func_type(p) )                      // <<==-- (1)
    : (p(n,n) | void)                           // <<==-- (1)
  = if i >= n // i == n
    then (pfi | ())
    else let
        val (pfi1 | _) = f{n,i}(pfi | i)
        //prval pfi1 = CALLind(pfi)             // <<==-- (2)
      in loop{p}{n, i+1}(pfi1 | n, i+1, f) end
  //
in loop{p}{n,0}(pf0 | n, 0, f) end

// ...

val _ = iterateN(CALLbas | 10, func)

// ...
```

Instead of concrete `CALL` now we have an abstract `p` and we no longer can use `CALLind` inside the `iterateN`. If we try we get compilation error (see `(2)`):

```
... warning(3): the constraint [S2Eeqeq(S2Evar(p(8314)); S2Ecst(CALL))] cannot be translated into a form accepted by the constraint solver.

... error(3): unsolved constraint: C3NSTRprop(C3TKmain(); S2Eeqeq(S2Evar(p(8314)); S2Ecst(CALL)))

... warning(3): the constraint [S2Eeqeq(S2Ecst(CALL); S2Evar(p(8314)))] cannot be translated into a form accepted by the constraint solver.

typechecking has failed: there are some unsolved constraints: please inspect the above reported error message(s) for information.
```

## See also

This approach is used in `iterate_primes` from `src/prime.dats`, `src/prime.sats`.
