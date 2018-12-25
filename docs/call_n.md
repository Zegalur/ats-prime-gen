# How to make sure that function is called consecutively n times (in ATS)

Suppose, we need to have a function `loopN(n,func)` that call `func(0)`, `func(1)`, ..., `func(n-1)` consecutively.

Is it possible somehow formally specify that `func` will be called n times, starting from `func(0)` then `func(1)` and so on? (Ideally, without any overhead)

The answer is - yes, it is possible!

## First Try

First naive idea is to use `dataprop`:

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
  

fn loopN
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

val _ = loopN(CALLbas | 10, func)

// ...
```

But nothing is preventing us to write (see `(*)`):

    prval pfi1 = CALLind(pfi)

instead of:

    val (pfi1 | _) = f{n,i}(pfi | i)

So, is it even possible?

## Almost there

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
  

fn loopN
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

val _ = loopN(CALLbas | 10, func)

// ...
```

Instead of concrete `CALL` now we have an abstract `p` and we no longer can use `CALLind` inside the `loopN`. If we try we get compilation error (see `(2)`):

```
... warning(3): the constraint [S2Eeqeq(S2Evar(p(8314)); S2Ecst(CALL))] cannot be translated into a form accepted by the constraint solver.

... error(3): unsolved constraint: C3NSTRprop(C3TKmain(); S2Eeqeq(S2Evar(p(8314)); S2Ecst(CALL)))

... warning(3): the constraint [S2Eeqeq(S2Ecst(CALL); S2Evar(p(8314)))] cannot be translated into a form accepted by the constraint solver.

typechecking has failed: there are some unsolved constraints: please inspect the above reported error message(s) for information.
```

## The Problem

We still can write this and pass the typechecker:

```ats
val          _ = f{n,i}(pfi | i)
val (pfi1 | _) = f{n,i}(pfi | i)
```

And this is not what we want to be allowed..

## Linear Types

Luckily, in ATS we have linear types. If we use `dataview` instead of `dataprop` we finally get what we want (see `(x)`):

```ats
dataview CALL (int, int) =
  | {n: nat}
    CALLbas(n, 0)
  | {n, i: nat | i <= n}
    CALLind(n, i) of (CALL(n,i-1))
    
        
fn func
  {n, i: nat | i < n}
  ( pf : !CALL(n,i) >> CALL(n,i+1)
  | i  : int i)
  :<fun1> void
= let 
  val   _ = println! ("func(", i+1, ")")
  prval _ = pf := CALLind(pf)
in () end


typedef func_type (p: (int, int) -> view) =     // <<==- (x)
  {n, i: nat | i < n} 
  (!p(n,i) >> p(n,i+1) | int i) 
  -<fun1> void
  

fn loopN
  {p: (int, int) -> view}                       // <<==- (x)
  {n: nat}
  ( pf0 : !p(n,0) >> p(n,n)                     // <<==- (x)
  | n   : int n 
  , f   : func_type(p) )                        
  : void                                        // <<==- (x)
= let
  fun loop
    {p: (int, int) -> view}                     // <<==- (x)
    {n, i: nat | i <= n}
    .<n - i>.
    ( pfi : !p(n,i) >> p(n,n)                   // <<==- (x)
    | n   : int n 
    , i   : int i
    , f   : func_type(p) )                      
    : void                                      // <<==- (x)
  = if i >= n // i == n
    then ()
    else let
        val _ = f{n,i}(pfi | i)                 // <<==- (x)
      in loop{p}{n, i+1}(pfi | n, i+1, f) end
  //
in loop{p}{n,0}(pf0 | n, 0, f) end

// ...

prval pf0 = CALLbas                             // <<==- (x)
val _ = loopN(pf0 | 10, func)                   // <<==- (x)

// ...

```

Any time we call `f` inside the `loopN` we automatically change linear `pfi` from `p(n,i)` to `p(n,i+1)`. If we write

```ats
val _ = f{n,i}(pfi | i)
val _ = f{n,i}(pfi | i)
```

we change `pfi` from `p(n,i)` to `p(n,i+2)` and program will not pass the typechecker.

## See also

This approach is used in `list_primes` from `src/prime.dats`, `src/prime.sats`.

