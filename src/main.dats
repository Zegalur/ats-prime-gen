#include "share/atspre_staload.hats"

staload "isqrt.sats"
staload "prime.sats"

dataview CALL (int, int) =
  | {n: nat}
    CALLbas(n, 0)
  | {n, i: nat | i <= n}
    CALLind(n, i) of (CALL(n,i-1))

fn print_prime 
  {n,i,p:nat | i < n} 
  ( pf_iprime      : IPRIME(i, p)
  , pfi            : !CALL(n,i) >> CALL(n,i+1)
  | n              : int n
  , i              : int i
  , p              : int p )
  :<fun1> void
= let
  val   _ = println! ("p(", i+1, ") = ", p)
  prval _ = pfi := CALLind(pfi)
in () end

prval pf0 = CALLbas
val _ = list_primes(pf0 | 10000, print_prime)


implement main0() = ()
