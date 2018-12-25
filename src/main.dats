#include "share/atspre_staload.hats"

staload "isqrt.sats"
staload "prime.sats"

dataprop CALL (int, int) =
  | {n: int}
	CALLbas(n, 0)
  | {n, i: int | i <= n}
	CALLind(n, i) of (CALL(n,i-1))

fn print_prime 
  {n,i,p:int | i < n} 
  ( pf_iprime      : IPRIME(i, p)
  , pfi            : CALL(n, i)
  | n              : int n
  , i              : int i
  , p              : int p )
  :<fun1> (CALL(n,i+1) | void)
= let
  val      _ = println! ("p(", i, ") = ", p)
  prval pfi1 = CALLind{n, i+1}(pfi)
in (pfi1 | ()) end

val _ = list_primes(CALLbas | 1000, print_prime)

implement main0() = ()
