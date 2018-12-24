#include "share/atspre_staload.hats"

staload "isqrt.sats"
staload "prime.sats"

fn print_prime 
  {n,i,p:int | i <= n} 
  ( n              : int n
  , i              : int i
  , (pf_prime | p) : (PRIME(p) | int p) )
  :<fun1> void
= let
  val _ = println! ("p(", i, ") = ", p)
in () end

val _ = tabulate_primes(1000, print_prime)

implement main0() = ()
