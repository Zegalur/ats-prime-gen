#include "share/atspre_staload.hats"

staload "isqrt.sats"

(* PRIME_FOR(n,m) means that integer n>1 is not divisible
   by any positive number <= m except 1 *)
dataprop PRIME_FOR (int, int) = 
  | (* PRIME_FOR(n,1) is obviously holds for any n>1 *)
    {n: pos | n > 1}
    PRIME_FOR_bas(n, 1) 
    of () 
  | (* PRIME_FOR(n,m) holds if n is not divisible 
       by m and we have that PRIME_FOR(n,m-1) *)
    {n: pos | n > 1}
    {m: pos | m > 1}
    {r: nat | r > 0}
    PRIME_FOR_ind(n, m)
    of (PRIME_FOR(n, m-1), MOD(n, m, r))
    

(* PRIME(n) - n is a prime number *)
dataprop PRIME (int) = 
  | (* n>1 is prime if it is not divisible by any 
       natural number m<n except 1 *)
    {n: pos | n > 1}
    PRIME(n)
    of (PRIME_FOR(n,n-1))
    
    
prfn lemma_2_is_prime () : PRIME(2)


prfn lemma_3_is_prime () : PRIME(3)


(* if p > q (where p is prime)
   then (p mod q) > 0 and (p mod q) < q for any q > 1 *)
prfn lemma_prime_mod_gtz
  {p: int | p > 1            }
  {q: pos | q < p; q > 1     }
  {r: int                    }
  ( pf_p_prime: PRIME(p)
  , pf_mod:     MOD(p,q,r) )
  : [r > 0; r < q] void
  

(* If p>2 is prime then p is odd. *)
prfn lemma_prime_gt_2_is_odd
  {n: int | n > 2}
  {r: int}
  ( pf_prime: PRIME(n) 
  , pf_mod2:  MOD(n,2,r))
  : [r == 1] void


(* For n > 1 if PRIME_FOR(n, isqrt(n)) then PRIME(n) *)
prfn lemma_isqrt_prime_1
  {n: int | n > 1 }
  {isqrt_n: pos | isqrt_n < n }
  ( pf_isqrt:             SQRT(n, isqrt_n)
  , pf_prime_for_isqrt:   PRIME_FOR(n, isqrt_n) )
  : PRIME(n)