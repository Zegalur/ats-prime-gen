#include "share/atspre_staload.hats"


(* SQRT(n,m) - m is the integer square root of n *)
dataprop SQRT (int, int) = 
  | {n,m: nat                   } 
    {m_2: nat     | n >= m_2    } 
    {m_inc_2: nat | n < m_inc_2 }
    SQRT(n, m) 
    of (MUL(m, m, m_2), MUL(m+1, m+1, m_inc_2))


(* Find the square root of a natural number *)
fn isqrt 
  {n: nat} 
  (n: int(n)) 
  : [m: nat] (SQRT(n, m) | int(m))


(* (b >= a) => (b^2 >= a^2) *)
prfn lemma_sqr_is_monotonic
  {a, b: nat | b >= a}
  {a2, b2: nat}
  ( a: int a
  , b: int b
  , pf_a2: MUL(a,a,a2)
  , pf_b2: MUL(b,b,b2) )
  : [b2 >= a2] void
  

(*  *)
prfn lemma_isqrt_div
    {n: pos         }
    {isqrt_n: pos   }
    {i: pos         }
    {div_ni: nat    }
    ( pf_isqrt_n : SQRT(n, isqrt_n) 
    , pf_div     : DIV(n, i, div_ni) )
    : [    (i >= isqrt_n+1 && div_ni <= isqrt_n)
        || (i <= isqrt_n   && div_ni >= isqrt_n)
      ] void