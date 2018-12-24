#include "share/atspre_staload.hats"


(* This proof function establishes x*1==x *)
prfn lemma_x_mul_1_is_x
    {x: int}
    {y: int}
    ( pf_x1: MUL(x,1,y) )
    : [y == x] void
      
     
(* Derive the sign of the multiplication result. *) 
prfn lemma_mul_sgn
    {a:  int}
    {b:  pos}
    {ab: int}
    ( pf: MUL(a,b,ab) )
    : [(ab < 0 && a < 0) 
        || (ab == 0 && a == 0) 
        || (ab > 0 && a > 0)] 
      void
     
     
(* Derive the sign of the multiplication result. *) 
prfn lemma_mul_sgn_2
    {a:  pos}
    {b:  int}
    {ab: int}
    ( pf: MUL(a,b,ab) )
    : [(ab < 0 && b < 0) 
        || (ab == 0 && b == 0) 
        || (ab > 0 && b > 0)] 
      void
      
      
(* 0 * n = 0 *)
prfn lemma_mul_zero_is_zero
    {n, n0: int}
    (pf_n0: MUL(0,n,n0))
    : [n0 == 0] void


(* n * 0 = 0 *)
prfn lemma_mul_zero_is_zero_2
    {n, n0: int}
    (pf_n0: MUL(n,0,n0))
    : [n0 == 0] void
      
  
(* Derive order information in the case
   when multiplier is the same. *)
prfn lemma_mul_cmp_l
    {a,b: int                  }
    {x:   nat | x > 0 || x < 0 }
    {ax,bx: int                }
    ( pfa : MUL(a,x,ax)
    , pfb : MUL(b,x,bx) )
    : [(x > 0 && ax < bx && a < b)
        || (x > 0 && ax > bx && a > b)
        || (x > 0 && ax ==bx && a ==b)
        || (x < 0 && ax < bx && a > b)
        || (x < 0 && ax > bx && a < b)
        || (x < 0 && ax ==bx && a ==b)] 
      void
      
      
(* Derive order information in the case 
   when multiplicand is the same. *)
prfn lemma_mul_cmp_l2
    {a,b: int                  }
    {x:   nat | x > 0 || x < 0 }
    {ax,bx: int                }
    ( pfa : MUL(x,a,ax)
    , pfb : MUL(x,b,bx) )
    : [(x > 0 && ax < bx && a < b)
        || (x > 0 && ax > bx && a > b)
        || (x > 0 && ax ==bx && a ==b)
        || (x < 0 && ax < bx && a > b)
        || (x < 0 && ax > bx && a < b)
        || (x < 0 && ax ==bx && a ==b)] 
      void
      

(* If d*x<d when d>0 then x<=0 *)
prfn lemma_pos_mul_x_sgn_x
    {d: pos         }
    {x: int         }
    {m: int | d > m }
    ( pf : MUL(d,x,m) )
    : [x <= 0] void



