#include "share/atspre_staload.hats"


(* This proof function generate DIVMOD from a 
   multiplication. *)
praxi divmod_make
  {x, y: nat | y > 0                }
  {q, r: nat | r < y                }
  {qy: nat   | x == qy + r; qy <= x } 
  ( pf : MUL(q, y, qy) )
  : DIVMOD(x, y, q, r)
  

(* Derive useful information about DIVMOD. *)
prfn divmod_derive
  {x, y: nat | y > 0       }
  {q, r: nat | r < y       }
  ( pf : DIVMOD(x, y, q, r) )
  : [   (y == 1 && q == x && r == 0)
     || (x == 0 && q == 0 && r == 0)
     || (y < x)
     || (y == x && q == 1 && r == 0)
     || (y  > x && q == 0 && r == x)]
    void


(* Same as divmod_istot but with more specific
   type information. *)
prfn divmod_istot_s
  {x, y: nat | y > 0}
  ()
  : [q,r:nat | r < y;
        (y == 1 && q == x && r == 0)
     || (x == 0 && q == 0 && r == 0)
     || (y < x)
     || (y == x && q == 1 && r == 0)
     || (y  > x && q == 0 && r == x)] 
    DIVMOD(x, y, q, r)
    
    
(* Show that (n*x)/x == n *)
prfn lemma_n_mul_x_div_x
    {n:  nat          }
    {x:  pos          }
    {nx: nat          }
    {q,r: nat | r < x }
    ( pf_mul : MUL(n,x,nx)
    , pf_dm  : DIVMOD(nx,x,q,r) )
    : [q == n; r == 0] void
    

(*  *)
prfn make_n_mul_x_div_x
    {n:  nat }
    {x:  pos }
    {nx: nat }
    ( pf_mul : MUL(n,x,nx) )
    : DIVMOD(nx,x,n,0)


(* For a given DIVMOD(x,y,..) this function will
   construct DIVMOD(x+1,y..) with a rich type. *)
prfn lemma_divmod_add_1
    {x, y: nat | y > 0 }
    {q, r: nat | r < y }
    ( pf : DIVMOD(x,y,q,r) )
    : [u, v: nat 
        | v < y 
        ;   (r  < y-1 && u == q   && v == r+1) 
         || (r == y-1 && u == q+1 && v == 0)]
      DIVMOD(x+1, y, u, v)
      
      
(* Construct DIVMOD(a+b,x,n+q,r) when we have
   DIVMOD(a,x,n,0) and DIVMOD(b,x,q,r) 
   (note that MOD(a,n,0)). *)
prfn divmod_add_m0
    {a,b:   nat }
    {x:     pos }
    {n,q,r: nat }
    ( pfa : DIVMOD(a,x,n,0)
    , pfb : DIVMOD(b,x,q,r) )
    : DIVMOD(a+b,x,n+q,r)


(* Construct DIVMOD(x1+x2,y,q1+q2+q,r) from 
   DIVMOD(x1,y,q1,r1) and DIVMOD(x2,y,q2,r2),
   where DIVMOD(r1+r2,y,q,r). *)
prfn divmod_add
    {x1, x2: nat                  }
    {y: pos                       }
    {q1, q2: nat                  }
    {r1, r2: nat | r1 < y; r2 < y }
    ( pf1 : DIVMOD(x1,y,q1,r1)
    , pf2 : DIVMOD(x2,y,q2,r2) )
    : [q, r: nat | r < y]
      ( DIVMOD(x1+x2, y, q1+q2+q, r)
      , DIVMOD(r1+r2, y, q, r) )


(* Show that if DIVMOD(n,x+1,q,r) and
   MUL(q,x,qx) then n == qx + q + r. *)
prfn lemma_divmod_expand_1
    {n:   nat         }
    {x:   pos         }
    {q,r: nat | r < x }
    {qx:  nat         }
    // n == q(x+1) + r
    ( pf_dm     : DIVMOD(n,x+1,q,r) 
    , pf_mul_qx : MUL(q,x,qx) )
    : [ n == qx + q + r ] void


(* From DIVMOD(n,x+1,q,r) construct
   DIVMOD(n,x,q+qr_div_x,qr_mod_x) and
   DIVMOD(q+r,x,qr_div_x,qr_mod_x). *)
prfn divmod_dist_1
    {n:    nat  }
    {x:    pos  }
    {q, r: nat  }
    ( pf : DIVMOD(n,x+1,q,r) )
    : [qr_div_x, qr_mod_x: nat]
      ( DIVMOD(n   ,x ,q+qr_div_x ,qr_mod_x)
      , DIVMOD(q+r ,x ,qr_div_x   ,qr_mod_x) )

      
      
(* (n div x) <= ((n+1) div x) *)
prfn div_inc
    {n: nat }
    {x: pos }
    ()
    : [ div_nx, div_np1_x: nat 
      | div_nx <= div_np1_x ]
      (DIV(n,x,div_nx), DIV(n+1,x,div_np1_x))
      
      
(* (n div x) >= (n div (x+1)) *)
prfn div_inc_2
    {n: nat }
    {x: pos }
    ()
    : [ div_nx, div_n_xp1: nat 
      | div_nx >= div_n_xp1 ]
      (DIV(n,x,div_nx), DIV(n,x+1,div_n_xp1))
      
      
(* If a <= b then (a div n) <= (b div n) *)
prfn div_cmp
    {a, b: nat | a <= b }
    {n: pos             }
    ()
    : [div_an, div_bn: nat | div_an <= div_bn] 
      (DIV(a,n,div_an), DIV(b,n,div_bn))
      
      
(* If a <= b then (a div n) <= (b div n) *)
prfn lemma_div_cmp
    {a, b: nat | a <= b  }
    {n: pos              }
    {div_an, div_bn: nat }
    ( pf_a : DIV(a,n,div_an)
    , pf_b : DIV(b,n,div_bn) )
    : [div_an <= div_bn] void
      
      
(* If a <= b then (n div a) >= (n div b) *)
prfn div_cmp_2
    {n: nat             }
    {a, b: pos | a <= b }
    ()
    : [div_na, div_nb: nat | div_na >= div_nb] 
      (DIV(n,a,div_na), DIV(n,b,div_nb))
      
      
(* If a <= b then (n div a) >= (n div b) *)
prfn lemma_div_cmp_2
    {n: nat              }
    {a, b: pos | a <= b  }
    {div_na, div_nb: nat }
    ( pf_a : DIV(n,a,div_na)
    , pf_b : DIV(n,b,div_nb) )
    : [div_na >= div_nb] void
    
    
(* If a < b and (a mod x)==(b mod x)
   then (a div x) < (b div x). *)
prfn divmod_cmp_law
    {a,b: nat   | a < b }
    {x: pos             }
    {u,v,r: nat | r < x }
    ( pfa : DIVMOD(a,x,u,r)
    , pfb : DIVMOD(b,x,v,r) )
    : [u < v] void
    
    
(* If n < ax then (n div x) < a. *)
prfn div_cmp_law
    {n: nat            }
    {a: nat            }
    {x: pos            }
    {ax: nat  | n < ax }
    {q,r: nat | r < x  }
    ( pf_mul : MUL(a,x,ax)
    , pf_dm  : DIVMOD(n,x,q,r) )
    : [q < a] void
    
    
(* If (n div x) == 0 then (n mod x) == n. *)
prfn lemma_divmod_nonzero_mod
    {n: nat         }
    {x: pos         }
    {r: nat | r < x }
    ( pf : DIVMOD(n,x,0,r) )
    : [r == n] void
    
    
(* *)
prfn lemma_mod_cmp
    {n:     nat                  }
    {a, b:  pos | a <= b         }
    {q:     nat                  }
    {ra,rb: nat | ra < a; rb < b }
    ( pf1 : DIVMOD(n,a,q,ra)
    , pf2 : DIVMOD(n,b,q,rb) )
    : [ra >= rb; 
             (q == 0 && ra == rb) 
          || (q > 0 && ((a == b && ra == rb) 
          || (a < b && ra > rb))) 
      ] void 
      
      
(*  *)
prfn lemma_pos_mod_commute
    {n, i, div_ni, mod_div_ni: pos 
      | mod_div_ni < div_ni; div_ni < i }
    {mod_ni,q: nat 
      | mod_ni < i; q >= i }
    ( pf_dm_ni      
      : DIVMOD(n,i,div_ni,mod_ni)
    , pf_mod_div_ni 
      : DIVMOD(n,div_ni,q,mod_div_ni) )
    : [mod_ni > 0] void
    
    
