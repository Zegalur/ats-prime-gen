#define ATS_DYNLOADFLAG 0 // no need for dynloading at run-time

#include "share/atspre_staload.hats"

staload "divmod.sats"
staload "mul.sats"

(*dataprop DIVMOD_prop (int, int, int, int) =
  | {x, y: nat | y > 0       }
    {q, r: nat | r < y       }
    {qy: nat   | x == qy + r } 
    (* x = q * y + r *)
    DIVMOD_make(x, y, q, r)
    of (MUL(q, y, qy))

assume DIVMOD = DIVMOD_prop


primplement divmod_make {x,y}{q,r}(pf)
  = DIVMOD_make{x,y}{q,r}(pf)*)
  

local
//
prfn div_make {n:nat}{m:pos} () : [q:nat] DIV(n,m,q)
  = let
    prval pf_div_nm = div_istot{n,m}()
    prval pf_mul_qm = divmod_elim(pf_div_nm) 
    prval pf_mul_mq = mul_commute(pf_mul_qm)
    prval _         = lemma_mul_sgn_2(pf_mul_mq)
  in pf_div_nm end
//
//
prfn lemma_div_greater
    {n: nat         }
    {x: pos | x > n }
    ()
    : [div_nx: int | div_nx == 0]
      DIV(n,x,div_nx)
  = let
    // n = qx + r, r < x, x > n => q == 0, r == n
    prval pf_mul_0x  = mul_istot{0,x}()
    prval _          = lemma_mul_zero_is_zero(pf_mul_0x)
    prval pf_div_nx  = divmod_make{n,x}{0,n}(pf_mul_0x)
  in pf_div_nx end
//
//
prfn lemma_mod_lt_n
    {n, x: nat | n < x; x > 0}
    ()
    : DIVMOD(n,x,0,n)
  = let 
    prval pf_0x = mul_istot{0,x}()
    prval _     = lemma_mul_zero_is_zero(pf_0x)
  in divmod_make(pf_0x) end 
  
  
  prfn mod_lt_n
    {n, x: nat | n < x; x > 0}
    {q, r: nat | r < x}
    ( pf : DIVMOD(n,x,q,r) )
    : [q == 0; r == n] void
  = let 
    prval pf2 = lemma_mod_lt_n{n,x}()
    prval _   = divmod_isfun(pf,pf2)
  in () end 
//
in
//
primplement divmod_derive{x,y}{q,r}(pf)
   = sif y <= 1 then let
     prval pf_x1 = mul_istot{x,1}()
     prval _     = lemma_x_mul_1_is_x(pf_x1)
     prval pf2   = divmod_make{x,y}{x,0}(pf_x1)
     prval _     = divmod_isfun(pf,pf2)
  in () end
else sif x <= 0 then let
     prval pf_0y = MULbas{y}()
     prval pf2   = divmod_make{x,y}{0,0}(pf_0y)
     prval _     = divmod_isfun(pf,pf2)
  in () end
else sif y  < x then ()
else sif y  > x then let
     prval _     = mod_lt_n(pf)
  in () end
else (*  y == x   *) let
     prval pf_x1 = mul_istot{x,1}()
     prval _     = lemma_x_mul_1_is_x(pf_x1)
     prval pf_1x = mul_commute(pf_x1)
     prval pf2   = divmod_make{x,y}{1,0}(pf_1x)
     prval _     = divmod_isfun(pf,pf2)
  in () end
//
end


primplement divmod_istot_s{x,y}()
 = let prval pf = divmod_istot{x,y}()
       prval _  = divmod_derive(pf)
   in pf end


primplement lemma_n_mul_x_div_x{n}{x}{nx}{q,r}(pf_mul,pf_dm)
  = let
    prval pf2_dm = divmod_make{nx,x}{n,0}(pf_mul)
    prval _      = divmod_isfun(pf_dm, pf2_dm)
  in () end
  
  
primplement make_n_mul_x_div_x{n}{x}{nx}(pf_mul)
  = divmod_make{nx,x}{n,0}(pf_mul)
  
  
primplement lemma_divmod_add_1{x,y}{q,r}(pf)
  = sif r >= y - 1 (* r == y - 1 *)
    then let
        // (q+1)*y + 0 == q*y + y == q*y + r + 1 == x + 1
        prval pf_mul_qy          = divmod_elim(pf) // qy + r == x
        prval pf_mul_qp1_y       = mul_add_const{1}(pf_mul_qy)
        prval _                  = mul_nat_nat_nat(pf_mul_qp1_y)
        // DIVMOD((q+1)*y, y, q+1, 0)
        prval pf_dm_qp1y_y       = make_n_mul_x_div_x{q+1}{y}(pf_mul_qp1_y)
      in pf_dm_qp1y_y  end
    else let 
        prval pf_mul_qy          = divmod_elim(pf)
        prval pf_dm_xp1_y        = divmod_make{x+1,y}{q,r+1}(pf_mul_qy)
      in pf_dm_xp1_y end
      
      
primplement divmod_add_m0 {a,b}{x}{n,q,r} (pfa,pfb)
  = let
    prval pf_mul_nx   = divmod_elim(pfa)                      // n * x
    prval pf_mul_qx   = divmod_elim(pfb)                      // q * x
    prval pf_mul_nq_x = mul_distribute2(pf_mul_nx, pf_mul_qx) // (n + q) * x
    prval pf_dm_ab    = divmod_make{a+b,x}{n+q,r}(pf_mul_nq_x)
  in pf_dm_ab end


primplement divmod_add {x1,x2}{y}{q1,q2}{r1,r2} (pf1,pf2)
  = let
    prval pf_dm_r1_r2  = divmod_istot_s{r1+r2,y}()
    prval pf_mul_q1_y  = divmod_elim(pf1)                          // q1 * y
    prval pf_mul_q2_y  = divmod_elim(pf2)                          // q2 * y
    prval pf_mul_q12_y = mul_distribute2(pf_mul_q1_y, pf_mul_q2_y) // (q1+q2) * y
    prval pf_dm_q12_y  = make_n_mul_x_div_x(pf_mul_q12_y)
    prval pf_dm_x1_x2  = divmod_add_m0(pf_dm_q12_y, pf_dm_r1_r2)
  in (pf_dm_x1_x2, pf_dm_r1_r2) end
  
  
primplement lemma_divmod_expand_1 {n}{x}{q,r}{qx} (pf_dm,pf_mul_qx)
  = let
    prval pf_mul_q1    = mul_istot{q,1}()                      // q * 1
    prval pf_mul_q_xp1 = mul_distribute(pf_mul_qx, pf_mul_q1)  // q(x+1) = qx+q
    prval _            = mul_nat_nat_nat(pf_mul_q_xp1)
    prval pf2_mul_qxp1 = divmod_elim(pf_dm)                    // q(x+1)
    prval _            = mul_isfun(pf_mul_q_xp1, pf2_mul_qxp1)
    prval _            = lemma_x_mul_1_is_x(pf_mul_q1)         // q * 1 = q
  in () end


primplement divmod_dist_1 {n}{x}{q,r} (pf)
  = let
    prval pf_dm_qr      = divmod_istot_s{q+r,x}()              // DIVMOD(q+r,x,..)
    prval pf_mul_q_xp1  = divmod_elim(pf)                      // q * (x + 1)
    prval pf_mul_qx     = mul_istot{q,x}()                     // q * x
    prval pf_mul_q1     = mul_istot{q,1}()                     // q * 1
    prval pf2_mul_q_xp1 = mul_distribute(pf_mul_qx, pf_mul_q1) // q(x+1) = qx+q
    prval _             = mul_isfun(pf_mul_q_xp1, pf2_mul_q_xp1)
    prval _             = mul_nat_nat_nat(pf_mul_qx)
    prval pf_dm_qx      = make_n_mul_x_div_x(pf_mul_qx)        // DIVMOD(qx,x,q,0)
    prval pf_dm_n       = divmod_add_m0(pf_dm_qx, pf_dm_qr)    // DIVMOD(qx+q+r,x..)
    prval _             = lemma_x_mul_1_is_x(pf_mul_q1)        // q * 1 = q
  in (pf_dm_n, pf_dm_qr) end
  
  
primplement div_inc_2 {n}{x} ()
  = let
    prval pf_div_n_xp1 = divmod_istot_s{n,x+1}()
    prval (pf_div_n_x, pf_dm_qr_x) = divmod_dist_1{n}{x}(pf_div_n_xp1)
  in (pf_div_n_x, pf_div_n_xp1) end
  
  
primplement div_inc {n}{x} ()
  = let
    prval pf_div_n_x   = divmod_istot_s{n,x}()
    prval pf_div_np1_x = lemma_divmod_add_1(pf_div_n_x)
  in (pf_div_n_x, pf_div_np1_x) end
  
  
primplement div_cmp {a,b}{n} ()
  = let
    prval pf_dm_a_n      = divmod_istot_s{a  ,n}()
    prval pf_dm_bma_n    = divmod_istot_s{b-a,n}()
    prval (pf_dm_b_n, _) = divmod_add(pf_dm_bma_n, pf_dm_a_n)
  in (pf_dm_a_n, pf_dm_b_n) end
  
  
primplement lemma_div_cmp {a,b}{n}{div_an,div_bn} (pf_a,pf_b)
  = let
    prval (pf2_a, pf2_b) = div_cmp{a,b}{n}()
    prval _              = divmod_isfun(pf2_a, pf_a)
    prval _              = divmod_isfun(pf2_b, pf_b)
  in () end
  

primplement div_cmp_2 {n}{a,b} ()
  = let
    prfun loop
      {n:              nat                    }
      {a, b:           pos | a <= b           }
      {i:              pos | i >= a; i <= b   }
      {div_na, div_ni: nat | div_na >= div_ni }
      .<b-i>.
      ( pf_div_na : DIV(n,a,div_na)
      , pf_div_ni : DIV(n,i,div_ni) )
      : [div_na, div_nb: nat | div_na >= div_nb] 
        (DIV(n,a,div_na), DIV(n,b,div_nb))
    = sif i >= b (* i == b *)
      then (pf_div_na, pf_div_ni)
      else let
          prval (pf2_ni, pf_nip1) = div_inc_2{n}{i}()
          prval _                 = divmod_isfun(pf2_ni, pf_div_ni)
        in loop(pf_div_na, pf_nip1) end
    //
    prval pf_dm_na = divmod_istot_s{n,a}()
  in loop(pf_dm_na, pf_dm_na) end
  
  
primplement lemma_div_cmp_2 {n}{a,b}{div_na,div_nb} (pf_a,pf_b)
  = let
    prval (pf2_a, pf2_b) = div_cmp_2{n}{a,b}()
    prval _              = divmod_isfun(pf2_a, pf_a)
    prval _              = divmod_isfun(pf2_b, pf_b)
  in () end
  
  
primplement divmod_cmp_law {a,b}{x}{u,v,r} (pfa,pfb)
  = let
    prval pf_mul_ux = divmod_elim(pfa) // MUL(u,x,ux), a == ux+r
    prval pf_mul_vx = divmod_elim(pfb) // MUL(v,x,vx), b == vx+r
    prval _         = lemma_mul_cmp_l(pf_mul_ux,pf_mul_vx) // u < v
  in () end
  
  
primplement div_cmp_law {n}{a}{x}{ax}{q,r} (pf_mul,pf_dm)
  = let
    prval pf_mul_qx = divmod_elim(pf_dm) // MUL(q,x,qx), qx <= n, n < ax
    prval _         = lemma_mul_cmp_l(pf_mul_qx,pf_mul) // qx < ax => q < a
  in () end
  

primplement lemma_divmod_nonzero_mod {n}{x}{r} (pf)
  = let
    prval pf_mul_0x = divmod_elim(pf)
    prval _         = lemma_mul_zero_is_zero(pf_mul_0x)
  in () end
  
  

primplement lemma_mod_cmp {n}{a,b}{q}{ra,rb} (pf1,pf2)
= let
prfun lemma_mod_cmp_impl
    {n:     nat                  }
    {a, b:  pos | a <= b         }
    {q:     nat                  }
    {ra,rb: nat | ra < a; rb < b }
    .<q>.
    ( pf1 : DIVMOD(n,a,q,ra)
    , pf2 : DIVMOD(n,b,q,rb) )
    : [ra >= rb; 
             (q == 0 && ra == rb) 
          || (q > 0 && ((a == b && ra == rb) || (a < b && ra > rb))) 
      ] void 
  = sif q <= 0 // q == 0
    then let
      prval _ = lemma_divmod_nonzero_mod(pf1) // ra == n
      prval _ = lemma_divmod_nonzero_mod(pf2) // rb == n
    in () end
    else sif a >= b // a == b
    then let
      prval _ = divmod_isfun(pf1,pf2)
    in () end
    else let   // q > 0, a < b
      prval pf_mul_qa    = divmod_elim(pf1)       // MUL(q,a,qa), n=qa+ra
      prval pf_mul_qb    = divmod_elim(pf2)       // MUL(q,b,qb), n=qb+rb
      prval pf_mul_qnega = mul_negate2(pf_mul_qa) // MUL(q,~a,~qa)
      prval pf_mul_q_bma = mul_distribute(pf_mul_qb,pf_mul_qnega) //MUL(q,b-a,qb-qa)
      prval pf_mul_bma_q = mul_commute(pf_mul_q_bma) // MUL(b-a,q,qb-qa)
      prval _            = mul_pos_pos_pos(pf_mul_bma_q) // qb-qa>0
    in () end
in lemma_mod_cmp_impl{n}{a,b}{q}{ra,rb}(pf1,pf2) end
    
  
primplement lemma_pos_mod_commute 
  {n,i,div_ni,mod_div_ni}{mod_ni,q} (pf_dm_ni,pf_mod_div_ni)
  = let // q >= i
    prval _              = lemma_div_cmp_2(pf_mod_div_ni,pf_dm_ni) // q>=div_ni
    prval pf_q_mul_divni = divmod_elim(pf_mod_div_ni)       // MUL(q,div_ni,h)
    prval pf_divni_mul_q = mul_commute(pf_q_mul_divni)      // MUL(div_ni,q,h)
    prval _              = mul_pos_pos_pos(pf_divni_mul_q)  // h > 0
    prval pf2_dm_nq      = divmod_make{n,q}{div_ni,mod_div_ni}(pf_divni_mul_q)
    prval _     = lemma_mod_cmp{n}{i,q}(pf_dm_ni,pf2_dm_nq) //mod_ni>mod_div_ni
  in () end
  
  
