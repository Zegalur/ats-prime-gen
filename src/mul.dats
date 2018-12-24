#define ATS_DYNLOADFLAG 0 // no need for dynloading at run-time

#include "share/atspre_staload.hats"

staload "mul.sats"


local
//
prfun lemma_nat_mul_1_is_nat
    {x: nat}
    {y: int}
    .<x>.
    ( pf_x1: MUL(x,1,y) )
    : [y == x] void
  = sif x <= 0  // x == 0
      then let
          prval pf_01_0 = MULbas{1}()
          prval _       = mul_isfun(pf_01_0, pf_x1)
        in () end
      else let // x > 0
          prval pf_xm1  = mul_istot{x-1,1}()
          prval _       = lemma_nat_mul_1_is_nat{x-1}(pf_xm1)
          prval pf2_x1  = mul_add_const{1}{x-1,1}(pf_xm1)
          prval _       = mul_isfun(pf_x1, pf2_x1)
        in () end
in
//
primplement 
  lemma_x_mul_1_is_x {x}{y} (pf_x1)
  = sif x < 0 
      then let
          prval pf_neg = mul_istot{~x,1}()
          prval _      = lemma_nat_mul_1_is_nat{~x}(pf_neg)
          prval pf2_x1 = mul_negate{~x,1}(pf_neg)
          prval _      = mul_isfun(pf_x1, pf2_x1)
        in () end
      else lemma_nat_mul_1_is_nat{x}{y}(pf_x1)
end


local
//
(* This proof function establishes that if we 
   have three integers a>0, b, ab>=0 such that 
   a*b=ab, then b>=0 and if ab=0 then b=0, 
   if ab>0 then ab>0.  *)
prfn lemma_mul_gez
    {a:  pos}
    {b:  int}
    {ab: nat}
    ( pf: MUL(a,b,ab) )
    : [b >= 0; 
            (ab == 0 && b == 0) 
         || (ab > 0  && b >  0)] 
      void
  = let
    prfun loop
      {a:  pos}
      {b:  int}
      {ab: int}
      {i:  pos | i <= a}
      {ib: int | (ib < 0 && b < 0) || (ib == 0 && b == 0) || (ib > 0 && b > 0) }
      .<a-i>.
      ( pfi: MUL(i,b,ib)
      , pf : MUL(a,b,ab) )
      : [(ab < 0 && b < 0) || (ab == 0 && b == 0) || (ab > 0 && b > 0)] void
    = sif i >= a (* i == a *)
      then mul_isfun(pf,pfi)
      else let
          prval pfi_inc = mul_add_const{1}(pfi)
        in loop(pfi_inc, pf) end
    //
    prval pf1 = mul_istot{1,b}()
    prval _   = lemma_x_mul_1_is_x(mul_commute(pf1))
  in loop(pf1, pf) end
//
in
//
primplement lemma_mul_sgn_2 {a}{b}{ab} (pf)
  = sif ab < 0
      then let
          prval pf_ba  = mul_commute(pf)
          prval pf_neg = mul_negate(pf_ba)
          prval pf_nab = mul_commute(pf_neg)
          prval _      = lemma_mul_gez(pf_nab)
        in () end
      else lemma_mul_gez(pf)
//
end
      
      
primplement lemma_mul_sgn {a}{b}{ab} (pf)
  = lemma_mul_sgn_2(mul_commute(pf))
      
      
primplement lemma_mul_zero_is_zero {n,n0} (pf_n0)
  = let prval MULbas() = pf_n0 in () end            
  
  
primplement lemma_mul_zero_is_zero_2 {n,n0} (pf_n0)
  = lemma_mul_zero_is_zero(mul_commute(pf_n0))
  

local
//
prfn mul_pos_eq_law
    {a,b,m: int }
    {x: pos }
    ( pfa : MUL(a,x,m)
    , pfb : MUL(b,x,m) )
    : [a == b] void
  = let
    prval pf_neg_a_x = mul_negate(pfa)                 // MUL(~a,x,~m)
    prval pf_mul_bma = mul_distribute2(pfb,pf_neg_a_x) // MUL(b-a,x,0)
    prval _          = lemma_mul_sgn(pf_mul_bma)       // b-a==0
  in () end
//
prfn mul_eq_law
    {a,b,m: int }
    {x: int | (x < 0) || (x > 0) }
    ( pfa : MUL(a,x,m)
    , pfb : MUL(b,x,m) )
    : [a == b] void
  = sif x < 0 
    then mul_pos_eq_law(mul_negate2(pfa),mul_negate2(pfb))
    else mul_pos_eq_law(pfa,pfb)
//
prfn mul_cmp_law
    {a,b: int             }
    {x:   pos             }
    {ax,bx: int | ax < bx }
    ( pfa : MUL(a,x,ax)
    , pfb : MUL(b,x,bx) )
    : [a < b] void
  = let
    prval pf_neg_a_x = mul_negate(pfa)                 // MUL(~a,x,~ax)
    prval pf_mul_bma = mul_distribute2(pfb,pf_neg_a_x) // MUL(b-a,x,bx-ax)
    prval pf2_mul    = mul_commute(pf_mul_bma)         // MUL(x,b-a,bx-ax)
    prval _          = lemma_mul_sgn_2(pf2_mul)        // bx-ax>0 => b-a>0
  in () end
//
in
// 
primplement lemma_mul_cmp_l {a,b}{x}{ax,bx}(pfa,pfb) = 
     sif (x > 0 && ax < bx) then mul_cmp_law(pfa,pfb)
else sif (x > 0 && ax > bx) then mul_cmp_law(pfb,pfa)
else sif (x > 0 && ax ==bx) then mul_eq_law(pfa,pfb)
else sif (x < 0 && ax < bx) then mul_cmp_law(mul_negate2(pfb),mul_negate2(pfa))
else sif (x < 0 && ax > bx) then mul_cmp_law(mul_negate2(pfa),mul_negate2(pfb))
else(*sif(x < 0 && ax ==bx)then*)mul_eq_law(pfa,pfb)
//
end


primplement lemma_mul_cmp_l2 {a,b}{x}{ax,bx}(pfa,pfb) 
  = lemma_mul_cmp_l(mul_commute(pfa), mul_commute(pfb))
  

primplement lemma_pos_mul_x_sgn_x {d}{x}{m} (pf)
   = sif x >= 0
     then let
       prval pf_d1 = mul_istot{d,1}() // MUL(d,1,d)
       prval _     = lemma_x_mul_1_is_x(pf_d1)
       prval _     = 
         lemma_mul_cmp_l(mul_commute(pf),mul_commute(pf_d1)) // x < 1
     in () end
     else () 
     
