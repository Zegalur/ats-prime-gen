#define ATS_DYNLOADFLAG 0 // no need for dynloading at run-time

#include "share/atspre_staload.hats"

staload "isqrt.sats"
staload "divmod.sats"


(* (b >= a) => (b^2 >= a^2) *)
primplement lemma_sqr_is_monotonic {a,b}{a2,b2} (pf_a2,pf_b2)
= let
  prfun build_b2_from_a2
    {a, b: nat | b >= a}
    {a2: nat}
    .<b>.
    ( pf_a2: MUL(a,a,a2) )
    : [b2: nat | b2 >= a2] MUL(b,b,b2)
  = sif b > a
      then let  
        prval pf_bd_bd = build_b2_from_a2{a,b-1}(pf_a2)
        prval pf_b_bd  = MULind(pf_bd_bd)
        prval pf_bd_b  = mul_commute(pf_b_bd)
        prval pf_b_b   = MULind(pf_bd_b)
      in pf_b_b end
      else pf_a2 (* b == a *)
    
  prval pf_b2r = build_b2_from_a2{a,b}(pf_a2)
  prval _ = mul_isfun(pf_b2r, pf_b2)
in () end


(* 0 * n = 0 *)
primplement lemma_mul_zero_is_zero {n,n0} (pf_n0)
= let prval MULbas() = pf_n0 in () end


(* n^2 > n for n > 1  *)
primplement lemma_n2_gt_n_for_n_gt_1 {n}{n2} (pf_n2)
= let prval _ = mul_pos_pos_pos(pf_n2) in () end


(* square of natural number with more specific type *)
implement sqr_nat {n} (n) 
= let 
  val   (pf_n2 | n2) = g1int_mul2(n,n)
  prval _            = mul_nat_nat_nat(pf_n2)
in 
  if n <= 0 then      (* n == 0 *)
    let prval _ = lemma_mul_zero_is_zero(pf_n2)
    in (pf_n2 | n2) end
  else if n <= 1 then (* n == 1 *)
    let prval one = 1
        prval pf_01_0 = MULbas{1}()
        prval pf_11_1 = MULind{0}{1}{0}(pf_01_0)
        prval _ = mul_isfun(pf_n2, pf_11_1)
    in (pf_n2 | n2) end
  else (* n > 1 *)
    let prval _ = lemma_n2_gt_n_for_n_gt_1{n}(pf_n2)
    in (pf_n2 | n2) end
end



implement isqrt (n)
= let
    fun loop
      {n,a,b: nat | n > 1; a < b; a < n}
      {a2,b2: nat | a2 <= n; b2 > n}
      .<b-a>.
      ( n: int(n), a: int(a), b: int(b)
      , (pf_a2 | a2): (MUL(a,a,a2) | int(a2))
      , (pf_b2 | b2): (MUL(b,b,b2) | int(b2)) )
      : [m:nat | m < n; m > 0] (SQRT (n, m) | int(m))
    = let
      val diff = b - a
    in 
      if diff > 1 
        then let
          val m            = a + half(diff)
          val (pf_m2 | m2) = sqr_nat(m)
        in 
          if m2 > n
            then loop(n, a, m, (pf_a2 | a2), (pf_m2 | m2))
            else loop(n, m, b, (pf_m2 | m2), (pf_b2 | b2))
        end
      else (*diff <= 1*) let 
          val ai              = a + 1
          val (pf_ai2 | ai2)  = sqr_nat(ai)
          prval _             = mul_isfun(pf_ai2, pf_b2)
        in (SQRT(pf_a2, pf_ai2) | a) end
    end

    val a = 0
    val b = n
    val (pf_a2 | a2) = sqr_nat(a)
    val (pf_b2 | b2) = sqr_nat(b)
in 
  if n > 1 
    then let 
      in loop(n, a, b, (pf_a2 | a2), (pf_b2 | b2)) end
    else let
      val ni             = n + 1
      val (pf_n2  | n2 ) = sqr_nat(n)
      val (pf_ni2 | ni2) = sqr_nat(ni)
      in (SQRT(pf_n2, pf_ni2) | n) end
end


prfn lemma_n_div_isqrt1_le_isqrt
    {n:       pos }
    {isqrt_n: pos }
    ( pf_isqrt_n : SQRT(n, isqrt_n) )
    : [q: nat | q <= isqrt_n] 
      DIV(n, isqrt_n+1, q)
  = let
    prval SQRT(_,pf_mp1_mp1) = pf_isqrt_n // MUL(m+1,m+1,(m+1)^2), m==isqrt(n)
    prval pf_dm_n_mp1        = divmod_istot{n,isqrt_n+1}() // DIVMOD(n,m+1,q,r)
    prval _                  = div_cmp_law(pf_mp1_mp1,pf_dm_n_mp1) // q < isqrt(n)+1
  in pf_dm_n_mp1 end
  
  
local
//
prfn lemma_n_div_isqrt_ge_isqrt
    {n:       pos }
    {isqrt_n: pos }
    ( pf_isqrt_n : SQRT(n, isqrt_n) )
    : [q: nat | q >= isqrt_n] 
      DIV(n, isqrt_n, q)
  = let
    prval SQRT(pf_mm,_) = pf_isqrt_n // MUL(m,m,m^2), m==isqrt(n)
    prval pf_dm_mm_m    = make_n_mul_x_div_x(pf_mm)   // DIVMOD(mm,m,m,0)
    prval pf_dm_n_m     = divmod_istot{n,isqrt_n}()   // DIVMOD(n,m,q,r)
    prval _             = lemma_div_cmp(pf_dm_mm_m, pf_dm_n_m)
  in pf_dm_n_m end
//
//
prfn lemma_isqrt1_div
    {n: pos                          }
    {isqrt_n: pos                    }
    {i: pos | i >= isqrt_n+1         }
    {div_ni: nat                     }
    ( pf_isqrt_n : SQRT(n, isqrt_n) 
    , pf_div     : DIV(n, i, div_ni) )
    : [div_ni <= isqrt_n] void
  = let
    // STEP 1: show that (n / (isqrt_n + 1)) <= (isqrt_n + 1)
    prval pf_dm_n_mp1 = lemma_n_div_isqrt1_le_isqrt(pf_isqrt_n)
    // STEP 2: show that for all i>=(isqrt_n + 1)  =>  n/i <= isqrt_n
    prval pf_dm_n_i   = divmod_istot{n,i}()
    prval _           = lemma_div_cmp_2(pf_dm_n_mp1, pf_dm_n_i)
    prval _           = divmod_isfun(pf_div,pf_dm_n_i)
  in () end
//
//
prfn lemma_isqrt1_div_2
    {n: pos                          }
    {isqrt_n: pos                    }
    {i: pos | i <= isqrt_n           }
    {div_ni: nat                     }
    ( pf_isqrt_n : SQRT(n, isqrt_n) 
    , pf_div     : DIV(n, i, div_ni) )
    : [div_ni >= isqrt_n] void
  = let
    // STEP 1: show that (n / isqrt_n) >= isqrt_n
    prval pf_dm_n_mp1 = lemma_n_div_isqrt_ge_isqrt(pf_isqrt_n)
    // STEP 2: show that for all i <= isqrt_n  =>  n/i >= isqrt_n
    prval pf_dm_n_i   = divmod_istot{n,i}()
    prval _           = lemma_div_cmp_2(pf_dm_n_i,pf_dm_n_mp1)
    prval _           = divmod_isfun(pf_div,pf_dm_n_i)
  in () end
//
in 
//
primplement lemma_isqrt_div {n}{isqrt_n}{i}{div_ni} (pf_isqrt_n,pf_div)
= sif i >= isqrt_n + 1 
   then lemma_isqrt1_div(pf_isqrt_n,pf_div)
   else lemma_isqrt1_div_2(pf_isqrt_n,pf_div)
//
end



