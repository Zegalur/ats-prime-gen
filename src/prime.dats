#define ATS_DYNLOADFLAG 0 // no need for dynloading at run-time

#include "share/atspre_staload.hats"

staload "prime.sats"
staload "isqrt.sats"
staload "divmod.sats"
staload "mul.sats"



primplement lemma_2_is_prime ()
= PRIME(PRIME_FOR_bas{2}())
  
  
primplement lemma_3_is_prime ()
= let prval pf_1x2e2 = mul_make{1,2}()
      prval dmp1     = divmod_make{3,2}{1,1}{2}(pf_1x2e2)
      prval pf1      = PRIME_FOR_bas{3}()            
      prval pf2      = PRIME_FOR_ind{3}{2}{1}(pf1, dmp1)
  in PRIME(pf2) end


(*  *)
prfn lemma_prime_for_mod_gtz
  {n: pos                 }
  {m: pos | m > 0; m < n  }
  {i: pos | i <= m; i > 1 }
  ( pf_prime_for: PRIME_FOR(n, m) )
  : [r: pos] MOD(n, i, r)
= let
  prfun loop
    {n: pos                 }
    {m: pos | m > 0; m < n  }
    {i: pos | i <= m; i > 1 }
    .<m>.
    ( pf_prime_for: PRIME_FOR(n, m) )
    : [r: pos] MOD(n, i, r)
  = let prval PRIME_FOR_ind(prime_for_mm1, mod_nm) = pf_prime_for
  in sif i >= m 
    then (* i == m *) mod_nm
    else (* i != m *) loop{n}{m-1}{i}(prime_for_mm1)
  end
in loop{n}{m}{i}(pf_prime_for) end
  
  
primplement lemma_prime_mod_gtz {p}{q}{r} (pf_p_prime,pf_mod)
  = let 
    prfun mod_gt_0
        {p: int                 }
        {q: pos | p > q; q > 1  }
        {m: pos | m > 1; m >= q }
        {r: int                 }
        .<m>.
        ( pf_prime_for_m: PRIME_FOR(p,m)
        , pf_mod:         MOD(p,q,r) )
        : [r > 0; r < q] void
        = sif m > q then 
            let prval PRIME_FOR_ind(pf, _) = pf_prime_for_m
            in mod_gt_0{p}{q}{m-1}(pf, pf_mod) end
          else (* m == q *) 
            let prval PRIME_FOR_ind(_, pf2_mod) = pf_prime_for_m
                prval pf_divmod = divmod_istot{p,q}()
                prval _         = divmod_isfun(pf_divmod, pf_mod)
                prval _         = divmod_isfun(pf2_mod,   pf_mod)
            in () end
      //
      prval PRIME(pf_prime_for) = pf_p_prime 
      prval _ = mod_gt_0{p}{q}{p-1}(pf_prime_for, pf_mod)
  in () end 


primplement lemma_prime_gt_2_is_odd {n}{r} (pf_prime,pf_mod2)
  = lemma_prime_mod_gtz{n}{2}(pf_prime, pf_mod2)


local
//
prfn lemma_derive_mod_gtz
    {n, i:    pos | i < n             }
    {isqrt_n: pos | i >= isqrt_n + 1  }
    {div_ni, mod_ni: nat | mod_ni < i }
    ( pf_dm_ni           : DIVMOD(n, i, div_ni, mod_ni)
    , pf_isqrt           : SQRT(n, isqrt_n)
    , pf_prime_for_isqrt : PRIME_FOR(n, isqrt_n) )
    : [mod_ni > 0] void
  = sif div_ni <= 0 (* div_ni == 0 *)
      then lemma_divmod_nonzero_mod{n}{i}(pf_dm_ni)
    else sif div_ni <= 1 (* div_ni == 1 *)
      then let
        // n == 1*i+r
        prval pf_mul_1i = divmod_elim(pf_dm_ni) // MUL(1,i,i*i)
        prval _         = lemma_x_mul_1_is_x(mul_commute(pf_mul_1i)) // i*1==1
      in () end
    else let 
      (* STEP 1: show that (n/i) <= isqrt(n), when i >= isqrt(n)+1 *)
      prval _ = lemma_isqrt_div(pf_isqrt, pf_dm_ni)
      //
      (* STEP 2: show that n mod (n/i) > 0, i >= isqrt(n)+1 *)
      prfn aux_n_dm_div_ni
        {n, i: pos    | i < n                           }
        {isqrt_n: pos | isqrt_n < n; i >= isqrt_n + 1   }
        {div_ni: pos  | div_ni <= isqrt_n; div_ni > 1   }
        {mod_ni: nat  | mod_ni < i                      }
        ( pf_prime_for_isqrt : PRIME_FOR(n, isqrt_n)
        , pf_div_ni          : DIVMOD(n,i,div_ni,mod_ni)
        , pf_isqrt           : SQRT(n, isqrt_n) )
        : [r, q: nat | r > 0; q >= i; r < div_ni]
          DIVMOD(n, div_ni, q, r) 
      = let
        prval pf_dm  = 
          lemma_prime_for_mod_gtz{n}{isqrt_n}{div_ni}(pf_prime_for_isqrt)
        //prval _      = lemma_prime_mod_gtz(pf_prime_for_isqrt, pf_dm)
        prval pf2_dm = divmod_istot_s{n,div_ni}()
        prval _      = divmod_isfun(pf_dm, pf2_dm)
        prval _      = lemma_div_cmp_2(pf_dm, pf_div_ni) // q >= div_ni
        // q >= div_ni; div_ni < i
        prval _      = lemma_isqrt_div(pf_isqrt,pf_dm)   // q >= sqrt_n
        // 
        prval pf_mul_divni_i   = divmod_elim(pf_div_ni)       // 
        prval pf_mul_divni_ni  = mul_negate2(pf_mul_divni_i)  // 
        prval pf_mul_q_divni   = divmod_elim(pf_dm)           // 
        prval pr_mul_divni_q   = mul_commute(pf_mul_q_divni)  // 
        prval pr_divni_mul_qmi = 
          mul_distribute(pr_mul_divni_q, pf_mul_divni_ni)
        prval pr_divni_mul_imq = mul_negate2(pr_divni_mul_qmi)
        //
        (* TODO: make this as lemma *)
        prfn check_1
          {div_ni,i,n : pos | div_ni < i; i < n }
          {r,q,m: int | r >= 0; q >= 0; r >= m; r < div_ni }
          ( pf  : MUL(div_ni, i-q, m)
          , pf2 : DIV(n, i, div_ni)
          , pf3 : DIVMOD(n, div_ni, q, r) )
          : [q >= i] void 
        = sif r <= 0 // r == 0
          then lemma_mul_sgn_2(pf) // m <= 0 => i-q <= 0
          else lemma_pos_mul_x_sgn_x{div_ni}{i-q}{m}(pf)
        //
        prval _ = check_1{div_ni,i,n}(pr_divni_mul_imq,pf_div_ni,pf_dm)
        //
      in pf_dm end
      //
      prval pf_n_dm_div_ni = (* DIVMOD(n,div_ni,q,r), r > 0 *)
        aux_n_dm_div_ni{n,i}{isqrt_n}(pf_prime_for_isqrt, pf_dm_ni, pf_isqrt)
      //
      (* STEP 3: show that S2 => n mod i > 0 *)
      prval _ = lemma_pos_mod_commute(pf_dm_ni, pf_n_dm_div_ni)
    in () end
//
in
//
primplement 
  lemma_isqrt_prime_1 
  {n}{isqrt_n} 
  (pf_isqrt,pf_prime_for_isqrt)
= let
  //
  prfun loop
    {n: int       | n > 1              }
    {isqrt_n: int | isqrt_n > 0        }
    {i: int       | i >= isqrt_n; i < n}
    .<n - i>.
    ( pf_isqrt:             SQRT(n, isqrt_n)
    , pf_prime_for_isqrt:   PRIME_FOR(n, isqrt_n)
    , pf_prime_for_i:       PRIME_FOR(n, i) )
    : PRIME(n)
  = sif i >= n - 1 
      then PRIME(pf_prime_for_i)
      else let
        prval pf_dm_n_ip1 = divmod_istot{n,i+1}()
        prval _ = 
          lemma_derive_mod_gtz{n,i+1}(pf_dm_n_ip1, pf_isqrt, pf_prime_for_isqrt)
        prval pf_prime_for_ip1 = 
          PRIME_FOR_ind(pf_prime_for_i, pf_dm_n_ip1)
        in loop(pf_isqrt, pf_prime_for_isqrt, pf_prime_for_ip1)
        end
  //
in loop{n}{isqrt_n}{isqrt_n}
  (pf_isqrt, pf_prime_for_isqrt, pf_prime_for_isqrt) end
//
end


(* tabulate all primes <= n *)
implement list_primes {pr}{n} (pf | n, func)
= let
  prval pf_iprime2   = IPRIMEbas()         // 2 is the first prime number
  prval pf_2is_prime = lemma_2_is_prime()  // 2 is the prime number
  prval pf_cprime2   = CPRIMEprime(pf_2is_prime) // 2 is closest prime for 2
  prval pf_3isprime  = lemma_3_is_prime()  // 3 is prime number
  prval pf_iprime3                         // 3 is the second prime number
    = IPRIMEind{1}{3}{2}(pf_iprime2, pf_cprime2, pf_3isprime) 
in    
  if n <= 1 then let
      val _ = func{n,0,2}(pf_iprime2, pf | n, 0, 2)
    in () end
  else if n <= 2 then let
      val _ = func{n,0,2}(pf_iprime2, pf | n, 0, 2)
      val _ = func{n,1,3}(pf_iprime3, pf | n, 1, 3)
    in () end
  else let
      val _ = func{n,0,2}(pf_iprime2, pf | n, 0, 2)
      val _ = func{n,1,3}(pf_iprime3, pf | n, 1, 3)
      
      // TODO: add wheel factorization or other sieve
      
    in () end
end
