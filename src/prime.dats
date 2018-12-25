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

primplement lemma_4_is_composite() 
= let prval pf_dm_4_2 = divmod_make{4,2}{2,0}{4}(mul_make{2,2}())
  in COMPOSITE(pf_dm_4_2) end
  
primplement lemma_5_is_prime ()
= let prval dm2     = divmod_make{5,2}{2,1}{4}(mul_make{2,2}())
      prval dm3     = divmod_make{5,3}{1,2}{3}(mul_make{1,3}())
      prval dm4     = divmod_make{5,4}{1,1}{4}(mul_make{1,4}())
      prval pf1      = PRIME_FOR_bas()            
      prval pf2      = PRIME_FOR_ind(pf1, dm2)
      prval pf3      = PRIME_FOR_ind(pf2, dm3)
      prval pf4      = PRIME_FOR_ind(pf3, dm4)
  in PRIME(pf4) end

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


datatype PCHECK_RES (int) =
  | {n : int}
    PCHECK_prime(n) 
    of (PRIME(n) | int(n))
  | {n : int}
    PCHECK_composite(n)
    of (COMPOSITE(n) | int(n))

// check if number is prime (slow)
fn check_if_prime_slow
  {n : nat | n > 1}
  ( n : int n )
  : PCHECK_RES(n)
= let
  //
  fun loop
    {n : pos | n  > 1 }
    {s : pos | s  < n }
    {i : pos | i <= s }
    .<s-i>.
    ( pfp : PRIME_FOR(n,i)
    , pfs : SQRT(n,s)
    | n   : int n
    , s   : int s
    , i   : int i )
    : PCHECK_RES(n)
  = if i >= s // i == s
    then let
        prval pf_prime = lemma_isqrt_prime_1(pfs, pfp)
        val r  = PCHECK_prime(pf_prime | n)
      in r end
    else let
        val (pf_dm | n_mod_ip1) = g1int_nmod2(n,i+1) // n mod (i+1)
      in if n_mod_ip1 > 0 // n mod (i+1) > 0
        then let
            prval pfp1 = PRIME_FOR_ind(pfp, pf_dm)
          in loop{n}{s}{i+1}(pfp1, pfs | n, s, i+1) end
        else let          // n mod (i+1) == 0
            prval pf_composite = COMPOSITE{n}{i+1}(pf_dm)
            val r = PCHECK_composite(pf_composite | n)
          in r end
      end
  //
  val (pfs | s) = isqrt(n)
in loop(PRIME_FOR_bas{n}(), pfs | n, s, 1) end

(* tabulate all primes <= n *)
implement list_primes {pr}{n} (pf | n, func)
= let
  //
  prval pf_2is_prime = lemma_2_is_prime()        // 2 is the prime number
  prval pf_cprime2   = CPRIMEprime(pf_2is_prime) // 2 is closest prime for 2
  prval pf_3is_prime = lemma_3_is_prime()        // 3 is prime number
  prval pf_cprime3   = CPRIMEprime(pf_3is_prime) // 3 is closest prime for 2
  prval pf_4is_comp  = lemma_4_is_composite()    // 4 is a composite number
  prval pf_cprime4                               // 3 is closest prime for 4
    = CPRIMEcomp(pf_cprime3, pf_4is_comp)
  prval pf_5is_prime = lemma_5_is_prime()        // 5 is the prime number
  prval pf_cprime5   = CPRIMEprime(pf_5is_prime) // 5 is closest prime for 5
  //
  prval pf_iprime2   = IPRIMEbas()         // 2 is the first prime number
  prval pf_iprime3                         // 3 is the second prime number
    = IPRIMEind{1}{3}{2}(pf_iprime2, pf_cprime2, pf_3is_prime) 
  prval pf_iprime5                         // 5 is the third prime number
    = IPRIMEind{2}{5}{3}(pf_iprime3, pf_cprime4, pf_5is_prime) 
in    
  if n <= 1 then let
      val _ = func{n,0,2}(pf_iprime2, pf | n, 0, 2)
    in () end
  else if n <= 2 then let
      val _ = func{n,0,2}(pf_iprime2, pf | n, 0, 2)
      val _ = func{n,1,3}(pf_iprime3, pf | n, 1, 3)
    in () end
  else if n <= 3 then let
      val _ = func{n,0,2}(pf_iprime2, pf | n, 0, 2)
      val _ = func{n,1,3}(pf_iprime3, pf | n, 1, 3)
      val _ = func{n,2,5}(pf_iprime5, pf | n, 2, 5)
    in () end
  else let // n >= 4, p > 5
      val _ = func{n,0,2}(pf_iprime2, pf | n, 0, 2)
      val _ = func{n,1,3}(pf_iprime3, pf | n, 1, 3)
      val _ = func{n,2,5}(pf_iprime5, pf | n, 2, 5)
      
      // TODO: add wheel factorization or other optimization
      
      fun loop
        {pr: (int, int) -> view     } // callback function
        {n : nat | n >= 4           } // how many primes we need
        {i : nat | i >= 2; i+1 <= n } // last prime number index (from 0)
        {q : nat | q >= 5           } // last prime number
        {p : nat | p >= q           } // last checked number
        //.<n-i>.
        ( pf   : !pr(n,i+1) >> pr(n,n)
        , pfi  : IPRIME(i,q)
        , pfp  : PRIME(q)
        , pfc  : CPRIME(p,q)
        | n    : int n
        , i    : int i
        , p    : int p
        , func : prime_list_func(pr) )
        : void
      = if i+1 >= n // i+1 == n
        then () // we done
        else let
          val pcheck = check_if_prime_slow(p+1)
        in case+ pcheck of
          | PCHECK_prime(pfp1 | _) => let // p+1 is prime number
              prval pfi1 = IPRIMEind{i+1}{p+1}{q}(pfi,pfc,pfp1)
              val      _ = func{n,i+1,p+1}(pfi1, pf | n, i+1, p+1)
              prval pfc1 = CPRIMEprime{p+1}(pfp1)
            in loop
               {pr}{n}{i+1}{p+1}{p+1}
               ( pf,pfi1,pfp1,pfc1 
               | n,i+1,p+1,func )
            end
          | PCHECK_composite(pf_pp1_comp | _) => let // p+1 is not a prime
              prval pfc1 = CPRIMEcomp{p+1}{q}(pfc,pf_pp1_comp)
            in loop
               {pr}{n}{i}{q}{p+1}
               ( pf,pfi,pfp,pfc1 
               | n,i,p+1,func ) 
            end
        end
      //
      prval pfc = CPRIMEprime{5}(pf_5is_prime)
    in loop 
       {pr}{n}{2}{5}{5} 
       (pf, pf_iprime5, pf_5is_prime, pfc | n, 2, 5, func) 
    end
    //in () end
end
