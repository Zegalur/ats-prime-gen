#include "share/atspre_staload.hats"

staload "isqrt.sats"
staload "prime.sats"

val n = 1000
val (pf_sqrt_n | sqrt_n) = isqrt(n)
val _ = println! ("sqrt(", n, ") = ", sqrt_n)

implement main0() = ()
