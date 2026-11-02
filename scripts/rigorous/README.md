# Rigorous re-checks of the computation axioms

These programs re-check the finite numerical axioms that rest on our own computations. They are
independent of the float scripts in `scripts/`: different code, sieves and summation order.

* `rig_checks.c` encloses every real quantity in an interval `[lo, hi]` of MPFR numbers (64-bit
  mantissa). Each operation rounds `lo` down and `hi` up. MPFR is correctly rounded, including
  `log`, `exp`, `sqrt` and Euler's constant, so the enclosures are rigorous. Sieves, `φ`, `μ` and
  `λ` are exact integer computations. A check passes only if it holds for the whole interval.
* `eta2_fourier_rig.py` (python-flint/Arb ball arithmetic) checks `eta2DD_small` with the
  closed form in Si/Ci and a rigorous Lipschitz bound (see its docstring).
* `moebius_sqrt_rig.c` (`moebius_sqrt_small`, `10¹⁰` terms) uses IEEE double arithmetic with the
  rounding mode set to round-down; upper bounds are computed as `−((−a) ∘ b)`. Each operation is a
  correctly rounded IEEE operation (compiled with `-frounding-math`, no contraction to FMA).
* `p1224_rig.c` (`prop1224_check`, `2.2·10¹⁰` values of `q`) is interval arithmetic. The arithmetic
  is IEEE double with upward rounding in every thread, and lower bounds are computed by negation; a
  self-test checks the rounding mode. Constants, the per-prime values `log p`, `log p/p`,
  `p/(p−1)`, `f₁(p)` for `p ≤ √Q₁`, and tables of `log n`, `n^{−1/3}` come from MPFR, rounded
  outward. For the one prime factor `p > √Q₁` of `q`, `log p` comes from the `artanh` series with
  a tail bound, and `p^{1/3}` from a double `c` with `c³ ≤ p` checked by upward multiplication.
  `exp` is bounded below by Taylor partial sums. `p1224_check.c` is the earlier long-double version,
  with the same counts and margins.
* `ramare_check.c` checks Ramaré's (12.12) numerically: `c_E` in MPFR from the primes `≤ 10⁹` plus a
  tail bound, and (12.12) in interval arithmetic for `d ≤ 2000`, three primorials, and `X ≤ 2·10⁶`.
  It was written when (12.12) was the published axiom `ramare_Gq`, which is now proved in Lean
  (`Prelim/Ramare.lean`).

| Check | Axiom | Range | Time |
|---|---|---|---|
| `nonprime` | (former axiom `nonprime_small`; now proved) | prime powers `p^k ≤ 10¹²`, `k ≥ 2` | < 1 s |
| `mertens_lower` | (former axioms `mertens_lower_small`, `mertens_point`; now proved, kernel to `10⁴`) | `n ≤ 10⁶` | 1 s |
| `logsq` | (former axiom `logsq_small`; now proved) | `n ≤ 10⁶` | 2 s |
| `mertens_product` | `mertens_product_small` | primes `≤ 2·10⁸` | 70 s |
| `K` | (former axioms `K_blocks`, `K_pieces`; replaced by `ramare_moebius`) | prime powers `≤ 10⁹` | 2 min |
| `liouville` | (former axiom `liouville_small`; now proved) | `k ≤ 10⁵` | < 1 s |
| `C_grid` | (former axiom `C_grid`; now kernel-checked on 17 intervals) | 7720 grid points × 3000 terms | 25 s |
| `lemma7` | (former axioms `lemma7_numeric`, `GS_N0`; now proved) | `r ≤ 3·10⁷` | 20 s |
| `lemma8` | (former axiom `lemma8_numeric`; now proved) | `n ≤ 10⁴` | 10 s |
| `moebius_sqrt_rig` | `moebius_sqrt_small` | `k < 10¹⁰` | 6 min |
| `eta2_fourier_rig.py` | `eta2DD_small` ([B, (B.6)] on `0 ≤ t ≤ 655`) | Lipschitz stepping, 137334 points | 3 s |
| `eta_circ_rig.py` | former axiom `etaO_numerics` (input of [B, (9.94)]; now proved) | four integrals over `[0, 2]` | < 1 s |
| `t2_rig.c` | `T2_small`, `T2_mid` (inputs of [B, (5.31)]) | `g₂(n)` for `n ≤ 10⁸`; `T₂` on `[16, 10⁵)` | 8 min |
| `p1224_rig.c` | `prop1224_check` (the finite part of [B, Prop 12.2.4]) | every `q < 2.2·10¹⁰`, every `n < λ(q)`: 87 972 745 explicit checks for 2 102 258 values of `q` | about 40 min on 22 threads |
| `ramare_check.c` | (former published axiom `ramare_Gq`; now proved) | `c_E`; `d ≤ 2000` and three primorials, `X ≤ 2·10⁶` | 2 min |
| `g2_rig.c` | (exploration: `g₂` and `max \|g₂(n)\| n`) | `n ≤ N` | seconds |

The reference output is `output.txt`.

How the ranges are covered:
* Step functions (`ψ − θ`, `∑ Λ(m)/m`, `G(r)`, `Ψ(k)`) are constant between consecutive jump points.
  Each check is made at the worst point of each run, using the monotonicity of the other side
  (`√n`, `log(n+1)`, `log t`).
* The other checks are made at every point of their range.

Build (needs `gcc`; the MPFR/GMP headers come with the Python package `gmpy2`, the libraries are the
system's `libmpfr.so.6` and `libgmp.so.10`):

```
sh scripts/rigorous/build.sh
scripts/rigorous/rig_checks            # all checks, or name some: rig_checks K lemma7
scripts/rigorous/moebius_sqrt_rig
```
