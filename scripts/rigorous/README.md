# Rigorous re-checks of the computation axioms

These programs re-check the finite numerical axioms that rest on our own computations. They are
independent of the float scripts in `scripts/`: different code, sieves and summation order.

* `rig_checks.c` encloses every real quantity in an interval `[lo, hi]` of MPFR numbers (64-bit
  mantissa). Each operation rounds `lo` down and `hi` up. MPFR is correctly rounded, including
  `log`, `exp`, `sqrt` and Euler's constant, so the enclosures are rigorous. Sieves, `φ`, `μ` and
  `λ` are exact integer computations. A check passes only if it holds for the whole interval.
* `moebius_sqrt_rig.c` (`moebius_sqrt_small`, `10¹⁰` terms) uses IEEE double arithmetic with the
  rounding mode set to round-down; upper bounds are computed as `−((−a) ∘ b)`. Each operation is a
  correctly rounded IEEE operation (compiled with `-frounding-math`, no contraction to FMA).

| Check | Axiom | Range | Time |
|---|---|---|---|
| `nonprime` | `nonprime_small` | prime powers `p^k ≤ 10¹²`, `k ≥ 2` | < 1 s |
| `mertens_lower` | `mertens_lower_small`, `mertens_point` | `n ≤ 10⁶` | 1 s |
| `logsq` | `logsq_small` | `n ≤ 10⁶` | 2 s |
| `mertens_product` | `mertens_product_small` | primes `≤ 2·10⁸` | 70 s |
| `K` | `K_blocks`, `K_pieces` | prime powers `≤ 10⁹` | 2 min |
| `liouville` | `liouville_small` | `k ≤ 10⁵` | < 1 s |
| `C_grid` | `C_grid` | 7720 grid points × 3000 terms | 25 s |
| `lemma7` | `lemma7_numeric`, `GS_N0` | `r ≤ 3·10⁷` | 20 s |
| `lemma8` | `lemma8_numeric` | `n ≤ 10⁴` | 10 s |
| `moebius_sqrt_rig` | `moebius_sqrt_small` | `k < 10¹⁰` | 6 min |

The reference output is `output.txt`.

How the ranges are covered:
* Step functions (`ψ − θ`, `∑ Λ(m)/m`, `G(r)`, `Ψ(k)`) are constant between consecutive jump points.
  Each check is made at the worst point of each run, using the monotonicity of the other side
  (`√n`, `log(n+1)`, `log t`).
* `K_blocks` takes the maximum over each run `[a, b)` of `|Ψ(k) − log t − E(10⁹)|`, `t ∈ {k, k+1}`, at
  `t = a` or `t = b`, splitting runs at the block boundaries `1000·2ʲ`.
* The other checks are made at every point of their range.

Build (needs `gcc`; the MPFR/GMP headers come with the Python package `gmpy2`, the libraries are the
system's `libmpfr.so.6` and `libgmp.so.10`):

```
sh scripts/rigorous/build.sh
scripts/rigorous/rig_checks            # all checks, or name some: rig_checks K lemma7
scripts/rigorous/moebius_sqrt_rig
```
