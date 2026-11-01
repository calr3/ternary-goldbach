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
* `p1224_check.c` (`prop1224_check`, `2.2·10¹⁰` values of `q`) uses x87 long double (64-bit
  mantissa) without directed rounding. Instead, every inequality must hold with a margin of at
  least `10⁻⁹` absolute, or `10⁻¹²` relative where noted. The largest possible accumulated rounding
  error is about `10⁻¹¹`: `G_q(n)` is a sum of at most `3·10⁷` positive terms `≤ 1`. The other
  quantities are short products and sums of glibc's `logl`, `cbrtl`, `expl`, `powl`, whose
  documented errors are a few ulps. The margins found are `0.0236` for the explicit check (C) and
  `1.3·10⁻⁷` for (S).

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
| `eta2_fourier_rig.py` | `eta2DD_small` ([B, (B.6)] on `0 ≤ t ≤ 655`) | Lipschitz stepping, 137334 points | 3 s |
| `eta_circ_rig.py` | `etaO_numerics` (input of [B, (9.94)]) | four integrals over `[0, 2]` | < 1 s |
| `t2_rig.c` | `T2_small`, `T2_mid` (inputs of [B, (5.31)]) | `g₂(n)` for `n ≤ 10⁸`; `T₂` on `[16, 10⁵)` | 8 min |
| `p1224_check.c` | `prop1224_check` (the finite part of [B, Prop 12.2.4]) | every `q < 2.2·10¹⁰`, every `n < λ(q)`: 87 972 745 explicit checks for 2 102 258 values of `q` | 22 min on 22 threads |
| `g2_rig.c` | (exploration: `g₂` and `max \|g₂(n)\| n`) | `n ≤ N` | seconds |

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
