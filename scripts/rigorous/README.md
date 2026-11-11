# Rigorous checks in interval arithmetic

These programs check, in rigorous arithmetic, finite computations behind [H] and behind our own
`Prelim/` and `MinorArcs/` bounds. The Lean proof does not depend on them: every computation it
needs is evaluated by the kernel (`decide +kernel`). They are independent of the float scripts in
`scripts/` (different code, sieves and summation order), and several cover longer ranges than the
Lean proof uses, or check [H]'s own constants.

* `rig_checks.c` encloses every real quantity in an interval `[lo, hi]` of MPFR numbers (64-bit
  mantissa). Each operation rounds `lo` down and `hi` up. MPFR is correctly rounded, including
  `log`, `exp`, `sqrt` and Euler's constant, so the enclosures are rigorous. Sieves, `φ`, `μ` and
  `λ` are exact integer computations. A check passes only if it holds for the whole interval.
* `eta2_fourier_rig.py` (python-flint/Arb ball arithmetic) checks [H, (B.6)] with [H]'s constant
  `31.521` on `0 ≤ t ≤ 655`, using the closed form in Si/Ci and a rigorous Lipschitz bound (see its
  docstring).
* `moebius_sqrt_rig.c` (`10¹⁰` terms) uses IEEE double arithmetic with the rounding mode set to
  round-down; upper bounds are computed as `−((−a) ∘ b)`. Each operation is a correctly rounded IEEE
  operation (compiled with `-frounding-math`, no contraction to FMA).
* `p1224_rig.c` checks the finite part of [H, Prop 12.2.4] with [H]'s `c₊ = 1.36` (`2.2·10¹⁰` values
  of `q`). It is interval arithmetic: IEEE double with upward rounding in every thread, and lower
  bounds computed by negation; a self-test checks the rounding mode. Constants, the per-prime values
  `log p`, `log p/p`, `p/(p−1)`, `f₁(p)` for `p ≤ √Q₁`, and tables of `log n`, `n^{−1/3}` come from
  MPFR, rounded outward. For the one prime factor `p > √Q₁` of `q`, `log p` comes from the `artanh`
  series with a tail bound, and `p^{1/3}` from a double `c` with `c³ ≤ p` checked by upward
  multiplication. `exp` is bounded below by Taylor partial sums. `p1224_check.c` is a long-double
  version, with the same counts and margins. (The Lean proof has `c₊ = 2` and needs no such check.)
* `ramare_check.c` checks Ramaré's (12.12): `c_E` in MPFR from the primes `≤ 10⁹` plus a tail
  bound, and (12.12) in interval arithmetic for `d ≤ 2000`, three primorials, and `X ≤ 2·10⁶`. (12.12)
  is proved in Lean (`Prelim/Ramare.lean`).

| Check | Statement | In the Lean proof | Range | Time |
|---|---|---|---|---|
| `nonprime` | (5.5): `ψ(n) − θ(n) < 1.4262 √n` | kernel to `10⁶` (`SmallNonprime.lean`), analytic above | prime powers `p^k ≤ 10¹²`, `k ≥ 2` | < 1 s |
| `mertens_lower` | (2.13) and its base value | kernel to `10⁴` (`SmallMertensLower.lean`), summation by parts above | `n ≤ 10⁶` | 1 s |
| `logsq` | (2.19): `∑_{n/2<p≤n} (log p)² ≤ ½ n log n` | used for `n ≥ 2·10⁶` only, from the tables | `117 ≤ n ≤ 10⁶` | 2 s |
| `mertens_product` | [RS62, Thm 15] at primes | kernel to `10⁵` (`SmallMertensProd.lean`), `F_mid` above | primes `≤ 2·10⁸` | 70 s |
| `K` | `∑_{n≤x} \|E(x/n) − E(x)\|/n ≤ 0.54`, an elementary route to the `q = 1` Möbius bound | not used: `MoebiusBound.lean` derives that bound from `ramare_moebius` | prime powers `≤ 10⁹` | 2 min |
| `liouville` | `\|∑_{n≤k} λ(n)/n\| log(k+1) ≤ 0.99` | kernel (`SmallLiouville.lean`) | `k ≤ 10⁵` | < 1 s |
| `C_grid` | the grid inequality behind (2.22) with `2.8` | kernel on 17 intervals (`SmallCGrid.lean`) | 7720 grid points × 3000 terms | 25 s |
| `lemma7` | [MV73, Lemma 7]: `G(r) ≥ log r + 1.07` | kernel for `r < 21400` (`SmallG.lean`), (12.12) above | `r ≤ 3·10⁷` | 20 s |
| `lemma8` | [MV73, Lemma 8] | kernel for `R < 1000` (`SmallW.lean`), Abel summation above | `n ≤ 10⁴` | 10 s |
| `moebius_sqrt_rig` | `\|m(k)\| ≤ √(2/(k+1))` (cf. [H, (2.24)]) | kernel for `k < 11815` (`SmallMoebius.lean`) | `k < 10¹⁰` | 6 min |
| `eta2_fourier_rig.py` | [H, (B.6)] with `31.521` | (B.6) with `32` (`Eta2DDBound.lean`) | Lipschitz stepping, 137334 points | 3 s |
| `eta_circ_rig.py` | the four integrals behind [H, (9.94)] | exact polynomial integration (`EtaONum.lean`) | `[0, 2]` | < 1 s |
| `t2_rig.c` | (5.31): `T₂(S) ≤ 0.37273` | kernel to `10⁴` (`SmallG2.lean`), mean-square tail above | `g₂(n)` for `n ≤ 10⁸`; `T₂` on `[16, 10⁵)` | 8 min |
| `p1224_rig.c` | the finite part of [H, Prop 12.2.4] with `c₊ = 1.36` | Prop 12.2.4 with `c₊ = 2`, no finite check over `q` | every `q < 2.2·10¹⁰`, every `n < λ(q)`: 87 972 745 explicit checks for 2 102 258 values of `q` | about 40 min on 22 threads |
| `ramare_check.c` | (12.12) and `c_E` | proved (`Prelim/Ramare.lean`) | `c_E`; `d ≤ 2000` and three primorials, `X ≤ 2·10⁶` | 2 min |
| `g2_rig.c` | `g₂(n)` and `max \|g₂(n)\| n` (exploration) | — | `n ≤ N` | seconds |

The reference output is `output.txt`. `moebius_sqrt_rig` also found that [H, p. 38]'s remark on
`|m(x)| ≤ 1/(2√x)` is off by one (`HYPOTHESES.md`, Finding 6).

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
