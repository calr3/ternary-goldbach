# Axiom audit

`ternary_goldbach` depends on the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) and on 9 further axioms (`#print axioms`):
* 2 finite computations of our own;
* 7 published results;
* no result of Helfgott's book [B].

A false axiom would make the axiom set inconsistent, and then the formal proof would say nothing.
So each axiom has been checked:
* our computations against their scripts: range, edge cases, the exact Lean definitions involved,
  rounding, and margin;
* published results against the papers.

Sources: [B] = Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2. Papers are cited by
arXiv number where there is one. [RS62], [MV73] and [Ram95] are as in the README.

## Our own computations (2)

Each computation has an independent rigorous check in `scripts/rigorous/` (see its README):
`eta2_fourier_rig.py` (Arb ball arithmetic) and `p1224_rig.c` (interval arithmetic with directed
rounding).

A check passes only if it holds for the whole interval. All pass; the reference output is
`scripts/rigorous/output.txt`. "Also published" lists results in the literature that contain the
axiom.

| Axiom | Statement | Float script | Rigorous re-check: worst case | Also published |
|---|---|---|---|---|
| `MinorArcs.eta2DD_small` | [B, (B.6)] on `0 ≤ t ≤ 655` in explicit form: `‖eta2DD t‖ ≤ 31.521`, `eta2DD t = (2πt)² η̂₂(t)` | — | max `31.52065207` at `t ≈ 17.4148` (`eta2_fourier_rig.py`, Arb ball arithmetic, Si/Ci closed form, Lipschitz stepping: 137334 steps) | [B, Lemma B.1.2] (interval arithmetic, `\|t\| < 655`) |
| `MinorArcs.prop1224_check` | for `1 ≤ q < 2.2·10¹⁰` and `1 ≤ n < λ(q)`: `n` is in the range of `regionS`, or `checkC q n` ([B, (12.31)] at `R ∈ [n, n+1)`) | `p1224_check.c` (long double) | no failures; `87 972 745` explicit checks for `2 102 258` values of `q`; min margin of `checkC` `0.0236` at `q = 1` (`p1224_rig.c`, interval arithmetic: directed rounding, MPFR tables, rigorous series for `log` and `exp`) | [B]'s computation for Prop 12.2.4 covers `q < 3.3·10⁹` |

The rigorous values agree with the float scripts to the digits printed.

Three further axioms in `Prelim/LambdaMuExtra.lean` are not used by `ternary_goldbach`. They come
from `psi_extra_check.py`:
* `lambda_mul_small` (`k ≤ 2.5·10⁷`): max ratio `1.03583`;
* `lambda_sqrt_small` (`k ≤ 6·10⁶`): max ratio `1.99906`;
* `lambda_sqrt_point` (at `6·10⁶`): value `−3.6619`.

## Published results (7)

| Axiom | Statement | Source | Check |
|---|---|---|---|
| `Explicit.rh_upto` | zeros of `ζ` with `0 < ℜρ < 1`, `\|ℑρ\| ≤ 3·10¹²` have `ℜρ = 1/2` | Platt–Trudgian, arXiv:2004.09765 | abstract: "all zeroes `β + iγ` … with `0 < γ ≤ 3·10¹²` have `β = 1/2`". The axiom also covers `γ ≤ 0`: `γ < 0` by `ζ(s̄) = conj ζ(s)`, and `γ = 0` because `ζ(σ) < 0` on `(0, 1)` |
| `MajorArcs.platt_odd` | primitive `χ`, odd conductor `q ≤ 3·10⁵`: GRH up to `10⁸/q` | Platt, arXiv:1305.3087 | abstract: all primitive `χ`, `q ≤ 4·10⁵`; odd `q` to `max(10⁸/q, 3.75·10⁷/q + 200)`; Thm 3.2 counts zeros with `\|ℑs\| ≤ t₀`, `ℜs ∈ (0,1)`; see Finding 2 |
| `MajorArcs.platt_even` | even `q ≤ 4·10⁵`: GRH up to `max(10⁸/q, 200 + 7.5·10⁷/q)` | same | same |
| `Helfgott.binary_goldbach_input` | every even `4 ≤ n ≤ 4·10¹⁸` is a sum of two primes | [OeSHP14], Math. Comp. 83 (2014) | [B, §1.6]; the project page says "all consecutive even numbers up to `4·10¹⁸`" (the journal page returned 403). According to the project page, the independent double-check reaches `4·10¹⁷` |
| `Prelim.buthe_theta` | `\|θ(n) − n\| ≤ 1.95 √n`, `1423 ≤ n ≤ 10¹⁹` | Büthe, arXiv:1511.02032, Thm 2 | (1.6) `x − θ(x) ≤ 1.95√x` for `1423 ≤ x ≤ 10¹⁹`; (1.7) `x − θ(x) > 0.05√x`; this combines an analytic method with a computation |
| `Prelim.buthe_psi` | `\|ψ(n) − n\| ≤ 0.94 √n`, `12 ≤ n ≤ 10¹⁹` | Büthe, arXiv:1511.02032, Thm 2 | (1.5) `\|x − ψ(x)\| ≤ 0.94√x` for `11 < x ≤ 10¹⁹` |
| `Prelim.ramare_moebius` | `\|∑_{n≤x} μ(n)/n\| ≤ 0.03/log x` for real `x ≥ 11815` | Ramaré, Acta Arith. 157 (2013) 365–379, Cor. 1.4: for `x ≥ 11815` ([B, (2.21)]) | implied for `X ≥ 463 421` by Ramaré, Math. Comp. 84 (2015), Thm 1.2 (`≤ (0.0144 log X − 0.1)/(log X)²`), which Ramaré and Zuniga-Alterman re-derive in arXiv:2408.05969 (that paper also proves `≤ 0.010032/log X` for `X ≥ 617 990`, Cor. 1.2). A float check (`scripts/moebius_ramare_check.py`) gives `max \|m(k)\| log(k+1) = 0.029496` over `11815 ≤ k < 10⁸`, at `k = 11820` |

The axioms are stated as in the papers or weaker. `ramare_moebius` is used for the Liouville bound
behind [B, (2.22)] (`Prelim/LiouvilleBound.lean`, `MoebiusBound.lean`) and for the tail of
`∫ |g₂|/y` in (5.31) (`MinorArcs/G2Tail.lean`). `buthe_theta` and `rh_upto` (through
`Explicit/PsiPlateau.lean`) also give the small cases: a prime in `(n − 4·10¹⁸, n − 4]` for
`4·10¹⁸ + 3 < n ≤ 10²⁷` (`Helfgott/SmallCases.lean`). This replaces the Helfgott–Platt prime ladder
(arXiv:1305.3062), formerly the axiom `prime_ladder_input`.

## Errors found in the sources

1. **[B, (5.32)] is false for `v = 2`, and so is (5.36), which depends on it.**
   * Our `T2` is exactly the sum in [B, (5.19)]. It agrees with [B]'s stated
     `G₂(S) = 1 − 1/S` on `[1, 2)`, and `T₂(S) = 1/2` on `[2, 3)`.
   * Exactly, `∫₁⁴ T₂(S) dS/S = (log 2 − 1/2) + ½ log(3/2) + ⅓ log(4/3) + 1/24 = 0.53344`. This
     exceeds `0.37273 log 4 = 0.51671`, the bound that (5.32) claims for `G₂ ≥ T₂`. Hence
     `∫₁⁴ H₂(S)/S dS = 0.21619 > 0.15107 log 4 = 0.20943`.
   * We prove the corrected form `∫₁ᵀ H₂(S)/S dS ≤ 0.15107 log T + 0.0231` for all `T ≥ 1`
     (`integral_H2_le`, `MinorArcs/H2Bound.lean`). The supremum of the excess is `0.023059`.
     `scripts/h2_integral_check.py` is an independent check in interval arithmetic.
   * Consequences:
     * the Type II factor becomes `0.60428 Λ₀ + 0.0924 + 8ζ³√(x/V)/U`;
     * the first-case constant of Thm 3.1.1 becomes `0.8764`;
     * `B₀ᵃ`, `B₀ᵇ` gain `+0.0231`.

     (14.49) is still `1.0376`.
2. **[B] is inconsistent about Platt's range.** [B, §1.6] says odd conductors up to `2·10⁵`; [B, §9.6]
   says `3·10⁵`. Platt's paper covers all `q ≤ 4·10⁵`, so `platt_odd` is covered either way.
3. **[B]'s derivation of (9.94) drops a factor 2.**
   * [B, p. 197] expands `∫η₊² log xt` with the cross term `2∫(η₊ − η◦)η◦ log xt`. It bounds
     `|∫(η₊ − η◦)η◦ log xt| ≤ 1.944·10⁻⁶ log x + 5.2·10⁻⁷`, then concludes (9.94) with
     `O*(1.95·10⁻⁶) log x + O*(5.3·10⁻⁷)`, without the factor 2. With the factor, the same argument
     gives about `3.9·10⁻⁶ log x + 1.27·10⁻⁶`.
   * (9.94) with [B]'s constants is proved anyway (`MajorArcs/EtaPlusSqLog.lean`), by Parseval in
     `u = log t` instead of Cauchy–Schwarz on all of `L²`. A float computation of `η₊`
     (`scripts/eta_plus_check.py`) also puts both integrals well inside [B]'s intervals.
4. **Two slips in [B]'s proof of Prop 12.2.4 (the result holds; it is proved).**
   * The proof applies Lemma 12.2.3, which bounds the quotient by `(log Q₀ + σ)/(log Q + 1.312)`,
     with `σ = c₊ = 1.36` for the range (12.29) of small `R`. But (12.23) has `log Q + c_E` in the
     denominator, with `c_E = 1.33258 > 1.312`. So with `σ = c₊` the lemma does not give (12.23);
     `σ ≈ 1.347` would, at a cost of about `0.5 %` in `ϖ(q)`. Our proof (`regionS`) bounds the
     quotient against `log Q + c_E` directly.
   * (12.15) claims `G(R) ≥ log R + 1.312` from (12.12) for `R ≥ 4·10⁷`. But (12.12) gives
     `c_E − 7.284 R^{−1/3} ≥ 1.312` only from `R ≈ 4.42·10⁷` on. We do not use (12.15).
5. **[Ram95, (3.9)] understates a product (Lemma 3.4 holds; it is proved).**
   * Ramaré's proof of Lemma 3.4 (= [B, (12.12)]) uses (3.9):
     `∏_p (1 + (p^{1/3} + p^{2/3})/(p(p−1))) ≤ 8`. The product over the primes below `10⁷` is
     already `8.0775`, and the full product is about `8.0845`. The constant `7.284 = 0.9105·8`
     comes from (3.9); with `8.0845` the same argument gives about `7.36`.
   * Our proof (`Prelim/Ramare*.lean`) uses a different decomposition and gives `7.04 ≤ 7.284`.
6. **[B, p. 38] is off by one about `|m(x)| ≤ 1/(2√x)`.** [B] says the bound holds for
   `x ≤ 7727068587`. `moebius_sqrt_rig` finds that it fails already at `x = 7727068587`:
   `μ(7727068587) = 1`, and `4 m(x)² x ∈ [1.0000156, 1.0000165]` there. The remark is not used.

The README lists the other differences from [B].

## Proved in Lean, not assumed

These inputs are theorems:

| Result | File | Method |
|---|---|---|
| Ramaré's (12.12) ([Ram95, Lemma 3.4]), with `c_E ∈ [1.33258227, 1.33258229]` | `Prelim/Ramare.lean` | `g_d = h_d ∗ [odd]/n`; `∑ \|h_d(a)\| a^{1/3} ≤ 11 f₁(d)` by Euler products; `c_E = γ + log 2 + 2X/ζ(2) + ∑_p log p/(p³ − p)` via Mathlib's `L(Λ, s) = −ζ'(s)/ζ(s)` and a kernel walk (`RamareWalk.lean`) |
| (5.31) `T2_le` | `MinorArcs/T2Bound.lean`, `T2Small.lean`, `G2Tail.lean` | `g₂(n)` for `n ≤ 10⁴` by the kernel; `T₂ = α_n + β_n/S` exactly for `S < 700`; `T₂(S) = ¼ ∫₁^S g₂/y + O*(S⁻¹ ∫₁^S \|g₂\|)` above; `∫_{10⁴}^S \|g₂\|/y ≤ 0.0045` by Cauchy–Schwarz with weights `H_d(a) λ(da)`, which reduces it to `∫ m(⌊t⌋)²/t` (`m(k)` for `k < 11815` from the kernel, `ramare_moebius` beyond) and an Euler product `∏_{p>2} p²/(p²−1) ≤ π²/8` |
| Lemma 5.1.2: `\|g₂(x)\| ≤ 0.0236/(log x)² + 528 (1 + log x)²/x` (not used by `ternary_goldbach`) | `MinorArcs/G2Bound.lean` and `G2*.lean` | one convolution `f·1_{(·,d)=1} = H_d ∗ (μ/id)`; `ramare_moebius` for `x/u ≥ 11815` (Rankin weight `u^{1/9}`), [B, (2.24)] below; Euler products |
| (5.36) corrected, (5.37) | `MinorArcs/H2Bound.lean` | `T₂ = α_n + β_n/S` on `[n, n+1)`, kernel for `n ≤ 15` |
| Prop 12.2.4 | `MinorArcs/LSQuot1–6.lean` | (12.12) and `prop1224_check`; `regionS`, and `λ(q)⁷ ≤ (103/120)⁹ q²` for `q ≥ 2.2·10¹⁰` |
| (9.94) | `MajorArcs/EtaPlusSqLog.lean`, `EtaONum.lean` | Parseval in `log t`; the four integrals by Taylor bounds and exact polynomial integration |
| (B.6), (B.11) | `MinorArcs/Eta2Fourier.lean` | integration by parts for `\|t\| ≥ 655`; `eta2DD_small` below |
| [B, (2.13)] | `Prelim/LambdaMu.lean`, `SmallMertensLower.lean` | summation by parts from `10⁴` with `buthe_psi`; kernel for `N ≤ 10⁴` |
| [B, (2.22)] with constant `2.8` | `Prelim/LiouvilleBound.lean`, `SmallCGrid.lean` | Ramaré's Liouville route: `ramare_moebius` for `x ≥ 11815`, [B, (2.24)] and a kernel check below; Ramaré's `ρ(U, y)` optimisation on a kernel-checked grid of 17 intervals |
| [B, (2.24)] for `x < 11815` | `Prelim/SmallMoebius.lean` | kernel walk; `μ` by trial division |
| [RS62, Thm 15] (`∏_{p≤x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)`, [B, (C.19)]) | `Prelim/MertensProduct.lean`, `SmallMertensProd.lean` | Mertens' theorem with explicit error: `theta_explicit` above `2·10⁸`, Büthe's bounds and a sharper prime-power tail on `[10⁵, 2·10⁸]`, kernel for primes `≤ 10⁵` |
| [MV73, Lemmas 7, 8] | `Prelim/MVLemma7.lean`, `MVLemma8.lean` | (12.12) for `r ≥ 21400`, Abel summation for `R ≥ 1000`; kernel below |
| the `ψ`, `θ` bounds of [B, §2] | `Prelim/LambdaMu.lean`, `ThetaExplicit.lean` | `buthe_psi`, `buthe_theta` up to `10¹⁹`, our explicit prime number theorem beyond; kernel for small `n` |

The kernel evaluates these finite checks (`decide +kernel`, no `native_decide`):

| File | Check | Time |
|---|---|---|
| `Prelim/SmallPsi.lean` | `ψ(n) < 1.03883 n`, `n ≤ 586` (via `lcm(1, …, n)`) | seconds |
| `Prelim/SmallMertens.lean` | `∑_{m≤n} Λ(m)/m ≤ log n`, `n ≤ 100` | seconds |
| `Prelim/SmallProdAp.lean` | `∏_{p<10⁴} (1 + (p^{−2/3} + p^{−1/3})/(p − 1)) ≤ 7.99` | seconds |
| `Prelim/SmallFsq.lean` | [B, p. 83] for `⌊X⌋ < 200` | seconds |
| `Prelim/SmallNonprime.lean` | `ψ(n) − θ(n) < 1.4262 √n`, `n ≤ 10⁶` | 9 s |
| `Prelim/SmallG.lean` | `G(r) ≥ log r + 1.07`, `6 ≤ r < 21400` | 23 s |
| `Prelim/SmallW.lean` | [MV73, Lemma 8], `6 ≤ R < 1000` | seconds |
| `Prelim/SmallLogSq.lean` | `∑_{n/2<p≤n} (log p)² ≤ ½ n log n`, `117 ≤ n < 40000` | 78 s |
| `Prelim/SmallLiouville.lean` | `\|∑_{n≤k} λ(n)/n\| log(k+1) ≤ 0.99`, `k ≤ 10⁵` | 4.7 min |
| `Prelim/SmallMuPhi.lean` | `6.798779 ≤ ∑_{q≤150000 odd} μ²(q)/φ(q) ≤ 6.79878` | about 10 min |
| `Prelim/SmallMertensLower.lean` | (2.13) for `3 ≤ N ≤ 10⁴`, and its base value at `10⁴` | about 1 min |
| `Prelim/SmallCGrid.lean` | `y ∑_{u≤3000} \|μ(u)\|/u² β(y, u) ≤ 2.8` on `[2.8, 80)` | 21 s |
| `Prelim/SmallMoebius.lean` | `\|∑_{n≤k} μ(n)/n\| ≤ √(2/(k+1))`, `k < 11815` | 51 s |
| `Prelim/SmallMertensProd.lean` | [RS62, Thm 15] for primes `5 ≤ x ≤ 10⁵`, `log θ(x)` to `10⁻²⁵` (tightest at `x = 23`, margin `2.4·10⁻⁷`) | 5.5 min |
| `Prelim/RamareBound.lean`, `RamareWalk.lean` | the product over primes `≤ 1000` and the walk for `c_E` | about 2 min |
| `MinorArcs/H2Bound.lean` | `α_n`, `β_n` for `n ≤ 15` | seconds |
| `MinorArcs/SmallG2.lean` | `g₂(n)` for `n ≤ 10⁴` in fixed point (a trie of the sums `A_d(n)`); `T₂ ≤ 0.37273` on `[16, 10⁴)`; `∫₁^{10⁴} g₂/y`, `∫₁^{10⁴} \|g₂\|` | 54 s |
| `MinorArcs/G2TailNum.lean` | `∫_k^∞ m(⌊t⌋)²/t` for `k ≤ 10⁴` (from `m(j)`, `j < 11815`), and the sum over `d ≤ 10⁴`, `a ≤ 10⁴/d` of the `g₂` tail bound | 82 s |

## Outlook

* Each remaining computation covers a range too large for the kernel as stated. A kernel check
  handles about `10⁵` simple steps per declaration, and `Nat.primesBelow 10⁴` already runs out of
  memory. Larger checks would need `native_decide`, which means trusting Lean's compiler.
* `eta2DD_small` is nearly sharp: the maximum is `31.52065` against `31.521`. A weaker bound
  (about `43.5`) has a short proof. But `c₀ = 31.521` enters the minor-arc numerics of about 15
  files, some of them tightly; for example, `BaseGap2.fourier_const_le` needs
  `c₀ √(2π)/(8π²) ≤ 1.0007`.
* `ramare_moebius` (`|m(x)| ≤ 0.03/log x`, `m(x) = ∑_{n≤x} μ(n)/n`, `x ≥ 11815`) is not a
  realistic target:
  * Ramaré's proof (Acta Arith. 157, hal-02572812) and its improvement arXiv:2408.05969 both start
    from bounds for `M(x) = ∑_{n≤x} μ(n)` that rest on large computations:
    * `|M(x)| ≤ x/4345` for `x ≥ 2 160 535` (Cohen–Dress–El Marraki);
    * `|M(x)| ≤ 0.571√x` for `33 ≤ x ≤ 10¹²` (Dress), or `|M(x)| ≤ √x` for `x ≤ 10¹⁶` (Hurst).
  * Ramaré's paper also uses Pari/GP computations up to `1.8·10⁹` (its Lemma 6.3).
  * Near `x = 10¹⁰`, `x/4345` is the operative input: the analytic bound `0.013 x/log x` is weaker
    until `log x ≈ 56`.
  * `|m(x)| ≤ 0.55/(log x − 0.7521)` (`Prelim/MoebiusBound.lean`) is derived from
    `ramare_moebius`. Without the cancellation in `μ` only `|m(x)| ≤ 1` is available, far from the
    `c/log x` that the tail of (5.31) and the Liouville bound need.
* The other published results are large computations (binary Goldbach, RH and GRH to the heights
  used, Büthe's bounds). From `rh_upto` alone the explicit formula gives about `√x log²x/(8π)` below
  `10¹⁹`, 10 to 80 times Büthe's `0.94√x`, too weak for its uses in [B, §2].
