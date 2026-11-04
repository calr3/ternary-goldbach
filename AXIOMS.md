# Axiom audit

`ternary_goldbach` depends on the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) and on 5 further axioms (`#print axioms`), all published results. Each axiom has been checked:

* our computations against their scripts: range, edge cases, the exact Lean definitions involved,
  rounding, and margin;
* published results against the papers.

Sources: [H] = Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2. Papers are cited by
arXiv number where there is one. [RS62], [MV73] and [Ram95] are as in the README.

## Our own computations (none left)

The two former computation axioms are now theorems:
* `eta2DD_small` ([H, (B.6)] for `0 ≤ t ≤ 655` with `31.521`) is proved with `32`
  (`MinorArcs/Eta2DDBound.lean`); `scripts/rigorous/eta2_fourier_rig.py` remains as a check of the
  true maximum `31.52065`;
* `prop1224_check` (the finite part of [H, Prop 12.2.4]: `87 972 745` checks over `q < 2.2·10¹⁰`) is
  replaced by a proof of Prop 12.2.4 with `c₊ = 2` (see "Proved in Lean" below);
  `scripts/rigorous/p1224_rig.c` remains as the record of the old check.

## Published results (5)

Each row was re-checked against the paper on 2026-11-02 (PDFs of all the sources except Ramaré's
Acta Arith. 157 paper, for which the later papers and the float check below stand in).

| Axiom | Statement | Source | Check |
|---|---|---|---|
| `Explicit.rh_upto` | zeros of `ζ` with `0 < ℜρ < 1`, `\|ℑρ\| ≤ 3·10¹²` have `ℜρ = 1/2` | Platt–Trudgian, arXiv:2004.09765 | abstract: "all zeroes `β + iγ` … with `0 < γ ≤ 3·10¹²` have `β = 1/2`". The axiom also covers `γ ≤ 0`: `γ < 0` by `ζ(s̄) = conj ζ(s)`, and `γ = 0` because `ζ(σ) < 0` on `(0, 1)` |
| `MajorArcs.platt_verification` | primitive `χ` of conductor `q`: GRH up to `10⁸/q` for odd `q ≤ 3·10⁵`, and up to `max(10⁸/q, 200 + 7.5·10⁷/q)` for even `q ≤ 4·10⁵` (`platt_odd`, `platt_even` are its two halves) | Platt, arXiv:1305.3087 | Thm 7.1 and abstract: all primitive `χ`, `q ≤ 4·10⁵`; odd `q` to `max(10⁸/q, 3.75·10⁷/q + 200)`; Thm 3.2 counts zeros with `\|ℑs\| ≤ t₀`, `ℜs ∈ (0,1)`; see Finding 2 |
| `Helfgott.binary_goldbach_input` | every even `4 ≤ n ≤ 1.45·10¹⁷` is a sum of two primes | [OeSHP14], Math. Comp. 83 (2014) | abstract: "confirmed to be true for all even numbers not larger than `4·10¹⁸`"; Table 1 and §1.3: "the entire interval up to `3·10¹⁷` was double-checked" (we earlier cited `4·10¹⁷` from the project page). `SmallCases.lean` needs only `1.45·10¹⁷`, inside the double-checked range |
| `Prelim.buthe_psi` | `\|ψ(n) − n\| ≤ 0.94 √n`, `12 ≤ n ≤ 10¹⁹` | Büthe, arXiv:1511.02032, Thm 2 | (1.5) `\|x − ψ(x)\| ≤ 0.94√x` for `11 < x ≤ 10¹⁹`. The `θ` bounds (1.6)–(1.7) of the same theorem are not used: our `θ` bounds are derived from (1.5) (`ThetaExplicit.psi_sub_theta_le_buthe`, `LambdaMu.thetaN_close_small`) |
| `Prelim.ramare_moebius` | `\|∑_{n≤x} μ(n)/n\| ≤ 0.03/log x` for real `x ≥ 11815` | Ramaré, Acta Arith. 157 (2013) 365–379, Cor. 1.4: for `x ≥ 11815` ([H, (2.21)]) | implied for `X ≥ 463 421` by Ramaré, Math. Comp. 84 (2015), Thm 1.2 (`≤ (0.0144 log X − 0.1)/(log X)²`), which Ramaré and Zuniga-Alterman re-derive in arXiv:2408.05969 (that paper also proves `≤ (0.010032 log X − 0.0568)/(log X)²` for `X ≥ 617 990`, Cor. 1.2). A float check (`scripts/moebius_ramare_check.py`) gives `max \|m(k)\| log(k+1) = 0.029496` over `11815 ≤ k < 10⁸`, at `k = 11820` |

The axioms are stated as in the papers or weaker. `ramare_moebius` is used for the Liouville bound
behind [H, (2.22)] (`Prelim/LiouvilleBound.lean`, `MoebiusBound.lean`) and for the tail of
`∫ |g₂|/y` in (5.31) (`MinorArcs/G2Tail.lean`). `buthe_psi` and `rh_upto` (through
`Explicit/PsiPlateau.lean`) also give the small cases: a prime in `(n − 1.45·10¹⁷, n − 4]` for
`1.45·10¹⁷ + 3 < n ≤ 10²⁷` (`Helfgott/SmallCases.lean`). This replaces the Helfgott–Platt prime ladder
(arXiv:1305.3062), formerly the axiom `prime_ladder_input`.

## Errors found in the sources

1. **[H, (5.32)] is false for `v = 2`, and so is (5.36), which depends on it.**
   * Our `T2` is exactly the sum in [H, (5.19)]. It agrees with [H]'s stated
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
2. **[H] is inconsistent about Platt's range.** [H, §1.6] says odd conductors up to `2·10⁵`; [H, §9.6]
   says `3·10⁵`. Platt's paper covers all `q ≤ 4·10⁵`, so `platt_odd` is covered either way.
3. **[H]'s derivation of (9.94) drops a factor 2.**
   * [H, p. 197] expands `∫η₊² log xt` with the cross term `2∫(η₊ − η◦)η◦ log xt`. It bounds
     `|∫(η₊ − η◦)η◦ log xt| ≤ 1.944·10⁻⁶ log x + 5.2·10⁻⁷`, then concludes (9.94) with
     `O*(1.95·10⁻⁶) log x + O*(5.3·10⁻⁷)`, without the factor 2. With the factor, the same argument
     gives about `3.9·10⁻⁶ log x + 1.27·10⁻⁶`.
   * (9.94) with [H]'s constants is proved anyway (`MajorArcs/EtaPlusSqLog.lean`), by Parseval in
     `u = log t` instead of Cauchy–Schwarz on all of `L²`. A float computation of `η₊`
     (`scripts/eta_plus_check.py`) also puts both integrals well inside [H]'s intervals.
4. **Two slips in [H]'s proof of Prop 12.2.4 (the result holds; it is proved).**
   * The proof applies Lemma 12.2.3, which bounds the quotient by `(log Q₀ + σ)/(log Q + 1.312)`,
     with `σ = c₊ = 1.36` for the range (12.29) of small `R`. But (12.23) has `log Q + c_E` in the
     denominator, with `c_E = 1.33258 > 1.312`. So with `σ = c₊` the lemma does not give (12.23);
     `σ ≈ 1.347` would, at a cost of about `0.5 %` in `ϖ(q)`. Our proof (`regionS`) bounds the
     quotient against `log Q + c_E` directly.
   * (12.15) claims `G(R) ≥ log R + 1.312` from (12.12) for `R ≥ 4·10⁷`. But (12.12) gives
     `c_E − 7.284 R^{−1/3} ≥ 1.312` only from `R ≈ 4.42·10⁷` on. We do not use (12.15).
5. **[Ram95, (3.9)] understates a product (Lemma 3.4 holds; it is proved).**
   * Ramaré's proof of Lemma 3.4 (= [H, (12.12)]) uses (3.9):
     `∏_p (1 + (p^{1/3} + p^{2/3})/(p(p−1))) ≤ 8`. The product over the primes below `10⁷` is
     already `8.0775`, and the full product is about `8.0845`. The constant `7.284 = 0.9105·8`
     comes from (3.9); with `8.0845` the same argument gives about `7.36`. (Checked against the page
     images of [Ram95], p. 659.)
   * Our proof (`Prelim/Ramare*.lean`) uses a different decomposition and gives `7.04 ≤ 7.284`.
6. **[H, p. 38] is off by one about `|m(x)| ≤ 1/(2√x)`.** [H] says the bound holds for
   `x ≤ 7727068587`. `moebius_sqrt_rig` finds that it fails already at `x = 7727068587`:
   `μ(7727068587) = 1`, and `4 m(x)² x ∈ [1.0000156, 1.0000165]` there. The remark is not used.

The README lists the other differences from [H].

## Proved in Lean, not assumed

These inputs are theorems:

| Result | File | Method |
|---|---|---|
| Ramaré's (12.12) ([Ram95, Lemma 3.4]), with `c_E ∈ [1.33258227, 1.33258229]` | `Prelim/Ramare.lean` | `g_d = h_d ∗ [odd]/n`; `∑ \|h_d(a)\| a^{1/3} ≤ 11 f₁(d)` by Euler products; `c_E = γ + log 2 + 2X/ζ(2) + ∑_p log p/(p³ − p)` via Mathlib's `L(Λ, s) = −ζ'(s)/ζ(s)` and a kernel walk (`RamareWalk.lean`) |
| (5.31) `T2_le` | `MinorArcs/T2Bound.lean`, `T2Small.lean`, `G2Tail.lean` | `g₂(n)` for `n ≤ 10⁴` by the kernel; `T₂ = α_n + β_n/S` exactly for `S < 700`; `T₂(S) = ¼ ∫₁^S g₂/y + O*(S⁻¹ ∫₁^S \|g₂\|)` above; `∫_{10⁴}^S \|g₂\|/y ≤ 0.0045` by Cauchy–Schwarz with weights `H_d(a) λ(da)`, which reduces it to `∫ m(⌊t⌋)²/t` (`m(k)` for `k < 11815` from the kernel, `ramare_moebius` beyond) and an Euler product `∏_{p>2} p²/(p²−1) ≤ π²/8` |
| Lemma 5.1.2: `\|g₂(x)\| ≤ 0.0236/(log x)² + 528 (1 + log x)²/x` (not used by `ternary_goldbach`) | `MinorArcs/G2Bound.lean` and `G2*.lean` | one convolution `f·1_{(·,d)=1} = H_d ∗ (μ/id)`; `ramare_moebius` for `x/u ≥ 11815` (Rankin weight `u^{1/9}`), [H, (2.24)] below; Euler products |
| (5.36) corrected, (5.37) | `MinorArcs/H2Bound.lean` | `T₂ = α_n + β_n/S` on `[n, n+1)`, kernel for `n ≤ 15` |
| Prop 12.2.4 with `c₊ = 2` (for [H]'s `1.36`) | `MinorArcs/LSQuot1–9.lean`, `LSQuotRed.lean`, `LSQuot8g.lean` | `q ≥ 2.2·10¹⁰`: [H]'s argument, (12.12), `regionS` and `λ(q)⁷ ≤ (103/120)⁹ q²`. `q < 2.2·10¹⁰`: with `R ∈ [n, n+1)` it suffices that `Φ(q, n) ≤ 0`; removing a prime `p ≥ 17` from `q` keeps `Φ ≤ 0` (`G_{q'}(n) = G_{q'p}(n) + G_{q'p}(n/p)/(p−1)`, `(q/φ(q)) G_q(x) ≥ G(x) ≥ log x`), which reduces `n ≥ 4` to the 64 divisors of `30030` (kernel walks over `r < 2600`, Ramaré beyond); `n ≤ 3` by an exchange argument with `log sq ≥ log(10⁵/(n+1))` |
| (9.94) | `MajorArcs/EtaPlusSqLog.lean`, `EtaONum.lean` | Parseval in `log t`; the four integrals by Taylor bounds and exact polynomial integration |
| (B.6), (B.11) with `32` for [H]'s `31.521` | `MinorArcs/Eta2DDExpand.lean`, `Eta2DDTaylor.lean`, `Eta2DDBound.lean` | `t ≥ 2`: three integrations by parts, `eta2DD t = F(e(−t/4), 1/2πt) + O*(6120/(2πt)³)`, and a kernel bisection of `‖F(z, w)‖ + 6120w³ ≤ 32` over `\|z\| = 1`, `w ≤ 2/25` (Lipschitz in `z` and `w`); `t ≤ 2`: Taylor polynomials of degree `< 50` with rational coefficients, kernel bisection of `[0, 12.6]` in `x = 2πt`. About 4 minutes of `decide +kernel`. (`Eta2Fourier.lean`'s bound for `\|t\| ≥ 655` is no longer used.) |
| [H, (2.13)] | `Prelim/LambdaMu.lean`, `SmallMertensLower.lean` | summation by parts from `10⁴` with `buthe_psi`; kernel for `N ≤ 10⁴` |
| [H, (2.22)] with constant `2.8` | `Prelim/LiouvilleBound.lean`, `SmallCGrid.lean` | Ramaré's Liouville route: `ramare_moebius` for `x ≥ 11815`, [H, (2.24)] and a kernel check below; Ramaré's `ρ(U, y)` optimisation on a kernel-checked grid of 17 intervals |
| [H, (2.24)] for `x < 11815` | `Prelim/SmallMoebius.lean` | kernel walk; `μ` by trial division |
| [RS62, Thm 15] (`∏_{p≤x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)`, [H, (C.19)]) | `Prelim/MertensProduct.lean`, `SmallMertensProd.lean` | Mertens' theorem with explicit error: `theta_explicit` above `10⁹`, Büthe's `ψ` bound, `|θ(x) − x| ≤ 2.37 √x` and a sharper prime-power tail on `[10⁵, 10⁹]`, kernel for primes `≤ 10⁵` |
| [MV73, Lemmas 7, 8] | `Prelim/MVLemma7.lean`, `MVLemma8.lean` | (12.12) for `r ≥ 21400`, Abel summation for `R ≥ 1000`; kernel below |
| the `ψ`, `θ` bounds of [H, §2] | `Prelim/LambdaMu.lean`, `ThetaExplicit.lean` | `buthe_psi` up to `10¹⁹` (with `ψ − θ` bounded from it for `θ`), our explicit prime number theorem beyond; kernel for small `n` |

The kernel evaluates these finite checks (`decide +kernel`, no `native_decide`):

| File | Check | Time |
|---|---|---|
| `Prelim/SmallPsi.lean` | `ψ(n) < 1.03883 n`, `n ≤ 586` (via `lcm(1, …, n)`) | seconds |
| `Prelim/SmallMertens.lean` | `∑_{m≤n} Λ(m)/m ≤ log n`, `n ≤ 100` | seconds |
| `Prelim/SmallProdAp.lean` | `∏_{p<10⁴} (1 + (p^{−2/3} + p^{−1/3})/(p − 1)) ≤ 7.99` | seconds |
| `Prelim/SmallFsq.lean` | [H, p. 83] for `⌊X⌋ < 200` | seconds |
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

Helfgott's comments (2026-11) on the axioms, and what follows from the code:

* **`buthe_psi` is stronger than needed above `10¹²`.** Its `√x`-quality is used only for
  `n ≤ 10¹²`:
  * `psi_lower2`, `psi_lower_all` and `psi_upper_all` switch to `theta_explicit` at `10¹⁰`;
  * `MertensProduct` uses it on `[10⁵, 10⁹]`, `psi_mul_buthe` up to `10⁸`, and
    `psi_sub_theta_le_buthe` at `√N ≤ 3.2·10⁹`;
  * `nonprime_mid`, `logsq_mid`, `thetaN_ge` and `thetaN_close_small` go up to `10¹²`.

  On `[10¹², 10¹⁹]`, three uses remain, and none needs `√x` quality:
  * `theta_explicit` needs `|θ(n) − n| < n/log³n`, that is
    `|ψ(n) − n| ≤ c √n` with `c` allowed up to `45` at `10¹²`, `296` at `10¹⁴` and `2000` at `10¹⁶`
    (after `ψ − θ ≤ √n (1.0054 + 0.048 log n)`);
  * `psi_bounds` needs only `ψ ≤ 1.0004 n`;
  * `SmallCases` needs only `|θ(m) − m| ≤ 7·10¹⁶`.

  So Büthe can be replaced by:
  1. a direct computation, `|ψ(x) − x| ≤ c√x` for `x ≤ X₀`, with `c ≤ 0.94` (or the downstream
     constants retuned). Chirre–Helfgott, "Optimal bounds for sums of non-negative arithmetic
     functions" (arXiv:2512.15709, Dec. 2025), Lemma 9.2, is this kind of input: by brute force,
     `−√2 < (ψ(x) − x)/√x ≤ 0.7906` for `1 ≤ x ≤ 10¹³` (and `≥ −0.7510` on `[10⁴, 10¹³]`). Their
     Cor. 1.3 gives `|ψ(x) − x| ≤ πx/(3·10¹²) + 113.67√x` for all `x ≥ 1`, from RH up to
     `3·10¹² + 1 + π/3` alone;
  2. our explicit formula from `rh_upto` on `[X₀, 10¹⁹]`, proved in Lean. As it stands, `psi_plateau`
     gives `1533 √x + 2.15·10⁻¹¹ x + 4 y₀` (`y₀ = 10¹⁰`). With `y₀` lowered, that covers `x ≳ 10¹⁶`.
     Reaching `X₀ = 10¹⁴` needs `c ≲ 296`. The zeros up to `3·10¹²` allow about
     `(log(T/2π))²/(2π) ≈ 115`, so the loss is in our zero counting (Jensen windows). A sharp explicit
     `N(T)` would remove it.

  The axiom count stays the same. But the input becomes a sieve computation up to `10¹³` instead of
  Büthe's analytic theorem up to `10¹⁹`.
* **`ramare_moebius`** is a citation, and the citation can change: Helfgott expects Ramaré's bound to
  be superseded by his work with Chirre (arXiv:2511.14736, "Optimal bounds for sums of bounded
  arithmetic functions"). Proving it in Lean is still not realistic: every known proof rests on large
  computations of `M(x)`:
  * `|M(x)| ≤ x/4345` for `x ≥ 2 160 535` (Cohen–Dress–El Marraki);
  * `|M(x)| ≤ 0.571√x` up to `10¹²` (Dress), or `|M(x)| ≤ √x` up to `10¹⁶` (Hurst);
  * Ramaré's own Pari/GP check up to `1.8·10⁹`.
* **`eta2DD_small` ([H, Lemma B.1.2]) is gone.** Following Helfgott's suggestion, it is replaced by
  the slightly weaker `|η̂₂''|_∞ ≤ 32`, proved in Lean. The cost downstream: `√c₀` grows by
  `1.0076`, so Theorem 3.1.1's `2.5 x/√t` becomes `2.511 x/√t`, Type I constants move in the third
  or fourth digit, the base gap becomes `0.0121 y` (was `0.012 y`), and the worst cell of the final
  minor-arc inequality goes from `0.96499` to `0.96534` (against `1.037`).
* No computation of our own is assumed any more. The remaining axioms are published results; the
  computational ones (RH and GRH to given heights, binary Goldbach, Büthe's `ψ`) are far beyond the
  kernel without `native_decide`.
* The other published results are large computations: binary Goldbach, and RH and GRH to the heights
  used.
