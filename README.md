# Ternary Goldbach in Lean 4 (a blueprint of Helfgott's proof)

**Status: not a complete formal proof.** `TernaryGoldbach.ternary_goldbach` states that every
odd integer greater than 5 is a sum of three primes. It is derived in Lean from **4 explicitly
stated results from the literature**, which are still `sorry`, and **33 numerical axioms**
(finite computations, listed below). Everything that connects them to the theorem is proved.

```
$ lake build
$ echo 'import TernaryGoldbach
#print axioms TernaryGoldbach.ternary_goldbach' > /tmp/ax.lean && lake env lean /tmp/ax.lean
'TernaryGoldbach.ternary_goldbach' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 TernaryGoldbach.Helfgott.binary_goldbach_input,
 TernaryGoldbach.Helfgott.prime_ladder_input,
 TernaryGoldbach.MajorArcs.integral_etaPlus_sq_log,
 TernaryGoldbach.MajorArcs.platt_even,
 TernaryGoldbach.MajorArcs.platt_odd,
 TernaryGoldbach.MajorArcs.sum_odd_mu_sq_div_totient,
 TernaryGoldbach.MinorArcs.H2_le,
 TernaryGoldbach.MinorArcs.T2_le,
 TernaryGoldbach.MinorArcs.eta2_fourier_bound',
 TernaryGoldbach.MinorArcs.eta2log_fourier_bound,
 TernaryGoldbach.MinorArcs.integral_H2_le,
 TernaryGoldbach.MinorArcs.prop_12_2_4,
 TernaryGoldbach.Prelim.C_grid,
 TernaryGoldbach.Prelim.K_blocks,
 TernaryGoldbach.Prelim.K_pieces,
 TernaryGoldbach.Prelim.fsq_le,
 TernaryGoldbach.Prelim.liouville_small,
 TernaryGoldbach.Prelim.logsq_small,
 TernaryGoldbach.Prelim.mertens_lower_small,
 TernaryGoldbach.Prelim.mertens_point,
 TernaryGoldbach.Prelim.mertens_product_small,
 TernaryGoldbach.Prelim.mertens_small,
 TernaryGoldbach.Prelim.moebius_sqrt_small,
 TernaryGoldbach.Prelim.nonprime_small,
 TernaryGoldbach.Prelim.psi_mid,
 TernaryGoldbach.Prelim.psi_mul_mid,
 TernaryGoldbach.Prelim.psi_small,
 TernaryGoldbach.Prelim.psi_sqrt,
 TernaryGoldbach.Prelim.theta_sqrt,
 TernaryGoldbach.Prelim.MV.GS_N0,
 TernaryGoldbach.Prelim.MV.lemma7_numeric,
 TernaryGoldbach.Prelim.MV.lemma8_numeric,
 TernaryGoldbach.Prelim.MV.prod_ap_le]
```

See [`BLUEPRINT.md`](BLUEPRINT.md) for the chapter-by-chapter map from the book to Lean.

The 4 `sorry`s that `ternary_goldbach` depends on are:

* **three cited Part II results**: the explicit-formula estimates [B, Prop 9.3.2], [B, Prop 9.4.2] and
  [B, Prop 9.5.1] (`MajorArcs/GRH.lean`, `MajorArcs/Thm714.lean`, `MajorArcs/Prop715.lean`), each stated
  *conditionally* on GRH up to a height `T₀`. From them, Platt's GRH verification (numerical axioms
  `platt_odd`, `platt_even`) and the value (9.94) (numerical axiom), [B, Cor 7.1.3], [B, Thm 7.1.4] and
  [B, Prop 7.1.5] are proved; [B, (14.7)] (the `ℓ²` norm over the major arcs, Lemma 10.3.1 + §14.1) is
  proved from Thm 7.1.4 in `MajorArcs/L2Major.lean`, with one more numerical axiom
  (`Σ_{q≤150000 odd} μ²(q)/φ(q) = 6.798779…`); [B, (14.27)] (the major-arc total, Chs. 10–11 and
  §14.2) is proved from Cor 7.1.3, Prop 7.1.5 and (14.7) in `MajorArcs/MajorTotal.lean`, with constant
  `1.049` in place of [B]'s `1.058259`; [B, (14.28)] is proved, in a weaker form, in
  `MinorArcs/EBound.lean`;
* **one literature result** in `Prelim/LambdaMu.lean`: Dusart's explicit prime number theorem
  `|θ(x) − x| < x/log³ x` for `x ≥ 89 967 803` ([Dus18, Thm. 4.2]).
  All the bounds on `ψ` and `θ` that [B] quotes — (2.12)–(2.15), (2.17), (2.19), (5.5) — and
  Lemma C.2.2 ([RS62, Thm. 15], in `Prelim/MertensProduct.lean`) are proved from Dusart's bound
  plus finite checks; C.2.2 also uses Mertens' theorem with Euler's constant, ported from PNT+.
  (2.23) is proved elementarily with the weaker constant `q/φ(q) + 2.67` (`Prelim/MoebiusLog.lean`;
  [B]: `1.00303 q/φ(q)`), absorbed downstream. (2.22) is proved with constant `2.8` (for [B]'s `4/5`)
  by Ramaré's Liouville route from our own `|∑_{n≤x} μ(n)/n| ≤ 0.54/(log x − 0.7521)`, `x ≥ 10¹⁰`
  (`Prelim/MoebiusBound.lean`, `Prelim/Liouville.lean`, `Prelim/LiouvilleBound.lean`), also absorbed
  downstream. (The sharp large sieves and [MV73, Lemmas 7, 8] in
  `Prelim/LargeSieveMV.lean` are also proved.)

Of [B]'s remaining §2 statements that `ternary_goldbach` does not use,
(2.16) and (2.18) are proved in `Prelim/LambdaMuExtra.lean` (with three more finite checks, listed
below but not in the `#print axioms` output), (2.24) is proved for `x < 10¹⁰` (our sieve; [B] cites
Helfgott's check to `10¹²`), and (2.21) (Ramaré's `0.03/log x`) is not stated: our substitute is
`|∑_{n≤x} μ(n)/n| ≤ 0.54/(log x − 0.7521)` for `x ≥ 10¹⁰`.

## Numerical axioms

These are finite computer computations: seven from [B] (the book describes the method but
doesn't include the code or the output), the two computational inputs for small `N`, four finite
checks behind [MV73, Lemmas 7, 8], eleven checks of `ψ`, `θ` and Mertens products over finite ranges, and five
checks behind (2.22), plus Platt's GRH verification [B, §9.6], the value [B, (9.94)] and the sum
`Σ μ²(q)/φ(q)` of [B, §14.1] (our own computations, reproducible with `scripts/mv_lemma8_check.py`,
`scripts/psi_checks.py`, `scripts/psi_mid_check.py`, `scripts/mertens_product_check.py`,
`scripts/moebius_K_check.py`, `scripts/moebius_sqrt_check.py`, `scripts/liouville_small_check.py`,
`scripts/moebius_C_grid.py`, `scripts/check_sum_mu2_phi.py`). They are stated as Lean `axiom`s, so `#print axioms`
lists each one by name. Most are interval-arithmetic computations.

| Axiom | [B] | Statement | How [B] obtains it |
|---|---|---|---|
| `MinorArcs.eta2_fourier_bound'` (`InnerSums.lean`) | App. B, (B.6) | `\|η̂₂''\|_∞ ≤ 31.521` | rigorous numerical bound on the Fourier transform of `η₂` |
| `MinorArcs.eta2log_fourier_bound` (`Eta2Log.lean`) | App. B, Lemma B.2.3 | `\|η̂_(ρ)''\|_∞ ≤ 31.521 log ρ` for `ρ ≥ 4`, `η_(ρ)(t) = log(ρt) η₂(t)` | the same method |
| `MinorArcs.prop_12_2_4` (`LargeSievePrimes.lean`) | Prop 12.2.4 | `G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + 1.36)/(log Q + 1.33258)` | large `R` analytically (Ramaré's (12.12)); then a finite check of `R ∈ [ϖ(q), λ(q))` for `q < 3.3·10⁹` (`q < 2.2·10¹⁰` if `210 ∣ q`) |
| `MinorArcs.T2_le` (`TypeIIS1.lean`) | (5.31), p. 92 | `T₂(S) ≤ 0.37273` for `S ≥ 16` | `S ≥ 10⁵`: Lemma 5.1.2 (itself a computation for `x ≤ 10⁶`) and the numerics after (5.30); `16 ≤ S < 10⁵`: direct computation |
| `MinorArcs.integral_H2_le` (`TypeIIS1.lean`) | (5.36) | `∫₁ᵀ H₂(S)/S dS ≤ 0.15107 log T` | numerical, from (5.32) |
| `MinorArcs.H2_le` (`TypeIIS1.lean`) | (5.37) | `H₂(S) ≤ 2/π²` | numerical: `T₂(S) ≤ 1/2` for `S < 16` |
| `Prelim.fsq_le` (`SqfreeCount.lean`) | p. 83 | `f(X) ≤ 1.27 X` | `f(X)/X` has local maxima only at squarefree integers: check up to a constant, then a crude bound gives `< 1.26981` |
| `Helfgott.binary_goldbach_input` (`Inputs.lean`) | [OeSHP] | every even `4 ≤ n ≤ 4·10¹⁸` is a sum of two primes | exhaustive computer search |
| `Helfgott.prime_ladder_input` (`Inputs.lean`) | [HP] | a chain of certified odd primes from 3 to `≥ 8.875694·10³⁰` with gaps `≤ 4·10¹⁸ − 4` | computer construction with primality certificates |
| `Prelim.MV.lemma8_numeric` (`MVLemma8.lean`) | [B, p. 97] | for `2 ≤ n ≤ 10⁴`: `∑_{r≤n} μ²(r)/φ(r)·(n+1)/(n+1+r) > log(n+1) + 0.25068` and `∑_{r≤n} μ²(r)/φ(r)·r(n+1)/((n+1+r)(n+r)) ≤ 1` | direct computation (`scripts/mv_lemma8_check.py`; margin `1.1·10⁻⁶` at `n = 4`, also checked exactly) |
| `Prelim.MV.lemma7_numeric` (`MVLemma7.lean`) | [B, (12.9)] range | `G(r) = ∑_{s≤r} μ²(s)/φ(s) ≥ log(r+1) + 1.07` for `6 ≤ r < 3·10⁷` | sieve computation (same script; margin `0.044`) |
| `Prelim.MV.GS_N0` (`MVLemma7.lean`) | — | `G(3·10⁷) ≥ log(3·10⁷) + 1.3325` | same computation (value `1.33258`) |
| `Prelim.MV.prod_ap_le` (`MVLemma7.lean`) | — | `∏_{p<10⁴} (1 + (p^{−2/3} + p^{−1/3})/(p−1)) ≤ 7.99` | finite product (value `7.98552`) |
| `Prelim.psi_small` (`LambdaMu.lean`) | [RS62, Thm 12] range | `ψ(n) < 1.03883 n` for `1 ≤ n < 2·10⁶` | sieve (`scripts/psi_checks.py`; max `1.0388206` at `n = 113`) |
| `Prelim.nonprime_small` (`LambdaMu.lean`) | [RS62, Thm 13] range | `ψ(n) − θ(n) < 1.4262 √n` for `1 ≤ n ≤ 10¹²` | prime powers `p^k ≤ 10¹²`, `k ≥ 2` (same script; max `1.4261933` at `n = 361`) |
| `Prelim.mertens_small` (`LambdaMu.lean`) | [RS62, (3.23)] range | `∑_{m≤n} Λ(m)/m ≤ log n` for `1 ≤ n ≤ 100` | direct (same script) |
| `Prelim.psi_mid` (`LambdaMu.lean`) | (2.14) range | `ψ(n) ≤ 1.0004 n` for `2·10⁶ ≤ n ≤ 10⁹` | segmented sieve (`scripts/psi_mid_check.py`; max `1.0003639` at `n = 3 445 943`) |
| `Prelim.psi_sqrt` (`LambdaMu.lean`) | — | `\|ψ(n) − n\| ≤ 0.95 √n` for `11 ≤ n ≤ 10¹⁰` | same sieve (max `0.7906`; cf. Büthe's `0.94√x` for `x ≤ 10¹⁹`) |
| `Prelim.theta_sqrt` (`LambdaMu.lean`) | — | `\|θ(n) − n\| ≤ 1.95 √n` for `5·10⁵ ≤ n ≤ 10¹⁰` | same sieve (max `1.8071`; Büthe's constant is `1.95`) |
| `Prelim.psi_mul_mid` (`LambdaMu.lean`) | (2.17) range | `∑_{m≤n} Λ(m) m < 1.0008 n²/2` for `1.6·10⁶ ≤ n ≤ 10⁸` | same sieve (min margin `4.3·10⁻⁵ n²`) |
| `Prelim.mertens_lower_small` (`LambdaMu.lean`) | (2.13) range | `∑_{m≤n} Λ(m)/m ≥ log(n+1) − log(3/√2)` for `3 ≤ n ≤ 10⁶` | direct (`scripts/psi_checks.py`; min margin `0.014`) |
| `Prelim.mertens_point` (`LambdaMu.lean`) | — | `∑_{m≤X} Λ(m)/m − ψ(X)/(X+1) − log(X+2) ≥ −1.5776`, `X = 10⁶` | direct (same script; value `−1.57721`) |
| `Prelim.logsq_small` (`LambdaMu.lean`) | (2.19) range | `∑_{n/2<p≤n} (log p)² ≤ (1/2) n log n` for `117 ≤ n ≤ 10⁶` | direct (same script; min margin `2.14`) |
| `Prelim.K_pieces` (`MoebiusBound.lean`) | (2.22) input | `∑_{k<1000} ∑_{i<⌈400/k⌉} g_{k,i} log(b/a) ≤ 0.4035`: pieces `[a,b)` of `[k,k+1)`, `g` the larger endpoint value of `\|∑_{n≤k}Λ(n)/n − log y − E(10⁹)\|` | segmented sieve to `10⁹` (`scripts/moebius_K_check.py`; value `0.40342`) |
| `Prelim.K_blocks` (`MoebiusBound.lean`) | (2.22) input | for `1000 ≤ k < 10⁹`: `\|∑_{n≤k}Λ(n)/n − log t − E(10⁹)\| ≤ h_j` at `t = k, k+1`, `j = ⌊log₂(k/1000)⌋`, 20 block constants | same sieve (block maxima `+ 10⁻⁷`, rounded up) |
| `Prelim.moebius_sqrt_small` (`LiouvilleBound.lean`) | (2.24) range | `\|∑_{n≤k} μ(n)/n\| ≤ √(2/(k+1))` for `1 ≤ k < 10¹⁰` | segmented Möbius sieve (`scripts/moebius_sqrt_check.py`; equality at `k = 1`, otherwise max ratio `0.612` at `k = 2`; [B] cites Helfgott's check to `10¹²`) |
| `Prelim.liouville_small` (`LiouvilleBound.lean`) | — | `\|∑_{n≤k} λ(n)/n\| log(k+1) ≤ 0.99` for `1 ≤ k ≤ 10⁵` | direct (`scripts/liouville_small_check.py`; max `0.7831` at `k = 10`) |
| `Prelim.C_grid` (`LiouvilleBound.lean`) | (2.22) optimisation | `(2.8 + (i+1)/100)·G(2.8 + i/100) ≤ 2.8` for `i < 7720`, `G(a) = ∑_{u≤3000} \|μ(u)\|/u² min(5/3, 0.99/(a − 2 log u)) + (5/3)/3000.5` | direct (`scripts/moebius_C_grid.py`; max `2.7422`) |
| `MajorArcs.platt_odd` (`MajorArcs/GRH.lean`) | §9.6, [Plab] | GRH for `L(s, χ)` up to height `10⁸/q`, every primitive `χ` of odd conductor `q ≤ 3·10⁵` | D. Platt's rigorous (interval-arithmetic) computation |
| `MajorArcs.platt_even` (`MajorArcs/GRH.lean`) | §9.6, [Plab] | the same for even `q ≤ 4·10⁵`, up to `max(10⁸/q, 200 + 7.5·10⁷/q)` | the same |
| `MajorArcs.integral_etaPlus_sq_log` (`MajorArcs/Prop715.lean`) | (9.94) | `∫₀^∞ η₊²(t) log(xt) dt = (0.640206 + O*(1.95·10⁻⁶)) log x − 0.021095 + O*(5.3·10⁻⁷)` | rigorous integration (VNODE-LP) of `η◦` and the bounds (A.23), (A.24) on `η₊ − η◦` |
| `MajorArcs.sum_odd_mu_sq_div_totient` (`MajorArcs/SumMuPhi.lean`) | §14.1 | `6.798779 ≤ ∑_{q≤150000, q odd} μ²(q)/φ(q) ≤ 6.79878` | interval arithmetic; ours: directed-rounding decimal sum (`scripts/check_sum_mu2_phi.py`; value `6.7987791731…`) |
| `Prelim.lambda_mul_small` (`LambdaMuExtra.lean`, unused) | (2.16) range | `∑_{n≤k} Λ(n) n < 1.03884 k²/2` for `663 ≤ k ≤ 1.6·10⁶` | sieve (`scripts/psi_extra_check.py`; max ratio `1.03583` at `k = 663`) |
| `Prelim.lambda_sqrt_small` (`LambdaMuExtra.lean`, unused) | (2.18) range | `∑_{n≤k} Λ(n)/√n < 2.0008 √k` for `1 ≤ k ≤ 2·10⁶` | same script (max ratio `1.99838`) |
| `Prelim.lambda_sqrt_point` (`LambdaMuExtra.lean`, unused) | (2.18) | `∑_{n≤K} Λ(n)/√n − ψ(K)/√(K+1) − 1.0004√(K+1) ≤ −2`, `K = 2·10⁶` | same script (value `−3.2553`) |
| `Prelim.mertens_product_small` (`MertensProduct.lean`) | Lemma C.2.2 range | `∏_{p≤x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)` for primes `5 ≤ x ≤ 10⁸` | direct (`scripts/mertens_product_check.py`; tightest at `x = 23`, margin `2.4·10⁻⁷`, checked to 40 digits) |

`fsq_le` and `H2_le` look small enough to prove in Lean. `prop_12_2_4` and `T2_le` would need an
external certificate.

In the table below, "uses trusted bounds" means that the file's main theorems depend on some of
these `sorry`s or numerical axioms (through `#print axioms`); the file itself contains neither.

## Layout

| File | Content | `sorry`-free? |
|---|---|---|
| `Statement.lean` | `Statement`, the finite-range versions, and how to combine them | ✅ |
| `Reduction.lean` | binary Goldbach up to `N` + a prime ladder with gaps `≤ N − 4` ⇒ ternary Goldbach up to the top of the ladder | ✅ |
| `CircleMethod.lean` | finite circle method: orthogonality, `∫₀¹ S_a S_b S_c e(−Nα) = #weighted reps`, Parseval, an L² Cauchy–Schwarz bound, the minor-arc bound `≤ sup_𝔪|S_a| ‖b‖₂‖c‖₂`, a general "major > minor ⇒ three primes" criterion, and the circle identity for absolutely summable series | ✅ |
| `Helfgott/Defs.lean` | Helfgott's η₊, η_*, h_H, F_H, η₂, φ, Mellin convolution, `S_η(α,x)`, the major arcs `𝔐_{δ₀,r}`, `x = N/(2+9/(196√(2π)))`, the weighted count | ✅ (definitions) |
| `Helfgott/Decay.lean` | Gaussian decay of η₊ and η_*, so `S_η(α,x)` converges absolutely | ✅ |
| `Helfgott/NonPrime.lean` | [H, (7.50)] from sup bounds on η₊, η_* and bounds on ψ, ψ − θ (constants as parameters) | ✅ |
| `Helfgott/SupNorms.lean` | easy sup bounds `|η₊| ≤ 400`, `|η_*| ≤ 6.2` | ✅ |
| `Helfgott/Chebyshev.lean` | elementary `θ(N) ≤ N log 4`, `ψ(N) − θ(N) ≤ 1.6√N`, `ψ(N) ≤ 1.387 N` (for `N ≥ 10²⁷`) | ✅ |
| `Helfgott/Numerics.lean` | the final inequality of [B, §14.4], `C·N^{3/2} log N < (1.049 − 1.0376) x²/κ = 0.0114 x²/κ` for `N ≥ 10²⁷`, both with Helfgott's `C = 7.3306` and with the cruder `C = 6.7·10⁶` we actually use | ✅ |
| `MinorArcs/Vaughan.lean` | Vaughan's identity `Λ = Λ_{≤V} + μ_{≤U}∗log − μ_{≤U}∗Λ_{≤V}∗1 + μ_{>U}∗Λ_{>V}∗1` | ✅ |
| `MinorArcs/LargeSieve.lean` | Gallagher's lemma; the large sieve `∑_r |S(α_r)|² ≤ (δ⁻¹ + 4πX)‖a‖²` for `δ`-spaced points; the Farey version with `Q² + 4πX` | ✅ |
| `Helfgott/Eta2.lean` | explicit formulas for `η₂`, `|η₂|₁ = 1`, continuity, compact support, total variation `8 log 2` | ✅ |
| `MinorArcs/TrigSums.lean` | [B, §4.1, Lemmas 4.1.1–4.1.3]: trigonometric sums (4.1.3 by a sharper argument than the book's; 4.1.1 also with the summand read as `A` where `sin = 0`) | ✅ |
| `MinorArcs/FourierSums.lean` | [B, §2.3]: `∑ 1/(n−s)² = π²/sin²(πs)` (via Parseval), `∑_{n≠0} 1/(n−r)² ≤ π² − 4`, Lemma 2.3.1 (via Poisson summation), both bounds of (2.2) (with total variation for `|f'|₁`) | ✅ |
| `MinorArcs/InnerSums.lean` | `T_{m,∘}` and its bounds [B, (4.36)]; the Poisson main term [B, (4.33)–(4.34)]; the numerical axiom `|η̂₂''|_∞ ≤ c₀` | ✅ (one numerical axiom) |
| `MinorArcs/BlockSums.lean` | splitting sums into blocks of length `q`; `∑ 1/(R+jq)` and `∑ √(1+q/(R+jq))` bounds | ✅ |
| `MinorArcs/TypeI.lean` | definitions and bounds of [B, Lemmas 4.2.2–4.2.4] (the bounds of 4.2.4 in our corrected form) | ✅ (one lemma uses the axiom (B.6)) |
| `MinorArcs/TypeIProof.lean` | **[B, Lemma 4.2.2] proved** (both cases), modulo the numerical axiom `|η̂₂''|_∞ ≤ 31.521` | ✅ (uses trusted bounds) |
| `MinorArcs/InnerSumsGen.lean` | (4.36) and the Poisson main term for a general smoothing function | ✅ |
| `MinorArcs/Eta2Log.lean` | `η_(ρ)(t) = log(ρt) η₂(t)`: [B, (4.38)], Lemma B.2.1; Lemma B.2.3 as a numerical axiom | ✅ (one numerical axiom) |
| `MinorArcs/SumTools.lean` | sums vs antiderivatives (MVT); the log-weighted sums of [B, Lemma 4.2.3] | ✅ |
| `MinorArcs/TypeILogProof.lean` | **[B, Lemma 4.2.3] proved** in the form [B, §6.2.1] uses ((4.40) corrected, (4.41) slightly weakened; the unused (4.42) omitted) | ✅ (uses the trusted bounds) |
| `Prelim/LambdaMu.lean` | bounds on sums of `Λ` and `μ` [B, (2.12)–(2.24), (5.5)]. **Proved** from Dusart's `\|θ(x) − x\| < x/log³x` ([Dus18], cited) and finite checks: (2.14) and (2.15) (strong induction with `ψ − θ ≤ ψ(√n) + n^{1/3} log n`), (2.12) (Chebyshev's identity, summation by parts), (2.13) (summation by parts from `10⁶` with telescoping tails), (2.17) (`∑Λ(n)n = Nψ(N) − ∑_{m<N} ψ(m)`), (2.19) (split at `3N/4`), (5.5) | 🟡 Dusart + (2.22), (2.23) cited |
| `Helfgott/HHBound.lean` | `\|h₂₀₀\| ≤ 3.15`, `\|η₊\| ≤ 1.94`, `t\|η₊(t)\| ≤ 2.32`: substitution `y = t/u`, integration by parts against `−G_H(log(t/u))` with `\|G_H\| ≤ 3/π` (sine integral), total variation `2e^{1/2}` of `h` | ✅ |
| `MinorArcs/EBound.lean` | **[B, (14.28)] proved** with constant `8·10⁻¹¹` (B: `8.4029·10⁻¹²`): `E ≤ √x(24.12 log x + 18.01)` from the sup norms above, (2.15), (5.5) and dyadic blocks; the minor-arc total still closes (`1.0376`) | ✅ (Dusart via (2.15), (5.5)) |
| `Prelim/MoebiusLog.lean` | **(2.23), elementary form**: `\|∑_{n≤x,(n,q)=1} μ(n)/n log(x/n)\| ≤ q/φ(q) + 2.67` via `∑ μ_q(n)/n · H(x/n) = ∑_{k≤x, rad k ∣ q} 1/k ∈ [0, q/φ(q)]` (multiplicativity, Euler product over `q`-factored numbers), `H(M) = log y + γ + O*(1/M)` and (2.20); the Type I constants change accordingly (`log t + 1.63 → 2.96` in `typeI1_first`, `7.7 → 15.7` in `typeI1_second`) and still close | ✅ |
| `Prelim/PNTMertens.lean` | Mertens' second theorem `∑_{d≤x} Λ(d)/(d log d) = log log x + γ + E₂Λ(x)` with an integral formula for `E₂Λ`; **ported from PNT+** (Apache 2.0, `licenses/`) | ✅ |
| `Prelim/MertensProduct.lean` | **[B, Lemma C.2.2] proved**: `\|E₂Λ(x)\| = O(1/log³x)` from Dusart, the log series, `∏_{p≤x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)` for `x ≥ 10⁸` (finite check below), and the exchange argument `q/φ(q) ≤ ∏_{p≤p_{ω(q)}} p/(p−1)` | ✅ (Dusart, one numerical axiom) |
| `Prelim/MoebiusDecay.lean`, `Prelim/MoebiusBound.lean` | toward (2.22): `m(x)(log x + c) = −∑_{n≤x} μ(n)/n (E(x/n) − c)` (from `μ log = −Λ ∗ μ`), and **`\|∑_{n≤x} μ(n)/n\| ≤ 0.54/(log x − 0.7521)` for `x ≥ 10¹⁰`** via `∑_{n≤x} \|E(x/n) − E(x)\|/n ≤ 0.54` (pieces below `1000`, dyadic blocks to `10⁹`, Dusart beyond); two numerical axioms `K_pieces`, `K_blocks` (`scripts/moebius_K_check.py`) | ✅ (Dusart, two numerical axioms) |
| `Prelim/Liouville.lean` | Ramaré's identities (Acta Arith. 165 (2014), Lemmas 2.3, 2.5, 3.2): `λ = sq ∗ μ`, `μ = μ_sq ∗ λ`, `λχ_q = d_q ∗ λ` by multiplicativity, and their `1/n`-weighted partial-sum forms | ✅ |
| `Prelim/LiouvilleBound.lean` | **[B, (2.22)] proved with constant `2.8`** (for `4/5`): `\|ℓ(z)\| ≤ 0.99/log z` (`z > 1`), `\|ℓ_q(x)\| ≤ 0.99(q/φ(q))/log(x/q)`, and `\|∑_{n≤x,(n,q)=1} μ(n)/n\| ≤ 2.8(q/φ(q))/log(x/q)` for `q < x`; downstream `typeI1_first` `1.80303 → 3.8`, `typeI2_first` `0.8 → 2.8`, Theorem 3.1.1 unchanged | ✅ (three numerical axioms, Dusart) |
| `MajorArcs/GRH.lean`, `Eta2Moments.lean`, `Cor933.lean`, `Cor713.lean`, `Prop715.lean` | Part II split into analysis and computation: `GRHUpTo χ T` (Mathlib's `DirichletCharacter.LFunction`), Platt's verification as numerical axioms, [B, Prop 9.3.2] and [B, Prop 9.5.1] cited *conditionally on GRH up to `T₀`*; **[B, Cor 9.3.3] proved** from 9.3.2 by averaging over `η₂` (dominated convergence, `η̂_* (s) = ∫ η₂(r) η̂(rs) dr`, the moments `∫ w^{-k/2} η₂`), **[B, Cor 7.1.3] proved** (`T₀ = 10⁸/q`, same constants), **[B, Prop 7.1.5] proved** (`T₀ = 440`); `Thm714.lean`: **[B, Thm 7.1.4] proved** from the cited [B, Prop 9.4.2] (`q = 1`: `4.78·10⁻¹¹ + 251400/√x`; odd/even `q`: `1.35·10⁻¹⁴ + 1.62·10⁻¹⁰/q + (499900/√q + 52)/√x`, [B]'s constants rounded up slightly) | ✅ (three cited, three numerical axioms) |
| `Prelim/MoebiusCoprime.lean` | **[B, (2.20)] proved**: `\|∑_{n ≤ x, (n,q)=1} μ(n)/n\| ≤ 1` (elementary: `g = μ·1_{(·,q)=1} ∗ 1 ∈ {0, 1}`) | ✅ |
| `MinorArcs/TypeI2Proof.lean` | [B, Lemma 4.2.4]: regrouping by `a = uv`, the main term (4.50) (factor `3/2` added) | ✅ (uses trusted bounds) |
| `MinorArcs/TypeI2Rest.lean` | **[B, Lemma 4.2.4] proved** (both cases): log-weighted range sums, (4.51)/(4.52) in our form (corrected `c₁`, cruder lower-order terms) | ✅ (uses trusted bounds) |
| `Prelim/LargeSieveMV.lean` | the optimal large sieve `N − 1 + δ⁻¹` and the weighted large sieve [MV73, (1.6)] (from `LargeSieveMVProof`); [MV73, Lemma 8] (from `MVLemma7`) | ✅ (uses numerical axioms) |
| `Prelim/MVLemma8.lean`, `Prelim/MVLemma7.lean` | [MV73, Lemma 8] from Lemma 7 by Abel summation (finite check for `R ≤ 10⁴`); [MV73, Lemma 7] `G(r) ≥ log r + 1.07` from `|G(N) − log N − κ| ≤ (2 + 3/e + γ)·9.32·N^{−1/3}` (convolution `μ²/φ = (h ∗ 1)/n`, Euler product `∑ h(d)/d = 1`, Rankin's trick) and a finite check below `3·10⁷` | ✅ (four numerical axioms) |
| `Prelim/Shan.lean` | Shan's spacing lemma `∑_{k≠l} δ_k/|λ_k−λ_l|^σ ≤ 2ζ(σ)/δ_l^{σ−1}` (Yangjit, Lemmas 2.2–2.5) | ✅ |
| `Prelim/HilbertIdentity.lean`, `HilbertReal.lean` | Montgomery–Vaughan Hilbert inequalities on ℝ: eigenvector identity (Preissmann–Lévêque), Preissmann's Cauchy–Schwarz argument with our own substitute for his Lemme 6; weighted constant `4.66 < 3π/2`, uniform `π/δ` | ✅ |
| `Prelim/HilbertCsc.lean` | the `csc` forms on the circle by periodization (Fejér mean of the `csc` series) | ✅ |
| `Prelim/LargeSieveMVProof.lean` | large sieves by duality; `N − 1 + δ⁻¹` by a dilation trick | ✅ |
| `Prelim/SumMuSqPhi.lean` | `∑_{n≤N} 1/n ≤ ∑_{r≤N sq-free} 1/φ(r)`; the coprime reduction; [B, (5.41)] `(φ(q)/q) log R ≤ ∑_{r≤R,(r,q)=1} μ²/φ` | ✅ |
| `MinorArcs/Montgomery.lean` | Ramanujan sums at coprime `n`; Montgomery's inequality (case `ω(p) = 1`) | ✅ |
| `MinorArcs/TypeII.lean` | [B, §5.2]: **Lemma 5.2.1, Lemma 5.2.3 ((5.50)–(5.52)), Prop 5.2.4 ((5.53)–(5.57)) proved** (odd `m`, `v = 2`), modulo the trusted sharp large sieves | ✅ (uses trusted bounds) |
| `MinorArcs/TypeIINumerics.lean` | numerical inequalities for (5.51) | ✅ |
| `Prelim/SqfreeCount.lean` | `∑_{m²∣l} μ(m) = [l sq-free]`; `∑_{(m,P)=1} μ(m)/m² = (6/π²)/∏_{p∣P}(1-p⁻²)` (via `L(μ·χ₀, 2)`); squarefree `l ∈ (a, b]` coprime to `P`: `(b-a)(6/π²)P/σ(P) + O*(∑_{e∣P} f(√(b/e)))`; `f(X) ≤ 1.27X` [B, p. 83] as a numerical axiom | ✅ (one numerical axiom) |
| `MinorArcs/S1Lemma.lean` | [B, Lemma 5.1.1] (`v = 2`), with `∑_{t≤Y odd} t^{-1/2} ≤ √Y` and `∑_{d odd} d^{-3/2} ≤ (1-2^{-3/2})ζ(3/2)` | ✅ (uses the axiom `fsq_le`) |
| `MinorArcs/Decomposition.lean` | [B, (3.11)]: `S_{η₂} = S_{I,1} − S_{I,2} + S_{II} + S_{0,∞} + S_{0,2}` (`v = 2`) from Vaughan's identity | ✅ |
| `MinorArcs/TypeIIReduction.lean` | [B, (5.2)–(5.5)]: `S_{II} = 4∫ IIsum(W) dW/W`, Cauchy–Schwarz `|IIsum| ≤ √S₁(√S₂+√S₃)`; [RS62, Thm. 13] (trusted, in `Prelim/LambdaMu.lean`) | ✅ (uses trusted bounds) |
| `MinorArcs/TypeIITools.lean`, `MinorArcs/TypeIITotal.lean` | [B, §6.2.3]: integrals, our version of (6.37) `typeII_637` (Type II total for `q ≤ V/2e`) | ✅ (uses trusted bounds) |
| `MinorArcs/TypeIITotalGen.lean` | [B, §6.2.3]: general Type II total `typeII_gen`; our (6.40) `typeII_640` (`|δ| ≥ 8`) | ✅ (uses trusted bounds) |
| `MinorArcs/Eta2LogFourier.lean` | [B, (B.17), (B.18)]: `|(log·η₂)^| ≤ 2 − log 4`, `(2πt)²|(log·η₂)^(t)| ≤ 96 log 2` | ✅ |
| `MinorArcs/TypeITotal.lean` | [B, §6.2.1]: `|S_{I,1}|` total `typeI1_le` | ✅ (uses trusted bounds) |
| `MinorArcs/GcdSums.lean` | [B, (6.9)]: `∑ Λ(v)(q,v)/v ≤ log N + log q`, `∑ Λ(v) v (q,v) ≤ ∑ Λ(v) v + N q log q` | ✅ (uses (2.12)) |
| `MinorArcs/TypeI2Total.lean`, `TypeI2Sum.lean`, `TypeI2Large.lean` | [B, §6.2.2] (`qV ≤ Q`): (6.5)–(6.8), totals `typeI2_le_small` ((6.12)+(6.13)) and `typeI2_le_large` ((6.12)+(6.14)) | ✅ (uses trusted bounds) |
| `MinorArcs/TypeIIS1.lean` | [B, §5.1]: the reduction (5.7)–(5.8), (5.19), **(5.34) `S1_bound` proved**; numerical axioms: `T2_le` [B, (5.31)], (5.36), (5.37) | ✅ (three numerical axioms) |
| `MinorArcs/Assembly.lean` | [B, §6.1]: `S_{0,∞} = 0`, `|S_{0,2}| ≤ 3 log x`, `|S| ≤ |S_{I,1}| + |S_{I,2}| + |S_{II}| + 3 log x` | ✅ |
| `MinorArcs/FirstChoice*.lean` | [B, §6.3.1, §6.4]: the parameters (6.49); `S_{II}`, `S_{I,1}`, `S_{I,2}` at them; AM–GM (6.77) (corrected); **Thm 3.1.1 for `q ≤ x^{1/3}/6`** | ✅ (uses trusted bounds) |
| `MinorArcs/TypeIILarge.lean` | [B, (6.20), (6.38), (6.39), (6.41)]: Type II for large `q` (`W`-integral split at `W₀`) | ✅ (uses trusted bounds) |
| `MinorArcs/Second*.lean` | [B, §6.3.2] (`q > x^{1/3}/6`): re-approximation + corrected case split (`SecondChoice`), bridge case via the first case (`SecondBridge`), parameters `U = ⌊1225T⌋`, `V = ⌊T/3⌋`, `Q₀ = T²/349` (`SecondParams`), Type II cases (a1)/(a2)/(b) with piecewise numerics (`SecondTypeII*`, generated by `scripts/gen_*_pieces.py`), Type I (`SecondTypeI1/2`), **Thm 3.1.1 for `q > x^{1/3}/6`** (`SecondFinal`) | ✅ (uses trusted bounds) |
| `MinorArcs/PointwiseBound.lean` | **[B, Theorem 3.1.1]**, both cases (corrected first case: `0.8103` for `0.5`, `3.8x^{5/6}` for `3.36x^{5/6}`; second case with [B]'s `0.276`, `1234`) | ✅ (uses trusted bounds) |
| `MinorArcs/EtaStar.lean` | [B, (11.9)]: `S_{η_*}(α,x) = ∫₀^∞ S_{η₂}(α, wx/κ) φ(w) dw/w` (Mellin substitution + Fubini) and its triangle inequality | ✅ |
| `MinorArcs/EtaStarBound.lean` | towards [B, Prop 11.2.3]: Theorem 3.1.1 at scale `wy` with `δ` rescaled to `wδ` (`w ≤ 1` automatic; `w > 1` with the extra `Q_{wy}` hypothesis) | ✅ (uses trusted bounds) |
| `MinorArcs/GBound.lean` | [B, (11.11)–(11.13)]: `|S_{η₂}(α,x)| ≤ g_x(r) x`, `r = max(1,|δ|/8)q` (our constants `0.8103`, `3.8`) | ✅ (uses trusted bounds) |
| `MinorArcs/GMono.lean` | [B, Lemma 11.2.4] for one scale: `g_x(r)` non-increasing on `[670, x^{1/3}/6]` (by a different argument) | ✅ |
| `MinorArcs/Prop1123.lean` | **[B, Prop 11.2.3] in corrected form** (`δ ↦ wδ`; general cut-offs `w₀`, `w₁` and majorant `G`); trivial bound `|S_{η₂}(α,z)| ≤ 17z` | ✅ (uses trusted bounds) |
| `MinorArcs/Prop1312.lean` | [B, Lemma 13.1.1 (Abel summation, inequality form), Prop 13.1.2] in discrete, measure-space form: ℓ² over nested arcs + ℓ∞ off them | ✅ |
| `MinorArcs/OffArcs.lean` | [B, §13.2] ℓ∞ step: `2α = a/q + δ/y`, `q ≤ r`, `\|δ\|q < δ₀r` ⟹ `α ∈ 𝔐_{δ₀,r}(y)`; off the arcs `r_α ≥ r`; arcs monotone in `r` | ✅ |
| `MinorArcs/Thm1321.lean` | [B, Thm 13.2.1] conditional on an ℓ∞ bound off the scale-`x` arcs (ℓ² from Cor 12.2.5 + Plancherel + Prop 13.1.2); the gap `𝔐(y) \ 𝔐(x)` isolated (`hv_of_split`) ; `thm_13_2_1_repaired` (repair 3: base level at scale `x`, higher levels at scale `y`, (12.42) with `δ₀ = 392`) | ✅ (uses the axiom Prop 12.2.4) |
| `MinorArcs/Prop1123b.lean` | Prop 11.2.3′: ℓ∞ bound for `S_{η_*}` off `𝔐_{8,n}(x/κ)`, fresh Dirichlet approximation at each scale `wy` | ✅ (uses trusted bounds) |
| `MinorArcs/LinftyLevels.lean`, `PhiIntegrals.lean` | ℓ∞ bound per level, closed form `ĝ(y,n) = 1.398 max(g_y(n), h(y)) + 17(670/n)³/3`; `∫_{w₀}^∞ max(1,1/w)φ ≤ 1.398` | ✅ (uses trusted bounds) |
| `MinorArcs/BaseGap.lean`, `BaseGap2.lean`, `EtaU.lean` | base gap `𝔐_{8,r₀}(x/κ) \ 𝔐_{8,r₀}(x)`: character expansion, `|η̂(t)| ≤ c₀√(π/2)/(2πt)²` (Fubini), non-coprime terms; `|S_{η_*}| ≤ 0.012 x/κ` there | ✅ (uses cited Cor 7.1.3, axiom (B.6)) |
| `MinorArcs/PartIICited.lean` | the Part II results used by the minor arcs: [B, Cor 7.1.3], [B, Prop 7.1.5], [B, (14.7)], all proved in `MajorArcs/` | ✅ (uses cited 9.3.2, 9.4.2, 9.5.1) |
| `Prelim/PlancherelReal.lean` | Plancherel for `L¹ ∩ L²` on `ℝ` (Mathlib's `L²` transform identified with the integral one via tempered distributions) | ✅ |
| `MajorArcs/ArcsEq.lean`, `EtaCirc.lean`, `HHFourier.lean`, `EtaPlusL2.lean`, `ArcChars.lean`, `SumMuPhi.lean`, `L2Major.lean` | **[B, (14.7)] proved** (`l2_major_bounds`: `8.688x ≤ ∫_𝔐 \|S_{η₊}\|² ≤ 8.709x`): arcs as a disjoint union; `η◦` and its Fourier tail `≤ 98/(2πT)⁴`; `‖η₊ − η◦‖₂² ≤ 19.5/(2·200²)` (Fourier analysis of `h_H` in log coordinates: `h_H` is `h` with its spectrum cut at `H/2π`); `‖η₊‖₂²` from (9.94); per modulus: coprime split, Bombieri's identity, Thm 7.1.4 for the primitive characters; `Σ μ²/φ` (numerical axiom) | ✅ (cited 9.4.2, axioms Platt, (9.94), `Σ μ²/φ`) |
| `MajorArcs/CMain.lean`, `FourierMain.lean`, `Singular.lean`, `ArcCharsStar.lean`, `MajorTotal.lean` | **[B, (14.27)] proved with `1.049`** (`major_total`): `C_{η◦,η_*}(N/x) ≥ 0.800689/κ` (Ch. 11: polarization for `η◦∗η◦`, the moments of `η_*`); the Fourier identity (10.22) `∫ η̂◦²η̂_* e(ξρ) = C_{η◦,η_*}(ρ)`; the singular series `Σ_{q∈Q} c_q(N) ≥ 1.314` (Ramanujan sums, Euler product with Rankin's trick, `mertens_product_small` at `150001`) and `Σ μ²/φ² ≤ 2.85`; `S_{η_*}` on the arcs of one modulus via characters and Cor 7.1.3; per modulus, the principal character (`τ(1) = μ(q)`) with `ℓ²` residuals and AM–GM; `η₊ → η◦` and the Fourier tail cost `≤ 2.03·10⁻⁵ x²` per modulus | ✅ (cited 9.3.2, 9.4.2, 9.5.1; axioms Platt, (9.94), `Σ μ²/φ`, Mertens product) |
| `MinorArcs/MinorTotal.lean` | (14.49) via repair 3: `S₁/S₂` split, `I₀ ≥ 8.6294x` (from (14.7) with `O*(0.0756)`; [B]: `0.0754`, an arithmetic slip, see NOTES), `T ≤ σ(x)x`, assembly `minor_total` | ✅ (uses the above) |
| `MinorArcs/NumericsCore.lean`, `NumericsCells.lean` (generated by `scripts/gen_cells.py`), `NumericsAsymp.lean`, `NumericsFinal.lean` | the numerical inequality `Mexpr x r₂ ≤ 1.037` for all `x ≥ 4.9·10²⁶` | ✅ |
| `MinorArcs/LargeSievePrimes.lean` | [B, Ch. 12]: `G_q`; **Prop 12.2.4 (numerical axiom)** | ✅ (one numerical axiom) |
| `MinorArcs/Bombieri.lean`, `LargeSieveWeights.lean`, `Periodize.lean`, `LargeSieveArcs.lean`, `Plancherel.lean`, `LargeSieveProof.lean` | **[B, Prop 12.1.2] proved** (with `δ₀ ≥ 2`): Bombieri's identity (Parseval over characters, Gauss sums, grouping by conductor), the weights `(c/φ(c))κ_c G_{c̃}`, arcs (covering and Farey disjointness), Plancherel for `ℓ¹`; **Cor 12.2.5 (12.42)** from it and Prop 12.2.4 | ✅ (Cor 12.2.5 uses the axiom 12.2.4) |
| `Prelim/GaussInduced.lean` | Gauss sums: induced characters `τ(χ↑) = μ(r)χ(r)τ(χ)`; `|τ(χ)|² = N` for primitive `χ` | ✅ |
| `Helfgott/Inputs.lean` | proved inputs 1–4; numerical axioms 5 and 6 (see below) | ✅ (uses trusted bounds) |
| `Helfgott/Main.lean` | assembly: inputs ⇒ odd `N ≥ 10²⁷` is a sum of three primes; ladder ⇒ small cases; ⇒ `ternary_goldbach` | ✅ (uses all 4 `sorry`s and 33 axioms) |

## The inputs

The blueprint follows Helfgott's book *The ternary Goldbach problem*, arXiv:1501.05438v2 [B],
which supersedes the papers (arXiv:1205.5252, 1305.2897, 1312.7748 [H]). Its definitions and
constants match [H], with one exception: the corrected minor-arc bound is `1.00948 x²/κ` [B,
(14.49)] rather than `0.97392 x²/κ` [H, (7.48)], so [B]'s final margin is `0.04877 x²/κ` (ours: `1.049 − 1.0376 = 0.0114 x²/κ`, see Caveats).

1. ~~`circle_identity_input`~~ **proved**: [H, (3.3)/(7.49)] for the infinite smoothed sums,
   from `circle_identity_tsum` and the decay bounds in `Helfgott/Decay.lean`.
2. ~~`major_arcs_input`~~ **proved** (`MajorArcs/MajorTotal.lean: major_total`): [B, (14.27)] as
   `Re ∫_{𝔐_{8,150000}} S_{η₊}² S_{η_*} e(−Nα) ≥ 1.049 x²/κ` ([B]: `1.058259`). It depends on the
   cited Props 9.3.2, 9.4.2, 9.5.1 (explicit formulas), Platt's GRH verification for moduli up to
   `300000` and the other numerical axioms of Part II. Main term `1.314 · 0.800689 = 1.0521`;
   errors `0.0028` (almost all from replacing `η₊` by `η◦` and completing the `β`-integral).
3. ~~`minor_arcs_input`~~ **proved** (`MinorArcs/MinorTotal.lean: minor_total` +
   `NumericsFinal.lean: numerics_M`): [B, (14.49)] as `∫_𝔪 |S_{η_*}||S_{η₊}|² ≤ 1.0376 x²/κ`, by a
   *repaired* Thm 13.2.1 ("repair 3", see Caveats). It depends on the trusted inputs of Theorem
   3.1.1, the numerical axiom Prop 12.2.4, and the Part II results [B, Cor 7.1.3], [B, Prop 7.1.5],
   [B, (14.7)] (`MinorArcs/PartIICited.lean`, all proved from the cited Props 9.3.2, 9.4.2, 9.5.1), and
   [B, (14.28)] (proved in a weaker form).
4. ~~`nonprime_input`~~ **proved**, a weaker form of [B, (14.51)] with constant `6.7·10⁶` in place of
   `7.3306`. Helfgott's sharp inputs (`|η₊| ≤ 1.079955`, `|η_*| ≤ 1.414`, and Rosser–Schoenfeld)
   are replaced by easy ones: `|η₊| ≤ 400`, `|η_*| ≤ 6.2`, `ψ(N) ≤ 1.387 N`,
   `ψ(N) − θ(N) ≤ 1.6√N`. The final inequality still has room.
5. `binary_goldbach_input` (numerical axiom): even Goldbach up to `4·10¹⁸` (Oliveira e Silva–Herzog–Pardi).
6. `prime_ladder_input` (numerical axiom): the Helfgott–Platt prime ladder up to `8.875694·10³⁰`.

## Caveats

* [B]'s Theorem 3.1.1 constant `0.5` comes from an arithmetic slip in (6.77). The correct value
  is `0.8103`, and `3.36 x^{5/6}` becomes `3.8 x^{5/6}` in our proof. Re-running [B, §14.3] with
  these constants (`scripts/minor_arc_total_numerics.py`) gives the minor-arc total
  `1.0376 x²/κ` instead of `1.00948 x²/κ`. With our major-arc constant `1.049` the final margin is
  `0.0114 x²/κ` instead of `0.04877 x²/κ`, which still suffices (`Helfgott/Numerics.lean`).
* **[B]'s proof of Thm 13.2.1 (the minor-arc total) mixes two scales of major arcs.** Its ℓ∞ input is
  derived only off the arcs at scale `x/κ`, 49 times wider than the scale-`x` arcs of its ℓ² input
  and of (14.27); the obvious repairs fail (`scripts/minor_arc_scale_check.py`). **Fixed** ("repair
  3", `NOTES.md`): run Prop 13.1.2 with the scale-`x/κ` arcs above the base level, use a fresh
  Dirichlet approximation at each scale in (11.9), extend the levels to `≈ x^{0.3}` (instead of [B]'s
  `(3/8)(x/κ)^{4/15}`), and bound the base gap with [B, Cor 7.1.3]. This gives `≤ 0.960 x²/κ`
  numerically (we state `1.0376`), so the final margin is unaffected.
* [B]'s proof of Prop 11.2.3 applies Theorem 3.1.1 at scale `wx` without rescaling `δ` to `wδ`.
  The statement survives with about 11% to spare (`scripts/prop_11_2_3_check.py`, see `NOTES.md`).

* The definitions in `Helfgott/Defs.lean` were transcribed from extracted PDF text and
  cross-checked against [B] (η₁ = 2·1_{[1/2,1]}, η₂ as in [B, (11.10)], η₊ as in [B, (7.4)–(7.6)]
  with `H = 200`, major arcs [B, (10.5)]). A numerical check gives `max |η₊| ≈ 1.0000` and
  `max |η_*| ≈ 1.2267`, consistent with [B, (14.3), (14.21)].
* [B, (4.40)] (Lemma 4.2.3) states the main term of the all-`n` version; its own proof gives
  `x/2q`, `η̂(−δ/2)` and `(m, 2q) = 1`. `bound_4_40` is the corrected statement. The last term
  of (4.41) is proved with `log(2ex/c₂)` in place of `log(2√e x/c₂)`.
* [B]'s proof of Lemma 4.1.3 has a small gap: its intermediate bound can exceed the stated
  `(2Bq/π) max(2, log(Ce³q/(Bπ)))` for small `C`. The lemma is nonetheless true, and
  `MinorArcs/TrigSums.lean` proves it with a sharper argument (see the docstring there).
* Helfgott works on `ℝ/ℤ`; here it's `(0, 1]` with the major arcs lifted periodically to `ℝ`.
* Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0` (`lake exe cache get` fetches the Mathlib build).
