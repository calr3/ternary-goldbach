# Ternary Goldbach in Lean 4 (a blueprint of Helfgott's proof)

**Status: not a complete formal proof.** `TernaryGoldbach.ternary_goldbach` states that every
odd integer greater than 5 is a sum of three primes. It is derived in Lean from **20 explicitly
stated results from the literature**, which are still `sorry`, and **7 numerical axioms**
(computations from [B], listed below). Everything that connects them to the theorem is proved.

```
$ lake build
$ echo 'import TernaryGoldbach
#print axioms TernaryGoldbach.ternary_goldbach' > /tmp/ax.lean && lake env lean /tmp/ax.lean
'TernaryGoldbach.ternary_goldbach' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 TernaryGoldbach.MinorArcs.H2_le,
 TernaryGoldbach.MinorArcs.T2_le,
 TernaryGoldbach.MinorArcs.eta2_fourier_bound',
 TernaryGoldbach.MinorArcs.eta2log_fourier_bound,
 TernaryGoldbach.MinorArcs.integral_H2_le,
 TernaryGoldbach.MinorArcs.prop_12_2_4,
 TernaryGoldbach.Prelim.fsq_le]
```

See [`BLUEPRINT.md`](BLUEPRINT.md) for the chapter-by-chapter map from the book to Lean.

The 20 `sorry`s that `ternary_goldbach` depends on are:

* **three unproved inputs** in [`Helfgott/Inputs.lean`](TernaryGoldbach/Helfgott/Inputs.lean):
  `major_arcs_input`, `binary_goldbach_input`, `prime_ladder_input` (see "The inputs" below);
* **four cited Part II results** in `MinorArcs/PartIICited.lean`: [B, Cor 7.1.3], [B, Prop 7.1.5],
  [B, (14.7)], [B, (14.28)];
* **thirteen literature bounds** in `Prelim/`:
  * ten bounds on sums of `Λ`, `μ` and `1/φ` ([B, (2.12)–(2.23)], [RS62]) in `Prelim/LambdaMu.lean`;
  * the optimal and weighted large sieves and [MV73, Lemma 8] in `Prelim/LargeSieveMV.lean`.

`lake build` also warns about four further `sorry`s in `Prelim/LambdaMu.lean` that nothing uses.

## Numerical axioms

These are computations that Helfgott did by computer for [B]; the book describes the method
but doesn't include the code or the output. They are stated as Lean `axiom`s, so `#print axioms`
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
| `Helfgott/Numerics.lean` | the final inequality of [B, §14.4], `C·N^{3/2} log N < (1.058259 − 1.0376) x²/κ = 0.020659 x²/κ` for `N ≥ 10²⁷`, both with Helfgott's `C = 7.3306` and with the cruder `C = 6.7·10⁶` we actually use | ✅ |
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
| `Prelim/LambdaMu.lean` | trusted literature bounds on sums of `Λ` and `μ` [B, (2.12)–(2.24), (5.5)], Lemma C.2.2 | 🟡 trusted |
| `Prelim/MoebiusCoprime.lean` | **[B, (2.20)] proved**: `\|∑_{n ≤ x, (n,q)=1} μ(n)/n\| ≤ 1` (elementary: `g = μ·1_{(·,q)=1} ∗ 1 ∈ {0, 1}`) | ✅ |
| `MinorArcs/TypeI2Proof.lean` | [B, Lemma 4.2.4]: regrouping by `a = uv`, the main term (4.50) (factor `3/2` added) | ✅ (uses trusted bounds) |
| `MinorArcs/TypeI2Rest.lean` | **[B, Lemma 4.2.4] proved** (both cases): log-weighted range sums, (4.51)/(4.52) in our form (corrected `c₁`, cruder lower-order terms) | ✅ (uses trusted bounds) |
| `Prelim/LargeSieveMV.lean` | trusted literature: the optimal large sieve `N − 1 + δ⁻¹` (Selberg, Montgomery–Vaughan), the weighted large sieve [MV73, (1.6)], [MV73, Lemma 8] (+ numerical check) | 🟡 trusted |
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
| `MinorArcs/PartIICited.lean` | cited Part II results: [B, Cor 7.1.3], [B, Prop 7.1.5], [B, (14.7)], [B, (14.28)] | ❌ four cited results |
| `MinorArcs/MinorTotal.lean` | (14.49) via repair 3: `S₁/S₂` split, `I₀ ≥ 8.6296x`, `T ≤ σ(x)x`, assembly `minor_total` | ✅ (uses the above) |
| `MinorArcs/NumericsCore.lean`, `NumericsCells.lean` (generated by `scripts/gen_cells.py`), `NumericsAsymp.lean`, `NumericsFinal.lean` | the numerical inequality `Mexpr x r₂ ≤ 1.037` for all `x ≥ 4.9·10²⁶` | ✅ |
| `MinorArcs/LargeSievePrimes.lean` | [B, Ch. 12]: `G_q`; **Prop 12.2.4 (numerical axiom)** | ✅ (one numerical axiom) |
| `MinorArcs/Bombieri.lean`, `LargeSieveWeights.lean`, `Periodize.lean`, `LargeSieveArcs.lean`, `Plancherel.lean`, `LargeSieveProof.lean` | **[B, Prop 12.1.2] proved** (with `δ₀ ≥ 2`): Bombieri's identity (Parseval over characters, Gauss sums, grouping by conductor), the weights `(c/φ(c))κ_c G_{c̃}`, arcs (covering and Farey disjointness), Plancherel for `ℓ¹`; **Cor 12.2.5 (12.42)** from it and Prop 12.2.4 | ✅ (Cor 12.2.5 uses the axiom 12.2.4) |
| `Prelim/GaussInduced.lean` | Gauss sums: induced characters `τ(χ↑) = μ(r)χ(r)τ(χ)`; `|τ(χ)|² = N` for primitive `χ` | ✅ |
| `Helfgott/Inputs.lean` | proved inputs 1, 3 and 4, and **the three unproved inputs** (see below) | ❌ three inputs |
| `Helfgott/Main.lean` | assembly: inputs ⇒ odd `N ≥ 10²⁷` is a sum of three primes; ladder ⇒ small cases; ⇒ `ternary_goldbach` | ✅ (uses all 20 `sorry`s and 7 axioms) |

## The inputs

The blueprint follows Helfgott's book *The ternary Goldbach problem*, arXiv:1501.05438v2 [B],
which supersedes the papers (arXiv:1205.5252, 1305.2897, 1312.7748 [H]). Its definitions and
constants match [H], with one exception: the corrected minor-arc bound is `1.00948 x²/κ` [B,
(14.49)] rather than `0.97392 x²/κ` [H, (7.48)], so [B]'s final margin is `0.04877 x²/κ` (ours: `0.020659 x²/κ`, see Caveats).

1. ~~`circle_identity_input`~~ **proved**: [H, (3.3)/(7.49)] for the infinite smoothed sums,
   from `circle_identity_tsum` and the decay bounds in `Helfgott/Decay.lean`.
2. `major_arcs_input`: [B, (14.27)], `∫_{𝔐_{8,150000}} S_{η₊}² S_{η_*} e(−Nα) ≥ 1.058259 x²/κ`.
   This uses explicit formulas for Dirichlet L-functions and Platt's rigorous GRH verification
   for moduli up to 300000.
3. ~~`minor_arcs_input`~~ **proved** (`MinorArcs/MinorTotal.lean: minor_total` +
   `NumericsFinal.lean: numerics_M`): [B, (14.49)] as `∫_𝔪 |S_{η_*}||S_{η₊}|² ≤ 1.0376 x²/κ`, by a
   *repaired* Thm 13.2.1 ("repair 3", see Caveats). It depends on the trusted inputs of Theorem
   3.1.1, the numerical axiom Prop 12.2.4, and four cited Part II results
   (`MinorArcs/PartIICited.lean`: [B, Cor 7.1.3], [B, Prop 7.1.5], [B, (14.7)], [B, (14.28)]).
4. ~~`nonprime_input`~~ **proved**, a weaker form of [B, (14.51)] with constant `6.7·10⁶` in place of
   `7.3306`. Helfgott's sharp inputs (`|η₊| ≤ 1.079955`, `|η_*| ≤ 1.414`, and Rosser–Schoenfeld)
   are replaced by easy ones: `|η₊| ≤ 400`, `|η_*| ≤ 6.2`, `ψ(N) ≤ 1.387 N`,
   `ψ(N) − θ(N) ≤ 1.6√N`. The final inequality still has room.
5. `binary_goldbach_input`: even Goldbach up to `4·10¹⁸` (Oliveira e Silva–Herzog–Pardi).
6. `prime_ladder_input`: the Helfgott–Platt prime ladder up to `8.875694·10³⁰`.

## Caveats

* [B]'s Theorem 3.1.1 constant `0.5` comes from an arithmetic slip in (6.77). The correct value
  is `0.8103`, and `3.36 x^{5/6}` becomes `3.8 x^{5/6}` in our proof. Re-running [B, §14.3] with
  these constants (`scripts/minor_arc_total_numerics.py`) gives the minor-arc total
  `1.0376 x²/κ` instead of `1.00948 x²/κ`. The final margin is then `0.020659 x²/κ` instead of
  `0.04877 x²/κ`, which still suffices.
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
