# Working notes

Notes for continuing the formalization. For the overall map, see `BLUEPRINT.md`. For the
`sorry` policy, see `README.md`.

## Status (2026-10-31)

* `ternary_goldbach` depends only on the 4 `sorry`s in `Helfgott/Inputs.lean`: the major arcs
  (14.27), the minor arcs (14.49), binary Goldbach up to 4·10¹⁸, and the prime ladder.
* **(14.49) is now stated with `1.0376` instead of [B]'s `1.00948`** (final margin `0.020659`
  instead of `0.048779`; `final_inequality(_crude)` re-proved). That is what [B, §14.3] gives
  when re-run with the Theorem 3.1.1 we actually proved (`0.8103`, `3.8 x^{5/6}` instead of
  `0.5`, `3.36`): `scripts/minor_arc_total_numerics.py` reproduces [B]'s `M ≤ 0.80508` as
  `0.80279` (slightly less rounding) and gives `M ≤ 0.82744`, `Z ≤ 1.037499 x²/κ` with the
  corrected constants. The changes come from `g(r₀)` in (14.37) (`0.38491 → 0.39761`), the `+0.5`
  term of `f₁` and `f₂` in (14.47) (`0.11438 → 0.11802`), and (14.43) (`0.30351 → 0.31181`).
  Lemma 11.2.1 still holds (`g/h ≤ 0.61`).
* **Decision (2026-10-30): option (a).** Keep `minor_arcs_input` as a cited input with the
  caveat below, and keep formalizing the parts of Part I, Ch. 11, Ch. 12 and Prop 13.1.2 that do
  not depend on the scale question.
* ✅ Prop 13.1.2 (`Prop1312.lean`): any measure space; nested measurable `M n`; conclusion
  `g(r₀)(H(r₀) − I₀) + Σ_{r₀<n≤r₁} g(n)(H(n) − H(n−1))` (discrete; `≤ ∫ g H'` for monotone `g`, `H`).
* ✅ **Ch. 12: Prop 12.1.2 proved** (`LargeSieveProof.lean`, no `sorry`), so Cor 12.2.5 (12.42)
  depends only on the trusted computation Prop 12.2.4. Route: Bombieri's identity in the form
  `φ(q) Σ_b^* |S(b/q+β)|² = Σ_{Ψ mod L, cond Ψ ∣ q} w(q, cond Ψ) |S_{Ψ⁻¹}(β)|²`. That uses
  Parseval over characters, `gaussSum_mulShift_eq`, `τ(χ↑) = μ(r)χ(r)τ(χ)` (ℕ-indexed Möbius proof),
  `|τ(χ)|² = N` for primitive `χ`, and the lift to one modulus `L = ∏_{q ≤ 2Q} q`, which avoids
  dependent types. Then `weight_sum` gives `Σ_{q̃ ≤ X} [c∣q] w/φ(q) = (c/φ(c)) κ_c G_{c̃}(X/c̃)`.
  The arcs part is periodization, covering, and Farey disjointness at level `Q`. Pointwise in `β`,
  the hypothesis on `G` is used with `s = 2Q₀/m_{Q₀}(β)`.
  **Change from [B]: `δ₀ ≥ 2` instead of `δ₀ ≥ 1`**. The proof needs primes `n > √x` to be coprime
  to every modulus `q ≤ 2Q = √(2x/δ₀)`, which needs `2Q ≤ √x`. [B] uses `δ₀ = 8`.
* ✅ **Thm 13.2.1, conditional** (`Thm1321.lean`, depends only on Prop 12.2.4):
  `thm_13_2_1_conditional` instantiates Prop 13.1.2 with `M n = 𝔐_{8,n}` at scale `x`, the ℓ²
  bound from Cor 12.2.5 (`Q₀ = n + 1`, `δ₀ = 8`) and Plancherel at the top level `r₁`. The ℓ∞ input
  is a **hypothesis** `hv`: `|S_{η_*}(α,x)| ≤ g(n)` off `𝔐_{8,n}(x)`. `OffArcs.lean` proves the exact
  arc criterion behind [B]'s ℓ∞ step: `2α = a/q + δ/y` with `q ≤ r`, `|δ|q < δ₀r` ⟹
  `α ∈ 𝔐_{δ₀,r}(y)`, for every parity case (`mem_majorArcs_of_approx`). So off `𝔐_{δ₀,r}(y)`,
  `r_α ≥ r` (`le_rAlpha_of_not_mem`), giving `norm_S_le_off_arcs`. `hv_of_split` reduces `hv` to that
  plus a bound on the **gap `𝔐_{8,n}(y) \ 𝔐_{8,n}(x)`**, the one missing ingredient. (Also still
  needed for (14.49): splitting `S_{η₊}` into primes `> √x` plus the rest [B, §13.2], and the
  numerics of §14.3 for an explicit `g`.)
* ✅✅ **(14.49) fully assembled, including the numerics** (2026-10-31). `numerics_M`
  (`MinorArcs/NumericsFinal.lean`) is proved: 9 generated cells for `x ∈ [4.9·10²⁶, 4.9·10¹⁰¹]`
  (`scripts/gen_cells.py` → `NumericsCells.lean`, worst `Mexpr ≤ 0.960`), and `asymp_goal`
  (`NumericsAsymp.lean`, `r₂ = ⌊y^{1/4}⌋`, `≈ 0.692`) beyond. `ternary_goldbach` now depends on
  28 explicitly labelled items (`scripts/sorry_deps.lean`): the 3 remaining `Helfgott/Inputs`
  items (major arcs (14.27), binary Goldbach ≤ 4·10¹⁸, prime ladder), the cited Part II results
  `cor_7_1_3`, `prop_7_1_5`, `l2_major_14_7`, `E_le_14_28`, and the literature bounds in
  `Prelim/` ([RS62] etc., Lemma C.2.2): 21 `sorry`s. Plus 7 **numerical axioms** (Lean `axiom`s,
  2026-10-31, at the user's request; listed in README "Numerical axioms"): `prop_12_2_4`, the
  (B.6)/(B.2.3) Fourier bounds, `integral_H2_le`/`H2_le`/`T2_le`, `fsq_le`.
* ✅ **`minor_arcs_input` is now a theorem** (`Helfgott/Inputs.lean` → `MinorArcs/MinorTotal.lean:
  minor_total`). Its dependency closure: the trusted inputs of Thm 3.1.1, Prop 12.2.4 (trusted
  computation), the **cited Part II results** `cor_7_1_3`, `prop_7_1_5`, `l2_major_14_7` (14.7),
  `E_le_14_28` (`MinorArcs/PartIICited.lean`), and **`numerics_M`** (the remaining numerical
  lemma: ∃ level `r₂` with the size conditions and `Mexpr x r₂ ≤ 1.037`, all `x ≥ 4.9·10²⁶`;
  checked by `scripts/minor_arc_cells_check.py`, to be formalized).
* ✅ **The Ch. 13 scale erratum is fixable** ("repair 3" in the erratum section below:
  everything at scale `y`, a fresh Dirichlet approximation per scale `wy`, levels up to
  `x^{0.3}`, and Cor 7.1.3 on the base gap). `Z ≤ 0.866 x²/κ < 1.058259`. Formalizing it is the
  current work.
* (Superseded.) **Blocker for (14.49): [B, Thm 13.2.1] mixes two scales of major arcs** (see the section
  "Ch. 13: scale erratum" below). As written, [B]'s minor-arc bound covers only the complement
  of the arcs at scale `y = x/κ`, while (14.27) and our `minor_arcs_input` use the arcs at scale
  `x`. The obvious repairs fail numerically. Decide how to proceed before formalizing Ch. 13.
* **Next: Ch. 11 (Prop 11.2.3), then Ch. 12, Ch. 13 → (14.49).** See the Prop 11.2.3 erratum
  below before formalizing it. Done so far: (11.9) `S_etaStar_eq`, `norm_S_etaStar_le`
  (`EtaStar.lean`, no `sorry`); Theorem 3.1.1 at scale `wy` with `δ ↦ wδ`
  (`theorem_3_1_1_scaled(_le_one)`, `EtaStarBound.lean`); (11.11) `norm_S_eta2_le_gx`
  (`GBound.lean`, `q/φ(q) ≤ Ϝ(r)` via the trusted Lemma C.2.2); **`gx_antitoneOn`**: `g_x(r)` is
  non-increasing on `[670, x^{1/3}/6]` (`GMono.lean`, no `sorry`; proved via
  `Q(log r) r^{-p}` with `Q' ≤ pQ`, not [B]'s (11.23)–(11.25)). **`prop_11_2_3`** (`Prop1123.lean`):
  Prop 11.2.3 in corrected form, `|S_{η_*}| ≤ y(∫_{w₀}^{w₁} Gφ + 17(∫_0^{w₀}φ + ∫_{w₁}^∞φ))` for
  any integrable majorant `G(w) ≥ g_{wy}(min(1,w) r)` (trivial bound `17z` from Mathlib's
  Chebyshev `ψ ≤ (log 4 + 4)x`; same 20 trusted items as Thm 3.1.1, checked with
  `scripts/sorry_deps.lean`). Still to do: closed-form/numerical majorants `G` (the analogue of
  [B]'s `g_{y,φ}`, via Lemma 11.2.2 convexity and `C_{φ,2,K}`). Old list, for reference: the region
  `w < 1/K` (trivial bound `|S_{η₂}(α,z)| ≤ S_{η₂}(0,z) ≤ 1.04488 z`, Cor. C.1.3, trusted), the
  large-`w` tail, and integrating against `φ` (convexity, Lemma 11.2.2; `C_{φ,2,K}`).
* Part I (minor arcs):
  * [B, §2.3] proved (`MinorArcs/FourierSums.lean`), [B, §4.1] proved (`MinorArcs/TrigSums.lean`).
  * [B, §4.2]: **Lemma 4.2.2** (`TypeIProof.lean: lemma_4_2_2`) and **Lemma 4.2.3**
    (`TypeILogProof.lean: lemma_4_2_3`, the case §6.2.1 uses) are proved. Their only non-standard
    dependencies are the trusted `eta2_fourier_bound'` ([B, (B.6)]) and `eta2log_fourier_bound`
    ([B, Lemma B.2.3]); checked by temporarily turning them into `axiom`s and running
    `#print axioms`.
  * **Lemma 4.2.4** (`TypeI2Rest.lean: lemma_4_2_4`) is proved, both cases. Its non-standard
    dependencies are `eta2_fourier_bound'`, (2.12), (2.15), (2.20) (checked with a script that
    walks the dependency closure for `sorryAx`; (2.16) turned out not to be needed).
  * Thm 3.1.1 is proved (see Ch. 6 below).
* **Lemma 4.2.4: how it was done / decisions** (all documented in the `bound_4_5x` docstrings):
  * `typeI2 = ∑_{a odd} c(a) T_{a,∘}`, `|c(a)| ≤ log a`; main term (4.50) with factor `3/2` (erratum
    in (4.55)).
  * Rest: weights `log m`; on each block of length `q` use `log` of the block's upper end
    (`sum_log_mul_le_blocks`), with the per-block bounds `block_R2`/`block_R3` extracted from
    Lemma 4.2.2. (R2): `∑(j+3/2) log((j+3/2)q)` via `t log t` increasing and `F(t)=(t²/2)(log t-1/2)`
    (upper limit `D'+2q`), giving `(2√c₀/π) D'(log D' - 1/2) + O(√x log D)`. (R3): `log(R+q)` for the
    first block, then `log(min(R+(j+1)q, D)) ≤ log y_j + q/y_j` and `∑ log y_j ≤ (G(D)-G(R))/q + …`,
    `G(t) = t(log t - 1)`. Case (a): weight `log M` on `(0, M]` (crude, costs `Bc·M ≤ Bc(1+ε)Y/2`),
    second approximation above `M` (`sum_R3W'`, general `q' ≤ 2(1+ε)M`).
  * **Errata/changes**: `c₁ = 1 + |η'|₁/(x/D)` (odd `n`; [B] prints the all-`n` value `2x/D`);
    (4.59)–(4.60) as printed is garbled ("`≤ x`" for "`≤ log x`") and its constant could not be
    reproduced — our (R2) gives `(2√c₀/π)√(2c₂x)(2 + 12 log 5D) + 5c₀/6π²` instead of
    `(25c₀/4π²)(2c₂)^{3/2}√x log x` (similar size); `log⁺(q/2)` for `log(q/2)` (negative at `q=1`).
    Leading terms are [B]'s: `(2√(c₀c₁)/π) D log(D/√e)` in (b), `D log(D/e)` in (a); the `q`- and
    `x/Q₀`-terms have the same shape but cruder constants (`bound_4_52` keeps `x/Q₀`, which is
    `≤ √x/2` when `Q₀ ≥ 2√x`). Hypotheses: `x ≥ 10`, `UV ≥ 2` (instead of `x ≥ e²c₂/2`);
    [B]'s `UV + (19/18)Q₀ ≤ x/5.6` is not needed.
  * **To check in Ch. 6** (§6.2.2): plug our `bound_4_51/52` in place of [B]'s; the lower-order
    changes should be harmless, but the corrected `c₁` and the (R2) constant must be re-run.
* **Ch. 5, §5.2 (S₂) done** (`MinorArcs/TypeII.lean`, `v = 2`, i.e. `m` odd):
  * Trusted (`Prelim/LargeSieveMV.lean`): optimal large sieve `(N - 1 + δ⁻¹)` (needs `δ ≤ 1` for a
    single point), MV weighted large sieve `∑ (N + (3/2)δ_r⁻¹)⁻¹|S|² ≤ ‖a‖²`, [MV73, Lemma 8]
    `∑_{r≤R}(1+r/R)⁻¹μ²/φ ≥ log R + 0.25068` (`R ≥ 2`, with [B]'s numerical check below 100).
  * Proved: Montgomery's inequality (ω(p)=1: Ramanujan sum `c_r(n) = μ(r)` + Cauchy–Schwarz),
    (5.41) via `rad`/σ-multiplicativity, Lemma 5.2.1 (both parts), Lemma 5.2.3 (5.50)–(5.52),
    Prop 5.2.4 (5.53)–(5.57).
  * **Errata/changes**: Lemma 5.2.1 needs `R ≤ W'` (primes `p > W'` coprime to `r ≤ R`) — we cap `R`
    (statement (ii) takes any `1 ≤ R ≤ W'` with `qR²(ν+υ) ≤ 1`, gain `(φ(q)/q) log R`);
    (5.52) must be over odd `m` (display omits it); (5.51)/(5.54): `#(W', W] ≤ W/2 + 1`, not
    `W/2`, so we assume `W ≥ 50000` (the slack `1 - 3σ/(1-σ/3.5) = 0.0054` absorbs the `+1`);
    `σ₀ = 0.30286` (rational) instead of `σ = e^{-0.50136}/2`. (5.56) is stated as (i) without and
    (ii) with the log gain (`R` capped at `W'`), avoiding `min(1, ·/log)` with `log ≤ 0`.
* **Ch. 5, §5.1 (S₁) done** modulo numerics (`Prelim/SqfreeCount.lean`, `MinorArcs/S1Lemma.lean`,
  `MinorArcs/TypeIIS1.lean`):
  * Proved: the reduction (5.7)–(5.8) (`S1_eq`, bijection `(m,d₁,d₂) ↔ (s,r₁,r₂,l)`); Lemma 5.1.1
    for `v = 2` (`lemma_5_1_1`; main-term constant `(6/π²)P/σ(P)` from Mathlib's
    `L(χ₀μ, 2) = 1/L(χ₀, 2)`); (5.19) (`integral_g2`); **(5.34) `S1_bound`**.
  * Numerical axioms: `fsq_le` (`f(X) ≤ 1.27X`, [B p. 83]; provable: reduce to integers `n ≤ 37` using
    `∑ μ²(m)/m² = 15/π²` — the extremal case `n = 2` needs `15/π² ≤ 1.52`, i.e. `π² ≥ 9.8684`);
    `T2_le` (`T₂(S) ≤ 0.37273` for `S ≥ 16`: Lemma 5.1.2 + the computations of [B pp. 90–92]);
    (5.36) `integral_H2_le`, (5.37) `H2_le`.
  * Changes: `S1_bound` assumes `U ≥ 1` (so `x/(WUs) ≤ x/W`; harmless in Ch. 6). `H₂` is defined
    with the exact triple sum `T₂` in place of the book's computable bound `G₂ ≥ T₂`. The error
    constant `1.27(1+1/√2)(1-2^{-3/2})³ ζ(3/2)³ ≈ 0.586 ζ(3/2)³` is rounded up to `1.27 ζ(3/2)³`
    as in [B]. `T₂(S) = 1 - 1/S` on `[1, 2)` (matches [B]'s `G_v`).
* **Ch. 6 in progress.**
  * Step 1 ✅ `MinorArcs/Decomposition.lean`: (3.11) `S_{η₂} = S_{I,1} - S_{I,2} + S_{II} + S_{0,∞} + S_{0,2}`
    (`decomposition`, `U V : ℕ`), from Vaughan via `sum_odd_conv`; `S_{I,1} = typeILog`,
    `S_{I,2} = typeI2`.
  * Step 2 ✅ `MinorArcs/TypeIIReduction.lean`: (5.2)–(5.5): `η₂(mn/x) = 4∫ 1[…] dW/W`,
    `S_{II} = 4∫_V^{x/U} IIsum(W) dW/W`, `|IIsum| ≤ √S₁(√S₂ + √S₃)`, `S₃ ≤ (x/2W+1)·1.4262²W`
    (trusted [RS62, Thm. 13] in `LambdaMu.lean`); `norm_typeII_le` takes any integrable majorant
    `g(W)`. Needs `U ≥ 1`, `V ≥ 2`, `V ≤ x/U`.
  * Step 3a ✅ `MinorArcs/TypeIITools.lean`, `MinorArcs/TypeIITotal.lean`: **`typeII_637`**, our
    (6.37) (`q ≤ V/2e`, any `δ`, `U, V : ℕ`, `V ≥ 50000`, `Q ≥ 3.5x/U`). Main term exactly [B]'s
    `x/√(2φ) √((Λ₀+Φ)(0.60428Λ₀ + 8κ₀ζ³√(x/V)/U))`; secondary terms cruder:
    `4√(κ₁qx/2φ)(2√(x/U) + √log 2q (2e√(2q) + 4√((x/U)/log(x/2Uq))))` (vs [B]'s
    `√2κ₂√(q/φ)(1+1.15√…)x/√U`; we replace the numerical (6.22) `2.3√(T/log T)` by a split at `ce²`)
    and `8·1.4262 x√(κ₁(1/2+1/U))/√V` (vs `κ₉x/√V`). `κ₁ = 2/π² + κ₀ζ³√(x/V)/U` kept exact (no
    (6.17) needed). `H₂` now uses `max(T₂, 0)` (so `H₂ ≥ 0`); trusted inputs as listed by
    `#sorry_deps`, plus the TODO `intervalIntegrable_H2_div`.
  * Step 3b ✅ `MinorArcs/TypeIITotalGen.lean`: `typeII_gen` (any `c`, `m` with
    `S₂ ≤ (m x/(φL) + (q/φ)W/L)Σ`, `L = log(W/c)`), and **`typeII_640`** (our (6.40): `|δ| ≥ 8`,
    `c' = |δ|q(1+ε₁)/4`, `c'e ≤ V`, `x ≤ Q²`), with `S2_le_640` from (5.56)(ii) (`R = √(W/c')`).
    Main term `2x/√(|δ|φ) √((Λ₀+Φ)(0.60428Λ₀ + 8κ₀ζ³√(x/V)/U))` as [B]'s.
  * Step 3c ✅ `MinorArcs/Eta2LogFourier.lean`: (B.17) `|(log·η₂)^| ≤ 2 - log 4` and (B.18)
    `(2πt)²|(log·η₂)^(t)| ≤ 96 log 2`, **proved** (two integrations by parts on `[1/4,1/2]`, `[1/2,1]`).
  * Step 3d ✅ `MinorArcs/TypeITotal.lean`: **`typeI1_le`** (§6.2.1, `|S_{I,1}|` for `U ≤ Q₀/2`) from
    the corrected Lemma 4.2.3 with (2.20), (2.22), (2.23), (B.17), (B.18). Prefactor `x/2q`,
    `min(1, c₀/(πδ)²)`, sums over `(m, 2q) = 1` (cf. the (4.40) erratum).
  * Step 3e ✅ `MinorArcs/TypeI2Total.lean`, `GcdSums.lean`, `TypeI2Sum.lean`, `TypeI2Large.lean`
    (§6.2.2, `qV ≤ Q`): (6.5) `typeI2_eq_sum`; the induced approximation `approx2_mul`;
    (6.6)–(6.8) `typeI2_le_sum`; (6.9) `∑ Λ(v)(q,v)/v ≤ log N + log q` and
    `∑ Λ(v) v (q,v) ≤ ∑ Λ(v) v + N q log q` (proved via `(q,v) = ∑_{d|(q,v)} φ(d)`);
    **`typeI2_le_small`** ((6.12)+(6.13), `|δ| ≤ 1/2c₂`) and **`typeI2_le_large`** ((6.12)+(6.14)).
    Needs `V ≥ 2·10⁶` (for (2.14), (2.17)), `16V ≤ Q`, `UV ≤ x`. Differences from [B]:
    `U²V log V` → `U²V log q`; the `Q log(U/(q/2))` term → `Q (log⁺(2U/q) + 1/e)` (no `Q ≤ 2UV/e`);
    the `c_{5,I2} max(log(c₁₁q²V/x), 2) Q` term is ours from `bound_4_31`:
    `(2|η₂'|₁/π) max(1, log(c₀e³q²V/4π|η₂'|₁x)) Q` (to compare in §6.3); in (6.14) the `UV/e` term carries a factor `1 + V/Q`, and
    the coefficients are kept as exact expressions in `c₊` (no rounding to `c_{4,I2}` etc.).
  * Step 3 (next): Lemma 4.2.4 case `q > Q/V` of `S_{I,2}`; Type II (6.38)/(6.39)/(6.41) (larger
    `q`; second parameter choice); `S_{0,2}` (powers of 2, negligible), `S_{0,∞} = 0`.
  * Step 4 (in progress): §6.3 parameter choices and numerics → Theorem 3.1.1 (`PointwiseBound.lean`).
    `scripts/thm_3_1_1_numerics.py` evaluates the right-hand sides of our Lean bounds at the
    (6.49) parameters (U, V rounded down) against Thm 3.1.1 (corrected constant `0.8103`): worst
    ratio ≈ 0.95 at `x = 2.16·10²⁰`, → 1 slowly as `x → ∞` (along the curve where the AM–GM step
    (6.77) is tight; there the main terms match [B]'s exactly). Plan for `q ≤ x^{1/3}/6`
    (`FirstChoice.lean`, with `T = x^{1/3}`, `t = δ₀q`):
    * ✅ `typeII_main_le`: main term of (6.37)/(6.40) ≤ `√(C_{x,t}(log t + .002) + log(4t)/2)·
      √(0.30214 log t + 0.67506)` (needs `ζ(3/2) ≤ 2.77`, proved);
    * ✅ `FirstChoiceParams.lean`: parameter facts for `U = ⌊T²/9√t⌋`, `V = ⌊9T/2⌋`, `Q = 3T²/4`;
    * ✅ `FirstChoiceTypeII.lean`: `typeII_rest_le` (lower-order Type II terms ≤ `3.2 x^{5/6}`, vs
      [B]'s 2.74; uses Lemma C.2.2 `q/φ(q) < Ϝ(r)`, trusted, and `e^γ < e^{2/3}`) and
      **`typeII_first`**: `|S_{II}| ≤ x/√(δ₀φ) √(C_{x,t}(log t + .002) + log(4t)/2)
      √(0.30214 log t + 0.67506) + 3.2 x^{5/6}` for `q ≤ x^{1/3}/6` (both `|δ| < 8` via (6.37) and
      `|δ| ≥ 8` via (6.40)). So the theorem's `3.36 x^{5/6}` will likely become `≈ 4 x^{5/6}`;
    * ✅ `FirstChoiceMain.lean`: `C_{x,t} ≤ 0.1 log t + 0.14`; AM–GM (6.77) with `√ρ = 1.84332`
      gives `R_{x,t} log t + 0.8103` (margins ~5·10⁻⁷ in the `log t` coefficient!).
    * ✅ `FirstChoiceTypeI.lean`, `FirstChoiceTypeI1.lean`: `typeI1_first`,
      `|S_{I,1}| ≤ 1.80303·2x/(δ₀φ) + (log t + 1.63)·2x/t + 0.014 x^{5/6}` (via
      `μ L ≤ (4/5)(2q/φ(2q)) + max(L - log(M/2q²), 0)`, `min(1,c₀/(πδ)²) ≤ 2/δ₀`).
    * ✅ `FirstChoiceTypeI2*.lean`: `typeI2_first`,
      `|S_{I,2}| ≤ 2.4916 x/√t + 0.8·2x/(δ₀φ) + (15.163 log t + 21.296)·2x/t + 0.553 x^{5/6}`
      (`ε = 0.07` in (6.14); the `x/|δ|q` term via monotonicity of `(A + log⁺(cy))/y`).
    * ✅ `FirstChoiceFinal.lean`: **`theorem_3_1_1_first`**, and `PointwiseBound.lean` now proves
      the first case of `theorem_3_1_1` (corrected constants `0.8103` and `3.8 x^{5/6}`). Our own
      allocation: the `x/(δ₀q)`-terms total `16.163 log t + 22.93`, which fits into
      `13.66 log t + 37.55` plus the unused part `3.25 log t + 5.217` of the `x/(δ₀φ)` slot
      (`x/(δ₀q) ≤ x/(δ₀φ)`). `x^{5/6}`: `3.2 + 0.014 + 0.553 + 0.0001 = 3.767`.
  * ✅ §6.3.2 (`q > x^{1/3}/6`): **Theorem 3.1.1 is proved in full** (`PointwiseBound.lean`,
    `#sorry_deps theorem_3_1_1` = the same 20 trusted items as the first case). Files:
    `TypeIILarge.lean` ((6.20) split integral; (6.38), (6.39), (6.41)), `SecondChoice.lean`
    (Dirichlet, `approx_gap`, `second_case_split`), `SecondBridge.lean` (case (c)),
    `SecondParams.lean`, `SecondNumerics.lean` (Taylor exp/log bounds `log_le_num`/`le_log_num`,
    `e^γ ≤ 1.7882` via `H₁₂₈`), `SecondTypeIIa*.lean` (case (a1): reduction
    `typeII_a1` + 12 generated pieces + tail ≥ 70), `SecondTypeIIb*.lean` (cases (a2), (b)),
    `SecondTypeI1/2.lean` (Type I: `≤ (0.0716L² + 3175.9L + 8399.2)T²`), `SecondFinal.lean`.
    Choices: `U = ⌊1225T⌋`, `V = ⌊T/3⌋`, `Q₀ = T²/349 ≥ 3.5x/U`, `θ = 8` in (6.38) and (6.41).
    All Type II cases are `≤ 1.413 L^{3/2} T^{5/2}` (`L = log T`; target `0.276·3√3 = 1.4341`),
    Type I borrows `≤ 205 L T²` of the remaining slack. Piece generators:
    `scripts/gen_a1_pieces.py`, `scripts/gen_b_pieces.py` (exact rational checks first).
  * Re-check numerics for the (4.40), Lemma 4.2.4 and §5.2 corrections, and `U ≥ 1` in (5.34).
* Optional: prove `fsq_le`; Lemma 5.1.2 (Rankin trick with (2.21)).
* `Prelim/LambdaMu.lean`: trusted literature bounds [B (2.12), (2.15), (2.16), (2.20)].
* Lemma 4.2.3 notes: the last term of (4.41) uses `log(2ex/c₂)` (the book's step needs `q ≥ 2`);
  the weighted sums are in `SumTools.lean` (`S2_le`, `sum_odd_mul_log_le`) and `sum_R3L`.

## Ch. 13: scale erratum (the ℓ∞ and ℓ² inputs use arcs at different scales)

Prop 13.1.2 combines, **for one family of arcs** `𝔐_{δ₀,r}` ((10.5), defined with a parameter
`x`), an ℓ² bound `∫_{𝔐_{δ₀,r+1}} |S₁|² ≤ H(r) Σ|aₙ|²` (13.4) and an ℓ∞ bound
`|S₂(α)| ≤ g(r)` off `𝔐_{δ₀,r}` (13.5). In the proof of Thm 13.2.1 (pp. 249–252):

* the ℓ² input `H(r) = (log(r+1) + c⁺)/(log √x + c⁻)` comes from Cor 12.2.5 (12.42) with
  arcs at **scale `x`**: `c⁻ = 0.6394 < log(1/√(2·8)) + log 2 + 1.3325822` is `log 2Q + c_E` with
  `Q = √(x/16)`. `J` (14.7), the major arcs (14.27) and `E_{η_*,r,8}` (14.17) are also at
  scale `x`, and so is our `majorArcs 8 r₀ (xOf N)` in `minor_arcs_input`;
* the ℓ∞ input (13.14)–(13.17) is derived only for `α` outside the arcs at **scale
  `y = x/κ`**: "Let α ∉ 𝔐_{8,r} … where y is used instead of x to define 𝔐_{8,r}" (p. 249). The
  paper arXiv:1312.7748, p. 48, has the same sentence.

The `y`-arcs are `κ = 49` times wider. For `α` outside the `x`-arcs but inside the `y`-arcs
(`q ≤ r`, `8r/κ ≤ |δ_y| q < 8r`), Thm 3.1.1 at scale `y` gives only
`r_α = max(q, |δ_y|q/8) ≥ max(q, r/κ)`. For example, take `q = 1` and `α` just outside the
`x`-arc around `0` at level `r₀`: `δ_y ≈ 8r₀/κ`, so `r_α ≈ 3061` and the bound is `g(3061) ≈ 7 g(r₀)`.
(The true value there is tiny: it is a major-arc point for the shorter sum `S_{η_*}`.)

Repairs tried (`scripts/minor_arc_scale_check.py`; all at `x = 4.9·10²⁶`, our constants):
1. **Everything at scale `y`**: `c⁻ → c⁻ − log 7`, which gives `M ≈ 0.8497` and
   `Z ≈ 1.0654 x²/κ > 1.058259`. **Fails.** (With [B]'s `0.5`, `Z ≈ 1.049`, which would pass.)
   It also needs the major arcs to be `𝔐_{392,r₀}` at scale `x`, beyond Thm 7.1.4's range
   `|δ| ≤ 600000·gcd(q,2)/q`.
2. **Everything at scale `x`, with Part II on the gap**: Cor 7.1.3 (GRH-verified, `q ≤ 300000`,
   `|δ_y| ≤ 4·300000/q`) bounds `S_{η_*}` on the gap whenever `q ≤ 300000`, including all of level
   `r₀`. But for levels `r ∈ (300000, r₁]` the gap contains `q ∈ (300000, r]`, where only
   `g(q) ≥ g(300000)` is available. The tail (14.43) needs `g(r₁)`; with `g(3·10⁵) ≈ 0.0317`
   instead of `g(r₁) ≈ 0.0156` it grows from `0.312` to `0.636`. **Fails** by a wide margin.

**Resolution (2026-10-31): repair 3 works, with room to spare** (`scripts/minor_arc_y_scale_repair.py`):
* Prop 13.1.2 with the family `M_{r₀} = 𝔐_{8,r₀}(x)`, `M_n = 𝔐_{8,n}(y) = 𝔐_{392,n}(x)` for
  `n > r₀` (nested). The base term keeps [B]'s `I₀ ≥ (√J − √E)² ≥ 8.6297x`.
* ℓ² from (12.42) with `δ₀ = 392`.
* ℓ∞ off `𝔐_{8,n}(y)` from a **fresh Dirichlet approximation at each scale `wy`** in (11.9). Since
  `𝔐_{8,r}(wy) ⊆ 𝔐_{8,r}(y)` for `w ≥ 1` and `⊆ 𝔐_{8,r/w}(y)` for `w < 1`, this gives
  `r_w ≥ min(1,w) n`. Thm 3.1.1 at scale `wy` then gives `max(g_{wy}(min(1,w)n), h(wy))`.
  The first case always has `r_w ≤ (wy)^{1/3}/6`, so `gx_antitoneOn` applies. This
  "Prop 11.2.3′" also sidesteps the `δ ↦ wδ` erratum.
* **Levels up to `r₂ ≈ x^{0.3}`** (the range of (12.42)), not [B]'s `r₁ = (3/8)y^{4/15} ≈ 10⁶`.
  The tail (14.43) shrinks from `0.30` to `0.12`.
* The base gap `𝔐_{8,r₀}(y) \ 𝔐_{8,r₀}(x)` (needed: `|S_{η_*}| ≤ |φ|₁ g(r₀) y ≈ 0.0555y`) is
  covered by [B, Cor 7.1.3]. Its range `q ≤ 300000`, `|δ| ≤ 1.2·10⁶/q` is exactly
  `𝔐_{8,r₀}(y)`. In the gap `|δ| ≥ 12245/q`, so `|S_{η_*}| ≤ (|η̂(δ)|/φ(q) + 1.3·10⁻⁷) y ≤ 0.02y`.

Result: `Z ≤ 0.866 x²/κ` at `y = 10²⁵` (decreasing: `0.823` at `10²⁶`, `0.617` at `10⁸⁰`), against
`1.058259`. That is better than [B]'s own `1.00948`, even with our corrected Thm 3.1.1. With
`r₂ = 10⁶` the same scheme gives `1.10`; the book's `r₁` was too small once the scale is handled
correctly. **So the flaw is fixable**; `minor_arcs_input` (`≤ 1.0376`) is true by this route.

Formalization plan (repair 3):
1. ✅ Prop 11.2.3′ (`Prop1123b.lean: prop_11_2_3'`, same 20 trusted items as Thm 3.1.1), and
   ✅ the repaired assembly `thm_13_2_1_repaired` (`Thm1321.lean`: mixed family `Mmix`, (12.42)
   with `δ₀ = 392`; uses only Prop 12.2.4).
   ✅ Per-level ℓ∞ in closed form (`LinftyLevels.lean: norm_S_etaStar_le_ghat`): off
   `𝔐_{8,n}(y)`, `|S_{η_*}| ≤ y·ghatY(y,n)`, `ghatY = 1.398·max(g_y(n), h(y)) + 17(670/n)³/3`
   (`w₀ = 670/n`, `w₁ = ∞`; `g_{wy}(min(1,w)n) ≤ g_y(n) max(1,1/w)`, `h(wy) ≤ h(y) max(1,1/w)`,
   `∫_{w₀}^∞ max(1,1/w)φ ≤ 1.398` in `PhiIntegrals.lean`). Numerics with exactly this majorant
   (`/tmp`-style check, to be turned into a script): cells in `y`, blocks of ratio 1.25 in the
   level, `r₂ = min((2√(x/784))^{0.6}/2 - 1, √(x/784)/20000)`: worst `Z ≈ 0.965` (cell
   `[1.01e25, 10^25.5]`), using `I₀ ≥ 8.6249x` and `E/x ≤ 10⁻⁶` with `t = 0.004` in
   `|a+b|² ≤ (1+t)|a|² + (1+1/t)|b|²`.
2. The base-gap bound from Cor 7.1.3 (a new cited Part II input) via the character expansion
   (`Bombieri.lean` tools, `gauss_induced`) and a bound on `η̂_*`.
3. Thm 13.2.1 assembly with the mixed family (generalize `thm_13_2_1_conditional`). Also the
   `S_{η₊} = S₁ + S₂` split (14.29)–(14.32), with [B]'s cited Part II constants `J`, `E`, (7.1.5).
4. Numerics for all `x ≥ 4.9·10²⁶`: closed-form majorants for `G`, then interval checks.

Earlier conclusion, kept for the record: neither [B]'s argument as written nor repairs 1–2
establishes (14.49) over the complement of the scale-`x` arcs. `minor_arcs_input` remains a cited-but-unverified input. Possible ways forward:
a finer ℓ² accounting of the gap region (by `q` and `δ`), different parameters (`κ`, `r₁`), or
checking whether a later version of [B] fixes this.

## Ch. 11: Prop 11.2.3 erratum (the proof ignores that `δ` scales with `w`)

[B]'s proof writes `S_{η_*}(α,x) = ∫ S_{η₂}(α, wx) φ(w) dw/w` (11.9) and applies Thm 3.1.1 to
each `S_{η₂}(α, wx)` with the same `r = max(1, |δ|/8) q`. At scale `wx`, though,
`2α = a/q + δ_w/(wx)` with **`δ_w = wδ`**, so:

* for `w < 1` the parameter is `r_w = max(1, w|δ|/8) q ≤ r`, and the bound `g_{wx}(r_w)` is
  *weaker* than the `g_{wx}(r)` [B] uses (`g` is decreasing);
* for `w > 1`, Thm 3.1.1's hypothesis `|δ_w/(wx)| ≤ 1/(q Q_{wx})` does not follow from
  `|δ/x| ≤ 1/(q Q_x)`, because `Q_{wx} > Q_x`. It holds for `w ≤ ((4/3)x^{1/3}/(8r))^{3/2}`,
  which is `≥ 94` when `r ≤ r₁ = (3/8)x^{4/15}`, `x ≥ 10²⁵`. Beyond that, `φ(w) ≤ e^{-4400}`
  and the trivial bound suffices. (Alternatively, a Dirichlet re-approximation `a'/q' ≠ a/q` at
  level `Q_{wx}` has `q' ≥ Q_x(1 - q/Q_{wx})`, which is the `h` case.)

The statement survives. For `|δ| ≤ 8`, `r_w = q = r` and nothing changes. For `|δ| > 8`,
`r_w ≥ w r`, and `A(r) = ∫ g_{wy,1}(wr) φ(w) dw ≤ 0.89 ∫ g_{wy,1}(r) φ(w) dw = C(r)` (the gain
for `w > 1` outweighs the loss for `w < 1`; `scripts/prop_11_2_3_check.py`, `r₀ ≤ r ≤ r₁`,
`y ∈ [10²⁵, 10¹⁰⁰]`). **Plan for Lean:** state Prop 11.2.3 only for `r ≤ r₁` (all that Ch. 13
needs; for `r > r₁` Ch. 13 uses `g(r₁)`). Prove it with per-`w` bounds `g_{wy,1}(r)` (`|δ| ≤ 8`)
and `g_{wy,1}(wr)` (`|δ| > 8`). Then either show the `|δ| > 8` integral is `≤` [B]'s closed form
`g_{y,φ}(r)`, or carry a closed form for `∫ g_{wy,1}(wr)φ(w)dw` into Ch. 13 directly.
Also note that the case `r > r₁` of Ch. 13 needs, for `w ≤ 1`, `g_{wy}(max(q, wr')) ≤ g_{wy}(w r₁)`.
That is not `g_{wy}(r₁)`, so the `g(r₁)` of (13.13)/(14.43) must be read the same way.

## How the 4.2.2 proof is organised (reuse for 4.2.3, 4.2.4)

* Case (a) uses `second_approx` (Dirichlet via `Real.exists_rat_abs_sub_le_and_den_le`,
  `q' ≥ εQ/(1+ε)`), `sum_A1` (blocks from 0, Lemma 4.1.2) and `sum_R3'` with `(a', q')`.
  The proof gives (4.32) with the unrounded `x/|δq|` where [B] has `min(⌊x/|δq|⌋ + 1, 2D)`
  (never larger).

* `typeI = mainPart + restPart` (`typeI_eq_main_add_rest`): `mainPart` is `q ∣ m ≤ M`.
* `mainPart` via `Todd_main` (Poisson); `restPart` via `|T_{m,∘}|` bounds (`norm_Todd_le_minA`,
  `norm_Todd_le_min_sin`) and Lemmas 4.1.1'/4.1.2/4.1.3 applied to `2α ≈ a/q + δ/x`
  (`approx_of` with a *real* `Q = x/|δq|`).
* Index sums are over `ℤ` (`Ioc ⌊y₁⌋ ⌊y₂⌋`, `Tn α x n = ‖Todd α x n.toNat‖`), to match §4.1.
* `Mof` now uses the unrounded `Q = x/|δq|` (allowed by the statement `M ∈ [min(Q₀/2,D), D]`);
  with `⌊x/|δq|⌋` the book's `min(c₂x/q, D) ≤ Q/2` can fail by `< 1/2`.

## Decisions made

* Follow the book [B] = arXiv:1501.05438v2, not the 2013 papers. Its minor-arc bound is
  1.00948 (not 0.97392), so [B]'s final margin is 0.048779·x²/κ (ours is 0.020659, see Status).
* Where the final inequality has room, prove cruder constants instead of the book's sharp
  ones (e.g. non-prime terms: 6.7·10⁶ instead of 7.3306). Record each such change in the
  docstrings and the README.
* Computations (binary Goldbach, prime ladder, Platt's GRH check, "rigorous computations") are
  meant to end up as explicitly labelled trusted facts.
* Blueprint statements use the book's exact constants and are transcribed from the typeset PDF.
  In Lean, watch division by zero: write `min(1, c/δ²)` with an explicit `δ = 0` case
  (`minInv`). `C / sin² = C/0 = 0` is fine, because it only makes the left side smaller.
* Book errata found so far: (4.32) cites "(4.8)" where it means (4.29). The proof of Lemma 4.1.3
  doesn't give its `max(2, …)` form (see the `TrigSums.lean` docstring). The η₁ typo in §7
  disagrees with (4.10)/(11.10); we use η₁ = 2·1_{[1/2,1]}. (4.34) ends with a stray factor `x`.
  In the proof of 4.2.1/4.2.2, `Q = ⌊x/|δq|⌋` is too small by rounding for `c₂x/q ≤ Q/2`
  (we use the unrounded `Q`). Lean's `C/0 = 0` makes `min(A, C/sin²)` vanish where `sin = 0`,
  so Lemma 4.1.1 is also proved with the honest summand (`lemma_4_1_1'`, `minA`).
  **(4.40) is inconsistent with its proof**: the statement has `x/q`, `η̂(-δ)` (so
  `min(1, c₀/(2πδ)²)`) and `(m,q) = 1`, the values for the all-`n` version; the proof (p. 67) gives
  `x/2q`, `η̂(-δ/2)` (so `min(1, c₀/(πδ)²)`) and `(m,2q) = 1`, as in (4.30). `bound_4_40` is the
  corrected form. **To check in Ch. 6**: §6.2.1 uses (4.40) for `S_{I,1}`; the corrected
  `δ`-decay is 4× weaker for large `δ` (the prefactor halves), so the final numerics there
  may need re-checking. Note §6.2.1 itself copies the uncorrected (4.40).
  **Theorem 3.1.1's constant `0.5` is not proved**: in §6.4, (6.77), the AM–GM step gives the
  constant `log 2/(2√ρ) + (√ρ/2)·0.67506 = 0.81020` (ρ = 3.397962), but [B] computes
  `(1/2)(log 2/√ρ + (√ρ/2)·0.67506) = 0.49911`. [B]'s own (6.63) exceeds the stated bound by up to
  ~2.6% (numerically, `q` prime, `δ₀q ~ 10⁵–10⁷`). `PointwiseBound.lean` now uses `0.8103`.
  ✅ Checked: the effect on Chs. 11, 13, §14.3 is `1.00948 → 1.0376` in (14.49) (see Status).
  **(6.12) understates the μ-sum for odd `q`**: the sum is over `(m, 2q) = 1`, so (2.22) applies
  with modulus `2q` and gives `(4/5)(2q/φ(2q))/log(M/2q²)`; [B] writes `q/φ(q)`. For odd `q`,
  `2q/φ(2q) = 2q/φ(q)`, so the term `(3/2 log q + 2.74) x/φ(q)` of (6.58) should be doubled.
  (It doesn't break Thm 3.1.1 numerically, but [B]'s slot-by-slot derivation of
  `L_{x,t,q}` doesn't go through as written; we use `min(1, a/ℓ)(ℓ + b) ≤ a + b` to move the `b`
  part into the `x/(δ₀q)` slot.)

  **§6.3.2 uses (5.54) outside its range**: Prop. 5.2.4 assumes `Q ≥ 3.5W`, but with [B]'s
  second choice `Q = x/U`, (6.38) applies (5.54) for `W` up to `x/U = Q`. Fix: re-approximate
  with `Q₀ ≥ 3.5x/U` (costs nothing visible; the `Q`-terms of `S_I` are lower order).
  **§6.3.2's case split has a gap**: [B] says that for the new approximation `a'/q'`, either
  `q' > y` or `|δ'| > 8y/q'`, "since otherwise `a'/q'` would already be a valid approximation under
  the first choice". But Thm 3.1.1's hypothesis is an *arbitrary* approximation `a/q` with
  `q > y`, and two approximations can coexist (e.g. `2α = 1/Q`: `1/1` with `δ = x/Q` and `1/⌊Q⌋`).
  Fix: in that case (`q' ≤ y`, `|δ'| ≤ 8y/q'`), `a'/q'` is an approximation for `Q = (3/4)x^{2/3}`
  and `1/qq' ≤ |a/q - a'/q'| ≤ 1/qQ + |δ'|/x` forces `δ₀'q' ∈ [2y(1 - y/Q), 2y]`, where the first
  case of the theorem gives `≈ 59 x^{5/6} ≤ 0.276 x^{5/6}(log x)^{3/2}`.

## Reading the book

* The arXiv PDF has 327 pages. **PDF page = printed page + 10.**
* Extracted text (`pypdf`) loses fraction structure. For formulas, render pages with PyMuPDF
  (`pip install pymupdf` in a venv, `page.get_pixmap(dpi=110).save(...)`) and read the images.
* Before formalizing any inequality, check it numerically (`mpmath`, high precision; float
  cancellation near 0 gives false negatives). This caught the Lemma 4.1.3 gap and picked the
  Taylor degrees.

## Lean 4 / Mathlib pitfalls hit so far

(Most were found on v4.15; we upgraded to v4.35 on 2026-10-30.)

* `linarith` can fail on decimal literals (`0.93`) and on `set`-introduced variables. Use
  fractions, and `obtain ⟨t, ht⟩ : ∃ t, t = … := ⟨_, rfl⟩` instead of `set`.
* `interval_cases q` does not update variables introduced by `set … := f q`, so handle small
  cases before any `set`.
* `rw [← integral_add_adjacent_intervals]` may rewrite the wrong side. Instead state
  `have e := integral_add_adjacent_intervals (a := …) (b := …) (c := …) (μ := volume) …` and
  use `linarith`.
* `∫ u in x / 2..y` misparses (`2..`): parenthesise the bounds.
* `ConvexOn.2 … (a := l)` clashes with local variables named `a`/`b`: give the expected type.
* Lemmas declared inside our namespace as `ConvexOn.foo` need `_root_.ConvexOn.foo` for
  dot notation.
* Opening `Set` and `Finset` together makes `mem_Icc` etc. ambiguous. Opening
  `ArithmeticFunction` makes `μ` mean Möbius. Use
  `open scoped ArithmeticFunction.vonMangoldt` instead.
* Big `nlinarith`/`linarith` calls time out in large contexts. Use `linarith only [...]`, split
  into explicit `have`s, or raise `maxHeartbeats` locally.
* Tight polynomial inequalities: reduce to one variable (replace C by its bound using the sign of
  its coefficient, then prove monotonicity in S via an explicit factorisation), then
  `nlinarith`. Alternatively, split into one-function inequalities (x cot x ≤ …, t²/sin²t ≤ …).
* Mathlib has `ConvexOn.comp_concaveOn`, `strictConcaveOn_sin_Icc`, `convexOn_zpow`,
  `monotone_arcsin`, `Real.cos_arcsin`, `primorial_le_4_pow`, `Real.lt_tan`.
* Reusable lemmas: `le_of_hasDerivAt_le` (compare functions via derivatives on [0,∞)), the sin/cos
  Taylor chain, `sum_range_pair`, `sum_Icc_low_high`, `sum_Icc_parity`, and the generic residue
  reduction `residue_form_gen` (any summand Φ(sin²(παn)) ≥ 0) in `TrigSums.lean`.

* `linarith` cannot use hypotheses with division by a decimal literal (`L / 2.9`, `x / 13.8`):
  rewrite as multiplication or with `div_le_iff₀` first. Unascribed numeral `have`s (`have : 4 * … ≤ 0.13`)
  may elaborate in the wrong type; write `(4 : ℝ)`. `set` does not abbreviate hypotheses created
  later, so `linarith` may see `Real.log …` and the `set` variable as different atoms.

## Environment

* Lean/Mathlib v4.35.0. Fetch the prebuilt Mathlib with `lake exe cache get` (the network
  allows it). Our own files build in a few minutes; `TrigSums.lean` is the slowest.
* Upgrade notes (v4.15 → v4.35), useful for the next bump:
  * Renames: `le_or_lt`→`le_or_gt`, `lt_or_le`→`lt_or_ge`, `Int.floor_add_int`→`Int.floor_add_intCast`,
    `Int.ediv_add_emod`→`Int.mul_ediv_add_emod`, `primorial_le_4_pow`→`primorial_le_four_pow`,
    `Finset.sum_eq_add_sum_diff_singleton`→`Finset.sum_eq_add_sum_sdiff_singleton_of_mem`,
    `Nat.Ico_succ_right`→`Finset.Ico_add_one_right_eq_Icc`, `left_mem_Ici`→`Set.self_mem_Ici`,
    `integral_finset_biUnion`→`integral_biUnion_finset`, `MeasureTheory.integral_mul_left`→
    `integral_const_mul`, `*_not_mem*`→`*_notMem*`, `if_pos/if_neg`→`ite_eq_left/right`,
    `push_neg`→`push Not`, `List.Chain R a l`→`List.IsChain R (a :: l)`.
  * `Complex.abs` is gone: use `‖·‖` (`Complex.norm_exp`, `Complex.abs_re_le_norm`, `Complex.norm_real`).
  * `setIntegral_const` now gives `volume.real s • c`: use `Real.volume_real_Ioc_of_le` etc.
    `integrableOn_const` takes the finiteness proofs as (auto)arguments.
  * `field_simp` is stronger: a trailing `ring` often errors with "no goals".
  * `convert … using 1` with `hasDerivAt_id`, `.sub`, `.add` now leaves function-equality goals
    (`(fun x => …) = id - …`): close them with `funext y; simp only [Pi.sub_apply, id_eq]`.
  * `ArithmeticFunction` notation needs `open scoped ArithmeticFunction.Moebius
    ArithmeticFunction.zeta` (Λ comes with `open ArithmeticFunction`).
  * `Real.sin_gt_sub_cube` is now `0 < x → x - x³/6 < sin x` (no `x ≤ 1`, sharper constant).
* Clone/push via SSH (`git@github.com:calr3/ternary-goldbach.git`). HTTPS has no credentials.
