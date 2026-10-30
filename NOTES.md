# Working notes

Notes for continuing the formalization. For the overall map, see `BLUEPRINT.md`. For the
`sorry` policy, see `README.md`.

## Status (2026-10-30)

* `ternary_goldbach` depends only on the 4 `sorry`s in `Helfgott/Inputs.lean`: the major arcs
  (14.27), the minor arcs (14.49), binary Goldbach up to 4·10¹⁸, and the prime ladder.
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
  * Still `sorry`: Thm 3.1.1 (Ch. 5 Type II, Ch. 6 assembly).
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
  * Trusted: `fsq_le` (`f(X) ≤ 1.27X`, [B p. 83]; provable: reduce to integers `n ≤ 37` using
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
  * Step 4: §6.3 parameter choices and numerics → Theorem 3.1.1 (`PointwiseBound.lean`).
  * Re-check numerics for the (4.40), Lemma 4.2.4 and §5.2 corrections, and `U ≥ 1` in (5.34).
* Optional: prove `fsq_le`; Lemma 5.1.2 (Rankin trick with (2.21)).
* `Prelim/LambdaMu.lean`: trusted literature bounds [B (2.12), (2.15), (2.16), (2.20)].
* Lemma 4.2.3 notes: the last term of (4.41) uses `log(2ex/c₂)` (the book's step needs `q ≥ 2`);
  the weighted sums are in `SumTools.lean` (`S2_le`, `sum_odd_mul_log_le`) and `sum_R3L`.

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
  1.00948 (not 0.97392), so the final margin is 0.048779·x²/κ.
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
