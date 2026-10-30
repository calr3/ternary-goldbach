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
  * Still `sorry`: Lemma 4.2.4 (in `TypeI.lean`), Thm 3.1.1.
* **Next: Lemma 4.2.4** ([B pp. 70–76], sum `∑_v Λ(v) ∑_u μ(u) ∑_n …`); both of its cases are used
  ([B, §6.2.2]). Reuse: `InnerSumsGen` (general smoothing), `SumTools` (sums vs antiderivatives),
  the R/A range lemmas of `TypeIProof`/`TypeILogProof` as templates. Then Ch. 5 (Type II).
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
