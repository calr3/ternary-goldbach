# Working notes

Notes for continuing the formalization. For the overall map, see `BLUEPRINT.md`. For the
`sorry` policy, see `README.md`.

## Status (2026-10-30)

* `ternary_goldbach` depends only on the 4 `sorry`s in `Helfgott/Inputs.lean`: the major arcs
  (14.27), the minor arcs (14.49), binary Goldbach up to 4·10¹⁸, and the prime ladder.
* Part I (minor arcs) blueprint:
  * [B, §4.1] (Lemmas 4.1.1–4.1.3) is proved in `MinorArcs/TrigSums.lean`.
  * [B, §4.2] (Lemmas 4.2.2–4.2.4) is stated with `sorry` in `MinorArcs/TypeI.lean`, for η = η₂.
  * Thm 3.1.1 is stated in `MinorArcs/PointwiseBound.lean`.
  * Vaughan's identity and a basic large sieve are proved.
* **Next:** [B, §4.2]. Needs Poisson summation for η₂ (Mathlib has
  `Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay`; check the decay hypotheses for η₂), the
  main-term separation from the proof of Lemma 4.2.1 (pp. 56–63 printed), and then 4.2.2–4.2.4
  as variants. The bound `|η̂₂''|_∞ ≤ 31.521` is `eta2_fourier_bound` (App. B, by computer):
  make it a labelled trusted fact unless we build interval arithmetic.

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
  disagrees with (4.10)/(11.10); we use η₁ = 2·1_{[1/2,1]}.

## Reading the book

* The arXiv PDF has 327 pages. **PDF page = printed page + 10.**
* Extracted text (`pypdf`) loses fraction structure. For formulas, render pages with PyMuPDF
  (`pip install pymupdf` in a venv, `page.get_pixmap(dpi=110).save(...)`) and read the images.
* Before formalizing any inequality, check it numerically (`mpmath`, high precision; float
  cancellation near 0 gives false negatives). This caught the Lemma 4.1.3 gap and picked the
  Taylor degrees.

## Lean 4 / Mathlib v4.15 pitfalls hit so far

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

* Mathlib v4.15.0 is copied from `../landau4/lean/.lake` (it isn't fetched).
  `lake build` takes about 10 minutes from clean for `TrigSums.lean`.
* Clone/push via SSH (`git@github.com:calr3/ternary-goldbach.git`). HTTPS has no credentials.
