import TernaryGoldbach.MinorArcs.InnerSums
import TernaryGoldbach.MinorArcs.TrigSums

/-!
# Type I sums [H, Ch. 4] — blueprint statements

Statements of the results of [H, Ch. 4] (H. A. Helfgott, *The ternary Goldbach problem*,
arXiv:1501.05438v2) that the minor-arc argument uses.  They are proved in
`TypeIProof.lean`, `TypeILogProof.lean` and `TypeI2Rest.lean`.  They were transcribed from
the typeset PDF; equation numbers are the book's.

* §4.1, trigonometric sums: Lemmas 4.1.1–4.1.3, stated in full generality and **proved** in
  `MinorArcs/TrigSums.lean`.
* §4.2, Type I estimates: Lemmas 4.2.2–4.2.4, which [H, §6.2] applies with `η = η₂`,
  `c₀ = 31.521`, `|η₂'|₁ = 8 log 2`, `ρ₀ = 4`.  We state them for exactly that `η`, so that the
  smoothing hypotheses ("η continuous, piecewise `C²`, compactly supported, `|η|₁ = 1`,
  `c₀ ≥ |η̂''|_∞`") become separate facts about `η₂` (`eta2_*` below).  Lemma 4.2.1 is only the
  template for these proofs and isn't stated.

Conventions.
* `O*(X)` in [H] means a quantity of absolute value `≤ X`; we fold such terms into the bound.
* `min(1, c/δ²)` is `1` at `δ = 0` (`minInv`), as in [H]; Lean's `c / 0 = 0` would make it `0`.
* In `C / sin²(παn)`, Lean's `C / 0 = 0` only *decreases* the left side, so the statements
  stay faithful (they are, if anything, slightly weaker).
* `M = min(Q/2, D)` with `Q = ⌊x/|δq|⌋` (and `M = D` if `δ = 0`), as in the proof of
  [H, Lemma 4.2.1]; the statements of Lemmas 4.2.2–4.2.3 only record `M ∈ [min(Q₀/2, D), D]`.
* Sums over `n` with `η₂(mn/x)` are finite, since `supp η₂ ⊆ [1/4, 1]`; we sum over `n ≤ x`.
-/

open Real Finset
open ArithmeticFunction (vonMangoldt moebius)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-! ## Notation -/

/-- `log⁺ x = max(log x, 0)`. -/
noncomputable def logPlus (x : ℝ) : ℝ := max (Real.log x) 0

/-- `min(1, c/δ²)`, read as `1` when `δ = 0`. -/
noncomputable def minInv (c δ : ℝ) : ℝ := if δ = 0 then 1 else min 1 (c / δ ^ 2)

/-- `c₂ = 6π / (5√c₀)` [H, Lemma 4.2.2]. -/
noncomputable def c₂ : ℝ := 6 * π / (5 * √c₀)

/-- The Fourier transform `f̂(t) = ∫ e(-xt) f(x) dx` [H, §2.3]. -/
noncomputable def fourier (f : ℝ → ℝ) (t : ℝ) : ℂ := ∫ x, e (-(x * t)) * f x

/-- `M = min(Q/2, D)` with `Q = x/|δq|` (`M = D` if `δ = 0`).  [H, proof of Lemma 4.2.1] uses
`Q = ⌊x/|δq|⌋`; the statement of [H, Lemma 4.2.2] only needs `M ∈ [min(Q₀/2, D), D]`, which
holds for this `M` too, and the unrounded `Q` avoids an issue with the rounding (with `⌊·⌋`,
`c₂x/q ≤ Q/2` can fail by less than `1/2` when `|δ| ≤ 1/2c₂`). -/
noncomputable def Mof (x δ : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  if δ = 0 then D else min (x / (|δ| * q) / 2) D

/-- `2α = a/q + δ/x (mod 1)`, `(a, q) = 1`, `|δ/x| ≤ 1/qQ₀`, `q ≤ Q₀` [H, Lemmas 4.2.2–4.2.4]. -/
def Approx2 (α x δ : ℝ) (a : ℤ) (q : ℕ) (Q₀ : ℝ) : Prop :=
  1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ (∃ k : ℤ, 2 * α = a / q + δ / x + k) ∧
    |δ / x| ≤ 1 / (q * Q₀) ∧ (q : ℝ) ≤ Q₀

open Classical in
/-- `∑_{m ≤ M/q, (m, r) = 1} μ(m)/m · w(m)`. -/
noncomputable def muSum (M : ℝ) (q r : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 ⌊M / q⌋₊, if Nat.Coprime m r then (μ m : ℝ) / m * w m else 0

open Classical in
/-- The Type I sum (4.29): `∑_{m ≤ D odd} μ(m) ∑_{n odd} e(αmn) η₂(mn/x)`. -/
noncomputable def typeI (α x D : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊D⌋₊, if Odd m then (μ m : ℂ) *
    ∑ n ∈ Icc 1 ⌊x⌋₊, (if Odd n then e (α * m * n) * (eta2 (m * n / x) : ℂ) else 0) else 0

open Classical in
/-- The Type I sum (4.39): `∑_{m ≤ D odd} μ(m) ∑_{n odd} (log n) e(αmn) η₂(mn/x)`. -/
noncomputable def typeILog (α x D : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊D⌋₊, if Odd m then (μ m : ℂ) *
    ∑ n ∈ Icc 1 ⌊x⌋₊,
      (if Odd n then (Real.log n : ℂ) * e (α * m * n) * (eta2 (m * n / x) : ℂ) else 0) else 0

open Classical in
/-- The Type I sum (4.49):
`∑_{v ≤ V odd} Λ(v) ∑_{u ≤ U odd} μ(u) ∑_{n odd} e(αvun) η₂(vun/x)`. -/
noncomputable def typeI2 (α x U V : ℝ) : ℂ :=
  ∑ v ∈ Icc 1 ⌊V⌋₊, if Odd v then (Λ v : ℂ) *
    ∑ u ∈ Icc 1 ⌊U⌋₊, (if Odd u then (μ u : ℂ) *
      ∑ n ∈ Icc 1 ⌊x⌋₊,
        (if Odd n then e (α * v * u * n) * (eta2 (v * u * n / x) : ℂ) else 0) else 0) else 0

/-! ## Facts about `η₂` used as hypotheses in [H, Ch. 4] -/

/-- `|η₂|₁ = 1` [H, (6.1)]. -/
theorem eta2_L1 : ∫ t, |eta2 t| = 1 := Helfgott.integral_abs_eta2

/-- `|η̂₂''|_∞ ≤ c₀` [H, (B.6), Lemma B.2.3] (`c₀ = 32`; [H]: `31.521`), written via
`η̂''(t) = (2πit)² η̂(t)`. From `eta2_fourier_bound'`. -/
theorem eta2_fourier_bound (t : ℝ) : (2 * π * t) ^ 2 * ‖fourier eta2 t‖ ≤ c₀ := by
  have h : fourier eta2 t = FourierTransform.fourier (fun u => (eta2 u : ℂ)) t :=
    (fourier_eq_integral_e _ _).symm
  rw [h]; exact eta2_fourier_bound' t

/-! ## §4.1 Trigonometric sums -/

/-- **[H, Lemma 4.1.1]**, proved in `MinorArcs/TrigSums.lean` (`TernaryGoldbach.MinorArcs.lemma_4_1_1`). -/
example {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) (y : ℝ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∑ n ∈ Finset.Ioc ⌊y⌋ ⌊y + q⌋, min A (C / Real.sin (π * α * n) ^ 2) ≤
      min (2 * A + 6 * q ^ 2 / π ^ 2 * C) (3 * A + 4 * q / π * √(A * C)) :=
  lemma_4_1_1 h y hA hC

open Classical in
/-- **[H, Lemma 4.1.2]**, proved in `MinorArcs/TrigSums.lean`. -/
example {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) {y₁ y₂ : ℝ}
    (hy : 0 ≤ y₁) (hy₁₂ : y₁ < y₂) (hlen : y₂ - y₁ ≤ q) (hy₂ : y₂ ≤ Q / 2) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋,
        (if (q : ℤ) ∣ n then 0 else min A (C / Real.sin (π * α * n) ^ 2)) ≤
      min (20 / (3 * π ^ 2) * C * q ^ 2) (2 * A + 4 * q / π * √(A * C)) :=
  lemma_4_1_2 h hy hy₁₂ hlen hy₂ hA hC

open Classical in
/-- **[H, Lemma 4.1.3]**, proved in `MinorArcs/TrigSums.lean` (by a sharper argument than [H]'s;
see the module docstring there). -/
example {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) {y₁ y₂ : ℝ}
    (hy : 0 ≤ y₁) (hy₁₂ : y₁ < y₂) (hlen : y₂ - y₁ ≤ q) (hy₂ : y₂ ≤ Q / 2) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋, (if (q : ℤ) ∣ n then 0 else
        min (B / |Real.sin (π * α * n)|) (C / Real.sin (π * α * n) ^ 2))) ≤
      2 * B * q / π * max 2 (Real.log (C * rexp 3 * q / (B * π))) ∧
    (∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋, (if (q : ℤ) ∣ n then 0 else
        min (B / |Real.sin (π * α * n)|) (C / Real.sin (π * α * n) ^ 2))) ≤
      2 * B * q / π * Real.log (2 * rexp 2 * q / π) :=
  lemma_4_1_3 h hy hy₁₂ hlen hy₂ hB hC

/-! ## §4.2 Type I estimates (for `η = η₂`) -/

/-- The main term (4.30) of [H, Lemma 4.2.2]. -/
noncomputable def bound_4_30 (x δ : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  x / (2 * q) * minInv c₀ (π * δ) * |muSum (Mof x δ q D) q (2 * q) fun _ => 1| +
    c₀ * q / x * (1 / 8 - 1 / (2 * π ^ 2)) * (D / q + 1) ^ 2

/-- The error term (4.31) of [H, Lemma 4.2.2], with `c₁ = 1 + |η'|₁/(x/D)`. -/
noncomputable def bound_4_31 (x : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  let c₁ := 1 + eta2'L1 / (x / D)
  2 * √(c₀ * c₁) / π * D + 3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) +
    √(c₀ * c₁) / π * q * logPlus (D / (q / 2)) +
    2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) +
    (2 * √(3 * c₀ * c₁) / π + 3 * c₁ / (2 * c₂) + 55 * c₀ * c₂ / (6 * π ^ 2)) * q

/-- The error term (4.32) of [H, Lemma 4.2.2] (case `|δ| ≥ 1/2c₂`). -/
noncomputable def bound_4_32 (x δ : ℝ) (q : ℕ) (D Q₀ ε : ℝ) : ℝ :=
  let c₁ := 1 + eta2'L1 / (x / D)
  let y := x / (|δ| * q)
  2 * √(c₀ * c₁) / π *
      (D + (1 + ε) * min ((⌊y⌋₊ : ℝ) + 1) (2 * D) * (√(3 + 2 * ε) + 1 / 2 * logPlus (2 * D / y))) +
    3 / 2 * c₁ * (2 + (1 + ε) / ε * logPlus (2 * D / y)) * (x / Q₀) +
    35 * c₀ * c₂ / (3 * π ^ 2) * q

-- [H, Lemma 4.2.2] itself is stated and proved in `MinorArcs/TypeIProof.lean`.

/-- The main term (4.40) of [H, Lemma 4.2.3], **corrected**.  [H] prints
`(x/q) min(1, c₀/(2πδ)²) |∑_{m ≤ M/q, (m,q)=1} μ(m)/m · log(x/mq)| + (x/q)|(log·η)^(-δ)| |…|`,
which are the values for the version with all `n` (cf. (4.9)); its own proof (p. 67) gives, for
odd `n`, `(x/2q) |η̂(-δ/2)| |∑_{(m,2q)=1} …| + (x/2q) |(log·η)^(-δ/2)| |∑_{(m,2q)=1} …|`, as in
(4.30).  We state the latter (with `|η̂(-δ/2)| ≤ min(1, c₀/(πδ)²)`). -/
noncomputable def bound_4_40 (x δ : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  x / (2 * q) * minInv c₀ (π * δ) *
      |muSum (Mof x δ q D) q (2 * q) fun m => Real.log (x / (m * q))| +
    x / (2 * q) * ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ *
      |muSum (Mof x δ q D) q (2 * q) fun _ => 1| +
    c₀ * (1 / 2 - 2 / π ^ 2) * (D ^ 2 / (4 * q * x) * Real.log (rexp (1 / 2) * x / D) + 1 / rexp 1)

/-- The error term (4.41) of [H, Lemma 4.2.3], with `c₁ = 1 + |η'|₁/(x/D)`.  **Slightly weakened**:
the last term has `log(2ex/c₂)` where [H] has `log(2√e x/c₂)`; [H]'s final step in (4.47) is only
justified for `q ≥ 2` (for `q = 1` it would need a numerical comparison). -/
noncomputable def bound_4_41 (x : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  let c₁ := 1 + eta2'L1 / (x / D)
  2 * √(c₀ * c₁) / π * D * Real.log (rexp 1 * x / D) +
    3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) * Real.log (q / c₂) +
    (2 * eta2'L1 / π * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) *
        Real.log x +
      2 * √(c₀ * c₁) / π * (√3 + 1 / 2 * logPlus (D / (q / 2))) * Real.log (q / c₂)) * q +
    3 * c₁ / 2 * √(2 * x / c₂) * Real.log (2 * x / c₂) +
    20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) * √(2 * x) * Real.log (2 * rexp 1 * x / c₂)

-- [H, Lemma 4.2.3] itself is stated and proved in `MinorArcs/TypeILogProof.lean` (the unused bound
-- (4.42) is omitted; see there).

/-- `c₄ = 1.03884` [H, Lemma 4.2.4]. -/
def c₄ : ℝ := 1.03884

/-- The main term (4.50) of [H, Lemma 4.2.4]. **Corrected**: the last term has a factor `3/2` that [H] lacks. [H, (4.55)] bounds
`∑_{p^α ≤ V, p | q} (log p) p^α` by `V log q`, but `∑_{α : p^α ≤ V} p^α` can exceed `V` (e.g.
`V = 9`, `p = 3`); it is at most `(3/2) V` for odd `p` (`sum_vonMangoldt_mul_not_coprime_le`). -/
noncomputable def bound_4_50 (x δ : ℝ) (q : ℕ) (U V : ℝ) : ℝ :=
  let D := U * V
  x / (2 * q) * minInv c₀ (π * δ) * Real.log (V * q) +
    (1 / 4 - 1 / π ^ 2) * c₀ *
      (D ^ 2 * Real.log V / (2 * q * x) + 3 * c₄ / 2 * (U * V ^ 2 / x) +
        3 / 2 * ((U + 1) ^ 2 * V / (2 * x) * Real.log q))

/-- The error term (4.51) of [H, Lemma 4.2.4] (case (b)), with `D = UV`, **as proved**
(`TypeI2Rest.lean: norm_restPartI2_le_caseB`). Same leading terms as [H]:
`(2√(c₀c₁)/π) D log(D/√e) + (3c₁/2)(x/q) log D log⁺(D/(c₂x/q)) + (2√(c₀c₁)/π)(q/2) log D log⁺(D/(q/2))`.
Changes, all documented in `NOTES.md`:
* `c₁ = 1 + |η'|₁/(x/D)` (odd `n`, as in Lemma 4.2.2); [H] prints `1 + |η'|₁/(2x/D)`, the all-`n` value.
* Lower-order `q` terms: `q(√3 log(3D) + 2 log⁺(D/(q/2)))` for [H]'s `√3 q log(c₂x/q)` (we bound
  the weight `log m` on each block of length `q` by `log` of its upper end).
* `log⁺(q/2)` for [H]'s `log(q/2)` (which is negative for `q = 1`).
* `(3c₁/2)√(2x/c₂)(log(3√(c₂x/2)) + 1)` for [H]'s `(3c₁/2)√(2x/c₂) log √(c₂x/2)`.
* `(2√c₀/π)√(2c₂x)(2 + 12 log(5D)) + 5c₀/6π²` for [H]'s `(25c₀/4π²)(2c₂)^{3/2} √x log x`
  (from our own version of [H, (4.59)–(4.60)], whose constant we could not reproduce). -/
noncomputable def bound_4_51 (x : ℝ) (q : ℕ) (U V : ℝ) : ℝ :=
  let D := U * V
  let c₁ := 1 + eta2'L1 / (x / D)
  2 * √(c₀ * c₁) / π *
      (D * Real.log (D / √(rexp 1)) +
        q * (√3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2)))) +
    3 * c₁ / 2 * (x / q) * Real.log D * logPlus (D / (c₂ * x / q)) +
    2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) *
      logPlus (q / 2) +
    3 * c₁ / 2 * √(2 * x / c₂) * (Real.log (3 * √(c₂ * x / 2)) + 1) +
    (2 * √c₀ / π * √(2 * c₂ * x) * (2 + 12 * Real.log (5 * D)) + 5 * c₀ / (6 * π ^ 2))

/-- The error term (4.52) of [H, Lemma 4.2.4] (case (a), `|δ| ≥ 1/2c₂`), with `D = UV`,
`y = x/|δ|q`, **as proved** (`TypeI2Rest.lean: norm_restPartI2_le_caseA`). Same leading term
`(2√(c₀c₁)/π) D log(D/e)` as [H]; the other terms have the same shape as [H]'s
(`(1+ε) (y+1) (… log …)` and `(x/Q₀)(… log …)`, the latter `≤ (√x/2)(…)` since `Q₀ ≥ 2√x`) but
cruder constants; `c₁ = 1 + |η'|₁/(x/D)` as in `bound_4_51`; `min(y+1, 2D)` as in `bound_4_32`. -/
noncomputable def bound_4_52 (x δ : ℝ) (q : ℕ) (U V Q₀ ε : ℝ) : ℝ :=
  let D := U * V
  let c₁ := 1 + eta2'L1 / (x / D)
  let y := x / (|δ| * q)
  let Y := min ((⌊y⌋₊ : ℝ) + 1) (2 * D)
  2 * √(c₀ * c₁) / π * (D * Real.log (D / rexp 1) +
      (1 + ε) * Y * (√(3 + 2 * ε) * Real.log (5 * D) + 1 / 2 +
        (2 + Real.log D / 2) * logPlus (2 * D / y))) +
    3 * c₁ / 2 * (2 * Real.log (5 * D) + (1 + ε) / ε * Real.log D * logPlus (2 * D / y)) * (x / Q₀) +
    35 * c₀ * c₂ / (3 * π ^ 2) * q * Real.log D

-- [H, Lemma 4.2.4] itself is stated and proved in `MinorArcs/TypeI2Rest.lean`.

end TernaryGoldbach.MinorArcs
