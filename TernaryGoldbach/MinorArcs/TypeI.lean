import TernaryGoldbach.MinorArcs.InnerSums
import TernaryGoldbach.MinorArcs.TrigSums

/-!
# Type I sums [B, Ch. 4] — blueprint statements

Statements of the results of [B, Ch. 4] (H. A. Helfgott, *The ternary Goldbach problem*,
arXiv:1501.05438v2) that the minor-arc argument uses.  **These are blueprint nodes: they are
stated with `sorry` and are not (yet) used by `ternary_goldbach`.**  They were transcribed from
the typeset PDF; equation numbers are the book's.

* §4.1, trigonometric sums: Lemmas 4.1.1–4.1.3, stated in full generality and **proved** in
  `MinorArcs/TrigSums.lean`.
* §4.2, Type I estimates: Lemmas 4.2.2–4.2.4, which [B, §6.2] applies with `η = η₂`,
  `c₀ = 31.521`, `|η₂'|₁ = 8 log 2`, `ρ₀ = 4`.  We state them for exactly that `η`, so that the
  smoothing hypotheses ("η continuous, piecewise `C²`, compactly supported, `|η|₁ = 1`,
  `c₀ ≥ |η̂''|_∞`") become separate facts about `η₂` (`eta2_*` below).  Lemma 4.2.1 is only the
  template for these proofs and isn't stated.

Conventions.
* `O*(X)` in [B] means a quantity of absolute value `≤ X`; we fold such terms into the bound.
* `min(1, c/δ²)` is `1` at `δ = 0` (`minInv`), as in [B]; Lean's `c / 0 = 0` would make it `0`.
* In `C / sin²(παn)`, Lean's `C / 0 = 0` only *decreases* the left side, so the statements
  stay faithful (they are, if anything, slightly weaker).
* `M = min(Q/2, D)` with `Q = ⌊x/|δq|⌋` (and `M = D` if `δ = 0`), as in the proof of
  [B, Lemma 4.2.1]; the statements of Lemmas 4.2.2–4.2.3 only record `M ∈ [min(Q₀/2, D), D]`.
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

/-- `c₂ = 6π / (5√c₀)` [B, Lemma 4.2.2]. -/
noncomputable def c₂ : ℝ := 6 * π / (5 * √c₀)

/-- The Fourier transform `f̂(t) = ∫ e(-xt) f(x) dx` [B, §2.3]. -/
noncomputable def fourier (f : ℝ → ℝ) (t : ℝ) : ℂ := ∫ x, e (-(x * t)) * f x

/-- `M = min(Q/2, D)` with `Q = x/|δq|` (`M = D` if `δ = 0`).  [B, proof of Lemma 4.2.1] uses
`Q = ⌊x/|δq|⌋`; the statement of [B, Lemma 4.2.2] only needs `M ∈ [min(Q₀/2, D), D]`, which
holds for this `M` too, and the unrounded `Q` avoids an issue with the rounding (with `⌊·⌋`,
`c₂x/q ≤ Q/2` can fail by less than `1/2` when `|δ| ≤ 1/2c₂`). -/
noncomputable def Mof (x δ : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  if δ = 0 then D else min (x / (|δ| * q) / 2) D

/-- `2α = a/q + δ/x (mod 1)`, `(a, q) = 1`, `|δ/x| ≤ 1/qQ₀`, `q ≤ Q₀` [B, Lemmas 4.2.2–4.2.4]. -/
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

/-! ## Facts about `η₂` used as hypotheses in [B, Ch. 4] -/

/-- `|η₂|₁ = 1` [B, (6.1)]. -/
theorem eta2_L1 : ∫ t, |eta2 t| = 1 := Helfgott.integral_abs_eta2

/-- `|η̂₂''|_∞ ≤ 31.521` [B, (B.6), Lemma B.2.3], written via `η̂''(t) = (2πit)² η̂(t)`.
Follows from the trusted fact `eta2_fourier_bound'` (in [B] a rigorous numerical computation). -/
theorem eta2_fourier_bound (t : ℝ) : (2 * π * t) ^ 2 * ‖fourier eta2 t‖ ≤ c₀ := by
  have h : fourier eta2 t = FourierTransform.fourier (fun u => (eta2 u : ℂ)) t :=
    (fourier_eq_integral_e _ _).symm
  rw [h]; exact eta2_fourier_bound' t

/-! ## §4.1 Trigonometric sums -/

/-- **[B, Lemma 4.1.1]**, proved in `MinorArcs/TrigSums.lean` (`TernaryGoldbach.MinorArcs.lemma_4_1_1`). -/
example {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) (y : ℝ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∑ n ∈ Finset.Ioc ⌊y⌋ ⌊y + q⌋, min A (C / Real.sin (π * α * n) ^ 2) ≤
      min (2 * A + 6 * q ^ 2 / π ^ 2 * C) (3 * A + 4 * q / π * √(A * C)) :=
  lemma_4_1_1 h y hA hC

open Classical in
/-- **[B, Lemma 4.1.2]**, proved in `MinorArcs/TrigSums.lean`. -/
example {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) {y₁ y₂ : ℝ}
    (hy : 0 ≤ y₁) (hy₁₂ : y₁ < y₂) (hlen : y₂ - y₁ ≤ q) (hy₂ : y₂ ≤ Q / 2) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋,
        (if (q : ℤ) ∣ n then 0 else min A (C / Real.sin (π * α * n) ^ 2)) ≤
      min (20 / (3 * π ^ 2) * C * q ^ 2) (2 * A + 4 * q / π * √(A * C)) :=
  lemma_4_1_2 h hy hy₁₂ hlen hy₂ hA hC

open Classical in
/-- **[B, Lemma 4.1.3]**, proved in `MinorArcs/TrigSums.lean` (by a sharper argument than [B]'s;
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

/-- The main term (4.30) of [B, Lemma 4.2.2]. -/
noncomputable def bound_4_30 (x δ : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  x / (2 * q) * minInv c₀ (π * δ) * |muSum (Mof x δ q D) q (2 * q) fun _ => 1| +
    c₀ * q / x * (1 / 8 - 1 / (2 * π ^ 2)) * (D / q + 1) ^ 2

/-- The error term (4.31) of [B, Lemma 4.2.2], with `c₁ = 1 + |η'|₁/(x/D)`. -/
noncomputable def bound_4_31 (x : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  let c₁ := 1 + eta2'L1 / (x / D)
  2 * √(c₀ * c₁) / π * D + 3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) +
    √(c₀ * c₁) / π * q * logPlus (D / (q / 2)) +
    2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) +
    (2 * √(3 * c₀ * c₁) / π + 3 * c₁ / (2 * c₂) + 55 * c₀ * c₂ / (6 * π ^ 2)) * q

/-- The error term (4.32) of [B, Lemma 4.2.2] (case `|δ| ≥ 1/2c₂`). -/
noncomputable def bound_4_32 (x δ : ℝ) (q : ℕ) (D Q₀ ε : ℝ) : ℝ :=
  let c₁ := 1 + eta2'L1 / (x / D)
  let y := x / (|δ| * q)
  2 * √(c₀ * c₁) / π *
      (D + (1 + ε) * min ((⌊y⌋₊ : ℝ) + 1) (2 * D) * (√(3 + 2 * ε) + 1 / 2 * logPlus (2 * D / y))) +
    3 / 2 * c₁ * (2 + (1 + ε) / ε * logPlus (2 * D / y)) * (x / Q₀) +
    35 * c₀ * c₂ / (3 * π ^ 2) * q

-- [B, Lemma 4.2.2] itself is stated and proved (case (b)) in `MinorArcs/TypeIProof.lean`.

/-- The main term (4.40) of [B, Lemma 4.2.3]. -/
noncomputable def bound_4_40 (x δ : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  x / q * minInv (c₀ / (2 * π) ^ 2) δ *
      |muSum (Mof x δ q D) q q fun m => Real.log (x / (m * q))| +
    x / q * ‖fourier (fun t => Real.log t * eta2 t) (-δ)‖ *
      |muSum (Mof x δ q D) q q fun _ => 1| +
    c₀ * (1 / 2 - 2 / π ^ 2) * (D ^ 2 / (4 * q * x) * Real.log (rexp (1 / 2) * x / D) + 1 / rexp 1)

/-- The error term (4.41) of [B, Lemma 4.2.3], with `c₁ = 1 + |η'|₁/(x/D)`. -/
noncomputable def bound_4_41 (x : ℝ) (q : ℕ) (D : ℝ) : ℝ :=
  let c₁ := 1 + eta2'L1 / (x / D)
  2 * √(c₀ * c₁) / π * D * Real.log (rexp 1 * x / D) +
    3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) * Real.log (q / c₂) +
    (2 * eta2'L1 / π * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) *
        Real.log x +
      2 * √(c₀ * c₁) / π * (√3 + 1 / 2 * logPlus (D / (q / 2))) * Real.log (q / c₂)) * q +
    3 * c₁ / 2 * √(2 * x / c₂) * Real.log (2 * x / c₂) +
    20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) * √(2 * x) * Real.log (2 * √(rexp 1) * x / c₂)

/-- The bound (4.42) of [B, Lemma 4.2.3] (case `|δ| ≥ 1/2c₂`; this is the whole bound). -/
noncomputable def bound_4_42 (x δ : ℝ) (q : ℕ) (D ε : ℝ) : ℝ :=
  let c₁ := 1 + eta2'L1 / (x / D)
  let y := x / (|δ| * q)
  2 * √(c₀ * c₁) / π * D * Real.log (rexp 1 * x / D) +
    2 * √(c₀ * c₁) / π * (1 + ε) * (y + 1) *
      (√(3 + 2 * ε) * logPlus (2 * √(rexp 1) * |δ| * q) +
        1 / 2 * logPlus (2 * D / y) * logPlus (2 * |δ| * q)) +
    (3 * c₁ / 4 * (2 / √5 + (1 + ε) / (2 * ε) * Real.log x) +
      40 / 3 * √2 * c₀ * c₂ ^ (3 / 2 : ℝ)) * √x * Real.log x

/-- **[B, Lemma 4.2.3]** for `η = η₂` (and `ρ₀ = 4`, by [B, (6.2)]). -/
theorem lemma_4_2_3 {α x δ Q₀ D : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hQ₀ : max 16 (2 * √x) ≤ Q₀) (hD : √3 ≤ D) (hDx : D ≤ min (x / 4) (x / rexp 1)) :
    ((|δ| ≤ 1 / (2 * c₂) ∨ D ≤ Q₀ / 2) →
      ‖typeILog α x D‖ ≤ bound_4_40 x δ q D + bound_4_41 x q D) ∧
    (1 / (2 * c₂) ≤ |δ| → ∀ ε, 0 < ε → ε ≤ 1 → ‖typeILog α x D‖ ≤ bound_4_42 x δ q D ε) := by
  sorry

/-- `c₄ = 1.03884` [B, Lemma 4.2.4]. -/
def c₄ : ℝ := 1.03884

/-- The main term (4.50) of [B, Lemma 4.2.4]. -/
noncomputable def bound_4_50 (x δ : ℝ) (q : ℕ) (U V : ℝ) : ℝ :=
  let D := U * V
  x / (2 * q) * minInv c₀ (π * δ) * Real.log (V * q) +
    (1 / 4 - 1 / π ^ 2) * c₀ *
      (D ^ 2 * Real.log V / (2 * q * x) + 3 * c₄ / 2 * (U * V ^ 2 / x) +
        (U + 1) ^ 2 * V / (2 * x) * Real.log q)

/-- The error term (4.51) of [B, Lemma 4.2.4], with `D = UV`, `c₁ = 1 + |η'|₁/(2x/D)`. -/
noncomputable def bound_4_51 (x : ℝ) (q : ℕ) (U V : ℝ) : ℝ :=
  let D := U * V
  let c₁ := 1 + eta2'L1 / (2 * x / D)
  2 * √(c₀ * c₁) / π *
      (D * Real.log (D / √(rexp 1)) +
        q * (√3 * Real.log (c₂ * x / q) + Real.log D / 2 * logPlus (D / (q / 2)))) +
    3 * c₁ / 2 * (x / q) * Real.log D * logPlus (D / (c₂ * x / q)) +
    2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) *
      Real.log (q / 2) +
    3 * c₁ / (2 * √(2 * c₂)) * √x * Real.log (c₂ * x / 2) +
    25 * c₀ / (4 * π ^ 2) * (2 * c₂) ^ (3 / 2 : ℝ) * √x * Real.log x

/-- The error term (4.52) of [B, Lemma 4.2.4] (case `|δ| ≥ 1/2c₂`). -/
noncomputable def bound_4_52 (x δ : ℝ) (q : ℕ) (U V ε : ℝ) : ℝ :=
  let D := U * V
  let c₁ := 1 + eta2'L1 / (2 * x / D)
  let y := x / (|δ| * q)
  2 * √(c₀ * c₁) / π * D * Real.log (D / rexp 1) +
    2 * √(c₀ * c₁) / π * (1 + ε) * (y + 1) *
      ((√(3 + 2 * ε) - 1) * Real.log ((y + 1) / √2) +
        1 / 2 * Real.log D * logPlus (rexp 2 * D / y)) +
    (3 * c₁ / 2 * (1 / 2 + 3 * (1 + ε) / (16 * ε) * Real.log x) +
      20 * c₀ / (3 * π ^ 2) * (2 * c₂) ^ (3 / 2 : ℝ)) * √x * Real.log x

/-- **[B, Lemma 4.2.4]** for `η = η₂`. -/
theorem lemma_4_2_4 {α x δ Q₀ U V : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hQ₀ : max (2 * rexp 1) (2 * √x) ≤ Q₀) (hx : rexp 2 * c₂ / 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUV : U * V + 19 / 18 * Q₀ ≤ x / 5.6) :
    ((|δ| ≤ 1 / (2 * c₂) ∨ U * V ≤ Q₀ / 2) →
      ‖typeI2 α x U V‖ ≤ bound_4_50 x δ q U V + bound_4_51 x q U V) ∧
    (1 / (2 * c₂) ≤ |δ| → ∀ ε, 0 < ε → ε ≤ 1 →
      ‖typeI2 α x U V‖ ≤ bound_4_50 x δ q U V + bound_4_52 x δ q U V ε) := by
  sorry

end TernaryGoldbach.MinorArcs
