import RSBounds.SchoenfeldQuadraticLeft

/-!
# Theorem 11 parameter balance: the algebraic layer

Schoenfeld (1976), Section 7. With `a = X²`, the split height `U = T₂ = 17 e^{vX}` (7.5) and
`d = log(17/2π)`, the Laplace primitives and zero weights in
`SchoenfeldQuadraticEnvelope.envelope` take the closed forms behind (7.11) and (7.18):

* `nearPrimitive (X²) d (vX) = X G₀ e^{−X/v}` with `G₀ = v²(v + d/X)` (7.12);
* `farPrimitive (X²) d 2 (vX) = X G₁ e^{−(2vX + X/v)}` with
  `G₁ = v²/(2v² − 1) · (v + (1 + 2d)/(2X))`, i.e. (7.19) for `m = 2`;
* `X/v = Y + 2X − vX` with `Y = X(1 − v)²/v` (7.9), (7.10).

The window lemma turns `1/√2 < v ≤ 1` into the near/far cutoff hypotheses of
`SchoenfeldQuadraticLeft.psi_error_le_envelope`. Unconditional real algebra only; see
`docs/SchoenfeldTheorem11Balance.md` for the remaining steps.
-/

open Real

namespace TernaryGoldbach.RSBounds.SchoenfeldBalanceAlgebra

open SchoenfeldLaplaceTails SchoenfeldZeroWeights

/-- Schoenfeld (7.12): `G₀ = v²(v + d/X)`. -/
noncomputable def G0 (d X v : ℝ) : ℝ := v ^ 2 * (v + d / X)

/-- Schoenfeld (7.19) with `m = 2`: `G₁ = v²/(2v² − 1) · (v + (1 + 2d)/(2X))`. -/
noncomputable def G1 (d X v : ℝ) : ℝ := v ^ 2 / (2 * v ^ 2 - 1) * (v + (1 + 2 * d) / (2 * X))

/-- Schoenfeld (7.10): `Y = X(1 − v)²/v`. -/
noncomputable def Ylow (X v : ℝ) : ℝ := X * (1 - v) ^ 2 / v

/-- Schoenfeld (7.9): `X/v = Y + 2X − vX`. -/
theorem X_div_v_eq {X v : ℝ} (hv : v ≠ 0) : X / v = Ylow X v + 2 * X - v * X := by
  unfold Ylow
  field_simp
  ring

theorem exp_neg_X_div_v {X v : ℝ} (hv : v ≠ 0) :
    Real.exp (-(X / v)) = Real.exp (-Ylow X v) * Real.exp (-(2 * X)) * Real.exp (v * X) := by
  rw [X_div_v_eq hv, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The height `U = 17 e^{vX}` has `log(U/17) = vX`. -/
theorem log_split_height (X v : ℝ) : Real.log (17 * Real.exp (v * X) / 17) = v * X := by
  rw [mul_div_cancel_left₀ _ (by norm_num : (17 : ℝ) ≠ 0), Real.log_exp]

/-- Closed form of the near primitive at `a = X²`, `u = vX`. -/
theorem nearPrimitive_eq {X v d : ℝ} (hX : 0 < X) (hv : 0 < v) :
    nearPrimitive (X ^ 2) d (v * X) = X * G0 d X v * Real.exp (-(X / v)) := by
  unfold nearPrimitive G0
  have he : -X ^ 2 / (v * X) = -(X / v) := by
    field_simp
  rw [he]
  field_simp

/-- Closed form of the far primitive (`m = 2`) at `a = X²`, `u = vX`. -/
theorem farPrimitive_eq {X v d : ℝ} (hX : 0 < X) (hv : 0 < v) (hv2 : 1 < 2 * v ^ 2) :
    farPrimitive (X ^ 2) d 2 (v * X) = X * G1 d X v * Real.exp (-(2 * v * X + X / v)) := by
  unfold farPrimitive G1
  have hq : (2 : ℝ) * v ^ 2 - 1 ≠ 0 := by linarith
  have he : -(2 * (v * X) + X ^ 2 / (v * X)) = -(2 * v * X + X / v) := by
    field_simp
  rw [he]
  have hden : (2 : ℝ) * (v * X) ^ 2 - X ^ 2 = X ^ 2 * (2 * v ^ 2 - 1) := by ring
  rw [hden]
  field_simp
  ring

/-- Closed form of the zero weight at the split height. -/
theorem Phi_eq {X v : ℝ} (hX : 0 < X) (hv : 0 < v) (m : ℕ) :
    Phi (X ^ 2) m (17 * Real.exp (v * X)) =
      Real.exp (-(X / v)) / (17 * Real.exp (v * X)) ^ (m + 1) := by
  unfold Phi
  rw [log_split_height]
  congr 2
  field_simp

/-- `1/√2 < v ≤ 1` gives the near and far cutoff conditions, in the form
`log(U/17)² ≤ X² < 2 log(U/17)²` used by `psi_error_le_envelope`. -/
theorem window {X v : ℝ} (hX : 0 < X) (hv : 0 < v) (hv1 : v ≤ 1) (hv2 : 1 < 2 * v ^ 2) :
    Real.log (17 * Real.exp (v * X) / 17) ^ 2 ≤ X ^ 2 ∧
      X ^ 2 < 2 * Real.log (17 * Real.exp (v * X) / 17) ^ 2 := by
  rw [log_split_height]
  have hX2 : 0 < X ^ 2 := by positivity
  constructor
  · have h : (v * X) ^ 2 = v ^ 2 * X ^ 2 := by ring
    have hv' : v ^ 2 ≤ 1 := by nlinarith
    rw [h]
    nlinarith
  · have h : 2 * (v * X) ^ 2 = 2 * v ^ 2 * X ^ 2 := by ring
    rw [h]
    nlinarith

/-- With `X = √(log x / R)`, `X² = log x / R` for `x ≥ 1`. -/
theorem X_sq {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (Real.log x / 9.645908801) ^ 2 = Real.log x / 9.645908801 := by
  apply Real.sq_sqrt
  exact div_nonneg (Real.log_nonneg hx) (by norm_num)

end TernaryGoldbach.RSBounds.SchoenfeldBalanceAlgebra
