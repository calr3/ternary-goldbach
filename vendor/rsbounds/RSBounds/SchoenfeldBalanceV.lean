import RSBounds.SchoenfeldBalanceAlgebra

/-!
# Theorem 11 parameter balance: the split parameter `v`

Schoenfeld (1976), (7.27)–(7.30). The split height `T₂ = 17 e^{vX}` is determined by
`k(v) = 1`, where

    k(v) = (17X/2π) · (G₀³/G₁)^{1/2} · e^{−2X(1−v)} · e^{−X(1−v)²/v}.

This file proves Schoenfeld's bounds for `H(v) = G₀³/G₁` (7.28), evaluates `k` at
`v_j = 1 − log(17X/((2+3j)π))/(2X)` (7.29), and obtains a root `v ∈ (v₀, v₁)` from the
intermediate value theorem. The numerical facts about `X` enter as explicit hypotheses.
Unconditional real analysis only.
-/

open Real Set

namespace TernaryGoldbach.RSBounds.SchoenfeldBalanceV

open SchoenfeldBalanceAlgebra

/-- Schoenfeld (7.28): `H(v) = G₀³/G₁`. -/
noncomputable def H (d X v : ℝ) : ℝ := G0 d X v ^ 3 / G1 d X v

/-- Schoenfeld (7.27). -/
noncomputable def k (d X v : ℝ) : ℝ :=
  17 * X / (2 * π) * Real.sqrt (H d X v) * Real.exp (-(2 * X * (1 - v))) *
    Real.exp (-(X * (1 - v) ^ 2 / v))

/-- Schoenfeld (7.29): `v_j = 1 − log(17X/((2+3j)π))/(2X)`. -/
noncomputable def vj (j X : ℝ) : ℝ := 1 - Real.log (17 * X / ((2 + 3 * j) * π)) / (2 * X)

theorem H_eq {d X v : ℝ} (hX : 0 < X) (hv : 0 < v) (hv2 : 1 < 2 * v ^ 2) (hd : 0 ≤ d) :
    H d X v = v ^ 4 * (2 * v ^ 2 - 1) * (v + d / X) ^ 3 / (v + (1 + 2 * d) / (2 * X)) := by
  have hq : (2 : ℝ) * v ^ 2 - 1 ≠ 0 := by linarith
  have hw : 0 < v + (1 + 2 * d) / (2 * X) := by positivity
  unfold H G0 G1
  field_simp


/-- Schoenfeld (7.28), upper bound: `H(v) < (v + d/X)²` for `1/√2 < v ≤ 1`. -/
theorem H_lt {d X v : ℝ} (hX : 0 < X) (hv : 0 < v) (hv1 : v ≤ 1) (hv2 : 1 < 2 * v ^ 2)
    (hd : 0 ≤ d) : H d X v < (v + d / X) ^ 2 := by
  rw [H_eq hX hv hv2 hd]
  have hu : 0 < v + d / X := by positivity
  have hw : v + d / X < v + (1 + 2 * d) / (2 * X) := by
    have : d / X < (1 + 2 * d) / (2 * X) := by
      rw [div_lt_div_iff₀ hX (by positivity)]
      nlinarith
    linarith
  have hw0 : 0 < v + (1 + 2 * d) / (2 * X) := by linarith
  have hc : v ^ 4 * (2 * v ^ 2 - 1) ≤ 1 := by
    have h4 : v ^ 4 ≤ 1 := pow_le_one₀ hv.le hv1
    have h2 : 2 * v ^ 2 - 1 ≤ 1 := by nlinarith
    have h2' : 0 ≤ 2 * v ^ 2 - 1 := by linarith
    calc v ^ 4 * (2 * v ^ 2 - 1) ≤ 1 * 1 := by
          apply mul_le_mul h4 h2 h2' zero_le_one
      _ = 1 := by ring
  rw [div_lt_iff₀ hw0]
  have hp : 0 < (v + d / X) ^ 2 := by positivity
  calc v ^ 4 * (2 * v ^ 2 - 1) * (v + d / X) ^ 3
      ≤ 1 * (v + d / X) ^ 3 := by
        apply mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (v + d / X) ^ 2 * (v + d / X) := by ring
    _ < (v + d / X) ^ 2 * (v + (1 + 2 * d) / (2 * X)) :=
        mul_lt_mul_of_pos_left hw hp

/-- Schoenfeld (7.28), lower bound: `H(v) > v⁶(2v² − 1)` once `d > 1/4`. -/
theorem H_gt {d X v : ℝ} (hX : 0 < X) (hv : 0 < v) (hv2 : 1 < 2 * v ^ 2) (hd : 1 / 4 < d) :
    v ^ 6 * (2 * v ^ 2 - 1) < H d X v := by
  rw [H_eq hX hv hv2 (by linarith)]
  have hw0 : 0 < v + (1 + 2 * d) / (2 * X) := by positivity
  have hq : 0 < 2 * v ^ 2 - 1 := by linarith
  rw [lt_div_iff₀ hw0]
  -- (v + d/X)³ > v²(v + (1+2d)/(2X)), since 2v²d/X > v²/(2X).
  have key : v ^ 2 * (v + (1 + 2 * d) / (2 * X)) < (v + d / X) ^ 3 := by
    have hy : 0 < 1 / X := by positivity
    have hd0 : 0 < d := by linarith
    have e : d / X = d * (1 / X) := by ring
    have e2 : (1 + 2 * d) / (2 * X) = (1 / 2 + d) * (1 / X) := by ring
    rw [e, e2]
    have hid : (v + d * (1 / X)) ^ 3 - v ^ 2 * (v + (1 / 2 + d) * (1 / X)) =
        v ^ 2 * (1 / X) * (2 * d - 1 / 2) + 3 * v * d ^ 2 * (1 / X) ^ 2 +
          d ^ 3 * (1 / X) ^ 3 := by ring
    have t1 : 0 < v ^ 2 * (1 / X) * (2 * d - 1 / 2) := by
      have : 0 < 2 * d - 1 / 2 := by linarith
      positivity
    have t2 : 0 ≤ 3 * v * d ^ 2 * (1 / X) ^ 2 := by positivity
    have t3 : 0 ≤ d ^ 3 * (1 / X) ^ 3 := by positivity
    linarith

  have hc : 0 < v ^ 4 * (2 * v ^ 2 - 1) := by positivity
  calc v ^ 6 * (2 * v ^ 2 - 1) * (v + (1 + 2 * d) / (2 * X))
      = v ^ 4 * (2 * v ^ 2 - 1) * (v ^ 2 * (v + (1 + 2 * d) / (2 * X))) := by ring
    _ < v ^ 4 * (2 * v ^ 2 - 1) * (v + d / X) ^ 3 := mul_lt_mul_of_pos_left key hc

/-- At `v_j`, the first exponential is `(2+3j)π/(17X)`, so (7.29):
`k(v_j) = ((2+3j)/2) · √H(v_j) · e^{−X(1−v_j)²/v_j}`. -/
theorem k_vj {d X j : ℝ} (hX : 0 < X) (hj : 0 ≤ j) :
    k d X (vj j X) = (2 + 3 * j) / 2 * Real.sqrt (H d X (vj j X)) *
      Real.exp (-(X * (1 - vj j X) ^ 2 / vj j X)) := by
  have hc : 0 < (2 + 3 * j) * π := by positivity
  have hpos : 0 < 17 * X / ((2 + 3 * j) * π) := by positivity
  have h1 : 2 * X * (1 - vj j X) = Real.log (17 * X / ((2 + 3 * j) * π)) := by
    unfold vj
    field_simp
    ring
  have h2 : Real.exp (-(2 * X * (1 - vj j X))) = (2 + 3 * j) * π / (17 * X) := by
    rw [h1, Real.exp_neg, Real.exp_log hpos, inv_div]
  unfold k
  rw [h2]
  field_simp

/-- `k(v₀) < 1`, given `1/√2 < v₀`, `v₀ + d/X ≤ 1` (that is, `X ≥ 17/(2π)`, (7.29)). -/
theorem k_v0_lt_one {d X : ℝ} (hX : 0 < X) (hd : 0 ≤ d) (hv0 : 0 < vj 0 X)
    (hv02 : 1 < 2 * vj 0 X ^ 2) (hsum : vj 0 X + d / X ≤ 1) :
    k d X (vj 0 X) < 1 := by
  have hv1 : vj 0 X ≤ 1 := by
    have : 0 ≤ d / X := by positivity
    linarith
  rw [k_vj hX le_rfl]
  have hH := H_lt hX hv0 hv1 hv02 hd
  have hu : 0 < vj 0 X + d / X := by positivity
  have hsq : Real.sqrt (H d X (vj 0 X)) < vj 0 X + d / X := by
    rw [Real.sqrt_lt' hu]
    exact hH
  have he : Real.exp (-(X * (1 - vj 0 X) ^ 2 / vj 0 X)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  have hs0 : 0 ≤ Real.sqrt (H d X (vj 0 X)) := Real.sqrt_nonneg _
  calc (2 + 3 * 0) / 2 * Real.sqrt (H d X (vj 0 X)) * Real.exp (-(X * (1 - vj 0 X) ^ 2 / vj 0 X))
      ≤ (2 + 3 * 0) / 2 * Real.sqrt (H d X (vj 0 X)) * 1 := by
        apply mul_le_mul_of_nonneg_left he; positivity
    _ = Real.sqrt (H d X (vj 0 X)) := by ring
    _ < 1 := by linarith

/-- `k(v₁) > 1`, from `H(v₁) > v₁⁶(2v₁² − 1)`, given the numerical inequality
`(5/2)·√(v₁⁶(2v₁²−1))·e^{−X(1−v₁)²/v₁} > 1`, which holds for `X ≥ X₀` (7.29). -/
theorem one_lt_k_v1 {d X : ℝ} (hX : 0 < X) (hd : 1 / 4 < d) (hv1 : 0 < vj 1 X)
    (hv12 : 1 < 2 * vj 1 X ^ 2)
    (hnum : 1 < (2 + 3 * 1) / 2 * Real.sqrt (vj 1 X ^ 6 * (2 * vj 1 X ^ 2 - 1)) *
      Real.exp (-(X * (1 - vj 1 X) ^ 2 / vj 1 X))) :
    1 < k d X (vj 1 X) := by
  rw [k_vj hX zero_le_one]
  have hH := H_gt hX hv1 hv12 hd
  have hs : Real.sqrt (vj 1 X ^ 6 * (2 * vj 1 X ^ 2 - 1)) ≤ Real.sqrt (H d X (vj 1 X)) :=
    Real.sqrt_le_sqrt hH.le
  have hpos : 0 < (2 + 3 * (1 : ℝ)) / 2 * Real.exp (-(X * (1 - vj 1 X) ^ 2 / vj 1 X)) := by
    positivity
  calc 1 < (2 + 3 * 1) / 2 * Real.sqrt (vj 1 X ^ 6 * (2 * vj 1 X ^ 2 - 1)) *
        Real.exp (-(X * (1 - vj 1 X) ^ 2 / vj 1 X)) := hnum
    _ ≤ (2 + 3 * 1) / 2 * Real.sqrt (H d X (vj 1 X)) *
        Real.exp (-(X * (1 - vj 1 X) ^ 2 / vj 1 X)) := by
        have := mul_le_mul_of_nonneg_right hs hpos.le
        nlinarith [this]

theorem G1_pos {d X v : ℝ} (hX : 0 < X) (hd : 0 ≤ d) (hv : 0 < v) (hv2 : 1 < 2 * v ^ 2) :
    0 < G1 d X v := by
  unfold G1
  have hq : 0 < 2 * v ^ 2 - 1 := by linarith
  have hw : 0 < v + (1 + 2 * d) / (2 * X) := by positivity
  exact mul_pos (div_pos (pow_pos hv 2) hq) hw

/-- `k` is continuous where `v > 0` and `2v² > 1`. -/
theorem continuousOn_k {d X : ℝ} (hX : 0 < X) (hd : 0 ≤ d) :
    ContinuousOn (k d X) {v | 0 < v ∧ 1 < 2 * v ^ 2} := by
  set S := {v : ℝ | 0 < v ∧ 1 < 2 * v ^ 2}
  have hG0 : Continuous (G0 d X) := by
    unfold G0
    fun_prop
  have hG1 : ContinuousOn (G1 d X) S := by
    unfold G1
    refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)
    intro v hv
    exact (sub_pos.mpr hv.2).ne'
  have hH : ContinuousOn (H d X) S := by
    unfold H
    refine ContinuousOn.div (hG0.pow 3).continuousOn hG1 ?_
    intro v hv
    exact (G1_pos hX hd hv.1 hv.2).ne'
  have hY : ContinuousOn (fun v : ℝ => X * (1 - v) ^ 2 / v) S := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro v hv
    exact hv.1.ne'
  have he : Continuous fun v : ℝ => Real.exp (-(2 * X * (1 - v))) := by fun_prop
  exact ((continuousOn_const.mul hH.sqrt).mul he.continuousOn).mul hY.neg.rexp

theorem vj0_le_vj1 {X : ℝ} (hX : 0 < X) : vj 0 X ≤ vj 1 X := by
  unfold vj
  have h : Real.log (17 * X / ((2 + 3 * 1) * π)) ≤ Real.log (17 * X / ((2 + 3 * 0) * π)) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [Real.pi_pos]
  have h2X : 0 < 2 * X := by positivity
  have := div_le_div_of_nonneg_right h h2X.le
  linarith

/-- The split parameter of (7.27): a root of `k(v) = 1` in `(v₀, v₁)`. -/
theorem exists_k_eq_one {d X : ℝ} (hX : 0 < X) (hd : 0 ≤ d) (hv0 : 0 < vj 0 X)
    (hv02 : 1 < 2 * vj 0 X ^ 2) (hk0 : k d X (vj 0 X) < 1) (hk1 : 1 < k d X (vj 1 X)) :
    ∃ v ∈ Ioo (vj 0 X) (vj 1 X), k d X v = 1 := by
  have h01 := vj0_le_vj1 hX
  have hsub : Icc (vj 0 X) (vj 1 X) ⊆ {v | 0 < v ∧ 1 < 2 * v ^ 2} := by
    intro v hv
    have hv' : vj 0 X ≤ v := hv.1
    refine ⟨by linarith, ?_⟩
    nlinarith
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Ioo h01 ((continuousOn_k hX hd).mono hsub) ⟨hk0, hk1⟩
  exact ⟨v, hv, hfv⟩

end TernaryGoldbach.RSBounds.SchoenfeldBalanceV

