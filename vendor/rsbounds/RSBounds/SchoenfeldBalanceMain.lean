import RSBounds.SchoenfeldBalanceHeight

/-!
# Theorem 11 parameter balance: the main-term identity

Schoenfeld (1976), (7.21)–(7.24). With the split parameter `v` determined by `k(v) = 1`
(7.27) and `δ` chosen by (7.24a),

    δ = (G₀G₁)^{1/4} e^{−Y/2} √(2/(17π)) X^{1/2} e^{−X},

the split height `T₂ = 17e^{vX}` satisfies `δ·T₂ = 2√(G₁/G₀)`, which is (7.21) for `m = 2`.
This is the identity that balances the near and far main terms. The fourth root is written
`√√(G₀G₁)`. Unconditional real algebra.
-/

open Real

namespace TernaryGoldbach.RSBounds.SchoenfeldBalanceMain

open SchoenfeldBalanceAlgebra SchoenfeldBalanceV

/-- Schoenfeld (7.24a). -/
noncomputable def delta (d X v : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) * Real.exp (-(Ylow X v / 2)) *
    Real.sqrt (2 / (17 * π)) * Real.sqrt X * Real.exp (-X)

theorem delta_pos {d X v : ℝ} (hX : 0 < X) (h0 : 0 < G0 d X v) (h1 : 0 < G1 d X v) :
    0 < delta d X v := by
  unfold delta
  have : 0 < Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos h0 h1))
  have : 0 < Real.sqrt (2 / (17 * π)) := Real.sqrt_pos.mpr (by positivity)
  have : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  positivity

/-- `k(v) = 1`, rewritten: `e^{2X(1−v) + Y} = (17X/2π)·√H`. -/
theorem exp_eq_of_k_eq_one {d X v : ℝ} (hk : k d X v = 1) :
    Real.exp (2 * X * (1 - v) + Ylow X v) = 17 * X / (2 * π) * Real.sqrt (H d X v) := by
  unfold k at hk
  have he2 : Real.exp (-(2 * X * (1 - v))) * Real.exp (-(X * (1 - v) ^ 2 / v)) *
      Real.exp (2 * X * (1 - v) + Ylow X v) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_eq_one_iff]
    unfold Ylow
    ring
  calc Real.exp (2 * X * (1 - v) + Ylow X v)
      = (17 * X / (2 * π) * Real.sqrt (H d X v) * Real.exp (-(2 * X * (1 - v))) *
          Real.exp (-(X * (1 - v) ^ 2 / v))) * Real.exp (2 * X * (1 - v) + Ylow X v) := by
        rw [hk, one_mul]
    _ = 17 * X / (2 * π) * Real.sqrt (H d X v) *
          (Real.exp (-(2 * X * (1 - v))) * Real.exp (-(X * (1 - v) ^ 2 / v)) *
            Real.exp (2 * X * (1 - v) + Ylow X v)) := by ring
    _ = 17 * X / (2 * π) * Real.sqrt (H d X v) := by rw [he2, mul_one]


/-- **Schoenfeld (7.21) for `m = 2`:** if `k(v) = 1` then `δ · T₂ = 2√(G₁/G₀)`. -/
theorem delta_mul_split_height {d X v : ℝ} (hX : 0 < X) (h0 : 0 < G0 d X v)
    (h1 : 0 < G1 d X v) (hk : k d X v = 1) :
    delta d X v * (17 * Real.exp (v * X)) = 2 * Real.sqrt (G1 d X v / G0 d X v) := by
  have hE := exp_eq_of_k_eq_one hk
  have hH : 0 < H d X v := by unfold H; positivity
  have hsH : 0 < Real.sqrt (H d X v) := Real.sqrt_pos.mpr hH
  have hdel := delta_pos hX h0 h1
  -- Both sides are positive; compare squares.
  have hL : 0 ≤ delta d X v * (17 * Real.exp (v * X)) := by positivity
  have hR : 0 ≤ 2 * Real.sqrt (G1 d X v / G0 d X v) := by positivity
  rw [← Real.sqrt_sq hL, ← Real.sqrt_sq hR]
  congr 1
  -- `(δT₂)² = 289·(2/(17π))·X·√(G₀G₁)·e^{−(Y + 2X(1−v))}`.
  have hsq : (delta d X v * (17 * Real.exp (v * X))) ^ 2 =
      289 * (2 / (17 * π)) * X * Real.sqrt (G0 d X v * G1 d X v) *
        (Real.exp (2 * X * (1 - v) + Ylow X v))⁻¹ := by
    unfold delta
    have hs1 : Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) ^ 2 =
        Real.sqrt (G0 d X v * G1 d X v) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hs2 : Real.sqrt (2 / (17 * π)) ^ 2 = 2 / (17 * π) := Real.sq_sqrt (by positivity)
    have hs3 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
    have hexp : (Real.exp (-(Ylow X v / 2)) * Real.exp (-X) * Real.exp (v * X)) ^ 2 =
        (Real.exp (2 * X * (1 - v) + Ylow X v))⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    calc (Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) * Real.exp (-(Ylow X v / 2)) *
          Real.sqrt (2 / (17 * π)) * Real.sqrt X * Real.exp (-X) * (17 * Real.exp (v * X))) ^ 2
        = 289 * Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) ^ 2 * Real.sqrt (2 / (17 * π)) ^ 2 *
            Real.sqrt X ^ 2 *
            (Real.exp (-(Ylow X v / 2)) * Real.exp (-X) * Real.exp (v * X)) ^ 2 := by ring
      _ = 289 * (2 / (17 * π)) * X * Real.sqrt (G0 d X v * G1 d X v) *
            (Real.exp (2 * X * (1 - v) + Ylow X v))⁻¹ := by
          rw [hs1, hs2, hs3, hexp]
          ring
  rw [hsq, hE]
  -- Now `289·(2/(17π))·X·√(G₀G₁)·(2π/(17X))/√H = 4·G₁/G₀`.
  have hrhs : (2 * Real.sqrt (G1 d X v / G0 d X v)) ^ 2 = 4 * (G1 d X v / G0 d X v) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  rw [hrhs]
  have hGG : Real.sqrt (G0 d X v * G1 d X v) / Real.sqrt (H d X v) = G1 d X v / G0 d X v := by
    rw [← Real.sqrt_div' _ hH.le]
    have : G0 d X v * G1 d X v / H d X v = (G1 d X v / G0 d X v) ^ 2 := by
      unfold H
      field_simp
    rw [this, Real.sqrt_sq (by positivity)]

  have hπ : 0 < π := Real.pi_pos
  calc 289 * (2 / (17 * π)) * X * Real.sqrt (G0 d X v * G1 d X v) *
        (17 * X / (2 * π) * Real.sqrt (H d X v))⁻¹
      = 4 * (Real.sqrt (G0 d X v * G1 d X v) / Real.sqrt (H d X v)) := by
        field_simp
        ring
    _ = 4 * (G1 d X v / G0 d X v) := by rw [hGG]

/-- `δ² = √(G₀G₁) · e^{−Y} · (2/(17π)) · X · e^{−2X}` (square of (7.24a)). -/
theorem delta_sq {d X v : ℝ} (hX : 0 < X) (h0 : 0 < G0 d X v) (h1 : 0 < G1 d X v) :
    delta d X v ^ 2 = Real.sqrt (G0 d X v * G1 d X v) * Real.exp (-Ylow X v) *
      (2 / (17 * π)) * X * Real.exp (-(2 * X)) := by
  unfold delta
  have hs1 : Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) ^ 2 =
      Real.sqrt (G0 d X v * G1 d X v) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs2 : Real.sqrt (2 / (17 * π)) ^ 2 = 2 / (17 * π) := Real.sq_sqrt (by positivity)
  have hs3 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  have he1 : Real.exp (-(Ylow X v / 2)) ^ 2 = Real.exp (-Ylow X v) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have he2 : Real.exp (-X) ^ 2 = Real.exp (-(2 * X)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) * Real.exp (-(Ylow X v / 2)) *
        Real.sqrt (2 / (17 * π)) * Real.sqrt X * Real.exp (-X)) ^ 2
      = Real.sqrt (Real.sqrt (G0 d X v * G1 d X v)) ^ 2 * Real.exp (-(Ylow X v / 2)) ^ 2 *
          Real.sqrt (2 / (17 * π)) ^ 2 * Real.sqrt X ^ 2 * Real.exp (-X) ^ 2 := by ring
    _ = _ := by rw [hs1, hs2, hs3, he1, he2]

/-- **The balanced main terms** (7.21)–(7.24): with `A = X e^{−Y} e^{−2X}/(34π)` and
`k(v) = 1`, the near and far main terms add up to exactly `δ`:
`A · (G₀ T₂ + 4 G₁/(δ² T₂)) = δ`. -/
theorem main_terms_eq {d X v : ℝ} (hX : 0 < X) (h0 : 0 < G0 d X v) (h1 : 0 < G1 d X v)
    (hk : k d X v = 1) :
    X * Real.exp (-Ylow X v) * Real.exp (-(2 * X)) / (34 * π) *
      (G0 d X v * (17 * Real.exp (v * X)) +
        4 * G1 d X v / (delta d X v ^ 2 * (17 * Real.exp (v * X)))) = delta d X v := by
  set T := 17 * Real.exp (v * X) with hT
  set δ := delta d X v with hδ
  have hdel : 0 < δ := delta_pos hX h0 h1
  have hTpos : 0 < T := by positivity
  have hdT := delta_mul_split_height hX h0 h1 hk
  rw [← hT, ← hδ] at hdT
  have hr : 0 < Real.sqrt (G1 d X v / G0 d X v) := Real.sqrt_pos.mpr (by positivity)
  -- `G₀ T = 2√(G₀G₁)/δ` and `4G₁/(δ²T) = 2√(G₀G₁)/δ`.
  have hsq : Real.sqrt (G1 d X v / G0 d X v) * G0 d X v = Real.sqrt (G0 d X v * G1 d X v) := by
    have : G0 d X v * G1 d X v = (G1 d X v / G0 d X v) * G0 d X v ^ 2 := by
      field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq h0.le]
  have hsq2 : Real.sqrt (G1 d X v / G0 d X v) ^ 2 = G1 d X v / G0 d X v :=
    Real.sq_sqrt (by positivity)
  have hT' : T = 2 * Real.sqrt (G1 d X v / G0 d X v) / δ := by
    field_simp
    linarith
  have hD := delta_sq hX h0 h1
  rw [← hδ] at hD
  rw [hT']
  have hπ : 0 < π := Real.pi_pos
  have hsGG : 0 < Real.sqrt (G0 d X v * G1 d X v) := Real.sqrt_pos.mpr (by positivity)
  -- Reduce to the square identity `4A√(G₀G₁) = δ²`.
  have key : G0 d X v * (2 * Real.sqrt (G1 d X v / G0 d X v) / δ) +
      4 * G1 d X v / (δ ^ 2 * (2 * Real.sqrt (G1 d X v / G0 d X v) / δ)) =
      4 * Real.sqrt (G0 d X v * G1 d X v) / δ := by
    rw [← hsq]
    field_simp
    rw [hsq2]
    field_simp
    ring
  rw [key, eq_comm, ← sub_eq_zero]

  have : δ - X * Real.exp (-Ylow X v) * Real.exp (-(2 * X)) / (34 * π) *
      (4 * Real.sqrt (G0 d X v * G1 d X v) / δ) =
      (δ ^ 2 - Real.sqrt (G0 d X v * G1 d X v) * Real.exp (-Ylow X v) * (2 / (17 * π)) * X *
        Real.exp (-(2 * X))) / δ := by
    field_simp
    ring
  rw [this, hD, sub_self, zero_div]

open SchoenfeldLaplaceTails SchoenfeldZeroWeights SchoenfeldQuadraticEnvelope

/-- Closed form of the near allowance at `a = X²`, `U = T₂ = 17e^{vX}`:
`A·G₀·T₂ + 2R(T₂)e^{−Y}e^{−2X}/17`, with `A = X e^{−Y} e^{−2X}/(34π)` (cf. (7.11)). -/
theorem nearAllowance_eq {X v : ℝ} (hX : 0 < X) (hv : 0 < v) :
    nearAllowance (X ^ 2) (17 * Real.exp (v * X)) =
      X * Real.exp (-Ylow X v) * Real.exp (-(2 * X)) / (34 * π) *
          (G0 SchoenfeldWeightedZeros.d X v * (17 * Real.exp (v * X))) +
        2 * rosserR 1.588 (17 * Real.exp (v * X)) * Real.exp (-Ylow X v) *
          Real.exp (-(2 * X)) / 17 := by
  unfold nearAllowance
  rw [log_split_height, nearPrimitive_eq hX hv, Phi_eq hX hv 0, exp_neg_X_div_v hv.ne']
  have he : (0 : ℝ) < Real.exp (v * X) := Real.exp_pos _
  simp only [zero_add, pow_one]
  field_simp
  ring

/-- Closed form of the far allowance at `a = X²`, `U = T₂`:
`(1 + 2πq(T₂))·A·G₁/T₂ + 2R(T₂)e^{−Y}e^{−2X}/(17 T₂²)` (cf. (7.18)). -/
theorem farAllowance_eq {X v : ℝ} (hX : 0 < X) (hv : 0 < v) (hv2 : 1 < 2 * v ^ 2) :
    farAllowance (X ^ 2) (17 * Real.exp (v * X)) =
      (1 + 2 * π * q (17 * Real.exp (v * X))) *
          (X * Real.exp (-Ylow X v) * Real.exp (-(2 * X)) / (34 * π)) *
          G1 SchoenfeldWeightedZeros.d X v / (17 * Real.exp (v * X)) +
        2 * rosserR 1.588 (17 * Real.exp (v * X)) * Real.exp (-Ylow X v) *
          Real.exp (-(2 * X)) / (17 * (17 * Real.exp (v * X)) ^ 2) := by
  unfold farAllowance
  rw [log_split_height, farPrimitive_eq hX hv hv2, Phi_eq hX hv 2]
  have he : (0 : ℝ) < Real.exp (v * X) := Real.exp_pos _
  have h1 : Real.exp (-(2 * v * X + X / v)) =
      Real.exp (-Ylow X v) * Real.exp (-(2 * X)) / Real.exp (v * X) := by
    rw [eq_div_iff he.ne', X_div_v_eq hv.ne', ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h1, exp_neg_X_div_v hv.ne']
  have hπ : 0 < π := Real.pi_pos
  field_simp
  ring

/-- Schoenfeld (7.20) with `m = 2`: `G₂ = R₂(δ)(1 + 2πq(T₂))/4`. -/
noncomputable def G2 (δ T : ℝ) : ℝ := QuadraticZeroKernel.R2 δ * (1 + 2 * π * q T) / 4

theorem R2_ge {δ : ℝ} (hδ : 0 ≤ δ) : 4 * (1 + δ) ≤ QuadraticZeroKernel.R2 δ := by
  unfold QuadraticZeroKernel.R2
  have h3 : 2 + 3 * δ ≤ (1 + δ) ^ 3 + 1 := by
    nlinarith [sq_nonneg δ, mul_nonneg hδ (sq_nonneg δ)]
  have h4 : (2 + 3 * δ) ^ 2 ≤ ((1 + δ) ^ 3 + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h3 2
  nlinarith

/-- **Analogue of (7.26)** for the exact allowances: with `k(v) = 1` and `δ` from (7.24a),
the weighted near and far allowances are at most `G₂δ` plus the boundary term
`(2R(T₂)e^{−Y}e^{−2X}/17)·G₂(1 + G₀/G₁)`. -/
theorem allowances_le {X v : ℝ} (hX : 0 < X) (hv : 0 < v) (hv2 : 1 < 2 * v ^ 2)
    (h0 : 0 < G0 SchoenfeldWeightedZeros.d X v) (h1 : 0 < G1 SchoenfeldWeightedZeros.d X v)
    (hk : k SchoenfeldWeightedZeros.d X v = 1) (hq : 0 ≤ q (17 * Real.exp (v * X)))
    (hR : 0 ≤ rosserR 1.588 (17 * Real.exp (v * X))) :
    (1 + delta SchoenfeldWeightedZeros.d X v) * nearAllowance (X ^ 2) (17 * Real.exp (v * X)) +
      QuadraticZeroKernel.R2 (delta SchoenfeldWeightedZeros.d X v) /
          delta SchoenfeldWeightedZeros.d X v ^ 2 *
        farAllowance (X ^ 2) (17 * Real.exp (v * X)) ≤
      G2 (delta SchoenfeldWeightedZeros.d X v) (17 * Real.exp (v * X)) *
          delta SchoenfeldWeightedZeros.d X v +
        2 * rosserR 1.588 (17 * Real.exp (v * X)) * Real.exp (-Ylow X v) *
            Real.exp (-(2 * X)) / 17 *
          (G2 (delta SchoenfeldWeightedZeros.d X v) (17 * Real.exp (v * X)) *
            (1 + G0 SchoenfeldWeightedZeros.d X v / G1 SchoenfeldWeightedZeros.d X v)) := by
  rw [nearAllowance_eq hX hv, farAllowance_eq hX hv hv2]
  have hmain := main_terms_eq hX h0 h1 hk
  have hdT := delta_mul_split_height hX h0 h1 hk
  set T := 17 * Real.exp (v * X) with hT
  set δ := delta SchoenfeldWeightedZeros.d X v with hδ
  set g0 := G0 SchoenfeldWeightedZeros.d X v
  set g1 := G1 SchoenfeldWeightedZeros.d X v
  set A := X * Real.exp (-Ylow X v) * Real.exp (-(2 * X)) / (34 * π) with hA
  set B := 2 * rosserR 1.588 T * Real.exp (-Ylow X v) * Real.exp (-(2 * X)) / 17 with hB
  set r := QuadraticZeroKernel.R2 δ with hr
  have hdel : 0 < δ := delta_pos hX h0 h1
  have hTpos : 0 < T := by positivity
  have hApos : 0 < A := by positivity
  have hBnn : 0 ≤ B := by positivity
  have hr4 : 4 * (1 + δ) ≤ r := R2_ge hdel.le
  have hg2 : G2 δ T = r * (1 + 2 * π * q T) / 4 := rfl
  have hr_le : r / 4 ≤ G2 δ T := by
    rw [hg2]
    have : 0 ≤ r * (2 * π * q T) := by
      have : 0 ≤ r := by linarith
      positivity
    linarith
  have h1d : 1 + δ ≤ G2 δ T := by linarith
  -- `δ²T² = 4 g1/g0`.
  have hdT2 : δ ^ 2 * T ^ 2 = 4 * (g1 / g0) := by
    have hs : Real.sqrt (g1 / g0) ^ 2 = g1 / g0 := Real.sq_sqrt (by positivity)
    calc δ ^ 2 * T ^ 2 = (δ * T) ^ 2 := by ring
      _ = (2 * Real.sqrt (g1 / g0)) ^ 2 := by rw [hdT]
      _ = 4 * Real.sqrt (g1 / g0) ^ 2 := by ring
      _ = 4 * (g1 / g0) := by rw [hs]


  -- Main terms.
  have hmain' : (1 + δ) * (A * (g0 * T)) + r / δ ^ 2 * ((1 + 2 * π * q T) * A * g1 / T) ≤
      G2 δ T * δ := by
    have e : r / δ ^ 2 * ((1 + 2 * π * q T) * A * g1 / T) = G2 δ T * (A * (4 * g1 / (δ ^ 2 * T))) := by
      rw [hg2]
      field_simp
    rw [e]

    have hle : (1 + δ) * (A * (g0 * T)) ≤ G2 δ T * (A * (g0 * T)) :=
      mul_le_mul_of_nonneg_right h1d (by positivity)
    calc (1 + δ) * (A * (g0 * T)) + G2 δ T * (A * (4 * g1 / (δ ^ 2 * T)))
        ≤ G2 δ T * (A * (g0 * T)) + G2 δ T * (A * (4 * g1 / (δ ^ 2 * T))) := by linarith
      _ = G2 δ T * (A * (g0 * T + 4 * g1 / (δ ^ 2 * T))) := by ring
      _ = G2 δ T * δ := by rw [hmain]
  -- Boundary terms.
  have hbd : (1 + δ) * B + r / δ ^ 2 * (B / T ^ 2) ≤ B * (G2 δ T * (1 + g0 / g1)) := by
    have e : r / δ ^ 2 * (B / T ^ 2) = B * (r / 4 * (g0 / g1)) := by
      have hx : δ ^ 2 * T ^ 2 ≠ 0 := by positivity
      rw [div_mul_div_comm, hdT2]
      field_simp

    rw [e]
    have hg : 0 ≤ g0 / g1 := by positivity
    have h2 : r / 4 * (g0 / g1) ≤ G2 δ T * (g0 / g1) := mul_le_mul_of_nonneg_right hr_le hg
    have h3 : (1 + δ) * B ≤ G2 δ T * B := mul_le_mul_of_nonneg_right h1d hBnn
    nlinarith [mul_le_mul_of_nonneg_left h2 hBnn]
  have e2 : 2 * rosserR 1.588 T * Real.exp (-Ylow X v) * Real.exp (-(2 * X)) /
      (17 * T ^ 2) = B / T ^ 2 := by
    rw [hB]
    field_simp
  rw [e2]
  nlinarith [hmain', hbd]

end TernaryGoldbach.RSBounds.SchoenfeldBalanceMain


