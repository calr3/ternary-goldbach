import TernaryGoldbach.MinorArcs.TypeIITotal

/-!
# Type II total, general form [B, §6.2.3]

`typeII_gen`: if `S₂ ≤ (m x/(φ L) + (q/φ) W/L) Σ(log p)²` with `L = log(W/c)` on `[V, x/U]`, then
`|S_{II}| ≤ 4x√(m/2φ) √(A B) + …` with `A = log(x/UV) + log c (log log(x/Uc) - log log(V/c))`,
`B = 0.15107 log(x/UV) + 2κ₀ζ³√(x/V)/U`. Instances: (6.37) (`c = 2q`, `m = 1/4`, from (5.54)) and
(6.40) (`c = |δ|q(1+ε₁)/4`, `m = 2/|δ|`, from (5.56)).
-/

open Real Finset MeasureTheory

namespace TernaryGoldbach.MinorArcs

/-- The integrand `G(W)` of our version of [B, (6.20)–(6.37)] (`W·G(W)` bounds
`√S₁ (√S₂ + √S₃)` for `q ≤ V/2e`). -/
noncomputable def Ggen (x U V : ℝ) (q : ℕ) (c m β W : ℝ) : ℝ :=
  x * √(m / (2 * Nat.totient q)) * β / 2 * (1 / W) +
    x * √(m / (2 * Nat.totient q)) * β / 2 * Real.log c * (1 / (W * Real.log (W / c))) +
    x * √(m / (2 * Nat.totient q)) / (2 * β) * (H2 (x / (W * U)) / W) +
    x * √(m / (2 * Nat.totient q)) / (2 * β) * (zeta3 * √x / U) * (1 / (W * √W)) +
    √(kap1 x U V * q * x / (2 * Nat.totient q)) * (√W / W) +
    √(kap1 x U V * q * x / (2 * Nat.totient q)) * √(Real.log c) *
      (√W / (W * √(Real.log (W / c)))) +
    1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (1 / (W * √W))

set_option maxHeartbeats 2000000 in
/-- The pointwise bound behind [B, (6.20)–(6.37)] in the range `W ≥ V ≥ 2eq`. -/
theorem pointwise_gen' {α x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (117 : ℝ) ≤ V) {A : ℝ} (hVA : (V : ℝ) ≤ A) {c m : ℝ} (hc1 : 1 ≤ c) (hm : 0 < m)
    (hcV : c * rexp 1 ≤ A)
    (hS2gen : ∀ W ∈ Set.Icc A (x / U), S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (m * x / (Nat.totient q * Real.log (W / c)) + q / Nat.totient q * (W / Real.log (W / c))) *
        logSqSum (max V (W / 2)) W)
    {β : ℝ} (hβ : 0 < β) {W : ℝ} (hW : W ∈ Set.Icc A (x / U)) :
    √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
      √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ W * Ggen x U V q c m β W := by
  obtain ⟨hAW, hWx⟩ := hW
  have hVW : (V : ℝ) ≤ W := hVA.trans hAW
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  have hW0 : 0 < W := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hc0 : 0 < c := by linarith
  have h2qW : c * rexp 1 ≤ W := by linarith
  have hL1 : 1 ≤ Real.log (W / c) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]; linarith
  set L := Real.log (W / c)
  have hlogW : Real.log W = L + Real.log c := by
    simp only [L]; rw [Real.log_div hW0.ne' (by positivity)]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hl2q : 0 ≤ Real.log c := Real.log_nonneg hc1
  -- `S₁ ≤ (x/W) h`, `0 ≤ h ≤ κ₁`.
  set h := H2 (x / (W * U)) + zeta3 * √(x / W) / U
  have hS1 : S1 x U W ≤ x / W * h := by
    refine (S1_bound hx hW0 hU1).trans (le_of_eq ?_)
    simp only [h, zeta3]
    rw [rpow_three_halves _ hx.le, rpow_three_halves _ hW0.le, Real.sqrt_div' _ hW0.le]
    have : 0 < √W := Real.sqrt_pos.2 hW0
    field_simp
  have hh0 : 0 ≤ h := by
    have := H2_nonneg (x / (W * U)); have := zeta3_nonneg; positivity
  have hhk : h ≤ kap1 x U V := by
    simp only [h, kap1]
    have h1 := H2_le (x / (W * U))
    have h2 : √(x / W) ≤ √(x / V) := Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_left hx.le (by linarith) hVW)
    have := zeta3_nonneg
    have : zeta3 * √(x / W) / U ≤ zeta3 * √(x / V) / U := by gcongr
    linarith
  -- `S₂ ≤ P + R`.
  have hW'1 : W / 2 ≤ max (V : ℝ) (W / 2) := le_max_right _ _
  have hW'2 : max (V : ℝ) (W / 2) ≤ W := max_le hVW (by linarith)
  have hS2 := hS2gen W ⟨hAW, hWx⟩
  have hlog := logSqSum_le_half (by linarith) hW'1 (W := W)
  set P := m * x / (Nat.totient q * L) * (1 / 2 * W * Real.log W)
  set R := q / Nat.totient q * (W / L) * (1 / 2 * W * Real.log W)
  have hlW : 0 ≤ Real.log W := by linarith
  have hP0 : 0 ≤ P := by positivity
  have hR0 : 0 ≤ R := by positivity
  have hS2' : S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤ P + R := by
    refine hS2.trans ?_
    simp only [P, R]
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  set κ := kap1 x U V
  have hκ0 : 0 ≤ κ := hh0.trans hhk
  set a := √(x / W * h)
  set S3 := (x / (2 * W) + 1) * (1.4262 ^ 2 * W)
  have hsqrt_add : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → √(u + v) ≤ √u + √v := fun u v hu hv => by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv, Real.sqrt_nonneg u, Real.sqrt_nonneg v,
      mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)]
  have hL0 : 0 < L := by linarith
  have hsW : 0 < √W := Real.sqrt_pos.2 hW0
  have hsL : 0 < √L := Real.sqrt_pos.2 hL0
  -- T1: the main term, by AM-GM.
  have T1 : a * √P ≤ x * √(m / (2 * Nat.totient q)) *
      ((β * (1 + Real.log c / L) + h / β) / 2) := by
    have e1 : x / W * h * P = (x * √(m / (2 * Nat.totient q))) ^ 2 *
        ((β * (1 + Real.log c / L)) * (h / β)) := by
      simp only [P]
      rw [mul_pow, Real.sq_sqrt (by positivity), hlogW]
      field_simp; try ring
    rw [← Real.sqrt_mul (by positivity), e1, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    gcongr
    exact sqrt_le_amgm (by positivity) (by positivity)
  -- T2.
  have T2 : a * √R ≤ √(κ * q * x / (2 * Nat.totient q)) * √W *
      (1 + √(Real.log c) / √L) := by
    have ha : a ≤ √(κ * x / W) := Real.sqrt_le_sqrt (by
      rw [show κ * x / W = x / W * κ by ring]; exact mul_le_mul_of_nonneg_left hhk (by positivity))
    have e2 : κ * x / W * R = κ * q * x / (2 * Nat.totient q) * (W * (1 + Real.log c / L)) := by
      simp only [R]; rw [hlogW]; field_simp; try ring
    calc a * √R ≤ √(κ * x / W) * √R := mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)
      _ = √(κ * q * x / (2 * Nat.totient q)) * √W * √(1 + Real.log c / L) := by
          rw [← Real.sqrt_mul (by positivity), e2, Real.sqrt_mul (by positivity),
            Real.sqrt_mul hW0.le]; ring
      _ ≤ _ := by
          gcongr
          refine (sqrt_one_add_le (by positivity)).trans (le_of_eq ?_)
          rw [Real.sqrt_div' _ hL0.le]
  -- T3.
  have T3 : a * √S3 ≤ 1.4262 * x * √(κ * (1 / 2 + 1 / U)) / √W := by
    have ha : a ≤ √(κ * x / W) := Real.sqrt_le_sqrt (by
      rw [show κ * x / W = x / W * κ by ring]; exact mul_le_mul_of_nonneg_left hhk (by positivity))
    have hS3 : κ * x / W * S3 ≤ (1.4262 * x * √(κ * (1 / 2 + 1 / U)) / √W) ^ 2 := by
      have hl : κ * x / W * S3 = 1.4262 ^ 2 * κ * x * (x / 2 + W) / W := by
        simp only [S3]; field_simp; try ring
      rw [hl, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hW0.le]
      apply div_le_div_of_nonneg_right _ hW0.le
      have hWU : W ≤ x * (1 / U) := by rw [mul_one_div]; exact hWx
      have h1 : κ * x * W ≤ κ * x * (x * (1 / U)) := mul_le_mul_of_nonneg_left hWU (by positivity)
      nlinarith
    calc a * √S3 ≤ √(κ * x / W) * √S3 := mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)
      _ = √(κ * x / W * S3) := (Real.sqrt_mul (by positivity) _).symm
      _ ≤ _ := Real.sqrt_le_left (by positivity) |>.2 hS3
  -- Assemble.
  have hS1' : √(S1 x U W) ≤ a := Real.sqrt_le_sqrt hS1
  have hS2'' : √(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) ≤ √P + √R :=
    (Real.sqrt_le_sqrt hS2').trans (hsqrt_add P R hP0 hR0)
  have hfin : W * Ggen x U V q c m β W = x * √(m / (2 * Nat.totient q)) *
      ((β * (1 + Real.log c / L) + h / β) / 2) +
      √(κ * q * x / (2 * Nat.totient q)) * √W * (1 + √(Real.log c) / √L) +
      1.4262 * x * √(κ * (1 / 2 + 1 / U)) / √W := by
    simp only [Ggen, h, κ, L]
    rw [Real.sqrt_div' _ hW0.le]
    generalize √(m / (2 * (Nat.totient q : ℝ))) = s8 at *
    generalize √(kap1 x U V * q * x / (2 * Nat.totient q)) = s3 at *
    generalize √(kap1 x U V * (1 / 2 + 1 / U)) = s4 at *
    generalize √(Real.log (W / c)) = sL at *
    generalize H2 (x / (W * U)) = HH at *
    field_simp
    ring
  rw [hfin]
  calc √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) + √S3)
      ≤ a * (√P + √R + √S3) := by
        gcongr
    _ = a * √P + a * √R + a * √S3 := by ring
    _ ≤ _ := by linarith


set_option maxHeartbeats 2000000 in
/-- Integrating `Ggen` over `[A, x/U]` (`V ≤ A` enters only through `κ₁ = kap1 x U V`). -/
theorem integral_Ggen_le' {x : ℝ} (hx : 0 < x) {U V : ℕ} {q : ℕ} (hq : 1 ≤ q) (hU : 1 ≤ U)
    {A : ℝ} (hV : 0 < A) (hVU : A ≤ x / U) {c m : ℝ} (hc1 : 1 ≤ c) (hm : 0 < m)
    (hcV : c * rexp 1 ≤ A) {β : ℝ} (hβ : 0 < β) :
    IntervalIntegrable (Ggen x U V q c m β) volume A (x / U) ∧
    ∫ W in A..x / U, Ggen x U V q c m β W ≤
      x * √(m / (2 * Nat.totient q)) * β / 2 * (Real.log (x / (U * A)) + Real.log c *
        (Real.log (Real.log (x / U / c)) - Real.log (Real.log (A / c)))) +
      x * √(m / (2 * Nat.totient q)) / (2 * β) *
        (0.15107 * Real.log (x / (U * A)) + 0.0231 + 2 * zeta3 * √(x / A) / U) +
      √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log c) *
        (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) +
      1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (2 / √A) := by
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hc0 : 0 < c := by linarith
  have h2q : c < A := by nlinarith
  have hpos : ∀ W ∈ Set.uIcc A (x / U), 0 < W := fun W hW => by
    rw [Set.uIcc_of_le hVU] at hW; exact lt_of_lt_of_le hV hW.1
  have hLpos : ∀ W ∈ Set.uIcc A (x / U), 0 < Real.log (W / c) := fun W hW => by
    rw [Set.uIcc_of_le hVU] at hW
    exact Real.log_pos (by rw [one_lt_div (by positivity)]; linarith [hW.1])
  set c1 := x * √(m / (2 * Nat.totient q)) * β / 2
  set c2 := x * √(m / (2 * Nat.totient q)) / (2 * β)
  set c3 := √(kap1 x U V * q * x / (2 * Nat.totient q))
  set c4 := 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U))
  -- The seven pieces.
  set f1 : ℝ → ℝ := fun W => 1 / W
  set f2 : ℝ → ℝ := fun W => 1 / (W * Real.log (W / c))
  set f3 : ℝ → ℝ := fun W => H2 (x / (W * U)) / W
  set f4 : ℝ → ℝ := fun W => 1 / (W * √W)
  set f5 : ℝ → ℝ := fun W => √W / W
  set f6 : ℝ → ℝ := fun W => √W / (W * √(Real.log (W / c)))
  have hcl : ContinuousOn (fun W => Real.log (W / c)) (Set.uIcc A (x / U)) :=
    ContinuousOn.log (continuousOn_id.div_const _) fun W hW => (div_pos (hpos W hW) (by positivity)).ne'
  have hsq : ContinuousOn (fun W : ℝ => √W) (Set.uIcc A (x / U)) :=
    Real.continuous_sqrt.continuousOn
  have i1 : IntervalIntegrable f1 volume A (x / U) := ContinuousOn.intervalIntegrable
    (continuousOn_const.div continuousOn_id fun W hW => (hpos W hW).ne')
  have i2 : IntervalIntegrable f2 volume A (x / U) := ContinuousOn.intervalIntegrable
    (continuousOn_const.div (continuousOn_id.mul hcl) fun W hW =>
      (mul_pos (hpos W hW) (hLpos W hW)).ne')
  obtain ⟨i3, I3⟩ := integral_H2_comp hx hU0 hV hVU
  have i4 : IntervalIntegrable f4 volume A (x / U) := ContinuousOn.intervalIntegrable
    (continuousOn_const.div (continuousOn_id.mul hsq) fun W hW =>
      (mul_pos (hpos W hW) (Real.sqrt_pos.2 (hpos W hW))).ne')
  have i5 : IntervalIntegrable f5 volume A (x / U) := ContinuousOn.intervalIntegrable
    (hsq.div continuousOn_id fun W hW => (hpos W hW).ne')
  have i6 : IntervalIntegrable f6 volume A (x / U) := ContinuousOn.intervalIntegrable
    (hsq.div (continuousOn_id.mul (Real.continuous_sqrt.comp_continuousOn hcl)) fun W hW =>
      (mul_pos (hpos W hW) (Real.sqrt_pos.2 (hLpos W hW))).ne')
  have hG : Ggen x U V q c m β = fun W => c1 * f1 W + c1 * Real.log c * f2 W + c2 * f3 W +
      c2 * (zeta3 * √x / U) * f4 W + c3 * f5 W + c3 * √(Real.log c) * f6 W + c4 * f4 W := by
    ext W; rfl
  have i3' : IntervalIntegrable f3 volume A (x / U) := i3
  have I3' : ∫ W in A..x / U, f3 W ≤ 0.15107 * Real.log (x / (U * A)) + 0.0231 := I3
  have p1 := (i1.const_mul c1).add (i2.const_mul (c1 * Real.log c))
  have p2 := p1.add (i3'.const_mul c2)
  have p3 := p2.add (i4.const_mul (c2 * (zeta3 * √x / U)))
  have p4 := p3.add (i5.const_mul c3)
  have p5 := p4.add (i6.const_mul (c3 * √(Real.log c)))
  have iG : IntervalIntegrable (Ggen x U V q c m β) volume A (x / U) := by
    rw [hG]; exact p5.add (i4.const_mul c4)
  refine ⟨iG, ?_⟩
  -- Evaluate / bound each piece.
  have J1 : ∫ W in A..x / U, f1 W = Real.log (x / (U * A)) := by
    rw [integral_one_div_of_pos hV (by positivity), div_div, mul_comm (U : ℝ)]
  have J2 : ∫ W in A..x / U, f2 W =
      Real.log (Real.log (x / U / c)) - Real.log (Real.log (A / c)) :=
    integral_inv_mul_log (by positivity) h2q hVU
  have J4 : ∫ W in A..x / U, f4 W ≤ 2 / √A := integral_inv_mul_sqrt_le hV hVU
  have J5 : ∫ W in A..x / U, f5 W ≤ 2 * √(x / U) := by
    rw [intervalIntegral.integral_congr (g := fun W => 1 / √W) fun W hW => by
      have h0 := hpos W hW
      simp only [f5]; rw [div_eq_div_iff h0.ne' (Real.sqrt_pos.2 h0).ne', one_mul,
        Real.mul_self_sqrt h0.le], integral_inv_sqrt hV hVU]
    have := Real.sqrt_nonneg A; linarith
  have J6 : ∫ W in A..x / U, f6 W ≤
      2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)) := by
    rw [intervalIntegral.integral_congr (g := fun W => 1 / (√W * √(Real.log (W / c))))
      fun W hW => by
        have h0 := hpos W hW
        have h1 := Real.sqrt_pos.2 (hLpos W hW)
        simp only [f6]
        rw [div_eq_div_iff (by positivity) (by positivity), one_mul,
          ← mul_assoc, Real.mul_self_sqrt h0.le]]
    exact integral_inv_sqrt_log_le hc0 hcV hVU
  rw [hG]
  rw [intervalIntegral.integral_add p5 (i4.const_mul c4), intervalIntegral.integral_add p4
    (i6.const_mul _), intervalIntegral.integral_add p3 (i5.const_mul c3),
    intervalIntegral.integral_add p2 (i4.const_mul _), intervalIntegral.integral_add p1
    (i3'.const_mul c2), intervalIntegral.integral_add (i1.const_mul c1) (i2.const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [J1, J2]
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := Real.sqrt_nonneg _
  have hc4 : 0 ≤ c4 := by have := Real.sqrt_nonneg (kap1 x U V * (1 / 2 + 1 / U)); positivity
  have hz : 0 ≤ zeta3 * √x / U := by have := zeta3_nonneg; positivity
  have e4 : zeta3 * √x / U * (2 / √A) = 2 * zeta3 * √(x / A) / U := by
    rw [Real.sqrt_div' _ hV.le]; ring
  have K3 := mul_le_mul_of_nonneg_left I3' hc2
  have K4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left J4 hz) hc2
  have K5 := mul_le_mul_of_nonneg_left J5 hc3
  have K6 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left J6 (Real.sqrt_nonneg
    (Real.log c))) hc3
  have K7 := mul_le_mul_of_nonneg_left J4 hc4
  rw [e4] at K4
  nlinarith [K3, K4, K5, K6, K7]


/-- `integral_Ggen_le'` with `A = V`. -/
theorem integral_Ggen_le {x : ℝ} (hx : 0 < x) {U V : ℕ} {q : ℕ} (hq : 1 ≤ q) (hU : 1 ≤ U)
    (hV : 0 < (V : ℝ)) (hVU : (V : ℝ) ≤ x / U) {c m : ℝ} (hc1 : 1 ≤ c) (hm : 0 < m)
    (hcV : c * rexp 1 ≤ V) {β : ℝ} (hβ : 0 < β) :
    IntervalIntegrable (Ggen x U V q c m β) volume V (x / U) ∧
    ∫ W in (V : ℝ)..x / U, Ggen x U V q c m β W ≤
      x * √(m / (2 * Nat.totient q)) * β / 2 * (Real.log (x / (U * V)) + Real.log c *
        (Real.log (Real.log (x / U / c)) - Real.log (Real.log (V / c)))) +
      x * √(m / (2 * Nat.totient q)) / (2 * β) *
        (0.15107 * Real.log (x / (U * V)) + 0.0231 + 2 * zeta3 * √(x / V) / U) +
      √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log c) *
        (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) +
      1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (2 / √V) :=
  integral_Ggen_le' hx hq hU hV hVU hc1 hm hcV hβ

/-- `pointwise_gen'` with `A = V`. -/
theorem pointwise_gen {α x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (117 : ℝ) ≤ V) {c m : ℝ} (hc1 : 1 ≤ c) (hm : 0 < m) (hcV : c * rexp 1 ≤ V)
    (hS2gen : ∀ W ∈ Set.Icc (V : ℝ) (x / U), S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (m * x / (Nat.totient q * Real.log (W / c)) + q / Nat.totient q * (W / Real.log (W / c))) *
        logSqSum (max V (W / 2)) W)
    {β : ℝ} (hβ : 0 < β) {W : ℝ} (hW : W ∈ Set.Icc (V : ℝ) (x / U)) :
    √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
      √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ W * Ggen x U V q c m β W :=
  pointwise_gen' hq hx hU hV le_rfl hc1 hm hcV hS2gen hβ hW

set_option maxHeartbeats 2000000 in
/-- **Type II total, general form** (see the module docstring). -/
theorem typeII_gen {α x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (117 : ℝ) ≤ V) (hVU : (V : ℝ) ≤ x / U) {c m : ℝ} (hc1 : 1 ≤ c) (hm : 0 < m)
    (hcV : c * rexp 1 ≤ V)
    (hS2gen : ∀ W ∈ Set.Icc (V : ℝ) (x / U), S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (m * x / (Nat.totient q * Real.log (W / c)) + q / Nat.totient q * (W / Real.log (W / c))) *
        logSqSum (max V (W / 2)) W) :
    ‖typeII α x U V‖ ≤
      4 * x * √(m / (2 * Nat.totient q)) * √((Real.log (x / (U * V)) + Real.log c *
        (Real.log (Real.log (x / U / c)) - Real.log (Real.log (V / c)))) *
        (0.15107 * Real.log (x / (U * V)) + 0.0231 + 2 * zeta3 * √(x / V) / U)) +
      4 * √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log c) *
        (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) +
      8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  have hV0 : (0 : ℝ) < V := by linarith
  have hV2 : 2 ≤ V := by exact_mod_cast (show (2 : ℝ) ≤ V by linarith)
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hc0 : 0 < c := by linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hκ : 0 ≤ kap1 x U V := by unfold kap1; have := zeta3_nonneg; positivity
  have hζ := zeta3_nonneg
  set φ := (Nat.totient q : ℝ)
  set Λ₀ := Real.log (x / (U * V))
  set Φ := Real.log c * (Real.log (Real.log (x / U / c)) - Real.log (Real.log (V / c)))
  set B := 0.15107 * Λ₀ + 0.0231 + 2 * zeta3 * √(x / V) / U
  have hRHS3 : 0 ≤ 8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by positivity
  have hRHS2 : 0 ≤ 4 * √(kap1 x U V * q * x / (2 * φ)) * (2 * √(x / U) + √(Real.log c) *
      (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) := by positivity
  have hRHS1 : 0 ≤ 4 * x * √(m / (2 * φ)) * √((Λ₀ + Φ) * B) := by positivity
  rcases hVU.lt_or_eq with hlt | heq
  swap
  · have hint : IntervalIntegrable (Ggen x U V q c m 1) volume V (x / U) := by
      first | (rw [← heq]; done) | (rw [← heq]; exact IntervalIntegrable.refl)
    have h := norm_typeII_le' α hx hU hV2 hVU hint (fun W hW =>
      pointwise_gen hq hx hU hV hc1 hm hcV hS2gen one_pos hW)
    rw [← heq, intervalIntegral.integral_same, mul_zero] at h
    linarith
  have hΛ : 0 < Λ₀ := Real.log_pos (by
    rw [lt_div_iff₀ (by positivity)]; rw [lt_div_iff₀ hU0] at hlt; linarith)
  have hL1 : 1 ≤ Real.log (V / c) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hc0]; linarith
  have hΦ : 0 ≤ Φ := by
    refine mul_nonneg hlc (sub_nonneg.2 (Real.log_le_log (by linarith)
      (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hVU hc0.le))))
  set A := Λ₀ + Φ
  have hA : 0 < A := by linarith
  have hB : 0 < B := by positivity
  set β := √(B / A)
  have hβ : 0 < β := Real.sqrt_pos.2 (div_pos hB hA)
  obtain ⟨iG, IG⟩ := integral_Ggen_le hx hq hU hV0 hVU hc1 hm hcV hβ
  have h := norm_typeII_le' α hx hU hV2 hVU iG (fun W hW =>
    pointwise_gen hq hx hU hV hc1 hm hcV hS2gen hβ hW)
  refine h.trans ((mul_le_mul_of_nonneg_left IG (by norm_num)).trans (le_of_eq ?_))
  have hsA : 0 < √A := Real.sqrt_pos.2 hA
  have hsB : 0 < √B := Real.sqrt_pos.2 hB
  have hβe : β = √B / √A := Real.sqrt_div' _ hA.le
  rw [hβe, Real.sqrt_mul hA.le]
  have hAA : √A * √A = A := Real.mul_self_sqrt hA.le
  have hBB : √B * √B = B := Real.mul_self_sqrt hB.le
  have balance : ∀ K a b : ℝ, 0 < a → 0 < b →
      4 * (K * (b / a) / 2 * (a * a) + K / (2 * (b / a)) * (b * b)) = 4 * K * (a * b) := by
    intro K a b ha hb; field_simp; ring
  have hbal := balance (x * √(m / (2 * φ))) (√A) (√B) hsA hsB
  rw [hAA, hBB] at hbal
  linear_combination hbal


set_option maxHeartbeats 2000000 in
/-- The bound on `S₂` from (5.56)(ii) used for [B, (6.32)]: with `ε₁ = x/2UQ`,
`c' = |δ|q(1+ε₁)/4`, `L = log(W/c')`, for `|δ| ≥ 8`, `x ≤ Q²`, `W ∈ [V, x/U]`, `c'e ≤ V`:
`S₂ ≤ ((2/|δ|) x/(φL) + (q/φ) W/L) Σ(log p)²`. -/
theorem S2_le_640' {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (h2α : 2 * α = a / q + δ / x + k) (hδQ : |δ / x| ≤ 1 / (q * Q)) (hδ8 : 8 ≤ |δ|) (hx : 0 < x)
    (hQx : x ≤ Q ^ 2) {U V : ℕ} (hU : 1 ≤ U) {A : ℝ} (hVA : (V : ℝ) ≤ A)
    (hcV : |δ| * q * (1 + x / (2 * U * Q)) / 4 * rexp 1 ≤ A)
    {W : ℝ} (hW : W ∈ Set.Icc A (x / U)) :
    S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (2 / |δ| * x / (Nat.totient q * Real.log (W / (|δ| * q * (1 + x / (2 * U * Q)) / 4))) +
        q / Nat.totient q * (W / Real.log (W / (|δ| * q * (1 + x / (2 * U * Q)) / 4)))) *
        logSqSum (max V (W / 2)) W := by
  obtain ⟨hAW, hWx⟩ := hW
  have hVW : (V : ℝ) ≤ W := hVA.trans hAW
  replace hcV := hcV.trans hAW
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hδ0 : δ ≠ 0 := by intro h; rw [h, abs_zero] at hδ8; linarith
  have hδp : 0 < |δ| := by linarith
  -- `|δ| q Q ≤ x`, `q ≤ x/8Q ≤ Q/8`.
  have hQ0 : 0 < Q := by
    by_contra hQ; push Not at hQ
    have : 1 / (q * Q) ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one
      (mul_nonpos_of_nonneg_of_nonpos hq0.le hQ)
    have : |δ / x| ≤ 0 := hδQ.trans this
    rw [abs_div, abs_of_pos hx] at this
    have : 0 < |δ| / x := by positivity
    linarith
  have hδqQ : |δ| * q * Q ≤ x := by
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity)] at hδQ; linarith
  have hq8 : q * (8 * Q) ≤ x := by nlinarith
  have hqQ : 8 * q ≤ Q := by
    by_contra h; push Not at h
    nlinarith
  set ε₁ := x / (2 * U * Q)
  have hε : 0 ≤ ε₁ := by positivity
  set c := |δ| * q * (1 + ε₁) / 4
  have hc2 : 2 ≤ c := by
    simp only [c]
    have : 8 * 1 * 1 ≤ |δ| * q * (1 + ε₁) := by
      have := mul_le_mul hδ8 hq1 zero_le_one hδp.le
      nlinarith
    linarith
  have hW0 : 0 < W := by have : (0 : ℝ) < c * rexp 1 := by positivity
                         linarith
  have hcW : c ≤ W := by nlinarith
  have hδqW : |δ| * q < 2 * W := by
    have h0 : 0 ≤ |δ| * q * ε₁ := by positivity
    have : |δ| * q ≤ 4 * c := by simp only [c]; linarith
    have h2c : 2 * c < W := by nlinarith
    linarith
  -- Hypotheses of (5.56).
  have hcond : x / (4 * W) + q ≤ x / (|δ| * q) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : x / (4 * W) * (|δ| * q) ≤ x / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : q * (|δ| * q) ≤ x / 8 := by nlinarith
    nlinarith
  set R := √(W / c)
  have hR2 : R ^ 2 = W / c := Real.sq_sqrt (by positivity)
  have hR1 : 1 ≤ R := by rw [Real.one_le_sqrt, one_le_div (by positivity)]; exact hcW
  have hRW : R ≤ max (V : ℝ) (W / 2) := by
    refine le_trans ?_ (le_max_right _ _)
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
    have hW2 : 2 ≤ W := le_trans hc2 hcW
    nlinarith
  have hRcond : R ^ 2 ≤ x / (|δ| * q) / (q + x / (4 * W)) := by
    rw [hR2, div_le_div_iff₀ (by positivity) (by positivity)]
    have hqx : (q : ℝ) ≤ x / (8 * Q) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hqW : q * W ≤ x * ε₁ / 4 := by
      have := mul_le_mul hqx hWx hW0.le (by positivity)
      refine this.trans (le_of_eq ?_)
      simp only [ε₁]; field_simp; ring
    simp only [c]
    rw [show x / (|δ| * q) * (|δ| * q * (1 + ε₁) / 4) = x * (1 + ε₁) / 4 by field_simp]
    have : W * (q + x / (4 * W)) = q * W + x / 4 := by field_simp; try ring
    rw [this]; linarith
  obtain ⟨-, hii⟩ := prop_5_2_4_c hq hcop h2α hx hW0 hδ0 hcond (U' := max (U : ℝ) (x / (2 * W)))
    (le_max_right _ _) (by positivity : (0 : ℝ) ≤ max (V : ℝ) (W / 2))
  have h := hii R hR1 hRW hRcond
  set L := Real.log (W / c)
  have hL : 0 < L := Real.log_pos (by rw [one_lt_div (by positivity)]; nlinarith)
  have hlogR : Real.log R = L / 2 := by simp only [R, L]; rw [Real.log_sqrt (by positivity)]; try ring
  rw [hlogR] at h
  have hlss := logSqSum_nonneg (max (V : ℝ) (W / 2)) W
  have hWW' : W - max (V : ℝ) (W / 2) ≤ W / 2 := by have := le_max_right (V : ℝ) (W / 2); linarith
  -- `S₂ ≤ (2q/(φL)) (W/2 + x/|δ|q) Σ`.
  have key : Nat.totient q / q * (L / 2) * S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      Nat.totient q / q * (L / 2) * ((2 / |δ| * x / (Nat.totient q * L) +
        q / Nat.totient q * (W / L)) * logSqSum (max V (W / 2)) W) := by
    calc Nat.totient q / q * (L / 2) * S2 α x (max U (x / (2 * W))) (max V (W / 2)) W
        ≤ (W - max (V : ℝ) (W / 2) + x / (|δ| * q)) * logSqSum (max V (W / 2)) W := h
      _ ≤ (W / 2 + x / (|δ| * q)) * logSqSum (max V (W / 2)) W :=
          mul_le_mul_of_nonneg_right (by linarith) hlss
      _ = _ := by field_simp; ring
  exact le_of_mul_le_mul_left key (by positivity)


/-- `S2_le_640'` with `A = V`. -/
theorem S2_le_640 {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (h2α : 2 * α = a / q + δ / x + k) (hδQ : |δ / x| ≤ 1 / (q * Q)) (hδ8 : 8 ≤ |δ|) (hx : 0 < x)
    (hQx : x ≤ Q ^ 2) {U V : ℕ} (hU : 1 ≤ U)
    (hcV : |δ| * q * (1 + x / (2 * U * Q)) / 4 * rexp 1 ≤ V)
    {W : ℝ} (hW : W ∈ Set.Icc (V : ℝ) (x / U)) :
    S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (2 / |δ| * x / (Nat.totient q * Real.log (W / (|δ| * q * (1 + x / (2 * U * Q)) / 4))) +
        q / Nat.totient q * (W / Real.log (W / (|δ| * q * (1 + x / (2 * U * Q)) / 4)))) *
        logSqSum (max V (W / 2)) W :=
  S2_le_640' hq hcop h2α hδQ hδ8 hx hQx hU le_rfl hcV hW

/-- **Type II total, our version of [B, (6.40)]** (`|δ| ≥ 8`, `|δq|` small): with
`c' = |δ|q(1+ε₁)/4`, `ε₁ = x/2UQ`, `Λ₀ = log(x/UV)`, `Φ = log c' (log log(x/Uc') - log log(V/c'))`,
`|S_{II}| ≤ 2x/√(|δ|φ(q)) √((Λ₀ + Φ)(0.60428 Λ₀ + 8κ₀ζ³√(x/V)/U)) + (secondary terms)`.
Requires `c'e ≤ V` (i.e. `|δq| ≤ V/θ` with `θ = e(1+ε₁)/4`; [B] takes `θ ≥ 3e²/8`) and
`x ≤ Q²` ([B] assumes `Q ≥ 2√x`). The main term is [B]'s with `Φ` as in (6.34). -/
theorem typeII_640 {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (h2α : 2 * α = a / q + δ / x + k) (hδQ : |δ / x| ≤ 1 / (q * Q)) (hδ8 : 8 ≤ |δ|) (hx : 0 < x)
    (hQx : x ≤ Q ^ 2) {U V : ℕ} (hU : 1 ≤ U) (hV : (117 : ℝ) ≤ V) (hVU : (V : ℝ) ≤ x / U)
    (hcV : |δ| * q * (1 + x / (2 * U * Q)) / 4 * rexp 1 ≤ V) :
    let c := |δ| * q * (1 + x / (2 * U * Q)) / 4
    ‖typeII α x U V‖ ≤
      2 * x / √(|δ| * Nat.totient q) * √((Real.log (x / (U * V)) + Real.log c *
        (Real.log (Real.log (x / U / c)) - Real.log (Real.log (V / c)))) *
        (0.60428 * Real.log (x / (U * V)) + 0.0924 + 8 * zeta3 * √(x / V) / U)) +
      4 * √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log c) *
        (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) +
      8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by
  intro c
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hQ0 : 0 < Q := by
    by_contra hQ; push Not at hQ
    have hq0 : (0 : ℝ) < q := by linarith
    have : 1 / (q * Q) ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one
      (mul_nonpos_of_nonneg_of_nonpos hq0.le hQ)
    have : |δ / x| ≤ 0 := hδQ.trans this
    rw [abs_div, abs_of_pos hx] at this
    have : 0 < |δ| / x := div_pos (by linarith) hx
    linarith
  have hc1 : 1 ≤ c := by
    have h0 : 0 ≤ x / (2 * U * Q) := by positivity
    have : 8 * 1 * 1 ≤ |δ| * q * (1 + x / (2 * U * Q)) :=
      mul_le_mul (mul_le_mul hδ8 hq1 zero_le_one (by linarith)) (by linarith) zero_le_one
        (by positivity)
    simp only [c]; linarith
  have hδp : 0 < |δ| := by linarith
  have hm : 0 < 2 / |δ| := by positivity
  have h := typeII_gen (α := α) hq hx hU hV hVU hc1 hm hcV (fun W hW =>
    S2_le_640 hq hcop h2α hδQ hδ8 hx hQx hU hcV hW)
  refine h.trans (le_of_eq ?_)
  congr 2
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have e1 : √(2 / |δ| / (2 * Nat.totient q)) = 1 / √(|δ| * Nat.totient q) := by
    rw [show 2 / |δ| / (2 * Nat.totient q) = 1 / (|δ| * Nat.totient q) by field_simp,
      Real.sqrt_div' _ (by positivity), Real.sqrt_one]
  rw [e1]
  set A := Real.log (x / (U * V)) + Real.log c *
    (Real.log (Real.log (x / U / c)) - Real.log (Real.log (V / c)))
  set B := 0.15107 * Real.log (x / (U * V)) + 0.0231 + 2 * zeta3 * √(x / V) / U
  rw [show A * (0.60428 * Real.log (x / (U * V)) + 0.0924 + 8 * zeta3 * √(x / V) / U) = 2 ^ 2 * (A * B) by
    simp only [B]; ring, Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num) (A * B),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end TernaryGoldbach.MinorArcs
