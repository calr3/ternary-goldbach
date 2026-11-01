import TernaryGoldbach.MinorArcs.TypeIITools

/-!
# Type II total [B, §6.2.3]

* `norm_typeII_le'`: `|S_{II}| ≤ 4 ∫_V^{x/U} G(W) dW` for a pointwise majorant `W·G(W)` of
  `√S₁(√S₂ + √S₃)`;
* `pointwise_637`, `integral_G637_le`, **`typeII_637`**: our version of [B, (6.37)] (`q ≤ V/2e`,
  any `δ`), from (5.34) (`S1_bound`), (5.54) (`prop_5_2_4_e`), (2.19), (5.36), (5.37).
  Main term exactly [B]'s; secondary terms with cruder constants (see the docstring).
-/

open Real Finset MeasureTheory

namespace TernaryGoldbach.MinorArcs

/-- `norm_typeII_le` with the integrand `G = g/W` given directly. -/
theorem norm_typeII_le' (α : ℝ) {x : ℝ} (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U) (hV : 2 ≤ V)
    (hVU : (V : ℝ) ≤ x / U) {G : ℝ → ℝ} (hG : IntervalIntegrable G volume V (x / U))
    (hbound : ∀ W ∈ Set.Icc (V : ℝ) (x / U),
      √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
        √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ W * G W) :
    ‖typeII α x U V‖ ≤ 4 * ∫ W in (V : ℝ)..x / U, G W := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast (by omega : 0 < V)
  have heq : Set.EqOn G (fun W => W * G W / W) (Set.uIoc (V : ℝ) (x / U)) := by
    intro W hW; rw [Set.uIoc_of_le hVU] at hW
    have : W ≠ 0 := (lt_trans hV0 hW.1).ne'
    simp only; field_simp
  have h := norm_typeII_le α hx hU hV hVU (g := fun W => W * G W) (hG.congr heq) hbound
  rwa [intervalIntegral.integral_congr_ae (g := G) (Filter.Eventually.of_forall
    fun W hW => (heq hW).symm)] at h

theorem logSqSum_le_half {W' W : ℝ} (hW : 117 ≤ W) (hW' : W / 2 ≤ W') :
    logSqSum W' W ≤ 1 / 2 * W * Real.log W := by
  refine le_trans ?_ (Prelim.sum_log_sq_primes_le hW)
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => sq_nonneg _
  exact filter_subset_filter _ (Ioc_subset_Ioc_left (Nat.floor_le_floor hW'))


/-- `κ₀ζ(3/2)³ = 1.27 ζ(3/2)³` [B, (6.16)]. -/
noncomputable def zeta3 : ℝ := 1.27 * (riemannZeta (3 / 2)).re ^ 3

theorem zeta3_nonneg : 0 ≤ zeta3 := by
  unfold zeta3; have := zeta_three_halves_nonneg; positivity

/-- `κ₁ = 2/π² + κ₀ζ(3/2)³ √(x/V)/U` [B, (6.18)] (we keep it as an expression). -/
noncomputable def kap1 (x U V : ℝ) : ℝ := 2 / π ^ 2 + zeta3 * √(x / V) / U

theorem sqrt_le_amgm {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : √(u * v) ≤ (u + v) / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (u - v)]

theorem sqrt_one_add_le {t : ℝ} (ht : 0 ≤ t) : √(1 + t) ≤ 1 + √t := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]

/-- The integrand `G(W)` of our version of [B, (6.20)–(6.37)] (`W·G(W)` bounds
`√S₁ (√S₂ + √S₃)` for `q ≤ V/2e`). -/
noncomputable def G637 (x U V : ℝ) (q : ℕ) (β W : ℝ) : ℝ :=
  x / √(8 * Nat.totient q) * β / 2 * (1 / W) +
    x / √(8 * Nat.totient q) * β / 2 * Real.log (2 * q) * (1 / (W * Real.log (W / (2 * q)))) +
    x / √(8 * Nat.totient q) / (2 * β) * (H2 (x / (W * U)) / W) +
    x / √(8 * Nat.totient q) / (2 * β) * (zeta3 * √x / U) * (1 / (W * √W)) +
    √(kap1 x U V * q * x / (2 * Nat.totient q)) * (√W / W) +
    √(kap1 x U V * q * x / (2 * Nat.totient q)) * √(Real.log (2 * q)) *
      (√W / (W * √(Real.log (W / (2 * q))))) +
    1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (1 / (W * √W))

set_option maxHeartbeats 2000000 in
/-- The pointwise bound behind [B, (6.20)–(6.37)] in the range `W ≥ V ≥ 2eq`. -/
theorem pointwise_637 {α x Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (50000 : ℝ) ≤ V) (hQ : 3.5 * (x / U) ≤ Q) (hqV : 2 * rexp 1 * q ≤ V) {β : ℝ} (hβ : 0 < β)
    {W : ℝ} (hW : W ∈ Set.Icc (V : ℝ) (x / U)) :
    √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
      √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ W * G637 x U V q β W := by
  obtain ⟨hVW, hWx⟩ := hW
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  have hW0 : 0 < W := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have h2qW : 2 * (q : ℝ) * rexp 1 ≤ W := by linarith
  have hL1 : 1 ≤ Real.log (W / (2 * q)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]; linarith
  set L := Real.log (W / (2 * q))
  have hlogW : Real.log W = L + Real.log (2 * q) := by
    simp only [L]; rw [Real.log_div hW0.ne' (by positivity)]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hl2q : 0 < Real.log (2 * q) := Real.log_pos (by linarith)
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
  have hS2 := prop_5_2_4_e hq hcop hα hx (by nlinarith) (by linarith) (by linarith) hW'1 hW'2
    (le_max_right _ _) (U' := max (U : ℝ) (x / (2 * W)))
  have hlog := logSqSum_le_half (by linarith) hW'1 (W := W)
  set P := x / (4 * Nat.totient q * L) * (1 / 2 * W * Real.log W)
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
  have T1 : a * √P ≤ x / √(8 * Nat.totient q) *
      ((β * (1 + Real.log (2 * q) / L) + h / β) / 2) := by
    have e1 : x / W * h * P = (x / √(8 * Nat.totient q)) ^ 2 *
        ((β * (1 + Real.log (2 * q) / L)) * (h / β)) := by
      simp only [P]
      rw [div_pow, Real.sq_sqrt (by positivity), hlogW]
      field_simp; ring
    rw [← Real.sqrt_mul (by positivity), e1, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    gcongr
    exact sqrt_le_amgm (by positivity) (by positivity)
  -- T2.
  have T2 : a * √R ≤ √(κ * q * x / (2 * Nat.totient q)) * √W *
      (1 + √(Real.log (2 * q)) / √L) := by
    have ha : a ≤ √(κ * x / W) := Real.sqrt_le_sqrt (by
      rw [show κ * x / W = x / W * κ by ring]; exact mul_le_mul_of_nonneg_left hhk (by positivity))
    have e2 : κ * x / W * R = κ * q * x / (2 * Nat.totient q) * (W * (1 + Real.log (2 * q) / L)) := by
      simp only [R]; rw [hlogW]; field_simp; try ring
    calc a * √R ≤ √(κ * x / W) * √R := mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)
      _ = √(κ * q * x / (2 * Nat.totient q)) * √W * √(1 + Real.log (2 * q) / L) := by
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
  have hfin : W * G637 x U V q β W = x / √(8 * Nat.totient q) *
      ((β * (1 + Real.log (2 * q) / L) + h / β) / 2) +
      √(κ * q * x / (2 * Nat.totient q)) * √W * (1 + √(Real.log (2 * q)) / √L) +
      1.4262 * x * √(κ * (1 / 2 + 1 / U)) / √W := by
    simp only [G637, h, κ, L]
    rw [Real.sqrt_div' _ hW0.le]
    have h8 : 0 < √(8 * (Nat.totient q : ℝ)) := Real.sqrt_pos.2 (by positivity)
    generalize √(8 * (Nat.totient q : ℝ)) = s8 at *
    generalize √(kap1 x U V * q * x / (2 * Nat.totient q)) = s3 at *
    generalize √(kap1 x U V * (1 / 2 + 1 / U)) = s4 at *
    generalize √(Real.log (W / (2 * q))) = sL at *
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
/-- Integrating `G637` over `[V, x/U]`. -/
theorem integral_G637_le {x : ℝ} (hx : 0 < x) {U V : ℕ} {q : ℕ} (hq : 1 ≤ q) (hU : 1 ≤ U)
    (hV : 0 < (V : ℝ)) (hVU : (V : ℝ) ≤ x / U) (hqV : 2 * rexp 1 * q ≤ V) {β : ℝ} (hβ : 0 < β) :
    IntervalIntegrable (G637 x U V q β) volume V (x / U) ∧
    ∫ W in (V : ℝ)..x / U, G637 x U V q β W ≤
      x / √(8 * Nat.totient q) * β / 2 * (Real.log (x / (U * V)) + Real.log (2 * q) *
        (Real.log (Real.log (x / U / (2 * q))) - Real.log (Real.log (V / (2 * q))))) +
      x / √(8 * Nat.totient q) / (2 * β) *
        (0.15107 * Real.log (x / (U * V)) + 0.0231 + 2 * zeta3 * √(x / V) / U) +
      √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log (2 * q)) *
        (2 * rexp 1 * √(2 * q) + 4 * √(x / U / Real.log (x / U / (2 * q))))) +
      1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (2 / √V) := by
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have h2q : 2 * (q : ℝ) < V := by nlinarith
  have hpos : ∀ W ∈ Set.uIcc (V : ℝ) (x / U), 0 < W := fun W hW => by
    rw [Set.uIcc_of_le hVU] at hW; exact lt_of_lt_of_le hV hW.1
  have hLpos : ∀ W ∈ Set.uIcc (V : ℝ) (x / U), 0 < Real.log (W / (2 * q)) := fun W hW => by
    rw [Set.uIcc_of_le hVU] at hW
    exact Real.log_pos (by rw [one_lt_div (by positivity)]; linarith [hW.1])
  set c1 := x / √(8 * Nat.totient q) * β / 2
  set c2 := x / √(8 * Nat.totient q) / (2 * β)
  set c3 := √(kap1 x U V * q * x / (2 * Nat.totient q))
  set c4 := 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U))
  -- The seven pieces.
  set f1 : ℝ → ℝ := fun W => 1 / W
  set f2 : ℝ → ℝ := fun W => 1 / (W * Real.log (W / (2 * q)))
  set f3 : ℝ → ℝ := fun W => H2 (x / (W * U)) / W
  set f4 : ℝ → ℝ := fun W => 1 / (W * √W)
  set f5 : ℝ → ℝ := fun W => √W / W
  set f6 : ℝ → ℝ := fun W => √W / (W * √(Real.log (W / (2 * q))))
  have hcl : ContinuousOn (fun W => Real.log (W / (2 * q))) (Set.uIcc (V : ℝ) (x / U)) :=
    ContinuousOn.log (continuousOn_id.div_const _) fun W hW => (div_pos (hpos W hW) (by positivity)).ne'
  have hsq : ContinuousOn (fun W : ℝ => √W) (Set.uIcc (V : ℝ) (x / U)) :=
    Real.continuous_sqrt.continuousOn
  have i1 : IntervalIntegrable f1 volume V (x / U) := ContinuousOn.intervalIntegrable
    (continuousOn_const.div continuousOn_id fun W hW => (hpos W hW).ne')
  have i2 : IntervalIntegrable f2 volume V (x / U) := ContinuousOn.intervalIntegrable
    (continuousOn_const.div (continuousOn_id.mul hcl) fun W hW =>
      (mul_pos (hpos W hW) (hLpos W hW)).ne')
  obtain ⟨i3, I3⟩ := integral_H2_comp hx hU0 hV hVU
  have i4 : IntervalIntegrable f4 volume V (x / U) := ContinuousOn.intervalIntegrable
    (continuousOn_const.div (continuousOn_id.mul hsq) fun W hW =>
      (mul_pos (hpos W hW) (Real.sqrt_pos.2 (hpos W hW))).ne')
  have i5 : IntervalIntegrable f5 volume V (x / U) := ContinuousOn.intervalIntegrable
    (hsq.div continuousOn_id fun W hW => (hpos W hW).ne')
  have i6 : IntervalIntegrable f6 volume V (x / U) := ContinuousOn.intervalIntegrable
    (hsq.div (continuousOn_id.mul (Real.continuous_sqrt.comp_continuousOn hcl)) fun W hW =>
      (mul_pos (hpos W hW) (Real.sqrt_pos.2 (hLpos W hW))).ne')
  have hG : G637 x U V q β = fun W => c1 * f1 W + c1 * Real.log (2 * q) * f2 W + c2 * f3 W +
      c2 * (zeta3 * √x / U) * f4 W + c3 * f5 W + c3 * √(Real.log (2 * q)) * f6 W + c4 * f4 W := by
    ext W; rfl
  have i3' : IntervalIntegrable f3 volume V (x / U) := i3
  have I3' : ∫ W in (V : ℝ)..x / U, f3 W ≤ 0.15107 * Real.log (x / (U * V)) + 0.0231 := I3
  have p1 := (i1.const_mul c1).add (i2.const_mul (c1 * Real.log (2 * q)))
  have p2 := p1.add (i3'.const_mul c2)
  have p3 := p2.add (i4.const_mul (c2 * (zeta3 * √x / U)))
  have p4 := p3.add (i5.const_mul c3)
  have p5 := p4.add (i6.const_mul (c3 * √(Real.log (2 * q))))
  have iG : IntervalIntegrable (G637 x U V q β) volume V (x / U) := by
    rw [hG]; exact p5.add (i4.const_mul c4)
  refine ⟨iG, ?_⟩
  -- Evaluate / bound each piece.
  have J1 : ∫ W in (V : ℝ)..x / U, f1 W = Real.log (x / (U * V)) := by
    rw [integral_one_div_of_pos hV (by positivity), div_div, mul_comm (U : ℝ)]
  have J2 : ∫ W in (V : ℝ)..x / U, f2 W =
      Real.log (Real.log (x / U / (2 * q))) - Real.log (Real.log (V / (2 * q))) :=
    integral_inv_mul_log (by positivity) h2q hVU
  have J4 : ∫ W in (V : ℝ)..x / U, f4 W ≤ 2 / √V := integral_inv_mul_sqrt_le hV hVU
  have J5 : ∫ W in (V : ℝ)..x / U, f5 W ≤ 2 * √(x / U) := by
    rw [intervalIntegral.integral_congr (g := fun W => 1 / √W) fun W hW => by
      have h0 := hpos W hW
      simp only [f5]; rw [div_eq_div_iff h0.ne' (Real.sqrt_pos.2 h0).ne', one_mul,
        Real.mul_self_sqrt h0.le], integral_inv_sqrt hV hVU]
    have := Real.sqrt_nonneg (V : ℝ); linarith
  have J6 : ∫ W in (V : ℝ)..x / U, f6 W ≤
      2 * rexp 1 * √(2 * q) + 4 * √(x / U / Real.log (x / U / (2 * q))) := by
    rw [intervalIntegral.integral_congr (g := fun W => 1 / (√W * √(Real.log (W / (2 * q)))))
      fun W hW => by
        have h0 := hpos W hW
        have h1 := Real.sqrt_pos.2 (hLpos W hW)
        simp only [f6]
        rw [div_eq_div_iff (by positivity) (by positivity), one_mul,
          ← mul_assoc, Real.mul_self_sqrt h0.le]]
    exact integral_inv_sqrt_log_le (by positivity) (by linarith) hVU
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
  have e4 : zeta3 * √x / U * (2 / √V) = 2 * zeta3 * √(x / V) / U := by
    rw [Real.sqrt_div' _ hV.le]; ring
  have K3 := mul_le_mul_of_nonneg_left I3' hc2
  have K4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left J4 hz) hc2
  have K5 := mul_le_mul_of_nonneg_left J5 hc3
  have K6 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left J6 (Real.sqrt_nonneg
    (Real.log (2 * q)))) hc3
  have K7 := mul_le_mul_of_nonneg_left J4 hc4
  rw [e4] at K4
  nlinarith [K3, K4, K5, K6, K7]

set_option maxHeartbeats 2000000 in
/-- **Type II total, our version of [B, (6.37)]** (`q ≤ V/2e`, any `δ`): with `φ = φ(q)`,
`Λ₀ = log(x/UV)`, `Φ = log 2q · (log log(x/2Uq) - log log(V/2q))`, `κ₁ = 2/π² + 1.27ζ(3/2)³√(x/V)/U`,
`|S_{II}| ≤ x/√(2φ) · √((Λ₀ + Φ)(0.60428 Λ₀ + 8 · 1.27ζ(3/2)³ √(x/V)/U))`
`+ 4√(κ₁qx/2φ) (2√(x/U) + √(log 2q)(2e√(2q) + 4√((x/U)/log(x/2Uq))))`
`+ 8 · 1.4262 x √(κ₁(1/2 + 1/U))/√V`.
The main term is [B]'s `x/√(2φ(q)) √((log x/UV + Φ)(κ₆ log x/UV + 2κ₇))` with the exact
`κ₀ζ(3/2)³`-term in place of `2κ₇`; the secondary terms have cruder constants than [B]'s
`√2κ₂√(q/φ)(1 + 1.15√(log 2q/log(x/2Uq)))x/√U + κ₉ x/√V`. -/
theorem typeII_637 {α x Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (50000 : ℝ) ≤ V) (hVU : (V : ℝ) ≤ x / U) (hQ : 3.5 * (x / U) ≤ Q)
    (hqV : 2 * rexp 1 * q ≤ V) :
    ‖typeII α x U V‖ ≤
      x / √(2 * Nat.totient q) * √((Real.log (x / (U * V)) + Real.log (2 * q) *
        (Real.log (Real.log (x / U / (2 * q))) - Real.log (Real.log (V / (2 * q))))) *
        (0.60428 * Real.log (x / (U * V)) + 0.0924 + 8 * zeta3 * √(x / V) / U)) +
      4 * √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log (2 * q)) *
        (2 * rexp 1 * √(2 * q) + 4 * √(x / U / Real.log (x / U / (2 * q))))) +
      8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  have hV0 : (0 : ℝ) < V := by linarith
  have hV2 : 2 ≤ V := by exact_mod_cast (show (2 : ℝ) ≤ V by linarith)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hκ : 0 ≤ kap1 x U V := by unfold kap1; have := zeta3_nonneg; positivity
  have hζ := zeta3_nonneg
  set φ := (Nat.totient q : ℝ)
  set Λ₀ := Real.log (x / (U * V))
  set Φ := Real.log (2 * q) * (Real.log (Real.log (x / U / (2 * q))) -
    Real.log (Real.log (V / (2 * q))))
  set B := 0.15107 * Λ₀ + 0.0231 + 2 * zeta3 * √(x / V) / U
  have hRHS3 : 0 ≤ 8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by positivity
  have hl2q : 0 < Real.log (2 * q) := Real.log_pos (by linarith)
  have hRHS2 : 0 ≤ 4 * √(kap1 x U V * q * x / (2 * φ)) * (2 * √(x / U) + √(Real.log (2 * q)) *
      (2 * rexp 1 * √(2 * q) + 4 * √(x / U / Real.log (x / U / (2 * q))))) := by positivity
  have hRHS1 : 0 ≤ x / √(2 * φ) * √((Λ₀ + Φ) * (0.60428 * Λ₀ + 0.0924 + 8 * zeta3 * √(x / V) / U)) := by
    positivity
  rcases hVU.lt_or_eq with hlt | heq
  swap
  · -- Degenerate range.
    have hint : IntervalIntegrable (G637 x U V q 1) volume V (x / U) := by
      first | (rw [← heq]; done) | (rw [← heq]; exact IntervalIntegrable.refl)
    have h := norm_typeII_le' α hx hU hV2 hVU hint (fun W hW =>
      pointwise_637 hq hcop hα hx hU hV hQ hqV one_pos hW)
    rw [← heq, intervalIntegral.integral_same, mul_zero] at h
    linarith
  -- Main case.
  have hΛ : 0 < Λ₀ := Real.log_pos (by
    rw [lt_div_iff₀ (by positivity)]; rw [lt_div_iff₀ hU0] at hlt; linarith)
  have hL1 : 1 ≤ Real.log (V / (2 * q)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]; linarith
  have hΦ : 0 ≤ Φ := by
    refine mul_nonneg hl2q.le (sub_nonneg.2 (Real.log_le_log (by linarith)
      (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hVU (by positivity)))))
  set A := Λ₀ + Φ
  have hA : 0 < A := by linarith
  have hB : 0 < B := by positivity
  set β := √(B / A)
  have hβ : 0 < β := Real.sqrt_pos.2 (div_pos hB hA)
  obtain ⟨iG, IG⟩ := integral_G637_le hx hq hU hV0 hVU hqV hβ
  have h := norm_typeII_le' α hx hU hV2 hVU iG (fun W hW =>
    pointwise_637 hq hcop hα hx hU hV hQ hqV hβ hW)
  refine h.trans ((mul_le_mul_of_nonneg_left IG (by norm_num)).trans (le_of_eq ?_))
  -- `β = √B/√A` balances the main term.
  have hsA : 0 < √A := Real.sqrt_pos.2 hA
  have hsB : 0 < √B := Real.sqrt_pos.2 hB
  have hβe : β = √B / √A := Real.sqrt_div' _ hA.le
  have h8 : √(8 * φ) = 2 * √(2 * φ) := by
    rw [show 8 * φ = 2 ^ 2 * (2 * φ) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have h4 : √(A * (0.60428 * Λ₀ + 0.0924 + 8 * zeta3 * √(x / V) / U)) = 2 * (√A * √B) := by
    rw [show A * (0.60428 * Λ₀ + 0.0924 + 8 * zeta3 * √(x / V) / U) = 2 ^ 2 * (A * B) by simp only [B]; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), Real.sqrt_mul hA.le]
  rw [h4, hβe, h8]
  have h2φ : 0 < √(2 * φ) := Real.sqrt_pos.2 (by positivity)
  have hAA : √A * √A = A := Real.mul_self_sqrt hA.le
  have hBB : √B * √B = B := Real.mul_self_sqrt hB.le
  have balance : ∀ X s a b : ℝ, 0 < s → 0 < a → 0 < b →
      4 * (X / (2 * s) * (b / a) / 2 * (a * a) + X / (2 * s) / (2 * (b / a)) * (b * b)) =
        X / s * (2 * (a * b)) := by
    intro X s a b hs ha hb; field_simp; ring
  have hbal := balance x (√(2 * φ)) (√A) (√B) h2φ hsA hsB
  rw [hAA, hBB] at hbal
  linear_combination hbal

end TernaryGoldbach.MinorArcs
