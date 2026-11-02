import TernaryGoldbach.MinorArcs.TypeIITotalGen

/-!
# Type II total for large `q` [H, §6.2.3, (6.20), (6.38), (6.39)]

For `q` large compared to `V`, [H] splits the `W`-integral at `W₀ = min(max(2θq, V), x/U)`:
on `[V, W₀]` it uses (5.53) and on `[W₀, x/U]` it uses (5.54) as before.

* `norm_typeII_le_split`: `|S_{II}| ≤ 4(∫_V^A G₁ + ∫_A^{x/U} G₂)` for pointwise majorants on the
  two pieces;
* `G53`, `pointwise_53`, `integral_G53_le`: the (5.53) piece, our version of [H, (6.20)];
* **`typeII_split_gen`**: the total, generalising `typeII_gen` (which is the case `A = V`).
-/

open Real Finset MeasureTheory

namespace TernaryGoldbach.MinorArcs

/-- `∫_a^b dW/(W √W) = 2/√a - 2/√b`. -/
theorem integral_inv_mul_sqrt_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ W in a..b, 1 / (W * √W) = 2 / √a - 2 / √b := by
  have hpos : ∀ W ∈ Set.uIcc a b, 0 < W := by
    intro W hW; rw [Set.uIcc_of_le hab] at hW; exact lt_of_lt_of_le ha hW.1
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun W => -2 / √W)
    (f' := fun W => 1 / (W * √W)) (a := a) (b := b) (fun W hW => by
      have hW := hpos W hW
      have h1 := ((Real.hasDerivAt_sqrt hW.ne').inv (Real.sqrt_pos.2 hW).ne').const_mul (-2)
      convert h1 using 1
      · ext; simp [div_eq_mul_inv]
      · have : √W * √W = W := Real.mul_self_sqrt hW.le
        field_simp
        nlinarith [Real.sqrt_pos.2 hW])
    (ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      fun W hW => (mul_pos (hpos W hW) (Real.sqrt_pos.2 (hpos W hW))).ne'))
  rw [hI]; ring

/-- `∫_a^b √(log W)/W dW = (2/3)((log b)^{3/2} - (log a)^{3/2})` for `1 < a ≤ b`. -/
theorem integral_sqrt_log_div {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ W in a..b, √(Real.log W) / W =
      2 / 3 * (Real.log b * √(Real.log b) - Real.log a * √(Real.log a)) := by
  have hpos : ∀ W ∈ Set.uIcc a b, 1 < W := by
    intro W hW; rw [Set.uIcc_of_le hab] at hW; exact lt_of_lt_of_le ha hW.1
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun W => 2 / 3 * (Real.log W * √(Real.log W))) (f' := fun W => √(Real.log W) / W)
    (a := a) (b := b) (fun W hW => by
      have hW1 := hpos W hW
      have hW0 : 0 < W := by linarith
      have hL : 0 < Real.log W := Real.log_pos hW1
      have h1 := Real.hasDerivAt_log hW0.ne'
      have h3 := (h1.mul (h1.sqrt hL.ne')).const_mul (2 / 3)
      convert h3 using 1
      have hs : 0 < √(Real.log W) := Real.sqrt_pos.2 hL
      have hss : √(Real.log W) * √(Real.log W) = Real.log W := Real.mul_self_sqrt hL.le
      field_simp
      nlinarith [hss])
    (ContinuousOn.intervalIntegrable ((Real.continuous_sqrt.comp_continuousOn
      (ContinuousOn.log continuousOn_id fun W hW => (by linarith [hpos W hW] : W ≠ 0))).div
        continuousOn_id fun W hW => (by linarith [hpos W hW] : W ≠ 0)))
  rw [hI]; ring

/-- Splitting the `W`-integral of `norm_typeII_le'` at `A ∈ [V, x/U]`. -/
theorem norm_typeII_le_split (α : ℝ) {x : ℝ} (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U) (hV : 2 ≤ V)
    {A : ℝ} (hVA : (V : ℝ) ≤ A) (hAU : A ≤ x / U) {G₁ G₂ : ℝ → ℝ}
    (h₁ : IntervalIntegrable G₁ volume V A) (h₂ : IntervalIntegrable G₂ volume A (x / U))
    (hb₁ : ∀ W ∈ Set.Icc (V : ℝ) A,
      √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
        √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ W * G₁ W)
    (hb₂ : ∀ W ∈ Set.Icc A (x / U),
      √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
        √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ W * G₂ W) :
    ‖typeII α x U V‖ ≤ 4 * ((∫ W in (V : ℝ)..A, G₁ W) + ∫ W in A..x / U, G₂ W) := by
  set G : ℝ → ℝ := fun W => if W ≤ A then G₁ W else G₂ W
  have e₁ : Set.EqOn G₁ G (Set.uIoc (V : ℝ) A) := by
    intro W hW; rw [Set.uIoc_of_le hVA] at hW; simp [G, hW.2]
  have e₂ : Set.EqOn G₂ G (Set.uIoc A (x / U)) := by
    intro W hW; rw [Set.uIoc_of_le hAU] at hW; simp [G, not_le.2 hW.1]
  have i₁ : IntervalIntegrable G volume V A := h₁.congr e₁
  have i₂ : IntervalIntegrable G volume A (x / U) := h₂.congr e₂
  have hG := norm_typeII_le' α hx hU hV (hVA.trans hAU) (i₁.trans i₂) (fun W hW => by
    by_cases h : W ≤ A
    · simp only [G, h, ite_true]; exact hb₁ W ⟨hW.1, h⟩
    · simp only [G, h, ite_false]; exact hb₂ W ⟨(not_le.1 h).le, hW.2⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals i₁ i₂] at hG
  have j₁ : ∫ W in (V : ℝ)..A, G W = ∫ W in (V : ℝ)..A, G₁ W :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun W hW => (e₁ hW).symm)
  have j₂ : ∫ W in A..x / U, G W = ∫ W in A..x / U, G₂ W :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun W hW => (e₂ hW).symm)
  rwa [j₁, j₂] at hG

/-- The integrand for the range `[V, W₀]` where (5.53) or (5.57) is used: with `κ = κ₁`,
`L = log W`, `W · G53(W)` bounds `√S₁(√S₂ + √S₃)` when `S₂ ≤ (2M/x + rx/2W + W/2) Σ(log p)²`.
For (5.53), `M = r x²/16q + qx` with `r = max(1, 2ρ)`; for (5.57),
`M = x²/2|δq| + x²/16(1-ρ)Q` and `r = 1/2(1-ρ)`. -/
noncomputable def G53 (x U V : ℝ) (M r W : ℝ) : ℝ :=
  √(kap1 x U V) * √M * (√(Real.log W) / W) +
    √(kap1 x U V) * (√r * x / 2) * (√(Real.log W) / (W * √W)) +
    √(kap1 x U V) * (√x / 2) * (√(Real.log W) / √W) +
    1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (1 / (W * √W))

set_option maxHeartbeats 1000000 in
/-- The pointwise bound behind [H, (6.20)]. -/
theorem pointwise_53 {α x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (117 : ℝ) ≤ V) {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r) {W : ℝ}
    (hW : W ∈ Set.Icc (V : ℝ) (x / U))
    (hS2 : S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (2 * M / x + r * x / (2 * W) + W / 2) * logSqSum (max V (W / 2)) W) :
    √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
      √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ W * G53 x U V M r W := by
  obtain ⟨hVW, hWx⟩ := hW
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  have hW0 : 0 < W := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- `S₁ ≤ κ x/W`.
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
  set κ := kap1 x U V
  have hκ0 : 0 ≤ κ := hh0.trans hhk
  have hS1' : S1 x U W ≤ κ * x / W := hS1.trans (by
    rw [show κ * x / W = x / W * κ by ring]; exact mul_le_mul_of_nonneg_left hhk (by positivity))
  -- `S₂ ≤ P₁ + P₂ + P₃`.
  have hW'1 : W / 2 ≤ max (V : ℝ) (W / 2) := le_max_right _ _
  have hlog := logSqSum_le_half (by linarith) hW'1 (W := W)
  set L := Real.log W
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  set P₁ := 2 * M / x * (W * L / 2)
  set P₂ := r * x / (2 * W) * (W * L / 2)
  set P₃ := W / 2 * (W * L / 2)
  have hP₁ : 0 ≤ P₁ := by positivity
  have hP₂ : 0 ≤ P₂ := by positivity
  have hP₃ : 0 ≤ P₃ := by positivity
  have hS2' : S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤ P₁ + P₂ + P₃ := by
    refine hS2.trans ((mul_le_mul_of_nonneg_left hlog (by positivity)).trans (le_of_eq ?_))
    simp only [P₁, P₂, P₃, L]; ring
  have hsqrt_add : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → √(u + v) ≤ √u + √v := fun u v hu hv => by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv, Real.sqrt_nonneg u, Real.sqrt_nonneg v,
      mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)]
  have hS2'' : √(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) ≤ √P₁ + √P₂ + √P₃ :=
    (Real.sqrt_le_sqrt hS2').trans ((hsqrt_add _ _ (by positivity) hP₃).trans
      (by have := hsqrt_add _ _ hP₁ hP₂; linarith))
  set a := √(κ * x / W)
  have ha : √(S1 x U W) ≤ a := Real.sqrt_le_sqrt hS1'
  have hsW : 0 < √W := Real.sqrt_pos.2 hW0
  have hWW : √W * √W = W := Real.mul_self_sqrt hW0.le
  have E1 : a * √P₁ = √κ * √M * √L := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hκ0, ← Real.sqrt_mul (by positivity)]
    congr 1; simp only [P₁]; field_simp
  have E2 : a * √P₂ = √κ * (√r * x / 2) * (√L / √W) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show √κ * (√r * x / 2) * (√L / √W) = √(κ * r * L / W) * (x / 2) by
      rw [Real.sqrt_div' _ hW0.le, Real.sqrt_mul (by positivity), Real.sqrt_mul hκ0]; ring]
    rw [show κ * x / W * P₂ = κ * r * L / W * (x / 2) ^ 2 by simp only [P₂]; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have E3 : a * √P₃ = √κ * (√x / 2) * (√L * √W) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show √κ * (√x / 2) * (√L * √W) = √(κ * x * L * W) * (1 / 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hκ0]; ring]
    rw [show κ * x / W * P₃ = κ * x * L * W * (1 / 2) ^ 2 by simp only [P₃]; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- The `S₃` term, as in `pointwise_gen`.
  set S3 := (x / (2 * W) + 1) * (1.4262 ^ 2 * W)
  have T3 : a * √S3 ≤ 1.4262 * x * √(κ * (1 / 2 + 1 / U)) / √W := by
    have hS3 : κ * x / W * S3 ≤ (1.4262 * x * √(κ * (1 / 2 + 1 / U)) / √W) ^ 2 := by
      have hl : κ * x / W * S3 = 1.4262 ^ 2 * κ * x * (x / 2 + W) / W := by
        simp only [S3]; field_simp; try ring
      rw [hl, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hW0.le]
      apply div_le_div_of_nonneg_right _ hW0.le
      have hWU : W ≤ x * (1 / U) := by rw [mul_one_div]; exact hWx
      have h1 : κ * x * W ≤ κ * x * (x * (1 / U)) := mul_le_mul_of_nonneg_left hWU (by positivity)
      nlinarith
    calc a * √S3 = √(κ * x / W * S3) := (Real.sqrt_mul (by positivity) _).symm
      _ ≤ _ := Real.sqrt_le_left (by positivity) |>.2 hS3
  have hfin : W * G53 x U V M r W = √κ * √M * √L + √κ * (√r * x / 2) * (√L / √W) +
      √κ * (√x / 2) * (√L * √W) + 1.4262 * x * √(κ * (1 / 2 + 1 / U)) / √W := by
    simp only [G53, κ, L]
    generalize √(kap1 x U V) = s1 at *
    generalize √(kap1 x U V * (1 / 2 + 1 / U)) = s4 at *
    generalize √(Real.log W) = sL at *
    field_simp
    rw [Real.sq_sqrt hW0.le]
  rw [hfin, ← E1, ← E2, ← E3]
  calc √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) + √S3)
      ≤ a * (√P₁ + √P₂ + √P₃ + √S3) := by gcongr
    _ = a * √P₁ + a * √P₂ + a * √P₃ + a * √S3 := by ring
    _ ≤ _ := by linarith

/-- [H, §6.2.3]: `∫_V^A √(log W)/W^{3/2} dW ≤ (2/√V)(√(log V) + 1/√(log V))` for `1 < V ≤ A`
(via `√(log W) ≤ √(log V) + (log W - log V)/(2√(log V))` and `∫_V^∞ log(W/V) W^{-3/2} dW = 4/√V`). -/
theorem integral_sqrt_log_div_W32_le {V A : ℝ} (hV : 1 < V) (hVA : V ≤ A) :
    ∫ W in V..A, √(Real.log W) / (W * √W) ≤
      2 * (√(Real.log V) + 1 / √(Real.log V)) / √V := by
  have hV0 : 0 < V := by linarith
  have hlV : 0 < Real.log V := Real.log_pos hV
  set k := √(Real.log V) with hk
  have hk0 : 0 < k := Real.sqrt_pos.2 hlV
  have hkk : k * k = Real.log V := Real.mul_self_sqrt hlV.le
  have hpos : ∀ W ∈ Set.uIcc V A, 1 < W := fun W hW => by
    rw [Set.uIcc_of_le hVA] at hW; linarith [hW.1]
  have hW0 : ∀ W ∈ Set.uIcc V A, W ≠ 0 := fun W hW => by linarith [hpos W hW]
  have hsq0 : ∀ W ∈ Set.uIcc V A, √W ≠ 0 := fun W hW =>
    (Real.sqrt_pos.2 (by linarith [hpos W hW])).ne'
  have hsq : ContinuousOn (fun W : ℝ => √W) (Set.uIcc V A) := Real.continuous_sqrt.continuousOn
  have hlogc : ContinuousOn (fun W => Real.log W) (Set.uIcc V A) :=
    ContinuousOn.log continuousOn_id hW0
  have i1 : IntervalIntegrable (fun W => √(Real.log W) / (W * √W)) volume V A :=
    ((Real.continuous_sqrt.comp_continuousOn hlogc).div (continuousOn_id.mul hsq)
      fun W hW => mul_ne_zero (hW0 W hW) (hsq0 W hW)).intervalIntegrable
  have i4 : IntervalIntegrable (fun W => 1 / (W * √W)) volume V A :=
    (continuousOn_const.div (continuousOn_id.mul hsq)
      fun W hW => mul_ne_zero (hW0 W hW) (hsq0 W hW)).intervalIntegrable
  have i6 : IntervalIntegrable (fun W => (Real.log W - Real.log V) / (W * √W)) volume V A :=
    ((hlogc.sub continuousOn_const).div (continuousOn_id.mul hsq)
      fun W hW => mul_ne_zero (hW0 W hW) (hsq0 W hW)).intervalIntegrable
  -- `∫ (log W - log V)/W^{3/2} = G(A) - G(V)`, `G(W) = -2(log W - log V)/√W - 4/√W`.
  have hI6 : ∫ W in V..A, (Real.log W - Real.log V) / (W * √W) =
      (-2 * (Real.log A - Real.log V) / √A - 4 / √A) -
        (-2 * (Real.log V - Real.log V) / √V - 4 / √V) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun W => -2 * (Real.log W - Real.log V) / √W - 4 / √W) (fun W hW => ?_) i6
    have hW := hpos W hW
    have hW0' : 0 < W := by linarith
    have hs : 0 < √W := Real.sqrt_pos.2 hW0'
    have h1 := (((Real.hasDerivAt_log hW0'.ne').sub_const (Real.log V)).const_mul (-2)).div
      (Real.hasDerivAt_sqrt hW0'.ne') hs.ne'
    have h2 := (hasDerivAt_const W (4 : ℝ)).div (Real.hasDerivAt_sqrt hW0'.ne') hs.ne'
    convert h1.sub h2 using 1
    have hss : √W * √W = W := Real.mul_self_sqrt hW0'.le
    field_simp
    rw [show √W ^ 2 = W by rw [sq, hss]]
    ring
  have hmono : ∀ W ∈ Set.Icc V A, √(Real.log W) / (W * √W) ≤
      k * (1 / (W * √W)) + 1 / (2 * k) * ((Real.log W - Real.log V) / (W * √W)) := by
    intro W hW
    have hW1 : 0 < W * √W := mul_pos (by linarith [hW.1]) (Real.sqrt_pos.2 (by linarith [hW.1]))
    have hlW : 0 ≤ Real.log W := Real.log_nonneg (by linarith [hW.1])
    have hsW := Real.sq_sqrt hlW
    have key : √(Real.log W) ≤ k + (Real.log W - Real.log V) / (2 * k) := by
      rw [← sub_nonneg]
      have : k + (Real.log W - Real.log V) / (2 * k) - √(Real.log W) =
          (√(Real.log W) - k) ^ 2 / (2 * k) := by
        field_simp; linear_combination hkk - hsW
      rw [this]; positivity
    calc √(Real.log W) / (W * √W) ≤ (k + (Real.log W - Real.log V) / (2 * k)) / (W * √W) :=
          div_le_div_of_nonneg_right key hW1.le
      _ = _ := by ring
  have hJ := intervalIntegral.integral_mono_on hVA i1 ((i4.const_mul k).add (i6.const_mul _)) hmono
  rw [intervalIntegral.integral_add (i4.const_mul k) (i6.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_mul_sqrt_eq hV0 hVA, hI6] at hJ
  refine hJ.trans ?_
  have hA0 : 0 < √A := Real.sqrt_pos.2 (by linarith)
  have hsV : 0 < √V := Real.sqrt_pos.2 hV0
  have hlA : Real.log V ≤ Real.log A := Real.log_le_log hV0 hVA
  have t1 : 0 ≤ k * (2 / √A) := by positivity
  have t2 : 0 ≤ 1 / (2 * k) * (2 * (Real.log A - Real.log V) / √A + 4 / √A) := by
    have : 0 ≤ Real.log A - Real.log V := by linarith
    positivity
  have e : 2 * (k + 1 / k) / √V = k * (2 / √V) + 1 / (2 * k) * (4 / √V) := by
    field_simp; ring
  rw [e]
  have e2 : k * (2 / √V - 2 / √A) + 1 / (2 * k) * (-2 * (Real.log A - Real.log V) / √A - 4 / √A -
      (-2 * (Real.log V - Real.log V) / √V - 4 / √V)) =
      k * (2 / √V) + 1 / (2 * k) * (4 / √V) - k * (2 / √A) -
        1 / (2 * k) * (2 * (Real.log A - Real.log V) / √A + 4 / √A) := by ring
  rw [e2]; linarith

set_option maxHeartbeats 1000000 in
/-- Integrating `G53` over `[V, A]`: with `κ = κ₁`, `M = r x²/16q + qx`, `L_A = log A`,
`∫ ≤ √κ (√M (2/3)(L_A^{3/2} - L_V^{3/2}) + √r x (√L_V + 1/√L_V)/√V + √(xA) √L_A) + c₄(2/√V - 2/√A)`. -/
theorem integral_G53_le {x : ℝ} (hx : 0 < x) (U V : ℝ) (M : ℝ) {r : ℝ} (hr : 0 ≤ r) {A : ℝ}
    (hV : 1 < V) (hVA : V ≤ A) :
    IntervalIntegrable (G53 x U V M r) volume V A ∧
    ∫ W in V..A, G53 x U V M r W ≤
      √(kap1 x U V) * (√M * (2 / 3 *
        (Real.log A * √(Real.log A) - Real.log V * √(Real.log V))) +
        √r * x * (√(Real.log V) + 1 / √(Real.log V)) / √V + √x * √(Real.log A) * √A) +
      1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (2 / √V - 2 / √A) := by
  have hV0 : 0 < V := by linarith
  have hpos : ∀ W ∈ Set.uIcc V A, 1 < W := fun W hW => by
    rw [Set.uIcc_of_le hVA] at hW; linarith [hW.1]
  have hW0 : ∀ W ∈ Set.uIcc V A, W ≠ 0 := fun W hW => by linarith [hpos W hW]
  have hsq0 : ∀ W ∈ Set.uIcc V A, √W ≠ 0 := fun W hW =>
    (Real.sqrt_pos.2 (by linarith [hpos W hW])).ne'
  have hlog : ContinuousOn (fun W => √(Real.log W)) (Set.uIcc V A) :=
    Real.continuous_sqrt.comp_continuousOn (ContinuousOn.log continuousOn_id hW0)
  have hsq : ContinuousOn (fun W : ℝ => √W) (Set.uIcc V A) := Real.continuous_sqrt.continuousOn
  set g1 : ℝ → ℝ := fun W => √(Real.log W) / W
  set g2 : ℝ → ℝ := fun W => √(Real.log W) / (W * √W)
  set g3 : ℝ → ℝ := fun W => √(Real.log W) / √W
  set g4 : ℝ → ℝ := fun W => 1 / (W * √W)
  set g5 : ℝ → ℝ := fun W => 1 / √W
  have i1 : IntervalIntegrable g1 volume V A :=
    (hlog.div continuousOn_id hW0).intervalIntegrable
  have i2 : IntervalIntegrable g2 volume V A :=
    (hlog.div (continuousOn_id.mul hsq) fun W hW => mul_ne_zero (hW0 W hW) (hsq0 W hW)).intervalIntegrable
  have i3 : IntervalIntegrable g3 volume V A := (hlog.div hsq hsq0).intervalIntegrable
  have i4 : IntervalIntegrable g4 volume V A := (continuousOn_const.div (continuousOn_id.mul hsq)
    fun W hW => mul_ne_zero (hW0 W hW) (hsq0 W hW)).intervalIntegrable
  have i5 : IntervalIntegrable g5 volume V A :=
    (continuousOn_const.div hsq hsq0).intervalIntegrable
  set κ := kap1 x U V
  set c1 := √κ * √M
  set c2 := √κ * (√r * x / 2)
  set c3 := √κ * (√x / 2)
  set c4 := 1.4262 * x * √(κ * (1 / 2 + 1 / U))
  have hG : G53 x U V M r = fun W => c1 * g1 W + c2 * g2 W + c3 * g3 W + c4 * g4 W := by
    ext W; rfl
  have p1 := ((i1.const_mul c1).add (i2.const_mul c2)).add (i3.const_mul c3)
  have iG : IntervalIntegrable (G53 x U V M r) volume V A := by
    rw [hG]; exact p1.add (i4.const_mul c4)
  refine ⟨iG, ?_⟩
  have hLA : 0 ≤ √(Real.log A) := Real.sqrt_nonneg _
  have hmono : ∀ W ∈ Set.Icc V A, √(Real.log W) ≤ √(Real.log A) := fun W hW =>
    Real.sqrt_le_sqrt (Real.log_le_log (by linarith [hW.1]) hW.2)
  have J1 := integral_sqrt_log_div hV hVA
  have J2 : ∫ W in V..A, g2 W ≤ 2 * (√(Real.log V) + 1 / √(Real.log V)) / √V :=
    integral_sqrt_log_div_W32_le hV hVA
  have J3 : ∫ W in V..A, g3 W ≤ √(Real.log A) * (2 * √A) := by
    calc ∫ W in V..A, g3 W ≤ ∫ W in V..A, √(Real.log A) * g5 W := by
          refine intervalIntegral.integral_mono_on hVA i3 (i5.const_mul _) fun W hW => ?_
          simp only [g3, g5]; rw [mul_one_div]
          exact div_le_div_of_nonneg_right (hmono W hW) (Real.sqrt_nonneg _)
      _ = √(Real.log A) * (2 * √A - 2 * √V) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_sqrt hV0 hVA]
      _ ≤ _ := by
          have : 0 ≤ √V := Real.sqrt_nonneg _
          nlinarith
  have J4 := integral_inv_mul_sqrt_eq hV0 hVA
  rw [hG, intervalIntegral.integral_add p1 (i4.const_mul c4),
    intervalIntegral.integral_add ((i1.const_mul c1).add (i2.const_mul c2)) (i3.const_mul c3),
    intervalIntegral.integral_add (i1.const_mul c1) (i2.const_mul c2)]
  simp only [intervalIntegral.integral_const_mul]
  have hg4 : ∫ W in V..A, g4 W = 2 / √V - 2 / √A := J4
  have hg1 : ∫ W in V..A, g1 W =
      2 / 3 * (Real.log A * √(Real.log A) - Real.log V * √(Real.log V)) := J1
  rw [hg4, hg1]
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  have K2 := mul_le_mul_of_nonneg_left J2 hc2
  have K3 := mul_le_mul_of_nonneg_left J3 hc3
  have e2 : c2 * (2 * (√(Real.log V) + 1 / √(Real.log V)) / √V) =
      √κ * (√r * x * (√(Real.log V) + 1 / √(Real.log V)) / √V) := by
    simp only [c2]; ring
  have e3 : c3 * (√(Real.log A) * (2 * √A)) = √κ * (√x * √(Real.log A) * √A) := by
    simp only [c3]; ring
  rw [e2] at K2; rw [e3] at K3
  have : c1 * (2 / 3 * (Real.log A * √(Real.log A) - Real.log V * √(Real.log V))) =
      √κ * (√M *
        (2 / 3 * (Real.log A * √(Real.log A) - Real.log V * √(Real.log V)))) := by
    simp only [c1]; ring
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **Type II total, split form** (generalising `typeII_gen`, the case `A = V`): an `S₂`-bound
of the shape of (5.53)/(5.57) (see `G53`) on `[V, A]`, and the `typeII_gen` hypothesis on `[A, x/U]`.
With `Λ_A = log(x/UA)`, `Φ_A = log c (log log(x/Uc) - log log(A/c))`, the main term is
`4x√(m/2φ) √((Λ_A + Φ_A)(0.15107 Λ_A + 2κ₀ζ³√(x/A)/U))`; the (5.53)-range contributes
`4√κ₁ (√M (2/3)((log A)^{3/2} - (log V)^{3/2}) + √r x √log A/√V + √(xA) √log A)`
(our version of [H, (6.20)]). -/
theorem typeII_split_gen {α x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (117 : ℝ) ≤ V) {A : ℝ} (hVA : (V : ℝ) ≤ A) (hAU : A ≤ x / U) {M r : ℝ} (hM : 0 ≤ M)
    (hr : 0 ≤ r)
    (hS2a : ∀ W ∈ Set.Icc (V : ℝ) A, S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (2 * M / x + r * x / (2 * W) + W / 2) * logSqSum (max V (W / 2)) W)
    {c m : ℝ} (hc1 : 1 ≤ c) (hm : 0 < m) (hcA : c * rexp 1 ≤ A)
    (hS2gen : ∀ W ∈ Set.Icc A (x / U), S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (m * x / (Nat.totient q * Real.log (W / c)) + q / Nat.totient q * (W / Real.log (W / c))) *
        logSqSum (max V (W / 2)) W) :
    ‖typeII α x U V‖ ≤
      4 * x * √(m / (2 * Nat.totient q)) * √((Real.log (x / (U * A)) + Real.log c *
        (Real.log (Real.log (x / U / c)) - Real.log (Real.log (A / c)))) *
        (0.15107 * Real.log (x / (U * A)) + 0.0231 + 2 * zeta3 * √(x / A) / U)) +
      4 * √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log c) *
        (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) +
      4 * (√(kap1 x U V) * (√M * (2 / 3 *
        (Real.log A * √(Real.log A) - Real.log V * √(Real.log V))) +
        √r * x * (√(Real.log V) + 1 / √(Real.log V)) / √V + √x * √(Real.log A) * √A)) +
      8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  have hV0 : (0 : ℝ) < V := by linarith
  have hV2 : 2 ≤ V := by exact_mod_cast (show (2 : ℝ) ≤ V by linarith)
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hc0 : 0 < c := by linarith
  have hA0 : 0 < A := by linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hκ : 0 ≤ kap1 x U V := by unfold kap1; have := zeta3_nonneg; positivity
  have hζ := zeta3_nonneg
  set φ := (Nat.totient q : ℝ)
  set Λ₀ := Real.log (x / (U * A))
  set Φ := Real.log c * (Real.log (Real.log (x / U / c)) - Real.log (Real.log (A / c)))
  set B := 0.15107 * Λ₀ + 0.0231 + 2 * zeta3 * √(x / A) / U
  set c4 := 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U))
  set R53 := √(kap1 x U V) * (√M * (2 / 3 *
    (Real.log A * √(Real.log A) - Real.log V * √(Real.log V))) +
    √r * x * (√(Real.log V) + 1 / √(Real.log V)) / √V + √x * √(Real.log A) * √A)
  have hc4 : 0 ≤ c4 := by positivity
  have hRHS2 : 0 ≤ 4 * √(kap1 x U V * q * x / (2 * φ)) * (2 * √(x / U) + √(Real.log c) *
      (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) := by positivity
  have hRHS1 : 0 ≤ 4 * x * √(m / (2 * φ)) * √((Λ₀ + Φ) * B) := by positivity
  obtain ⟨i53, I53⟩ := integral_G53_le hx (U : ℝ) (V : ℝ) M hr (by linarith : (1 : ℝ) < V) hVA
  have hb₁ : ∀ W ∈ Set.Icc (V : ℝ) A,
      √(S1 x U W) * (√(S2 α x (max U (x / (2 * W))) (max V (W / 2)) W) +
        √((x / (2 * W) + 1) * (1.4262 ^ 2 * W))) ≤ W * G53 x U V M r W := fun W hW =>
    pointwise_53 hq hx hU hV hM hr ⟨hW.1, hW.2.trans hAU⟩ (hS2a W hW)
  have hsA : 0 < √A := Real.sqrt_pos.2 hA0
  have h53 : 4 * (∫ W in (V : ℝ)..A, G53 x U V M r W) ≤ 4 * R53 + 8 * c4 / √V - 8 * c4 / √A := by
    have := mul_le_mul_of_nonneg_left I53 (by norm_num : (0 : ℝ) ≤ 4)
    refine this.trans (le_of_eq ?_)
    simp only [R53, c4]; ring
  have hfin : 8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V = 8 * c4 / √V := by
    simp only [c4]; ring
  rw [hfin]
  rcases hAU.lt_or_eq with hlt | heq
  swap
  · -- Degenerate upper range.
    have hint : IntervalIntegrable (Ggen x U V q c m 1) volume A (x / U) := by
      rw [← heq]
    have h := norm_typeII_le_split α hx hU hV2 hVA hAU i53 hint hb₁ (fun W hW =>
      pointwise_gen' hq hx hU hV hVA hc1 hm hcA hS2gen one_pos hW)
    rw [← heq, intervalIntegral.integral_same, add_zero] at h
    have : 0 ≤ 8 * c4 / √A := by positivity
    linarith
  have hΛ : 0 < Λ₀ := Real.log_pos (by
    rw [lt_div_iff₀ (by positivity)]; rw [lt_div_iff₀ hU0] at hlt; linarith)
  have hL1 : 1 ≤ Real.log (A / c) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hc0]; linarith
  have hΦ : 0 ≤ Φ := by
    refine mul_nonneg hlc (sub_nonneg.2 (Real.log_le_log (by linarith)
      (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hAU hc0.le))))
  set A' := Λ₀ + Φ
  have hA' : 0 < A' := by linarith
  have hB : 0 < B := by positivity
  set β := √(B / A')
  have hβ : 0 < β := Real.sqrt_pos.2 (div_pos hB hA')
  obtain ⟨iG, IG⟩ := integral_Ggen_le' hx hq hU hA0 hAU hc1 hm hcA hβ (V := V)
  have h := norm_typeII_le_split α hx hU hV2 hVA hAU i53 iG hb₁ (fun W hW =>
    pointwise_gen' hq hx hU hV hVA hc1 hm hcA hS2gen hβ hW)
  have hsA' : 0 < √A' := Real.sqrt_pos.2 hA'
  have hsB : 0 < √B := Real.sqrt_pos.2 hB
  have hβe : β = √B / √A' := Real.sqrt_div' _ hA'.le
  have hAA : √A' * √A' = A' := Real.mul_self_sqrt hA'.le
  have hBB : √B * √B = B := Real.mul_self_sqrt hB.le
  have balance : ∀ K a b : ℝ, 0 < a → 0 < b →
      4 * (K * (b / a) / 2 * (a * a) + K / (2 * (b / a)) * (b * b)) = 4 * K * (a * b) := by
    intro K a b ha hb; field_simp; ring
  have hbal := balance (x * √(m / (2 * φ))) (√A') (√B) hsA' hsB
  rw [hAA, hBB] at hbal
  have IG' : ∫ W in A..x / U, Ggen x U V q c m β W ≤
      x * √(m / (2 * φ)) * β / 2 * A' + x * √(m / (2 * φ)) / (2 * β) * B +
      √(kap1 x U V * q * x / (2 * φ)) * (2 * √(x / U) + √(Real.log c) *
        (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) +
      1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (2 / √A) := IG
  have IG4 := mul_le_mul_of_nonneg_left IG' (by norm_num : (0 : ℝ) ≤ 4)
  rw [← hβe] at hbal
  rw [Real.sqrt_mul hA'.le]
  have e2 : 4 * (1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (2 / √A)) = 8 * c4 / √A := by
    simp only [c4]; ring
  linarith [hbal, e2, h53, IG4, h]

/-- **Type II total, all of `[V, x/U]` in the (5.53)/(5.57) regime** (used for [H, (6.39)]). -/
theorem typeII_top {α x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (117 : ℝ) ≤ V) (hVU : (V : ℝ) ≤ x / U) {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hS2a : ∀ W ∈ Set.Icc (V : ℝ) (x / U), S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (2 * M / x + r * x / (2 * W) + W / 2) * logSqSum (max V (W / 2)) W) :
    ‖typeII α x U V‖ ≤
      4 * (√(kap1 x U V) * (√M * (2 / 3 *
        (Real.log (x / U) * √(Real.log (x / U)) - Real.log V * √(Real.log V))) +
        √r * x * (√(Real.log V) + 1 / √(Real.log V)) / √V +
        √x * √(Real.log (x / U)) * √(x / U))) +
      8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by
  have hV2 : 2 ≤ V := by exact_mod_cast (show (2 : ℝ) ≤ V by linarith)
  obtain ⟨i53, I53⟩ := integral_G53_le hx (U : ℝ) (V : ℝ) M hr (by linarith : (1 : ℝ) < V) hVU
  have h := norm_typeII_le' α hx hU hV2 hVU i53 fun W hW => pointwise_53 hq hx hU hV hM hr hW
    (hS2a W hW)
  have hA : 0 < √(x / U) := Real.sqrt_pos.2 (by linarith)
  have hc4 : 0 ≤ 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) := by positivity
  have : 0 ≤ 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (2 / √(x / U)) := by positivity
  have e : 8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V =
      4 * (1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) * (2 / √V)) := by ring
  rw [e]
  nlinarith

/-- (5.53) in the shape used by `G53`: `M = r x²/16q + qx`, `r = max(1, 2ρ)`. -/
theorem S2_le_53 {α x Q ρ : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hqρ : (q : ℝ) ≤ ρ * Q)
    (hx : 0 < x) {U V : ℕ} {W : ℝ} (hV : 0 < (V : ℝ)) (hVW : (V : ℝ) ≤ W) :
    S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (2 * (max 1 (2 * ρ) * x ^ 2 / (16 * q) + q * x) / x + max 1 (2 * ρ) * x / (2 * W) + W / 2) *
        logSqSum (max V (W / 2)) W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW : 0 < W := by linarith
  have h := prop_5_2_4_a hq hcop hα hρ hρ1 hqρ hx hW (le_max_right _ _) (max_le hVW (by linarith))
    (le_max_right _ _) (U' := max (U : ℝ) (x / (2 * W)))
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp; ring

/-- (5.57) in the shape used by `G53`: `M = x²/2|δ|q + x²/16(1-ρ)Q`, `r = 1/2(1-ρ)`. -/
theorem S2_le_57 {α x δ Q ρ : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (h2α : 2 * α = a / q + δ / x + k) (hδQ : |δ / x| ≤ 1 / (q * Q)) (hρ1 : ρ < 1)
    (hqρ : (q : ℝ) ≤ ρ * Q) (hx : 0 < x) (hδ0 : δ ≠ 0) {U V : ℕ} {W : ℝ} (hV : 0 < (V : ℝ))
    (hVW : (V : ℝ) ≤ W) (hQ : 0 < Q) :
    S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (2 * (x ^ 2 / (2 * |δ| * q) + x ^ 2 / (16 * (1 - ρ) * Q)) / x +
        1 / (2 * (1 - ρ)) * x / (2 * W) + W / 2) * logSqSum (max V (W / 2)) W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW : 0 < W := by linarith
  have hδp : 0 < |δ| := abs_pos.2 hδ0
  have h1ρ : 0 < 1 - ρ := by linarith
  have h := prop_5_2_4_d hq hcop h2α hδQ hρ1 hqρ hx hW hδ0 (le_max_right _ _) (le_max_right _ _)
    (U' := max (U : ℝ) (x / (2 * W))) (W' := max (V : ℝ) (W / 2))
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp; ring

/-- (5.54) in the shape used by `Ggen` (`c = 2q`, `m = 1/4`), on `[A, x/U]` with `A ≥ 2eq`. -/
theorem S2_le_54 {α x Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hx : 0 < x) {U V : ℕ}
    (hV : (50000 : ℝ) ≤ V) (hQ : 3.5 * (x / U) ≤ Q) {A : ℝ} (hVA : (V : ℝ) ≤ A)
    (hqA : 2 * q * rexp 1 ≤ A) {W : ℝ} (hW : W ∈ Set.Icc A (x / U)) :
    S2 α x (max U (x / (2 * W))) (max V (W / 2)) W ≤
      (1 / 4 * x / (Nat.totient q * Real.log (W / (2 * q))) +
        q / Nat.totient q * (W / Real.log (W / (2 * q)))) * logSqSum (max V (W / 2)) W := by
  obtain ⟨hAW, hWx⟩ := hW
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hW0 : 0 < W := by linarith
  have h := prop_5_2_4_e hq hcop hα hx (by nlinarith) (by linarith) (by linarith)
    (le_max_right _ _) (max_le (hVA.trans hAW) (by linarith)) (le_max_right _ _)
    (U' := max (U : ℝ) (x / (2 * W))) (W := W)
  refine h.trans (le_of_eq ?_)
  congr 2
  ring

set_option maxHeartbeats 1000000 in
/-- **Our version of [H, (6.38)]** (`V ≤ 2θq ≤ x/U`, `θ ≥ e`, any `δ`): (5.53) with `ρ = 1/2`
on `[V, 2θq]`, (5.54) on `[2θq, x/U]`. -/
theorem typeII_638 {α x Q θ : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hx : 0 < x) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (50000 : ℝ) ≤ V) (hQ : 3.5 * (x / U) ≤ Q) (hθ : rexp 1 ≤ θ)
    (hVA : (V : ℝ) ≤ 2 * θ * q) (hAU : 2 * θ * q ≤ x / U) :
    ‖typeII α x U V‖ ≤
      4 * x * √(1 / 4 / (2 * Nat.totient q)) * √((Real.log (x / (U * (2 * θ * q))) +
        Real.log (2 * q) * (Real.log (Real.log (x / U / (2 * q))) -
          Real.log (Real.log (2 * θ * q / (2 * q))))) *
        (0.15107 * Real.log (x / (U * (2 * θ * q))) + 0.0231 + 2 * zeta3 * √(x / (2 * θ * q)) / U)) +
      4 * √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log (2 * q)) *
        (2 * rexp 1 * √(2 * q) + 4 * √(x / U / Real.log (x / U / (2 * q))))) +
      4 * (√(kap1 x U V) * (√(x ^ 2 / (16 * q) + q * x) * (2 / 3 *
        (Real.log (2 * θ * q) * √(Real.log (2 * θ * q)) - Real.log V * √(Real.log V))) +
        x * (√(Real.log V) + 1 / √(Real.log V)) / √V +
        √x * √(Real.log (2 * θ * q)) * √(2 * θ * q))) +
      8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have he : (2 : ℝ) < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have h2qQ : (q : ℝ) ≤ 1 / 2 * Q := by nlinarith
  have hmax : max 1 (2 * (1 / 2 : ℝ)) = 1 := by norm_num
  have h := typeII_split_gen (α := α) hq hx hU (by linarith) hVA hAU (r := 1)
    (M := x ^ 2 / (16 * q) + q * x) (by positivity) zero_le_one (fun W hW => by
      have := S2_le_53 hq hcop hα (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) h2qQ hx
        (U := U) (by linarith) hW.1
      rwa [hmax, one_mul] at this) (c := 2 * q) (m := 1 / 4) (by linarith) (by norm_num)
    (by nlinarith) (fun W hW => S2_le_54 hq hcop hα hx hV hQ hVA (by nlinarith) hW)
  rw [Real.sqrt_one, one_mul] at h
  exact h

/-- **Our version of [H, (6.39)]** (`q ≤ Q`, any `δ`): (5.53) with `ρ = 1` on all of `[V, x/U]`. -/
theorem typeII_639 {α x Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x) {U V : ℕ}
    (hU : 1 ≤ U) (hV : (117 : ℝ) ≤ V) (hVU : (V : ℝ) ≤ x / U) :
    ‖typeII α x U V‖ ≤
      4 * (√(kap1 x U V) * (√(x ^ 2 / (8 * q) + q * x) * (2 / 3 *
        (Real.log (x / U) * √(Real.log (x / U)) - Real.log V * √(Real.log V))) +
        √2 * x * (√(Real.log V) + 1 / √(Real.log V)) / √V +
        √x * √(Real.log (x / U)) * √(x / U))) +
      8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hmax : max 1 (2 * (1 : ℝ)) = 2 := by norm_num
  have e : (2 : ℝ) * x ^ 2 / (16 * q) = x ^ 2 / (8 * q) := by field_simp; ring
  have h := typeII_top (α := α) hq hx hU hV hVU (r := 2) (M := x ^ 2 / (8 * q) + q * x)
    (by positivity) (by norm_num) (fun W hW => by
      have := S2_le_53 hq hcop hα one_pos le_rfl (by linarith) hx (U := U) (by linarith) hW.1
      rwa [hmax, e] at this)
  exact h

set_option maxHeartbeats 1000000 in
/-- **Our version of [H, (6.41)]** (`|δ| ≥ 8`, `V ≤ θ|δ|q ≤ x/U`, `θ ≥ e(1+ε₁)/4`): (5.57) on
`[V, θ|δq|]`, (5.56) (via `S2_le_640'`) on `[θ|δq|, x/U]`. With `c' = |δ|q(1+ε₁)/4`,
`ε₁ = x/2UQ`. -/
theorem typeII_641 {α x δ Q ρ θ : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (h2α : 2 * α = a / q + δ / x + k) (hδQ : |δ / x| ≤ 1 / (q * Q)) (hδ8 : 8 ≤ |δ|) (hx : 0 < x)
    (hQx : x ≤ Q ^ 2) (hρ1 : ρ < 1) (hqρ : (q : ℝ) ≤ ρ * Q) {U V : ℕ} (hU : 1 ≤ U)
    (hV : (117 : ℝ) ≤ V) (hVA : (V : ℝ) ≤ θ * |δ| * q) (hAU : θ * |δ| * q ≤ x / U)
    (hθ : |δ| * q * (1 + x / (2 * U * Q)) / 4 * rexp 1 ≤ θ * |δ| * q) :
    let c := |δ| * q * (1 + x / (2 * U * Q)) / 4
    ‖typeII α x U V‖ ≤
      4 * x * √(2 / |δ| / (2 * Nat.totient q)) * √((Real.log (x / (U * (θ * |δ| * q))) +
        Real.log c * (Real.log (Real.log (x / U / c)) -
          Real.log (Real.log (θ * |δ| * q / c)))) *
        (0.15107 * Real.log (x / (U * (θ * |δ| * q))) + 0.0231 + 2 * zeta3 * √(x / (θ * |δ| * q)) / U)) +
      4 * √(kap1 x U V * q * x / (2 * Nat.totient q)) * (2 * √(x / U) + √(Real.log c) *
        (2 * rexp 1 * √c + 4 * √(x / U / Real.log (x / U / c)))) +
      4 * (√(kap1 x U V) * (√(x ^ 2 / (2 * |δ| * q) + x ^ 2 / (16 * (1 - ρ) * Q)) * (2 / 3 *
        (Real.log (θ * |δ| * q) * √(Real.log (θ * |δ| * q)) - Real.log V * √(Real.log V))) +
        √(1 / (2 * (1 - ρ))) * x * (√(Real.log V) + 1 / √(Real.log V)) / √V +
        √x * √(Real.log (θ * |δ| * q)) * √(θ * |δ| * q))) +
      8 * 1.4262 * x * √(kap1 x U V * (1 / 2 + 1 / U)) / √V := by
  intro c
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hδ0 : δ ≠ 0 := by intro h; rw [h, abs_zero] at hδ8; linarith
  have hδp : 0 < |δ| := abs_pos.2 hδ0
  have hQ0 : 0 < Q := by
    by_contra hQ; push Not at hQ
    have hq0 : (0 : ℝ) < q := by linarith
    have : 1 / (q * Q) ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one
      (mul_nonpos_of_nonneg_of_nonpos hq0.le hQ)
    have : |δ / x| ≤ 0 := hδQ.trans this
    rw [abs_div, abs_of_pos hx] at this
    have : 0 < |δ| / x := div_pos hδp hx
    linarith
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hc1 : 1 ≤ c := by
    have h0 : 0 ≤ x / (2 * U * Q) := by positivity
    have : 8 * 1 * 1 ≤ |δ| * q * (1 + x / (2 * U * Q)) :=
      mul_le_mul (mul_le_mul hδ8 hq1 zero_le_one (by linarith)) (by linarith) zero_le_one
        (by positivity)
    simp only [c]; linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  exact typeII_split_gen (α := α) hq hx hU hV hVA hAU (by positivity) (by positivity)
    (fun W hW => S2_le_57 hq hcop h2α hδQ hρ1 hqρ hx hδ0 (U := U) (by linarith) hW.1 hQ0)
    hc1 (by positivity) hθ (fun W hW => S2_le_640' hq hcop h2α hδQ hδ8 hx hQx hU hVA hθ hW)

end TernaryGoldbach.MinorArcs
