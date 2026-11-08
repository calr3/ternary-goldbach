import TernaryGoldbach.Prelim.EOneNum

/-!
# Pointwise bounds for `E(y)` on all ranges `y ≥ 10⁶`

* `E_bound_A` (window `a = 3`) and `E_bound_A_half` (window `a = 1/2`): if `E₁Λ` varies by at most
  `A₀` from any integer point `m ∈ [Y e^{−0.003}, Y]` up to the top of the window, then
  `|E(Y)| ≤ A₀ + 1/M₂ + Z(Y)/M(1)`.
* The variation `A₀` comes from summation by parts (`E1_diff_gen`) with the pointwise errors of
  `ψ` of each range.
-/

open MeasureTheory Set Filter Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens TernaryGoldbach.Explicit

/-- `Z(Y)/M(1) ≤ 68/√Y + 5.3·10⁶/Y^{3/2} + 10⁻¹³` for `a = 1/2`, `δ = 10⁻⁴`. -/
theorem Zsm_div_le_half {Y : ℝ} (hY : 1 ≤ Y) :
    (Zsm 0.5 1e-4 Y + (22 + 36 * Real.exp (0.5 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4))) /
        (Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 0.5 - 1)) ≤
      68 / √Y + 5.3e6 * Y ^ (-(3 / 2) : ℝ) + 1e-13 := by
  have hY0 : 0 < Y := by linarith
  have hLQ := LQW_le (a := 0.5) (δ := 1e-4) (H := 1e8)
  have hT := TailBH_le (a := 0.5) (by norm_num) (by norm_num)
  have hV := Vg_le (a := 0.5) (by norm_num)
  have he1 : Real.exp ((1e-4 : ℝ) ^ 2 / 2) ≤ 1.0001 := by
    have h := exp_small_le (t := (1e-4 : ℝ) ^ 2 / 2) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have he1' : 1 ≤ Real.exp ((1e-4 : ℝ) ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hh : 1.6487 ≤ Real.exp 0.5 ∧ Real.exp 0.5 ≤ 1.6488 := by
    constructor
    · have := Real.add_one_le_exp 0.5
      have h2 := Real.exp_bound' (x := 0.5) (by norm_num) (by norm_num) (n := 6) (by norm_num)
      have h1 := Real.exp_one_gt_d9
      have e : Real.exp 0.5 * Real.exp 0.5 = Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 0.5]
    · have := exp_half_le; norm_num at this ⊢; linarith
  have h25 : Real.exp (0.5 / 2) ≤ 1.2841 := by
    have e : Real.exp (0.5 / 2) * Real.exp (0.5 / 2) = Real.exp 0.5 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (0.5 / 2)]
  have hM1 : 0.6487 ≤ Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 0.5 - 1) := by nlinarith
  have hLQ' : LQW 0.5 0 1e-4 1e8 ≤ 44 := by
    refine hLQ.trans ?_; nlinarith [Real.exp_pos (0.5 / 2)]
  have htail : (22 + 36 * Real.exp (0.5 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4)) ≤ 1e-14 := by
    have e1 : Real.exp (0.5 + 0.003) ≤ 1.7 := by
      rw [Real.exp_add]
      have := exp_small_le (t := 0.003) (by norm_num) (by norm_num)
      nlinarith [Real.exp_pos 0.003, Real.exp_pos 0.5]
    have e2 : Real.exp (-(0.003 / 1e-4)) ≤ 1e-13 := by
      have h32 := exp_neg32_le
      have e : Real.exp (-(0.003 / 1e-4)) = Real.exp (-32) * Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [exp_two_le, Real.exp_pos 2, Real.exp_pos (-32)]
    have : (22 + 36 * Real.exp (0.5 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4)) ≤
        (22 + 36 * 1.7) * 1e-4 * 1e-13 := by gcongr
    linarith [show ((22 : ℝ) + 36 * 1.7) * 1e-4 * 1e-13 ≤ 1e-14 by norm_num]
  have hsY : Y ^ (-(1 / 2) : ℝ) = 1 / √Y := by
    rw [Real.rpow_neg hY0.le, ← Real.sqrt_eq_rpow, one_div]
  have hp0 : 0 ≤ Y ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hY0.le _
  have hp1 : 0 ≤ Y ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hY0.le _
  have hpi : 3.14 ≤ Real.pi := Real.pi_gt_d2.le
  unfold Zsm
  rw [div_le_iff₀ (by linarith)]
  have hZ1 : Y ^ (-(1 / 2) : ℝ) * LQW 0.5 0 1e-4 1e8 ≤ 44 * Y ^ (-(1 / 2) : ℝ) := by nlinarith
  have hZ3 : 2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg 0.5 0 1e-4 / (2 * Real.pi) ≤ 3.4e6 * Y ^ (-(3 / 2) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have : Vg 0.5 0 1e-4 ≤ 3.2e7 := hV
    nlinarith
  have hT0 : 2 * TailBH 0.5 1e-4 1e8 / 1e8 ≤ 1e-22 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  have hsY' : 68 / √Y = 68 * Y ^ (-(1 / 2) : ℝ) := by rw [hsY]; ring
  rw [hsY']
  set M1 := Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 0.5 - 1) with hM1d
  have hM1u : M1 ≤ 1.0001 * 0.6488 := by rw [hM1d]; nlinarith
  nlinarith

/-- The window variation from a bound `A₀` for `E₁Λ(t) − E₁Λ(m)`, `m ∈ [M₂, Y]` integer, `t` up to
`Y e^{a+0.003}`. -/
theorem hwin_of_A0 {Y a A0 : ℝ} (hY : 1 ≤ Y) (ha : 0 ≤ a) (hM2 : 1 ≤ ⌊Y * Real.exp (-0.003)⌋₊)
    (hA0 : ∀ m : ℕ, ⌊Y * Real.exp (-0.003)⌋₊ ≤ m → (m : ℝ) ≤ Y → ∀ t : ℝ, (m : ℝ) ≤ t →
      t ≤ Y * Real.exp (a + 0.003) → |E₁Λ t - E₁Λ m| ≤ A0) :
    ∀ v : ℝ, Real.exp (-0.003) ≤ v → v ≤ Real.exp (a + 0.003) →
      |E₁Λ (Y * v) - E₁Λ Y| ≤ A0 + 1 / ⌊Y * Real.exp (-0.003)⌋₊ := by
  have hY0 : 0 < Y := by linarith
  set M₂ := ⌊Y * Real.exp (-0.003)⌋₊ with hM₂
  have hM₂0 : (0 : ℝ) < M₂ := by exact_mod_cast hM2
  have hek1 : Real.exp (-0.003) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hea : 1 ≤ Real.exp (a + 0.003) := Real.one_le_exp (by linarith)
  intro v hv1 hv2
  have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos _) hv1
  have hYv0 : 0 < Y * v := by positivity
  rcases le_or_gt Y (Y * v) with hge | hlt
  · set M₀ := ⌊Y⌋₊ with hM₀
    have hM₀1 : 1 ≤ M₀ := Nat.le_floor (by exact_mod_cast hY)
    have hM₀le : (M₀ : ℝ) ≤ Y := Nat.floor_le hY0.le
    have hM₂M₀ : M₂ ≤ M₀ := Nat.floor_mono (by nlinarith)
    have h1 := hA0 M₀ hM₂M₀ hM₀le (Y * v) (hM₀le.trans hge) (by nlinarith)
    have h2 := abs_E1_sub_floor_le (t := Y) hY
    rw [← hM₀] at h2
    have hM₂M₀' : (M₂ : ℝ) ≤ M₀ := by exact_mod_cast hM₂M₀
    have k1 : 1 / (M₀ : ℝ) ≤ 1 / M₂ := div_le_div_of_nonneg_left (by norm_num) hM₂0 hM₂M₀'
    calc |E₁Λ (Y * v) - E₁Λ Y| ≤ |E₁Λ (Y * v) - E₁Λ M₀| + |E₁Λ Y - E₁Λ M₀| := by
          have := abs_sub_le (E₁Λ (Y * v)) (E₁Λ M₀) (E₁Λ Y)
          rwa [abs_sub_comm (E₁Λ M₀) (E₁Λ Y)] at this
      _ ≤ A0 + 1 / M₂ := by linarith
  · set M₁ := ⌊Y * v⌋₊ with hM₁
    have hM₂M₁ : M₂ ≤ M₁ := Nat.floor_mono (by nlinarith)
    have hM₁1 : 1 ≤ M₁ := hM2.trans hM₂M₁
    have hM₁le : (M₁ : ℝ) ≤ Y := (Nat.floor_le hYv0.le).trans hlt.le
    have h1 := hA0 M₁ hM₂M₁ hM₁le Y hM₁le (le_mul_of_one_le_right hY0.le hea)
    have hYv1 : 1 ≤ Y * v := by
      have : (1 : ℝ) ≤ M₁ := by exact_mod_cast hM₁1
      have := Nat.floor_le hYv0.le (a := Y * v)
      linarith
    have h2 := abs_E1_sub_floor_le hYv1
    rw [← hM₁] at h2
    have hM₂M₁' : (M₂ : ℝ) ≤ M₁ := by exact_mod_cast hM₂M₁
    have k1 : 1 / (M₁ : ℝ) ≤ 1 / M₂ := div_le_div_of_nonneg_left (by norm_num) hM₂0 hM₂M₁'
    calc |E₁Λ (Y * v) - E₁Λ Y| ≤ |E₁Λ (Y * v) - E₁Λ M₁| + |E₁Λ Y - E₁Λ M₁| := by
          have := abs_sub_le (E₁Λ (Y * v)) (E₁Λ M₁) (E₁Λ Y)
          rwa [abs_sub_comm (E₁Λ M₁) (E₁Λ Y)] at this
      _ ≤ 1 / M₂ + A0 := by linarith
      _ = A0 + 1 / M₂ := by ring

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **The bound with the window `a = 3`.** -/
theorem E_bound_A {Y A0 : ℝ} (hY : 1 ≤ Y) (hA00 : 0 ≤ A0) (hM2 : 1 ≤ ⌊Y * Real.exp (-0.003)⌋₊)
    (hA0 : ∀ m : ℕ, ⌊Y * Real.exp (-0.003)⌋₊ ≤ m → (m : ℝ) ≤ Y → ∀ t : ℝ, (m : ℝ) ≤ t →
      t ≤ Y * Real.exp (3 + 0.003) → |E₁Λ t - E₁Λ m| ≤ A0) :
    |E₁Λ Y + Real.eulerMascheroniConstant| ≤ A0 + 1 / ⌊Y * Real.exp (-0.003)⌋₊ +
      (5.53 / √Y + 1.8e5 * Y ^ (-(3 / 2) : ℝ) + 1e-13) := by
  have hw := hwin_of_A0 hY (by norm_num) hM2 hA0
  have hE := E_bound_win (a := 3) (δ := 1e-4) (κ := 0.003) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hY (by positivity) hw
  exact hE.trans (add_le_add le_rfl (Zsm_div_le hY))

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **The bound with the window `a = 1/2`.** -/
theorem E_bound_A_half {Y A0 : ℝ} (hY : 1 ≤ Y) (hA00 : 0 ≤ A0) (hM2 : 1 ≤ ⌊Y * Real.exp (-0.003)⌋₊)
    (hA0 : ∀ m : ℕ, ⌊Y * Real.exp (-0.003)⌋₊ ≤ m → (m : ℝ) ≤ Y → ∀ t : ℝ, (m : ℝ) ≤ t →
      t ≤ Y * Real.exp (0.5 + 0.003) → |E₁Λ t - E₁Λ m| ≤ A0) :
    |E₁Λ Y + Real.eulerMascheroniConstant| ≤ A0 + 1 / ⌊Y * Real.exp (-0.003)⌋₊ +
      (68 / √Y + 5.3e6 * Y ^ (-(3 / 2) : ℝ) + 1e-13) := by
  have hw := hwin_of_A0 hY (by norm_num) hM2 hA0
  have hE := E_bound_win (a := 0.5) (δ := 1e-4) (κ := 0.003) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hY (by positivity) hw
  exact hE.trans (add_le_add le_rfl (Zsm_div_le_half hY))

/-! ### `ψ` below `2·10⁸` -/

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **`|ψ(n) − n| ≤ 2√n` for `12 ≤ n < 2·10⁸`.** -/
theorem psi_le_two {n : ℕ} (h1 : 12 ≤ n) (h2 : n < 200000000) : |psiN n - n| ≤ 2 * √(n : ℝ) := by
  have hs := Real.sqrt_nonneg (n : ℝ)
  rcases lt_or_ge n 1000000 with h | h
  · have := psi_two_sided h1 (by omega)
    rw [cB_small h, one_mul] at this
    unfold psiN; rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
  · have hR := SieveTab.sieve_table2 (t := (n : ℝ)) (by exact_mod_cast h) (by exact_mod_cast h2)
    unfold SieveTab.RtT at hR
    rw [Nat.floor_natCast] at hR
    have e : SmallTab.thS n = thetaN n := rfl
    rw [e] at hR
    norm_num at hR
    have hnp := sum_vonMangoldt_nonprime_lt (y := (n : ℝ)) (by positivity)
    rw [Nat.floor_natCast] at hnp
    have hnp0 : 0 ≤ ∑ m ∈ Finset.Icc 1 n, (if m.Prime then 0 else (Λ m : ℝ)) :=
      Finset.sum_nonneg fun m _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
    rw [psiN_eq, abs_le]
    constructor <;> nlinarith [hR.1, hR.2]

end TernaryGoldbach.Prelim
