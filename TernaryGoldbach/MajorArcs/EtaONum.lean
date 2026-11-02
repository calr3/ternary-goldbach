import TernaryGoldbach.MajorArcs.HHFourier2

/-!
# Exact polynomial integrals, and `∫₀² η◦²`, `∫₀² η◦² log t`

`pH cs t = ∑ c_j t^j` (Horner form, rational coefficients) has `∫_a^b t^k pH cs t = pI a b cs k` and
`∫₀² t^k log t · pH cs t = pI 0 2 cs k · log 2 − pJ cs k` exactly (`∫₀² t^m log t =
2^{m+1}/(m+1) · (log 2 − 1/(m+1))`). With `e^x = ∑_{i<14} x^i/i! + O*(15/(14!·14))` for `|x| ≤ 1`
(`Real.exp_bound`, `x = −(t−1)²`), `η◦² = (t(2−t))⁶ e^{−(t−1)²}` is a polynomial up to `1.3·10⁻¹¹`.
-/

open Real MeasureTheory Set Finset
open scoped Nat

namespace TernaryGoldbach.MajorArcs.PolyNum

/-- `∑ c_j t^j` in Horner form. -/
noncomputable def pH : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, t => (c : ℝ) + t * pH cs t

theorem continuous_pH : ∀ cs : List ℚ, Continuous (pH cs)
  | [] => by
    have : pH [] = fun _ => 0 := funext fun _ => rfl
    rw [this]; exact continuous_const
  | c :: cs => by
    have : pH (c :: cs) = fun t => (c : ℝ) + t * pH cs t := funext fun _ => rfl
    rw [this]; exact continuous_const.add (continuous_id.mul (continuous_pH cs))

/-- `∑ c_j (b^{k+j+1} − a^{k+j+1})/(k+j+1)`. -/
def pI (a b : ℚ) : List ℚ → ℕ → ℚ
  | [], _ => 0
  | c :: cs, k => c * (b ^ (k + 1) - a ^ (k + 1)) / (k + 1) + pI a b cs (k + 1)

/-- `∑ c_j 2^{k+j+1}/(k+j+1)²`. -/
def pJ : List ℚ → ℕ → ℚ
  | [], _ => 0
  | c :: cs, k => c * 2 ^ (k + 1) / ((k + 1) * (k + 1)) + pJ cs (k + 1)

theorem integral_pow_mul_pH (a b : ℚ) : ∀ (cs : List ℚ) (k : ℕ),
    ∫ t in (a : ℝ)..b, t ^ k * pH cs t = (pI a b cs k : ℝ)
  | [], k => by simp [pH, pI]
  | c :: cs, k => by
    have e : (fun t : ℝ => t ^ k * pH (c :: cs) t) =
        fun t => (c : ℝ) * t ^ k + t ^ (k + 1) * pH cs t := by
      funext t; simp only [pH]; ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow,
      integral_pow_mul_pH a b cs (k + 1)]
    · simp only [pI]; push_cast; ring
    · exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
    · exact ((continuous_pow (k + 1)).mul (continuous_pH cs)).intervalIntegrable _ _

theorem continuous_pow_mul_log (k : ℕ) : Continuous fun t : ℝ => t ^ (k + 1) * Real.log t := by
  have e : (fun t : ℝ => t ^ (k + 1) * Real.log t) = fun t => t ^ k * (t * Real.log t) := by
    funext t; ring
  rw [e]; exact (continuous_pow k).mul Real.continuous_mul_log

/-- `∫₀² t^{k+1} log t = 2^{k+2}/(k+2) · (log 2 − 1/(k+2))`. -/
theorem integral_pow_mul_log (k : ℕ) :
    ∫ t in (0 : ℝ)..2, t ^ (k + 1) * Real.log t =
      2 ^ (k + 2) / ((k : ℝ) + 2) * (Real.log 2 - 1 / ((k : ℝ) + 2)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  set F : ℝ → ℝ := fun t => t ^ (k + 2) / ((k : ℝ) + 2) * (Real.log t - 1 / ((k : ℝ) + 2)) with hF
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 2, HasDerivAt F (x ^ (k + 1) * Real.log x) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have h1 := (hasDerivAt_pow (k + 2) x).div_const ((k : ℝ) + 2)
    have h2 := (Real.hasDerivAt_log hx0.ne').sub_const (1 / ((k : ℝ) + 2))
    have := h1.mul h2
    convert this using 1
    field_simp
    push_cast
    ring
  have hcont : ContinuousOn F (Icc 0 2) := by
    have e : F = fun t => t ^ (k + 1) * (t * Real.log t) / ((k : ℝ) + 2) -
        t ^ (k + 2) / ((k : ℝ) + 2) / ((k : ℝ) + 2) := by
      funext t; simp only [hF]; ring
    rw [e]
    exact (((continuous_pow (k + 1)).mul Real.continuous_mul_log).div_const _ |>.sub
      (((continuous_pow (k + 2)).div_const _).div_const _)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv
    ((continuous_pow_mul_log k).intervalIntegrable _ _)]
  simp only [hF]
  rw [zero_pow (by omega), zero_div, zero_mul, sub_zero]

/-- `∫₀² t^{k+1} log t · pH cs t = pI 0 2 cs (k+1) · log 2 − pJ cs (k+1)`. -/
theorem integral_pow_log_mul_pH : ∀ (cs : List ℚ) (k : ℕ),
    ∫ t in (0 : ℝ)..2, t ^ (k + 1) * Real.log t * pH cs t =
      (pI 0 2 cs (k + 1) : ℝ) * Real.log 2 - pJ cs (k + 1)
  | [], k => by simp [pH, pI, pJ]
  | c :: cs, k => by
    have e : (fun t : ℝ => t ^ (k + 1) * Real.log t * pH (c :: cs) t) =
        fun t => (c : ℝ) * (t ^ (k + 1) * Real.log t) + t ^ (k + 1 + 1) * Real.log t * pH cs t := by
      funext t; simp only [pH]; ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow_mul_log,
      integral_pow_log_mul_pH cs (k + 1)]
    · simp only [pI, pJ]; push_cast; field_simp; ring
    · exact (continuous_const.mul (continuous_pow_mul_log k)).intervalIntegrable _ _
    · exact ((continuous_pow_mul_log (k + 1)).mul (continuous_pH cs)).intervalIntegrable _ _

/-! ### `η◦²` as a polynomial -/

/-- `e^{−(t−1)²}` to 14 terms, times `(t(2−t))⁶`, is `t⁶ pH csA`. -/
def csA : List ℚ := [(63633137 / 2702700 : ℚ), (-229079293 / 9729720 : ℚ), (-715872799 / 24324300 : ℚ), (290894369 / 9266400 : ℚ), (15529499 / 772200 : ℚ), (-488236967 / 23587200 : ℚ), (-12010379 / 1201200 : ℚ), (425799491 / 47900160 : ℚ), (1884273863 / 479001600 : ℚ), (-1712803 / 623700 : ℚ), (-154550161 / 119750400 : ℚ), (85506371 / 119750400 : ℚ), (18057623 / 79833600 : ℚ), (26223343 / 778377600 : ℚ), (-428179783 / 1556755200 : ℚ), (88249621 / 345945600 : ℚ), (-131700773 / 566092800 : ℚ), (193958 / 868725 : ℚ), (-48011939 / 259459200 : ℚ), (102602341 / 778377600 : ℚ), (-9981481 / 119750400 : ℚ), (932201 / 19958400 : ℚ), (-195557 / 8553600 : ℚ), (2322049 / 239500800 : ℚ), (-188471 / 53222400 : ℚ), (103 / 93555 : ℚ), (-63511 / 222393600 : ℚ), (2839 / 47174400 : ℚ), (-10349 / 1037836800 : ℚ), (323 / 259459200 : ℚ), (-19 / 172972800 : ℚ), (19 / 3113510400 : ℚ), (-1 / 6227020800 : ℚ)]

theorem P0_sq (t : ℝ) : P0 t ^ 2 = (t * (2 - t)) ^ 6 * Real.exp (-(t - 1) ^ 2) := by
  unfold P0
  have : Real.exp (-(t - 1) ^ 2) = Real.exp (-(t - 1) ^ 2 / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]; ring

theorem pH_csA (t : ℝ) :
    (t * (2 - t)) ^ 6 * ∑ i ∈ range 14, (-(t - 1) ^ 2) ^ i / (i ! : ℝ) = t ^ 6 * pH csA t := by
  simp only [csA, pH, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  ring

/-- The Taylor error: `|η◦(t)² − t⁶ pH csA t| ≤ (t(2−t))⁶ ε` with `ε = 15/(14!·14)`. -/
theorem P0_sq_approx {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |P0 t ^ 2 - t ^ 6 * pH csA t| ≤ (t * (2 - t)) ^ 6 * (15 / (14 ! * 14)) := by
  have hx : |(-(t - 1) ^ 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hb := Real.exp_bound hx (n := 14) (by norm_num)
  rw [P0_sq, ← pH_csA, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left (hb.trans ?_) (by positivity)
  have h1 : |(-(t - 1) ^ 2)| ^ 14 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have h2 : (0 : ℝ) ≤ (Nat.succ 14 : ℝ) / (14 ! * 14) := by positivity
  calc |(-(t - 1) ^ 2)| ^ 14 * ((Nat.succ 14 : ℝ) / (14 ! * 14)) ≤ 1 * ((Nat.succ 14 : ℝ) / (14 ! * 14)) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = 15 / (14 ! * 14) := by push_cast; ring

theorem tt_le {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) : 0 ≤ t * (2 - t) ∧ t * (2 - t) ≤ 1 :=
  ⟨mul_nonneg ht0 (by linarith), by nlinarith [sq_nonneg (t - 1)]⟩

theorem csA_val : (6402059973 : ℚ) / 10 ^ 10 + 2 * (15 / (14 ! * 14)) ≤ pI 0 2 csA 6 ∧
    pI 0 2 csA 6 + 2 * (15 / (14 ! * 14)) ≤ 6402059974 / 10 ^ 10 := by
  decide +kernel

/-- **`0.640205997 ≤ ∫₀² η◦² ≤ 0.640205998`** (value `0.6402059973663…`). -/
theorem integral_P0_sq : 0.640205997 ≤ ∫ t in (0 : ℝ)..2, P0 t ^ 2 * 1 ∧
    ∫ t in (0 : ℝ)..2, P0 t ^ 2 * 1 ≤ 0.640205998 := by
  have hI := integral_pow_mul_pH 0 2 csA 6
  push_cast at hI
  have hc : Continuous fun t : ℝ => P0 t ^ 2 * 1 := by unfold P0; fun_prop
  have hd : |(∫ t in (0 : ℝ)..2, P0 t ^ 2 * 1) - ∫ t in (0 : ℝ)..2, t ^ 6 * pH csA t| ≤
      (15 / (14 ! * 14)) * |(2 : ℝ) - 0| := by
    have hp : IntervalIntegrable (fun t : ℝ => t ^ 6 * pH csA t) volume 0 2 :=
      ((continuous_pow 6).mul (continuous_pH csA)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) hp]
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le (by norm_num)] at ht
    rw [Real.norm_eq_abs, mul_one]
    have h := P0_sq_approx ht.1.le ht.2
    have h6 : (t * (2 - t)) ^ 6 ≤ 1 := pow_le_one₀ (tt_le ht.1.le ht.2).1 (tt_le ht.1.le ht.2).2
    calc _ ≤ (t * (2 - t)) ^ 6 * (15 / (14 ! * 14)) := h
      _ ≤ 1 * (15 / (14 ! * 14)) := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = _ := one_mul _
  rw [hI] at hd
  have hq := csA_val
  have q1 := (Rat.cast_le (K := ℝ)).2 hq.1
  have q2 := (Rat.cast_le (K := ℝ)).2 hq.2
  push_cast at q1 q2 hd
  rw [abs_le] at hd
  constructor <;> nlinarith [hd.1, hd.2]

/-- `(t(2−t))⁶ |log t| ≤ 3` on `(0, 2]`. -/
theorem tt_log_le {t : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 2) : (t * (2 - t)) ^ 6 * |Real.log t| ≤ 3 := by
  obtain ⟨h0, h1⟩ := tt_le ht0.le ht2
  have hl1 : |Real.log t| ≤ 1 / t + 1 := by
    rcases le_total t 1 with h | h
    · rw [abs_of_nonpos (Real.log_nonpos ht0.le h)]
      have := Real.one_sub_inv_le_log_of_pos ht0
      rw [one_div]; have : 0 < t⁻¹ := inv_pos.2 ht0; linarith
    · rw [abs_of_nonneg (Real.log_nonneg h)]
      have := Real.log_le_sub_one_of_pos ht0
      have : 0 < 1 / t := by positivity
      linarith
  have h5 : (t * (2 - t)) ^ 6 * (1 / t) = (t * (2 - t)) ^ 5 * (2 - t) := by field_simp
  have h6 : (t * (2 - t)) ^ 5 ≤ 1 := pow_le_one₀ h0 h1
  have h6' : (t * (2 - t)) ^ 6 ≤ 1 := pow_le_one₀ h0 h1
  have h50 : 0 ≤ (t * (2 - t)) ^ 5 := pow_nonneg h0 5
  calc (t * (2 - t)) ^ 6 * |Real.log t| ≤ (t * (2 - t)) ^ 6 * (1 / t + 1) :=
        mul_le_mul_of_nonneg_left hl1 (pow_nonneg h0 6)
    _ = (t * (2 - t)) ^ 5 * (2 - t) + (t * (2 - t)) ^ 6 := by rw [mul_add, h5, mul_one]
    _ ≤ 1 * 2 + 1 := by nlinarith
    _ = 3 := by norm_num

theorem csA_log_val :
    (-2109479 : ℚ) / 10 ^ 8 + 6 * (15 / (14 ! * 14)) ≤
        pI 0 2 csA 6 * (6931471803 / 10 ^ 10) - pJ csA 6 ∧
      pI 0 2 csA 6 * (6931471808 / 10 ^ 10) - pJ csA 6 + 6 * (15 / (14 ! * 14)) ≤
        -2109477 / 10 ^ 8 ∧ 0 ≤ pI 0 2 csA 6 := by
  decide +kernel

/-- **`−0.02109479 ≤ ∫₀² η◦² log t ≤ −0.02109477`** (value `−0.0210947786988…`). -/
theorem integral_P0_sq_log : -0.02109479 ≤ ∫ t in (0 : ℝ)..2, P0 t ^ 2 * Real.log t ∧
    ∫ t in (0 : ℝ)..2, P0 t ^ 2 * Real.log t ≤ -0.02109477 := by
  have hI := integral_pow_log_mul_pH csA 5
  push_cast at hI
  have hc : IntervalIntegrable (fun t : ℝ => P0 t ^ 2 * Real.log t) volume 0 2 := by
    have e : (fun t : ℝ => P0 t ^ 2 * Real.log t) =
        fun t => (t ^ 5 * (2 - t) ^ 6 * Real.exp (-(t - 1) ^ 2)) * (t * Real.log t) := by
      funext t; rw [P0_sq]; ring
    rw [e]
    exact ((by fun_prop : Continuous fun t : ℝ => t ^ 5 * (2 - t) ^ 6 * Real.exp (-(t - 1) ^ 2)).mul
      Real.continuous_mul_log).intervalIntegrable _ _
  have hd : |(∫ t in (0 : ℝ)..2, P0 t ^ 2 * Real.log t) -
      ∫ t in (0 : ℝ)..2, t ^ (5 + 1) * Real.log t * pH csA t| ≤ (3 * (15 / (14 ! * 14))) * |(2 : ℝ) - 0| := by
    have hp : IntervalIntegrable (fun t : ℝ => t ^ (5 + 1) * Real.log t * pH csA t) volume 0 2 :=
      ((continuous_pow_mul_log 5).mul (continuous_pH csA)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hc hp]
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le (by norm_num)] at ht
    rw [Real.norm_eq_abs]
    have h := P0_sq_approx ht.1.le ht.2
    have e : P0 t ^ 2 * Real.log t - t ^ (5 + 1) * Real.log t * pH csA t =
        (P0 t ^ 2 - t ^ 6 * pH csA t) * Real.log t := by ring
    rw [e, abs_mul]
    have hl := tt_log_le ht.1 ht.2
    calc |P0 t ^ 2 - t ^ 6 * pH csA t| * |Real.log t| ≤
          (t * (2 - t)) ^ 6 * (15 / (14 ! * 14)) * |Real.log t| :=
          mul_le_mul_of_nonneg_right h (abs_nonneg _)
      _ = (t * (2 - t)) ^ 6 * |Real.log t| * (15 / (14 ! * 14)) := by ring
      _ ≤ 3 * (15 / (14 ! * 14)) := mul_le_mul_of_nonneg_right hl (by positivity)
  rw [hI] at hd
  have hq := csA_log_val
  have q1 := (Rat.cast_le (K := ℝ)).2 hq.1
  have q2 := (Rat.cast_le (K := ℝ)).2 hq.2.1
  have q3 := (Rat.cast_le (K := ℝ)).2 hq.2.2
  push_cast at q1 q2 q3 hd
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have m1 := mul_le_mul_of_nonneg_left l1.le q3
  have m2 := mul_le_mul_of_nonneg_left l2.le q3
  rw [abs_le] at hd
  constructor <;> nlinarith [hd.1, hd.2]

end TernaryGoldbach.MajorArcs.PolyNum
