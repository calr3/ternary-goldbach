import TernaryGoldbach.Prelim.SchoenfeldInd

/-!
# El Marraki's inequality

For `x ≥ 1`, with `M(t) = ∑_{n ≤ t} μ(n)` and `m(x) = ∑_{n ≤ x} μ(n)/n`:
`|m(x)| ≤ |M(x)|/x + (log x + ∫₁^x |M(t)|/t dt)/x` (`el_marraki`).

From Abel summation, `m(x) = M(x)/x + ∫₁^x M(t)/t² dt` (`m_abel`); and from `∑_{n ≤ y} M(y/n) = 1`,
`log x = ∑_{n ≤ x} ∫₁^{x/n} M(t)/t dt = ∫₁^x ⌊x/t⌋ M(t)/t dt` (`log_eq_int_floor`), so
`x ∫₁^x M(t)/t² dt − log x = ∫₁^x {x/t} M(t)/t dt`.
-/

open Finset MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sch

/-- `M(t) = M(⌊t⌋)` as a function of a real variable. -/
noncomputable def Mr (t : ℝ) : ℝ := Mn ⌊t⌋₊

theorem Mn_zero : Mn 0 = 0 := by simp [Mn]

theorem abs_Mn_le (k : ℕ) : |Mn k| ≤ k := by
  unfold Mn
  calc |∑ m ∈ Ioc 0 k, (μ m : ℝ)| ≤ ∑ m ∈ Ioc 0 k, |(μ m : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Ioc 0 k, (1 : ℝ) := sum_le_sum fun m _ => by
        have := ArithmeticFunction.abs_moebius_le_one (n := m); exact_mod_cast this
    _ = k := by simp

/-- A function of `⌊t/c⌋` is interval integrable on `[a, b]`, `0 ≤ a ≤ b`, `c > 0`. -/
theorem intervalIntegrable_step (φ : ℕ → ℝ) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c) :
    IntervalIntegrable (fun t => φ ⌊t / c⌋₊) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hm : Measurable (fun t : ℝ => φ ⌊t / c⌋₊) :=
    (measurable_from_nat (f := φ)).comp (Nat.measurable_floor.comp (measurable_id.div_const c))
  refine IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable
    (∑ k ∈ range (⌊b / c⌋₊ + 1), |φ k|) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [Real.norm_eq_abs]
  have hk : ⌊t / c⌋₊ ∈ range (⌊b / c⌋₊ + 1) := by
    rw [mem_range]
    have := Nat.floor_le_floor (div_le_div_of_nonneg_right ht.2 hc.le) (R := ℝ)
    omega
  exact single_le_sum (f := fun k => |φ k|) (fun k _ => abs_nonneg _) hk

/-- **Abel summation**: `m(x) = M(x)/x + ∫₁^x M(t)/t² dt`. -/
theorem m_abel {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n = Mr x / x + ∫ t in (1 : ℝ)..x, Mr t / t ^ 2 := by
  have h := sum_mul_eq_sub_integral_mul₀ (c := fun n => (μ n : ℝ)) (f := fun t : ℝ => t⁻¹)
    (by simp) x (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      have : Set.EqOn (deriv fun t : ℝ => t⁻¹) (fun t => -(t ^ 2)⁻¹) (Set.Icc 1 x) := fun t _ => by
        simp [deriv_inv]
      refine (IntegrableOn.congr_fun ?_ this.symm measurableSet_Icc)
      exact (ContinuousOn.integrableOn_compact isCompact_Icc
        (ContinuousOn.neg (ContinuousOn.inv₀ (continuousOn_pow 2) fun t ht => by
          have : 0 < t := by linarith [ht.1]
          positivity))))
  have e1 : ∑ k ∈ Icc 0 ⌊x⌋₊, (fun t : ℝ => t⁻¹) k * (μ k : ℝ) = ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n := by
    rw [show Icc 0 ⌊x⌋₊ = insert 0 (Icc 1 ⌊x⌋₊) by ext k; simp; omega, sum_insert (by simp)]
    simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
    exact sum_congr rfl fun n _ => by ring
  have e2 : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, (μ k : ℝ) = Mr t := by
    intro t
    unfold Mr Mn
    rw [show Icc 0 ⌊t⌋₊ = insert 0 (Ioc 0 ⌊t⌋₊) by ext k; simp, sum_insert (by simp)]
    simp
  rw [e1, e2] at h
  rw [h, intervalIntegral.integral_of_le hx]
  have : ∫ t in Set.Ioc 1 x, deriv (fun t : ℝ => t⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, (μ k : ℝ) =
      -∫ t in Set.Ioc 1 x, Mr t / t ^ 2 := by
    rw [← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [deriv_inv', e2]
    ring
  rw [this]; ring

theorem ae_ne_one : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
  rw [ae_iff]; simp

theorem ae_ne_pt (a : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
  rw [ae_iff]; simp

theorem intervalIntegrable_Mr_div {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) :
    IntervalIntegrable (fun t => Mr (t / c) / t) volume a b := by
  have h1 := intervalIntegrable_step Mn ha.le hab hc
  have h2 : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc a b) :=
    ContinuousOn.inv₀ continuousOn_id fun t ht => by
      rw [Set.uIcc_of_le hab] at ht; exact (lt_of_lt_of_le ha ht.1).ne'
  have := h1.mul_continuousOn h2
  simpa [Mr, div_eq_mul_inv] using this

/-- The kernel of El Marraki's identity: `M(t)/t`. -/
noncomputable def gM (t : ℝ) : ℝ := Mr t / t

theorem gM_zero_of_lt {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : gM t = 0 := by
  unfold gM Mr; rw [Nat.floor_eq_zero.2 h1, Mn_zero, zero_div]

/-- `∫₁^x M(y/n)/y dy = ∫₁^{x/n} M(t)/t dt`. -/
theorem integral_Mr_div {x : ℝ} {n : ℕ} (hn : 1 ≤ n) (hx : (n : ℝ) ≤ x) :
    ∫ y in (1 : ℝ)..x, Mr (y / n) / y = ∫ t in (1 : ℝ)..(x / n), gM t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ y, Mr (y / n) / y = (1 / (n : ℝ)) * gM (y / n) := by
    intro y; unfold gM
    by_cases hy : y = 0
    · simp [hy]
    · field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div gM hn0.ne', smul_eq_mul]
  have hle : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact_mod_cast hn
  have hle2 : (1 : ℝ) ≤ x / n := by rw [le_div_iff₀ hn0]; linarith
  have hI1 : IntervalIntegrable gM volume (1 / n) 1 := by
    have := intervalIntegrable_Mr_div (c := 1) (by positivity) hle one_pos
    simp only [div_one] at this; exact this
  have hI2 : IntervalIntegrable gM volume 1 (x / n) := by
    have := intervalIntegrable_Mr_div (c := 1) one_pos hle2 one_pos
    simp only [div_one] at this; exact this
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hz : ∫ t in (1 / (n : ℝ))..1, gM t = 0 := by
    have : ∫ t in (1 / (n : ℝ))..1, gM t = ∫ t in (1 / (n : ℝ))..1, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_one] with t ht hmem
      rw [Set.uIoc_of_le hle] at hmem
      exact gM_zero_of_lt (le_trans (by positivity) hmem.1.le) (lt_of_le_of_ne hmem.2 ht)
    rw [this, intervalIntegral.integral_zero]
  rw [← hsplit, hz, zero_add]
  field_simp

/-- `∑_{n ≤ y} M(y/n) = 1` in the real variable. -/
theorem sum_Mr_div {x y : ℝ} (hy1 : 1 ≤ y) (hyx : y ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, Mr (y / n) = 1 := by
  have hfy : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy1)
  have hfx : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hyx
  have e : ∀ n ∈ Icc 1 ⌊x⌋₊, Mr (y / n) = if n ≤ ⌊y⌋₊ then Mn (⌊y⌋₊ / n) else 0 := by
    intro n hn
    unfold Mr
    rw [Nat.floor_div_natCast]
    split_ifs with h
    · rfl
    · rw [Nat.div_eq_of_lt (by omega), Mn_zero]
  rw [sum_congr rfl e, ← sum_filter]
  have : (Icc 1 ⌊x⌋₊).filter (fun n => n ≤ ⌊y⌋₊) = Ioc 0 ⌊y⌋₊ := by
    ext n; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  rw [this]
  exact sum_Mn_div hfy

/-- **`log x = ∑_{n ≤ x} ∫₁^{x/n} M(t)/t dt`**. -/
theorem log_eq_sum_int {x : ℝ} (hx : 1 ≤ x) :
    Real.log x = ∑ n ∈ Icc 1 ⌊x⌋₊, ∫ t in (1 : ℝ)..(x / n), gM t := by
  have h1 : ∫ y in (1 : ℝ)..x, y⁻¹ = Real.log x := by
    rw [integral_inv (by rw [Set.uIcc_of_le hx]; simp), div_one]
  have h2 : ∫ y in (1 : ℝ)..x, y⁻¹ = ∫ y in (1 : ℝ)..x, ∑ n ∈ Icc 1 ⌊x⌋₊, Mr (y / n) / y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hx] at hy
    rw [← sum_div, sum_Mr_div hy.1 hy.2, one_div]
  rw [← h1, h2, intervalIntegral.integral_finsetSum fun n hn =>
    intervalIntegrable_Mr_div one_pos hx (by exact_mod_cast (mem_Icc.1 hn).1)]
  refine sum_congr rfl fun n hn => ?_
  have hn1 := (mem_Icc.1 hn).1
  have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.1 hn).2) (Nat.floor_le (by linarith))
  exact integral_Mr_div hn1 hnx

theorem intervalIntegrable_gM {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable gM volume a b := by
  have := intervalIntegrable_Mr_div (c := 1) ha hab one_pos
  simp only [div_one] at this; exact this

/-- `∫₁^{c} M(t)/t dt = ∫₁^x 1_{t ≤ c} M(t)/t dt` for `1 ≤ c ≤ x`. -/
theorem integral_indicator {x c : ℝ} (hc1 : 1 ≤ c) (hcx : c ≤ x) :
    ∫ t in (1 : ℝ)..c, gM t = ∫ t in (1 : ℝ)..x, (Set.Iic c).indicator gM t := by
  have hI1 : IntervalIntegrable ((Set.Iic c).indicator gM) volume 1 c :=
    (intervalIntegrable_gM one_pos hc1).congr (fun t ht => by
      rw [Set.uIoc_of_le hc1] at ht
      rw [Set.indicator_of_mem (show t ∈ Set.Iic c from ht.2)])
  have hI2 : IntervalIntegrable ((Set.Iic c).indicator gM) volume c x := by
    refine (intervalIntegrable_const (c := (0 : ℝ))).congr fun t ht => ?_
    rw [Set.uIoc_of_le hcx] at ht
    rw [Set.indicator_of_notMem (show t ∉ Set.Iic c by simp; exact ht.1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have h2 : ∫ t in c..x, (Set.Iic c).indicator gM t = ∫ t in c..x, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t ht
    rw [Set.uIoc_of_le hcx] at ht
    rw [Set.indicator_of_notMem (show t ∉ Set.Iic c by simp; exact ht.1)]
  rw [h2, intervalIntegral.integral_zero, add_zero]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hc1] at ht
  rw [Set.indicator_of_mem (show t ∈ Set.Iic c from ht.2)]

theorem sum_indicator_eq {x t : ℝ} (ht1 : 1 ≤ t) (htx : t ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (Set.Iic (x / n)).indicator gM t = gM t * ⌊x / t⌋₊ := by
  have ht0 : 0 < t := by linarith
  have e : ∀ n ∈ Icc 1 ⌊x⌋₊, (Set.Iic (x / n)).indicator gM t = if n ≤ ⌊x / t⌋₊ then gM t else 0 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
    by_cases h : n ≤ ⌊x / t⌋₊
    · rw [if_pos h, Set.indicator_of_mem]
      simp only [Set.mem_Iic]
      have : (n : ℝ) ≤ x / t := le_trans (by exact_mod_cast h) (Nat.floor_le (div_nonneg (by linarith) ht0.le))
      rw [le_div_iff₀ hn0]; rw [le_div_iff₀ ht0] at this; linarith
    · rw [if_neg h, Set.indicator_of_notMem]
      simp only [Set.mem_Iic, not_le]
      push Not at h
      have : x / t < n := by
        have := Nat.lt_floor_add_one (x / t)
        have h' : ((⌊x / t⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h
        linarith
      rw [div_lt_iff₀ hn0]; rw [div_lt_iff₀ ht0] at this; linarith
  rw [sum_congr rfl e, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have : (Icc 1 ⌊x⌋₊).filter (fun n => n ≤ ⌊x / t⌋₊) = Icc 1 ⌊x / t⌋₊ := by
    ext n; simp only [mem_filter, mem_Icc]
    have : ⌊x / t⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (div_le_self (by linarith) ht1)
    omega
  rw [this]; simp

/-- **`log x = ∫₁^x ⌊x/t⌋ M(t)/t dt`**, and the integrand is integrable. -/
theorem log_eq_int_floor {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t => gM t * ⌊x / t⌋₊) volume 1 x ∧
      Real.log x = ∫ t in (1 : ℝ)..x, gM t * ⌊x / t⌋₊ := by
  have hint : ∀ n ∈ Icc 1 ⌊x⌋₊, IntervalIntegrable ((Set.Iic (x / n)).indicator gM) volume 1 x := by
    intro n hn
    have := intervalIntegrable_gM one_pos hx
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx] at this ⊢
    exact this.indicator measurableSet_Iic
  have hsum : IntervalIntegrable (fun t => ∑ n ∈ Icc 1 ⌊x⌋₊, (Set.Iic (x / n)).indicator gM t) volume 1 x := by
    convert IntervalIntegrable.sum (Icc 1 ⌊x⌋₊) hint using 1
    ext t; simp [Finset.sum_apply]
  have hcongr : ∀ t ∈ Set.uIcc 1 x, ∑ n ∈ Icc 1 ⌊x⌋₊, (Set.Iic (x / n)).indicator gM t = gM t * ⌊x / t⌋₊ := by
    intro t ht; rw [Set.uIcc_of_le hx] at ht; exact sum_indicator_eq ht.1 ht.2
  refine ⟨hsum.congr (fun t ht => hcongr t (Set.uIoc_subset_uIcc ht)), ?_⟩
  rw [log_eq_sum_int hx, ← intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_finsetSum hint]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
  have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.1 hn).2) (Nat.floor_le (by linarith))
  exact integral_indicator (by rw [le_div_iff₀ hn0]; linarith) (div_le_self (by linarith)
    (by exact_mod_cast (mem_Icc.1 hn).1))

/-- **El Marraki's inequality**: `|m(x)| ≤ |M(x)|/x + (log x + ∫₁^x |M(t)|/t dt)/x`. -/
theorem el_marraki {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤
      |Mr x| / x + (Real.log x + ∫ t in (1 : ℝ)..x, |gM t|) / x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hfl, hlog⟩ := log_eq_int_floor hx
  have hg := intervalIntegrable_gM one_pos hx
  have hcont : ContinuousOn (fun t : ℝ => x / t) (Set.uIcc 1 x) :=
    ContinuousOn.div continuousOn_const continuousOn_id fun t ht => by
      rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
  have hg2 : IntervalIntegrable (fun t => gM t * (x / t)) volume 1 x := hg.mul_continuousOn hcont
  have hI : x * ∫ t in (1 : ℝ)..x, Mr t / t ^ 2 = ∫ t in (1 : ℝ)..x, gM t * (x / t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have : t ≠ 0 := by linarith [ht.1]
    unfold gM; field_simp
  have hdiff : x * (∫ t in (1 : ℝ)..x, Mr t / t ^ 2) - Real.log x =
      ∫ t in (1 : ℝ)..x, (gM t * (x / t) - gM t * ⌊x / t⌋₊) := by
    rw [hI, hlog, ← intervalIntegral.integral_sub hg2 hfl]
  have hbound : |∫ t in (1 : ℝ)..x, (gM t * (x / t) - gM t * ⌊x / t⌋₊)| ≤ ∫ t in (1 : ℝ)..x, |gM t| := by
    refine (intervalIntegral.abs_integral_le_integral_abs hx).trans ?_
    refine intervalIntegral.integral_mono_on hx (hg2.sub hfl).abs hg.abs fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : 0 ≤ x / t - ⌊x / t⌋₊ := sub_nonneg.2 (Nat.floor_le (by positivity))
    have h2 : x / t - ⌊x / t⌋₊ < 1 := by have := Nat.lt_floor_add_one (x / t); linarith
    rw [← mul_sub, abs_mul, abs_of_nonneg h1]
    nlinarith [abs_nonneg (gM t)]
  have habs : |∫ t in (1 : ℝ)..x, Mr t / t ^ 2| ≤ (Real.log x + ∫ t in (1 : ℝ)..x, |gM t|) / x := by
    rw [le_div_iff₀ hx0, ← abs_of_pos hx0, ← abs_mul, abs_of_pos hx0, mul_comm]
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    have := abs_sub_abs_le_abs_sub (x * ∫ t in (1 : ℝ)..x, Mr t / t ^ 2) (Real.log x)
    rw [hdiff, abs_of_nonneg hl] at this
    linarith
  rw [m_abel hx]
  calc |Mr x / x + ∫ t in (1 : ℝ)..x, Mr t / t ^ 2| ≤ |Mr x / x| + |∫ t in (1 : ℝ)..x, Mr t / t ^ 2| :=
        abs_add_le _ _
    _ ≤ |Mr x| / x + (Real.log x + ∫ t in (1 : ℝ)..x, |gM t|) / x := by
        rw [abs_div, abs_of_pos hx0]; linarith

end TernaryGoldbach.Prelim.Sch
