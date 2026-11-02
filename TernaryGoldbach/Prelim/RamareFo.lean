import TernaryGoldbach.Prelim.RamareConv
import TernaryGoldbach.Prelim.RamareHarm

/-!
# The odd harmonic sum: `V(x) = ½ log x + ½(γ + log 2) + O*(0.64 x^{−1/3})` for all `x > 0`

`Fo(x) = V(x) − ½ log x − C_γ`, `C_γ = ½(γ + log 2)`:
* `x < 1`: `V = 0`, and `|½ log(1/x) − C_γ| x^{1/3} ≤ max(C_γ, 3/(2e)) ≤ 0.64`;
* `x ∈ [1, 3)`: `V = 1`;
* `x ∈ [2m − 1, 2m + 1)`, `m ≥ 2`: `Fo(x) = ½ log(2m/x) + F(2m) − ½F(m)` with `F(n) = H_n − log n − γ`
  (`harm_bounds`), so `|Fo(x)| ≤ 1/(4m²) + 1/(4m − 2)`.
-/

open Finset Real

namespace TernaryGoldbach.Prelim.RamPf

/-- `C_γ = ½(γ + log 2)`. -/
noncomputable def Cg : ℝ := (eulerMascheroniConstant + Real.log 2) / 2

/-- `Fo(x) = V(x) − ½ log x − C_γ`. -/
noncomputable def Fo (x : ℝ) : ℝ := V x - (Real.log x / 2 + Cg)

theorem harmonic_eight : ((harmonic 8 : ℚ) : ℝ) = 761 / 280 := by
  rw [show harmonic 8 = 761 / 280 by norm_num [harmonic, Finset.sum_range_succ]]; push_cast; ring

theorem log_eight : Real.log (8 : ℕ) = 3 * Real.log 2 := by
  rw [show ((8 : ℕ) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring

theorem gamma_le : eulerMascheroniConstant ≤ 0.5829 := by
  have h := (harm_bounds (n := 8) (by norm_num)).1
  rw [harmonic_eight, log_eight] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

theorem gamma_ge : 0.5759 ≤ eulerMascheroniConstant := by
  have h := (harm_bounds (n := 8) (by norm_num)).2
  rw [harmonic_eight, log_eight] at h
  have := Real.log_two_lt_d9
  push_cast at h
  linarith

theorem Cg_le : Cg ≤ 0.6381 := by
  have := gamma_le; have := Real.log_two_lt_d9; unfold Cg; linarith

theorem Cg_ge : 0.6345 ≤ Cg := by
  have := gamma_ge; have := Real.log_two_gt_d9; unfold Cg; linarith

/-- `∑_{b ≤ 2m} [b odd]/b = H_{2m} − ½ H_m`. -/
theorem oddsum (m : ℕ) :
    ∑ b ∈ Icc 1 (2 * m), vO b = ((harmonic (2 * m) : ℚ) : ℝ) - ((harmonic m : ℚ) : ℝ) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_Icc_succ_top (by omega),
      sum_Icc_succ_top (by omega), ih, harmonic_succ, harmonic_succ, harmonic_succ]
    have h1 : vO (2 * m + 1) = 1 / ((2 * m + 1 : ℕ) : ℝ) := by
      rw [vO_apply, if_pos (by exact odd_two_mul_add_one m), one_div]
    have h2 : vO (2 * m + 1 + 1) = 0 := by
      rw [vO_apply, if_neg]
      rw [Nat.not_odd_iff_even]; exact ⟨m + 1, by ring⟩
    rw [h1, h2]
    push_cast
    field_simp
    ring

theorem oddsum' (m : ℕ) (hm : 1 ≤ m) :
    ∑ b ∈ Icc 1 (2 * m - 1), vO b = ((harmonic (2 * m) : ℚ) : ℝ) - ((harmonic m : ℚ) : ℝ) / 2 := by
  have h2 : vO (2 * m) = 0 := by
    rw [vO_apply, if_neg]
    rw [Nat.not_odd_iff_even]; exact ⟨m, by ring⟩
  have h := sum_Icc_succ_top (show 1 ≤ 2 * m - 1 + 1 by omega) (fun b => vO b)
  rw [show 2 * m - 1 + 1 = 2 * m by omega, h2, add_zero] at h
  rw [← h, oddsum]

theorem rpow_third_le_of {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x ≤ c ^ 3) :
    x ^ ((1 : ℝ) / 3) ≤ c := by
  have := Real.rpow_le_rpow hx h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hc, show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num,
    Real.rpow_one] at this

/-- `x^{1/3} ≤ (x + 2)/3`. -/
theorem rpow_third_le {x : ℝ} (hx : 0 ≤ x) : x ^ ((1 : ℝ) / 3) ≤ (x + 2) / 3 := by
  set t := x ^ ((1 : ℝ) / 3)
  have ht : 0 ≤ t := Real.rpow_nonneg hx _
  have ht3 : t ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  nlinarith [sq_nonneg (t - 1), mul_nonneg ht (sq_nonneg (t - 1))]

theorem Fo_small {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : |Fo x| * x ^ ((1 : ℝ) / 3) ≤ 0.64 := by
  have hV : V x = 0 := by
    rw [V, Nat.floor_eq_zero.2 hx1]; simp
  rw [Fo, hV, zero_sub, abs_neg]
  have hl : Real.log x < 0 := Real.log_neg hx0 hx1
  have hcg := Cg_le
  have hcg0 := Cg_ge
  have hr0 : 0 < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hx0 _
  have hr1 : x ^ ((1 : ℝ) / 3) ≤ 1 := Real.rpow_le_one hx0.le hx1.le (by norm_num)
  rcases le_or_gt (-(Real.log x / 2)) Cg with h | h
  · have : |Real.log x / 2 + Cg| ≤ Cg := by rw [abs_le]; constructor <;> linarith
    nlinarith
  · -- `½ log(1/x) x^{1/3} ≤ 3/(2e)`, with `u = x^{−1/3}`
    have habs : |Real.log x / 2 + Cg| ≤ -(Real.log x / 2) := by rw [abs_le]; constructor <;> linarith
    set u := x ^ (-((1 : ℝ) / 3)) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hx0 _
    have hlu : Real.log u = -(Real.log x / 3) := by rw [hu, Real.log_rpow hx0]; ring
    have hxu : x ^ ((1 : ℝ) / 3) * u = 1 := by
      rw [hu, ← Real.rpow_add hx0]; norm_num
    have hle : Real.log u ≤ u / Real.exp 1 := by
      have := Real.log_le_sub_one_of_pos (div_pos hu0 (Real.exp_pos 1))
      rw [Real.log_div hu0.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
      linarith
    have he : 2.718 ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have hue : u / Real.exp 1 ≤ u / 2.718 := div_le_div_of_nonneg_left hu0.le (by norm_num) he
    -- `−(log x)/2 · x^{1/3} = (3/2) log u · x^{1/3} ≤ (3/2) (u/2.718) x^{1/3} = 3/(2·2.718)`
    have h3 : -(Real.log x / 2) * x ^ ((1 : ℝ) / 3) ≤ 3 / 2 * (u / 2.718) * x ^ ((1 : ℝ) / 3) := by
      apply mul_le_mul_of_nonneg_right _ hr0.le
      linarith
    have h4 : 3 / 2 * (u / 2.718) * x ^ ((1 : ℝ) / 3) = 3 / (2 * 2.718) := by
      field_simp; linarith [hxu]
    calc |Real.log x / 2 + Cg| * x ^ ((1 : ℝ) / 3) ≤ -(Real.log x / 2) * x ^ ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right habs hr0.le
      _ ≤ 0.64 := by rw [h4] at h3; linarith

theorem Fo_one {x : ℝ} (hx1 : 1 ≤ x) (hx3 : x < 3) : |Fo x| * x ^ ((1 : ℝ) / 3) ≤ 0.64 := by
  have hx0 : 0 < x := by linarith
  have hV : V x = 1 := by
    rw [V]
    rcases lt_or_ge x 2 with h | h
    · rw [show ⌊x⌋₊ = 1 from Nat.floor_eq_iff hx0.le |>.2 ⟨by norm_num; linarith, by norm_num; linarith⟩]
      simp [vO_apply]
    · rw [show ⌊x⌋₊ = 2 from Nat.floor_eq_iff hx0.le |>.2 ⟨by norm_num; linarith, by norm_num; linarith⟩]
      rw [show (2 : ℕ) = 1 + 1 from rfl, sum_Icc_succ_top (by norm_num)]
      simp [vO_apply]
  rw [Fo, hV]
  have hcg := Cg_le
  have hcg0 := Cg_ge
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hl3 : Real.log x ≤ Real.log 3 := Real.log_le_log hx0 hx3.le
  have h3 : Real.log 3 < 1.0987 := by have := Real.log_three_lt_d9; linarith
  have habs : |1 - (Real.log x / 2 + Cg)| ≤ 0.3655 := by rw [abs_le]; constructor <;> linarith
  have hr : x ^ ((1 : ℝ) / 3) ≤ 1.443 := rpow_third_le_of hx0.le (by norm_num) (by nlinarith)
  have hr0 : 0 ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx0.le _
  nlinarith [abs_nonneg (1 - (Real.log x / 2 + Cg))]

theorem Fo_large {x : ℝ} (hx3 : 3 ≤ x) : |Fo x| * x ^ ((1 : ℝ) / 3) ≤ 0.64 := by
  have hx0 : 0 < x := by linarith
  set n := ⌊x⌋₊ with hn
  have hn3 : 3 ≤ n := Nat.le_floor (by exact_mod_cast hx3)
  set m := (n + 1) / 2 with hm
  have hm2 : 2 ≤ m := by omega
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hm1 : ((2 * m - 1 : ℕ) : ℝ) ≤ x := le_trans (by exact_mod_cast (by omega : 2 * m - 1 ≤ n)) hnx
  have hm1' : 2 * (m : ℝ) - 1 ≤ x := by
    rw [Nat.cast_sub (by omega)] at hm1; push_cast at hm1; linarith
  have hm3 : x < 2 * (m : ℝ) + 1 := by
    have : (n : ℝ) ≤ 2 * m := by exact_mod_cast (by omega : n ≤ 2 * m)
    linarith
  -- `V(x) = H_{2m} − ½ H_m`
  have hV : V x = ((harmonic (2 * m) : ℚ) : ℝ) - ((harmonic m : ℚ) : ℝ) / 2 := by
    rw [V, ← hn]
    rcases (show n = 2 * m - 1 ∨ n = 2 * m by omega) with h | h
    · rw [h, oddsum' m (by omega)]
    · rw [h, oddsum]
  have hF2 := harm_bounds (n := 2 * m) (by omega)
  have hF1 := harm_bounds (n := m) (by omega)
  have hm0 : (0 : ℝ) < m := by positivity
  have hlog2m : Real.log ((2 * m : ℕ) : ℝ) = Real.log 2 + Real.log m := by
    push_cast; rw [Real.log_mul (by norm_num) hm0.ne']
  rw [hlog2m] at hF2
  push_cast at hF2
  -- `Fo(x) = ½ log(2m/x) + (F(2m) − ½ F(m))`
  set A := ((harmonic (2 * m) : ℚ) : ℝ) - (Real.log 2 + Real.log m) - eulerMascheroniConstant
  set B := ((harmonic m : ℚ) : ℝ) - Real.log m - eulerMascheroniConstant
  have hFo : Fo x = (Real.log 2 + Real.log m - Real.log x) / 2 + (A - B / 2) := by
    rw [Fo, hV, Cg]; simp only [A, B]; ring
  -- the two pieces
  have hAB : |A - B / 2| ≤ 1 / (4 * (m : ℝ) ^ 2) := by
    rw [abs_le]
    obtain ⟨a1, a2⟩ := hF2
    obtain ⟨b1, b2⟩ := hF1
    have e1 : 1 / (2 * ((2 * (m : ℝ)) + 1)) - 1 / (2 * (m : ℝ)) / 2 ≥ -(1 / (4 * (m : ℝ) ^ 2)) := by
      rw [ge_iff_le, neg_le_sub_iff_le_add]
      rw [div_add_div _ _ (by positivity) (by positivity), div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e2 : 1 / (2 * (2 * (m : ℝ))) - 1 / (2 * ((m : ℝ) + 1)) / 2 ≤ 1 / (4 * (m : ℝ) ^ 2) := by
      rw [div_div, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    constructor <;> linarith
  have hm1'' : (0 : ℝ) < 2 * m - 1 := by linarith
  have hL : |Real.log (2 * m / x)| ≤ 1 / (2 * (m : ℝ) - 1) := by
    rw [abs_le]
    constructor
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hx0 (by positivity : (0 : ℝ) < 2 * m))
      have e2 : Real.log (x / (2 * m)) = -Real.log (2 * m / x) := by
        rw [← Real.log_inv, inv_div]
      rw [e2] at h1
      have h5 : x / (2 * m) - 1 ≤ 1 / (2 * (m : ℝ) - 1) := by
        rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) hm1'']; nlinarith
      linarith
    · have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < 2 * m) hx0)
      have h5 : 2 * (m : ℝ) / x - 1 ≤ 1 / (2 * m - 1) := by
        rw [div_sub_one hx0.ne', div_le_div_iff₀ hx0 hm1'']; nlinarith
      linarith
  have hlg : |(Real.log 2 + Real.log m - Real.log x) / 2| ≤ 1 / (4 * (m : ℝ) - 2) := by
    have e : Real.log 2 + Real.log m - Real.log x = Real.log (2 * m / x) := by
      rw [Real.log_div (by positivity) hx0.ne', Real.log_mul (by norm_num) hm0.ne']
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h6 : (1 : ℝ) / (4 * m - 2) = 1 / (2 * m - 1) / 2 := by
      rw [show (4 * (m : ℝ) - 2) = (2 * m - 1) * 2 by ring, div_div]
    rw [h6]
    exact div_le_div_of_nonneg_right hL (by norm_num)
  have hFo_le : |Fo x| ≤ 1 / (4 * (m : ℝ) ^ 2) + 1 / (4 * (m : ℝ) - 2) := by
    rw [hFo]; exact (abs_add_le _ _).trans (by linarith)
  have hr : x ^ ((1 : ℝ) / 3) ≤ (2 * (m : ℝ) + 3) / 3 := by
    have := rpow_third_le hx0.le; linarith
  have hr0 : 0 ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx0.le _
  have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  -- `(1/(4m²) + 1/(4m−2)) (2m+3)/3 ≤ 7/48 + 7/18 ≤ 0.64`
  have k1 : 1 / (4 * (m : ℝ) ^ 2) * ((2 * m + 3) / 3) ≤ 7 / 48 := by
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have k2 : 1 / (4 * (m : ℝ) - 2) * ((2 * m + 3) / 3) ≤ 7 / 18 := by
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
  calc |Fo x| * x ^ ((1 : ℝ) / 3)
      ≤ (1 / (4 * (m : ℝ) ^ 2) + 1 / (4 * (m : ℝ) - 2)) * ((2 * m + 3) / 3) :=
        mul_le_mul hFo_le hr hr0 (add_nonneg (by positivity)
          (le_of_lt (one_div_pos.2 (by linarith))))
    _ ≤ 0.64 := by rw [add_mul]; linarith

/-- **`|V(x) − ½ log x − ½(γ + log 2)| ≤ 0.64 x^{−1/3}`** for `x > 0`. -/
theorem Fo_bound {x : ℝ} (hx0 : 0 < x) : |Fo x| * x ^ ((1 : ℝ) / 3) ≤ 0.64 := by
  rcases lt_or_ge x 1 with h | h
  · exact Fo_small hx0 h
  rcases lt_or_ge x 3 with h' | h'
  · exact Fo_one h h'
  · exact Fo_large h'

end TernaryGoldbach.Prelim.RamPf
