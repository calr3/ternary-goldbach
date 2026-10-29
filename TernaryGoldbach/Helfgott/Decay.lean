import TernaryGoldbach.Helfgott.Defs

/-!
# Decay of Helfgott's smoothing functions

We prove Gaussian decay bounds

* `|η₊(t)| ≤ (25600/π) t e^{-t²/2}` (via `|h_H(t)| ≤ 128 H / π`), and
* `|η_*(t)| ≤ 144 κ² t² e^{-κ²t²/2}`,

for `t ≥ 0`.  From these, `∑ₙ Λ(n) |η(n/x)|` converges for `x > 0`, so `S_η(α, x)` is an
absolutely (and uniformly) convergent series.  The constants are crude; we only need
summability.

Proved, with no `sorry`.
-/

open MeasureTheory
open ArithmeticFunction (vonMangoldt_nonneg vonMangoldt_le_log)
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Helfgott

/-! ## Summability from Gaussian decay -/

/-- `e^{-ct²} ≤ e^{1/(4c)} e^{-t}`. -/
theorem exp_neg_sq_le (c t : ℝ) (hc : 0 < c) :
    Real.exp (-c * t ^ 2) ≤ Real.exp (1 / (4 * c)) * Real.exp (-t) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have : 0 ≤ c * (t - 1 / (2 * c)) ^ 2 := by positivity
  have e : c * (t - 1 / (2 * c)) ^ 2 = c * t ^ 2 - t + 1 / (4 * c) := by
    field_simp; ring
  linarith

/-- If `|η(t)| ≤ C tᵏ e^{-ct²}` for `t ≥ 0`, then `∑ₙ Λ(n) |η(n/x)|` converges for `x > 0`. -/
theorem summable_vonMangoldt_mul {η : ℝ → ℝ} {x C c : ℝ} {k : ℕ} (hx : 0 < x) (hc : 0 < c)
    (hη : ∀ t, 0 ≤ t → |η t| ≤ C * t ^ k * Real.exp (-c * t ^ 2)) :
    Summable fun n : ℕ => ‖((Λ n * η (n / x) : ℝ) : ℂ)‖ := by
  have hs := (Real.summable_pow_mul_exp_neg_nat_mul (k + 1) (inv_pos.2 hx)).mul_left
    (|C| * (x⁻¹) ^ k * Real.exp (1 / (4 * c)))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
  have ht : (0:ℝ) ≤ n / x := by positivity
  have hΛ : Λ n ≤ n := vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))
  calc Λ n * |η (n / x)| ≤ n * (|C| * (n / x) ^ k * (Real.exp (1 / (4 * c)) * Real.exp (-(n / x)))) := by
        refine mul_le_mul hΛ ((hη _ ht).trans ?_) (abs_nonneg _) (Nat.cast_nonneg n)
        refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
          (exp_neg_sq_le c _ hc) (Real.exp_pos _).le (by positivity)
    _ = _ := by
        rw [div_eq_mul_inv, mul_pow, neg_mul, mul_comm (x⁻¹) (n : ℝ)]
        ring

/-! ## `η_*` -/

theorem eta2_nonneg (r : ℝ) : 0 ≤ eta2 r := by
  unfold eta2; split_ifs <;> positivity

theorem eta2_le (r : ℝ) : eta2 r ≤ 3 := by
  unfold eta2
  have := Real.log_two_lt_d9
  split_ifs
  · have : max (Real.log 2 - |Real.log (2 * r)|) 0 ≤ Real.log 2 :=
      max_le (by linarith [abs_nonneg (Real.log (2 * r))]) (Real.log_nonneg (by norm_num))
    linarith
  · norm_num

theorem eta2_eq_zero {r : ℝ} (h : r ∉ Set.Ioo (1/4 : ℝ) 1) : eta2 r = 0 := by
  unfold eta2
  split_ifs with hr
  · simp only [Set.mem_Ioo, not_and_or, not_lt] at h
    rw [max_eq_right, mul_zero]
    rw [sub_nonpos]
    rcases h with h | h
    · rw [abs_of_nonpos (Real.log_nonpos (by positivity) (by linarith))]
      have : Real.log (2 * r) ≤ Real.log (1/2) := Real.log_le_log (by positivity) (by linarith)
      rw [one_div, Real.log_inv] at this
      linarith
    · rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
      exact Real.log_le_log (by norm_num) (by linarith)
  · rfl

theorem phi_le {u s : ℝ} (hu : 0 ≤ u) (h1 : u ≤ s) (h2 : s ≤ 4 * u) :
    phi s ≤ 16 * u ^ 2 * Real.exp (-u ^ 2 / 2) := by
  unfold phi
  have hs : 0 ≤ s := hu.trans h1
  apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity)
  · nlinarith
  · rw [Real.exp_le_exp]
    have : u ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hu h1 2
    linarith

theorem abs_mellinConv_eta2_phi_le {u : ℝ} (hu : 0 ≤ u) :
    |mellinConv eta2 phi u| ≤ 144 * u ^ 2 * Real.exp (-u ^ 2 / 2) := by
  set K := 3 * (16 * u ^ 2 * Real.exp (-u ^ 2 / 2)) * 4
  have hK : 0 ≤ K := by positivity
  set g := (Set.Ioo (1/4 : ℝ) 1).indicator fun _ => K
  have hgint : Integrable g := by
    refine (integrable_indicator_iff measurableSet_Ioo).2 ?_
    exact integrableOn_const.2 (Or.inr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top))
  have hbound : ∀ r, ‖eta2 r * phi (u / r) / r‖ ≤ g r := by
    intro r
    by_cases hr : r ∈ Set.Ioo (1/4 : ℝ) 1
    · simp only [g, Set.indicator_of_mem hr]
      obtain ⟨h1, h2⟩ := hr
      have hr0 : 0 < r := by linarith
      have hphi0 : 0 ≤ phi (u / r) := by unfold phi; positivity
      have hphi := phi_le (s := u / r) hu ((le_div_iff₀ hr0).2 (by nlinarith))
        ((div_le_iff₀ hr0).2 (by nlinarith))
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (eta2_nonneg r),
        abs_of_nonneg hphi0, abs_of_pos hr0, div_le_iff₀ hr0]
      calc eta2 r * phi (u / r) ≤ 3 * (16 * u ^ 2 * Real.exp (-u ^ 2 / 2)) :=
            mul_le_mul (eta2_le r) hphi hphi0 (by norm_num)
        _ ≤ K * r := by
            simp only [K]; nlinarith [show (0:ℝ) ≤ 16 * u ^ 2 * Real.exp (-u ^ 2 / 2) by positivity]
    · rw [eta2_eq_zero hr, zero_mul, zero_div, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hK) r
  have := norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioi 0)) hgint.integrableOn
    (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine (this.trans (setIntegral_le_integral hgint
    (Filter.Eventually.of_forall fun r => Set.indicator_nonneg (fun _ _ => hK) r))).trans ?_
  rw [integral_indicator measurableSet_Ioo, setIntegral_const, Real.volume_Ioo, smul_eq_mul,
    ENNReal.toReal_ofReal (by norm_num)]
  simp only [K]
  nlinarith [show (0:ℝ) ≤ u ^ 2 * Real.exp (-u ^ 2 / 2) by positivity]

theorem abs_etaStar_le {t : ℝ} (ht : 0 ≤ t) :
    |etaStar t| ≤ 144 * κ ^ 2 * t ^ 2 * Real.exp (-(κ ^ 2 / 2) * t ^ 2) := by
  have := abs_mellinConv_eta2_phi_le (u := κ * t) (by rw [κ]; positivity)
  unfold etaStar
  have e1 : 144 * κ ^ 2 * t ^ 2 * Real.exp (-(κ ^ 2 / 2) * t ^ 2) =
      144 * (κ * t) ^ 2 * Real.exp (-(κ * t) ^ 2 / 2) := by ring_nf
  rw [e1]; exact this

/-! ## `η₊` -/

theorem hBase_eq_zero {u : ℝ} (hu : 2 ≤ u) : hBase u = 0 := by
  unfold hBase
  split_ifs with h
  · have : u = 2 := le_antisymm h.2 hu
    subst this; norm_num
  · rfl

theorem abs_hBase_le (u : ℝ) : |hBase u| ≤ 64 * u ^ 2 := by
  unfold hBase
  split_ifs with h
  · obtain ⟨h0, h2⟩ := h
    have he : Real.exp (u - 1 / 2) ≤ 8 := by
      have : Real.exp (u - 1/2) ≤ Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    have h3 : (2 - u) ^ 3 ≤ 8 := by
      have : 0 ≤ 2 - u := by linarith
      nlinarith [pow_le_pow_left₀ this (show 2 - u ≤ 2 by linarith) 3]
    have h3' : 0 ≤ (2 - u) ^ 3 := pow_nonneg (by linarith) 3
    rw [abs_of_nonneg (by positivity)]
    calc u ^ 2 * (2 - u) ^ 3 * Real.exp (u - 1 / 2) ≤ u ^ 2 * 8 * 8 := by
          gcongr
      _ = 64 * u ^ 2 := by ring
  · simp; positivity

theorem abs_F_le {H : ℝ} (hH : 0 ≤ H) (y : ℝ) : |F H y| ≤ H / Real.pi := by
  unfold F
  rcases eq_or_ne (Real.log y) 0 with h | h
  · simp [h]; positivity
  · rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, div_le_div_iff₀ (by positivity) Real.pi_pos]
    have := Real.abs_sin_le_abs (x := H * Real.log y)
    rw [abs_mul, abs_of_nonneg hH] at this
    nlinarith [Real.pi_pos]

theorem abs_hH_le {H : ℝ} (hH0 : 0 ≤ H) {t : ℝ} (ht : 0 ≤ t) :
    |hH H t| ≤ 128 * H / Real.pi := by
  rcases ht.eq_or_lt with h0 | ht
  · subst h0
    have : hH H 0 = 0 := by
      unfold hH; simp [hBase]
    rw [this, abs_zero]; positivity
  set K := 64 * (H / Real.pi) * t ^ 2
  have hK : 0 ≤ K := by positivity
  have ht2 : 0 < t / 2 := by positivity
  set g := (Set.Ioi (t / 2)).indicator fun y : ℝ => K * y ^ (-3 : ℝ)
  have hgint : Integrable g := by
    refine (integrable_indicator_iff measurableSet_Ioi).2 ?_
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) ht2).const_mul K
  have hg0 : ∀ y, 0 ≤ g y := fun y => Set.indicator_nonneg
    (fun y hy => mul_nonneg hK (Real.rpow_nonneg (ht2.le.trans (le_of_lt hy)) _)) y
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ‖hBase (t / y) * F H y / y‖ ≤ g y := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy : (0:ℝ) < y := hy
    by_cases hyt : y ∈ Set.Ioi (t / 2)
    · simp only [g, Set.indicator_of_mem hyt]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hy, div_le_iff₀ hy]
      have hrp : y ^ (-3 : ℝ) * y = (y ^ 2)⁻¹ := by
        rw [Real.rpow_neg hy.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        field_simp; ring
      calc |hBase (t / y)| * |F H y| ≤ 64 * (t / y) ^ 2 * (H / Real.pi) :=
            mul_le_mul (abs_hBase_le _) (abs_F_le hH0 y) (abs_nonneg _) (by positivity)
        _ = K * y ^ (-3 : ℝ) * y := by
            rw [mul_assoc K, hrp]; simp only [K]; field_simp; ring
    · have : 2 ≤ t / y := by
        simp only [Set.mem_Ioi, not_lt] at hyt
        rw [le_div_iff₀ hy]; linarith
      rw [hBase_eq_zero this, zero_mul, zero_div, norm_zero]
      exact hg0 y
  have := norm_integral_le_of_norm_le hgint.integrableOn hbound
  rw [Real.norm_eq_abs] at this
  refine (this.trans (setIntegral_le_integral hgint (Filter.Eventually.of_forall hg0))).trans ?_
  rw [integral_indicator measurableSet_Ioi, MeasureTheory.integral_mul_left,
    integral_Ioi_rpow_of_lt (by norm_num) ht2]
  have : (t / 2) ^ ((-3 : ℝ) + 1) = 4 / t ^ 2 := by
    rw [show (-3 : ℝ) + 1 = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg ht2.le, Real.rpow_natCast]
    field_simp; ring
  rw [this]
  simp only [K]
  apply le_of_eq
  field_simp
  ring

theorem abs_etaPlus_le {t : ℝ} (ht : 0 ≤ t) :
    |etaPlus t| ≤ 128 * 200 / Real.pi * t ^ 1 * Real.exp (-(1 / 2) * t ^ 2) := by
  unfold etaPlus
  rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _), pow_one]
  have : -(1 / 2) * t ^ 2 = -t ^ 2 / 2 := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (abs_hH_le (by norm_num) ht) ht)
    (Real.exp_pos _).le

/-! ## Summability of the coefficients of `S_{η₊}` and `S_{η_*}` -/

theorem summable_etaPlus {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => ‖((Λ n * etaPlus (n / x) : ℝ) : ℂ)‖ :=
  summable_vonMangoldt_mul hx (by norm_num) fun _ ht => abs_etaPlus_le ht

theorem summable_etaStar {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => ‖((Λ n * etaStar (n / x) : ℝ) : ℂ)‖ :=
  summable_vonMangoldt_mul hx (by rw [κ]; norm_num) fun _ ht => abs_etaStar_le ht

end TernaryGoldbach.Helfgott
