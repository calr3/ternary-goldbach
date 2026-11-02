import TernaryGoldbach.MinorArcs.FirstChoiceTypeI

/-!
# [H, §6.3.1, (6.53)–(6.56)]: `S_{I,1}` at the first choice of parameters
-/

open Real

namespace TernaryGoldbach.MinorArcs

theorem delta0_ge (δ : ℝ) : 2 ≤ delta0 δ := le_max_left _ _

/-- `min(1, c₀/(πδ)²) ≤ 2/δ₀`. -/
theorem minInv_le_delta0 (δ : ℝ) : minInv c₀ (π * δ) ≤ 2 / delta0 δ := by
  have hpi := Real.pi_gt_d4
  have h1 : minInv c₀ (π * δ) ≤ 1 := by
    unfold minInv; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  unfold delta0
  rcases le_total 2 (|δ| / 4) with h | h
  · rw [max_eq_right h]
    have hδ0 : δ ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    unfold minInv
    rw [if_neg (mul_ne_zero Real.pi_pos.ne' hδ0)]
    refine (min_le_right _ _).trans ?_
    have hδ2 : |δ| ^ 2 = δ ^ 2 := sq_abs δ
    rw [div_le_div_iff₀ (by positivity) (by positivity), mul_pow, ← hδ2]
    have : c₀ = 31.521 := rfl
    rw [this]
    have h8 : 8 * |δ| ≤ |δ| ^ 2 := by nlinarith
    have hp2 : 9.8 ≤ π ^ 2 := by nlinarith
    nlinarith
  · rw [max_eq_left h]; linarith

/-- `|(log·η₂)^(-δ/2)|`-bound `≤ 0.6138 · 2/δ₀`. -/
theorem logFB_le_delta0 (δ : ℝ) : logFourierBound δ ≤ 0.6138 * (2 / delta0 δ) := by
  have hpi := Real.pi_gt_d4
  have hl4 : 2 - Real.log 4 ≤ 0.6138 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9; push_cast; linarith
  have h1 : logFourierBound δ ≤ 2 - Real.log 4 := by
    unfold logFourierBound; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  unfold delta0
  rcases le_total 2 (|δ| / 4) with h | h
  · rw [max_eq_right h]
    have hδ0 : δ ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    unfold logFourierBound
    rw [if_neg hδ0]
    refine (min_le_right _ _).trans ?_
    have hδ2 : |δ| ^ 2 = δ ^ 2 := sq_abs δ
    rw [div_le_iff₀ (by positivity), mul_pow, ← hδ2]
    have := Real.log_two_lt_d9
    have : 0.6138 * (2 / (|δ| / 4)) * (π ^ 2 * |δ| ^ 2) = 4.9104 * π ^ 2 * |δ| := by
      field_simp; norm_num
    rw [this]
    nlinarith
  · rw [max_eq_left h, show (2 : ℝ) / 2 = 1 by norm_num]; linarith

theorem muBound_le_one (U : ℝ) (q : ℕ) : muBound U q ≤ 1 := by
  unfold muBound; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- `μ L ≤ 2.8(2q/φ(2q)) + max(L - log(M/2q²), 0)` for `μ = muBound M q`, `L ≥ 0`. -/
theorem muBound_mul_le {M L : ℝ} {q : ℕ} (hq : 1 ≤ q) (hM : 0 < M) (hL : 0 ≤ L) :
    muBound M q * L ≤ 2.8 * (2 * q / Nat.totient (2 * q)) +
      max (L - Real.log (M / (2 * q ^ 2))) 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient (2 * q) := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have ha : 0 ≤ 2.8 * (2 * (q : ℝ) / Nat.totient (2 * q)) := by positivity
  unfold muBound
  split_ifs with h
  · set ℓ := Real.log (M / (2 * q ^ 2))
    have hℓ : 0 < ℓ := Real.log_pos (by rw [one_lt_div (by positivity)]; exact h)
    set a := 2.8 * (2 * (q : ℝ) / Nat.totient (2 * q))
    have hm0 : 0 ≤ min 1 (a / ℓ) := le_min zero_le_one (by positivity)
    have hm1 : min 1 (a / ℓ) * ℓ ≤ a := by
      calc min 1 (a / ℓ) * ℓ ≤ a / ℓ * ℓ := mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ.le
        _ = a := by field_simp
    have hm2 : min 1 (a / ℓ) * (L - ℓ) ≤ max (L - ℓ) 0 := by
      rcases le_total 0 (L - ℓ) with h' | h'
      · calc min 1 (a / ℓ) * (L - ℓ) ≤ 1 * (L - ℓ) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) h'
          _ ≤ max (L - ℓ) 0 := by rw [one_mul]; exact le_max_left _ _
      · exact (mul_nonpos_of_nonneg_of_nonpos hm0 h').trans (le_max_right _ _)
    have : min 1 (a / ℓ) * L = min 1 (a / ℓ) * ℓ + min 1 (a / ℓ) * (L - ℓ) := by ring
    linarith
  · push Not at h
    have hℓ : Real.log (M / (2 * q ^ 2)) ≤ 0 :=
      Real.log_nonpos (by positivity) (by rw [div_le_one (by positivity)]; exact h)
    have : L ≤ max (L - Real.log (M / (2 * q ^ 2))) 0 :=
      le_trans (by linarith) (le_max_left _ _)
    linarith

theorem totient_le_totient_two_mul (q : ℕ) : Nat.totient q ≤ Nat.totient (2 * q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  exact Nat.le_of_dvd (Nat.totient_pos.2 (by omega)) (Nat.totient_dvd_of_dvd (dvd_mul_left q 2))

/-- `x·μ_{2q}/φ(2q) ≤ 2x/(δ₀φ(q))` where `μ = min(1, c₀/(πδ)²)`. -/
theorem xphi_le {x δ : ℝ} {q : ℕ} (hx : 0 ≤ x) (hq : 1 ≤ q) :
    x / (2 * q) * minInv c₀ (π * δ) * (2 * q / Nat.totient (2 * q)) ≤
      2 * x / (delta0 δ * Nat.totient q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have hφ2 : (Nat.totient q : ℝ) ≤ Nat.totient (2 * q) := by
    exact_mod_cast totient_le_totient_two_mul q
  have hm := minInv_le_delta0 δ
  have hm0 : 0 ≤ minInv c₀ (π * δ) := by
    unfold minInv; split_ifs
    · norm_num
    · exact le_min zero_le_one (div_nonneg (by norm_num [c₀]) (sq_nonneg _))
  have hd := delta0_ge δ
  have e : x / (2 * q) * minInv c₀ (π * δ) * (2 * q / Nat.totient (2 * q)) =
      x * minInv c₀ (π * δ) / Nat.totient (2 * q) := by field_simp
  rw [e]
  calc x * minInv c₀ (π * δ) / Nat.totient (2 * q) ≤ x * (2 / delta0 δ) / Nat.totient q := by
        gcongr
    _ = _ := by field_simp

/-- `x μ/(2q) ≤ x/t`, `t = δ₀q`. -/
theorem xq_le {x δ : ℝ} {q : ℕ} (hx : 0 ≤ x) (hq : 1 ≤ q) :
    x / (2 * q) * minInv c₀ (π * δ) ≤ x / (delta0 δ * q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hm := minInv_le_delta0 δ
  have hd := delta0_ge δ
  calc x / (2 * q) * minInv c₀ (π * δ) ≤ x / (2 * q) * (2 / delta0 δ) := by gcongr
    _ = _ := by field_simp

/-- `log(2q²x/U²) ≤ 2 log t + 2.63` at the parameters of (6.49). -/
theorem log_xq_U_le {T t : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (ht2 : 2 ≤ t) (htT : t ≤ T / 3)
    (hq : 1 ≤ q) (hqt : 2 * (q : ℝ) ≤ t) :
    Real.log (T ^ 3 / U1 T t) - Real.log (U1 T t / (2 * q ^ 2)) ≤ 2 * Real.log t + 2.63 := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hU := U1_ge hT ht0 htT
  have hsT := sqrt_ge_2449 hT
  have hU0 : 0 < (U1 T t : ℝ) := lt_of_lt_of_le (by positivity) hU
  set Ur := T ^ 2 / (9 * √t) with hUr
  have hst : 0 < √t := Real.sqrt_pos.2 ht0
  have hfl : Ur - 1 ≤ (U1 T t : ℝ) := by
    unfold U1; have := Nat.lt_floor_add_one Ur; linarith
  have hUrge : 0.19245 * (T * √T) ≤ Ur := by
    have := U1_real_ge hT ht0 htT; have := sqrt3_div9
    have : 0 ≤ T * √T := by positivity
    nlinarith
  have hUr1 : 1 ≤ 1e-6 * Ur := by nlinarith
  have hUge : 0.999999 * Ur ≤ U1 T t := by linarith
  rw [← Real.log_div (by positivity) (by positivity)]
  have e : T ^ 3 / U1 T t / (U1 T t / (2 * q ^ 2)) = 2 * q ^ 2 * T ^ 3 / (U1 T t) ^ 2 := by
    field_simp
  rw [e]
  have hst2 : √t ^ 2 = t := Real.sq_sqrt ht0.le
  have hUr2 : Ur ^ 2 * (81 * t) = T ^ 4 := by
    simp only [hUr]; rw [div_pow, mul_pow, hst2]; field_simp; norm_num
  have h1 : 2 * q ^ 2 * T ^ 3 / (U1 T t : ℝ) ^ 2 ≤ 13.6 * t ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (0.999999 * Ur) ^ 2 ≤ (U1 T t : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hUge 2
    have h3 : (q : ℝ) ^ 2 ≤ t ^ 2 / 4 := by nlinarith
    -- `2q²T³ ≤ t²T³/2` and `13.6 t² U² ≥ 13.6 t² · 0.999998 T⁴/(81t)`.
    have h4 : 13.6 * t ^ 2 * (0.999999 * Ur) ^ 2 * (81 * t) = 13.6 * 0.999998000001 * t ^ 2 * T ^ 4 := by
      rw [← hUr2]; ring
    have h5 : t ^ 2 / 2 * T ^ 3 * (81 * t) ≤ 13.6 * 0.999998000001 * t ^ 2 * T ^ 4 := by
      have : t * (81 / 2) ≤ 13.6 * 0.999998000001 * T := by linarith
      have : 0 < t ^ 2 * T ^ 3 := by positivity
      nlinarith
    have h6 : 2 * q ^ 2 * T ^ 3 ≤ t ^ 2 / 2 * T ^ 3 := by nlinarith [pow_pos hT0 3]
    have h7 : 13.6 * t ^ 2 * (0.999999 * Ur) ^ 2 ≤ 13.6 * t ^ 2 * (U1 T t : ℝ) ^ 2 := by gcongr
    nlinarith
  calc Real.log (2 * q ^ 2 * T ^ 3 / (U1 T t) ^ 2) ≤ Real.log (13.6 * t ^ 2) :=
        Real.log_le_log (by positivity) h1
    _ = Real.log 13.6 + 2 * Real.log t := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    _ ≤ 2 * Real.log t + 2.63 := by
        have := log_le_tangent16 (show (0 : ℝ) < 13.6 by norm_num)
        linarith

/-- The `c₀(1/2 - 2/π²)(…)` term of `typeI1_le` at the parameters: `≤ 0.0001 x^{5/6}`. -/
theorem typeI1_c0_term_le {T U : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : 1 ≤ q) (hU1 : 1 ≤ U)
    (hU2 : U ≤ 0.0786 * T ^ 2) :
    c₀ * (1 / 2 - 2 / π ^ 2) * (U ^ 2 / (4 * q * T ^ 3) * Real.log (rexp (1 / 2) * T ^ 3 / U) +
      1 / rexp 1) ≤ 0.0001 * (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsT := sqrt_ge_2449 hT
  have hlog := log_le_sqrt_mul hT
  have hpi := Real.pi_gt_three
  have hc : c₀ * (1 / 2 - 2 / π ^ 2) ≤ 15.8 := by
    have : 0 ≤ 2 / π ^ 2 := by positivity
    have : c₀ = 31.521 := rfl
    rw [this]; nlinarith
  have hc0 : 0 ≤ c₀ * (1 / 2 - 2 / π ^ 2) := by
    have : 2 / π ^ 2 ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have : (0 : ℝ) < c₀ := by norm_num [c₀]
    have : 0 ≤ 1 / 2 - 2 / π ^ 2 := by linarith
    positivity
  have hl : Real.log (rexp (1 / 2) * T ^ 3 / U) ≤ 1 / 2 + 3 * (0.0298 * √T) := by
    have h1 : rexp (1 / 2) * T ^ 3 / U ≤ rexp (1 / 2) * T ^ 3 := div_le_self (by positivity) hU1
    refine (Real.log_le_log (by positivity) h1).trans ?_
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow]
    push_cast; linarith
  have hl0 : 0 ≤ Real.log (rexp (1 / 2) * T ^ 3 / U) := Real.log_nonneg (by
    rw [le_div_iff₀ (by linarith)]
    have : 1 ≤ rexp (1 / 2) := Real.one_le_exp (by norm_num)
    have : U ≤ T ^ 3 := by nlinarith
    nlinarith [pow_pos hT0 3])
  have hU2' : U ^ 2 / (4 * q * T ^ 3) ≤ 0.001545 * T := by
    rw [div_le_iff₀ (by positivity)]
    have : U ^ 2 ≤ (0.0786 * T ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hU2 2
    nlinarith [pow_pos hT0 4]
  have he : 1 / rexp 1 ≤ 1 := by rw [div_le_one (Real.exp_pos 1)]; exact Real.one_le_exp (by norm_num)
  calc _ ≤ 15.8 * (0.001545 * T * (1 / 2 + 3 * (0.0298 * √T)) + 1) := by gcongr
    _ ≤ 0.0001 * (T ^ 2 * √T) := by
        have : 0 < T * √T := by positivity
        nlinarith

set_option maxHeartbeats 1600000 in
/-- **[H, (6.56)], our version**: for `q ≤ x^{1/3}/6`, at the parameters of (6.49),
`|S_{I,1}| ≤ 3.8 · 2x/(δ₀φ(q)) + (log t + 2.96) · 2x/t + 0.014 x^{5/6}`, `t = δ₀q` (with the
elementary (2.23); [H]'s `1.00303` would give `1.63`). -/
theorem typeI1_first {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (3 / 4 * T ^ 2)) (hqT : (q : ℝ) ≤ T / 6) :
    ‖typeILog α (T ^ 3) (U1 T (delta0 δ * q))‖ ≤
      3.8 * (2 * T ^ 3 / (delta0 δ * Nat.totient q)) +
        (Real.log (delta0 δ * q) + 2.96) * (2 * T ^ 3 / (delta0 δ * q)) + 0.014 * (T ^ 2 * √T) := by
  obtain ⟨hδq, ht2, htT⟩ := first_choice_t hT h hqT
  have hq : 1 ≤ q := h.1
  set t := delta0 δ * q with ht
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsT := sqrt_ge_2449 hT
  have hU := U1_ge hT ht0 htT
  have hUle := U1_le (T := T) ht0
  have hU2 : (U1 T t : ℝ) ≤ 0.0786 * T ^ 2 := by
    refine hUle.trans ?_
    have h1 : √2 ≤ √t := Real.sqrt_le_sqrt ht2
    have h2 : 1.4142 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ T ^ 2 := by positivity
    nlinarith
  have hU1 : (1 : ℝ) ≤ U1 T t := le_trans (by nlinarith) hU
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hle := typeI1_le h (U := U1 T t)
    (by
      have : √3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      linarith [show (2 : ℝ) ≤ U1 T t from le_trans (by nlinarith) hU])
    (by
      refine le_min ?_ ?_
      · rw [le_div_iff₀ (by norm_num)]; nlinarith [pow_pos hT0 2]
      · rw [le_div_iff₀ (Real.exp_pos 1)]
        have : rexp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        nlinarith [pow_pos hT0 2])
    (by nlinarith)
  refine hle.trans ?_
  have hm0 : 0 ≤ minInv c₀ (π * δ) := by
    unfold minInv; split_ifs
    · norm_num
    · exact le_min zero_le_one (div_nonneg (by norm_num [c₀]) (sq_nonneg _))
  have hx0 : (0 : ℝ) ≤ T ^ 3 := by positivity
  have hmu := muBound_le_one (U1 T t : ℝ) q
  have hmu0 := muBound_nonneg (U1 T t : ℝ) hq
  have hρ : (0 : ℝ) ≤ 2 * q / Nat.totient (2 * q) := by positivity
  -- `log(x/U) μ ≤ 2.8ρ + 2 log t + 2.63`.
  have hLμ : Real.log (T ^ 3 / U1 T t) * muBound (U1 T t) q ≤
      2.8 * (2 * q / Nat.totient (2 * q)) + (2 * Real.log t + 2.63) := by
    rw [mul_comm]
    refine (muBound_mul_le hq (by linarith) (Real.log_nonneg ?_)).trans ?_
    · rw [le_div_iff₀ (by linarith)]; nlinarith [pow_pos hT0 2]
    · have hqt : 2 * (q : ℝ) ≤ t := by rw [ht]; nlinarith [delta0_ge δ]
      have := log_xq_U_le hT ht2 htT hq hqt
      have : max (Real.log (T ^ 3 / U1 T t) - Real.log (U1 T t / (2 * q ^ 2))) 0 ≤
          2 * Real.log t + 2.63 := max_le this (by linarith)
      linarith
  have h1 : T ^ 3 / (2 * q) * minInv c₀ (π * δ) *
      ((2 * q / Nat.totient (2 * q) + 2.67) + Real.log (T ^ 3 / U1 T t) * muBound (U1 T t) q) ≤
      3.8 * (2 * T ^ 3 / (delta0 δ * Nat.totient q)) + (2 * Real.log t + 5.30) * (T ^ 3 / t) := by
    have hA := xphi_le (x := T ^ 3) (δ := δ) hx0 hq
    have hB := xq_le (x := T ^ 3) (δ := δ) hx0 hq
    rw [← ht] at hB
    have hc0 : 0 ≤ T ^ 3 / (2 * q) * minInv c₀ (π * δ) := by positivity
    calc _ ≤ T ^ 3 / (2 * q) * minInv c₀ (π * δ) *
          (3.8 * (2 * q / Nat.totient (2 * q)) + (2 * Real.log t + 5.30)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc0
      _ = 3.8 * (T ^ 3 / (2 * q) * minInv c₀ (π * δ) * (2 * q / Nat.totient (2 * q))) +
          (2 * Real.log t + 5.30) * (T ^ 3 / (2 * q) * minInv c₀ (π * δ)) := by ring
      _ ≤ _ := by gcongr
  have h2 : T ^ 3 / (2 * q) * logFourierBound δ * muBound (U1 T t) q ≤ 0.6138 * (T ^ 3 / t) := by
    have hF := logFB_le_delta0 δ
    have hF0 : 0 ≤ logFourierBound δ := by
      unfold logFourierBound
      have : 0 ≤ 2 - Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have := Real.log_two_lt_d9; push_cast; linarith
      split_ifs
      · exact this
      · exact le_min this (by positivity)
    have hd := delta0_ge δ
    calc T ^ 3 / (2 * q) * logFourierBound δ * muBound (U1 T t) q
        ≤ T ^ 3 / (2 * q) * (0.6138 * (2 / delta0 δ)) * 1 := by gcongr
      _ = 0.6138 * (T ^ 3 / t) := by rw [ht]; field_simp
  have h3 := typeI1_c0_term_le hT hq hU1 hU2
  have h4 := bound_4_41_first hT hq hqT hU hU2
  have e : (Real.log t + 2.96) * (2 * T ^ 3 / t) =
      (2 * Real.log t + 5.30) * (T ^ 3 / t) + 0.6138 * (T ^ 3 / t) + 0.0062 * (T ^ 3 / t) := by
    field_simp; ring
  have : 0 ≤ T ^ 3 / t := by positivity
  rw [e]
  linarith

end TernaryGoldbach.MinorArcs
