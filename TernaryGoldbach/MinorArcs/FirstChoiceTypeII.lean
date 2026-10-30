import TernaryGoldbach.MinorArcs.FirstChoiceParams

/-!
# [B, §6.3.1]: the Type II terms at the first choice of parameters

The lower-order terms of (6.37)/(6.40) at `U = ⌊T²/(9√t)⌋`, `V = ⌊9T/2⌋` are at most
`3.2 x^{5/6}` (`typeII_rest_le`), using Lemma C.2.2 (`q/φ(q) < Ϝ(T)`, trusted).
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- `log y ≤ y/e`. -/
theorem log_le_div_exp {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / rexp 1 := by
  have := Real.log_le_sub_one_of_pos (show 0 < y / rexp 1 by positivity)
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
  linarith

theorem exp_gamma_le : rexp Real.eulerMascheroniConstant ≤ 1.948 := by
  have h1 : rexp Real.eulerMascheroniConstant ≤ rexp (2 / 3) :=
    Real.exp_le_exp.2 Real.eulerMascheroniConstant_lt_two_thirds.le
  have h2 : rexp (2 / 3) ^ 3 ≤ 1.948 ^ 3 := by
    rw [← Real.exp_nat_mul]
    have := Real.exp_one_lt_d9
    calc rexp ((3 : ℕ) * (2 / 3)) = rexp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 2
      _ ≤ 1.948 ^ 3 := by norm_num
  have h3 : rexp (2 / 3) ≤ 1.948 := le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h2
  linarith

/-- `Ϝ(T) = e^γ log log T + 2.50637/log log T ≤ 6.2799 + 0.974 √(T/6·10⁶)` for `T ≥ 6·10⁶`. -/
theorem F_le {T : ℝ} (hT : 6e6 ≤ T) :
    rexp Real.eulerMascheroniConstant * Real.log (Real.log T) + 2.50637 / Real.log (Real.log T) ≤
      6.2799 + 0.974 * √(T / 6e6) := by
  have hT0 : 0 < T := by linarith
  have he := Real.exp_one_lt_d9
  have hlT : 15 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    calc rexp 15 = rexp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 15 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 15
      _ ≤ T := by norm_num; linarith
  have hll : 2.5 ≤ Real.log (Real.log T) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : rexp 2.5 ^ 2 ≤ 15 ^ 2 := by
      rw [← Real.exp_nat_mul]
      calc rexp ((2 : ℕ) * 2.5) = rexp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 2.7182818286 ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 5
        _ ≤ 15 ^ 2 := by norm_num
    have := le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) this
    linarith
  set v := T / 6e6 with hv
  have hv1 : 1 ≤ v := by rw [hv, le_div_iff₀ (by norm_num)]; linarith
  -- `log log T ≤ log(15 + v) ≤ 2.7091 + 0.5 √v`.
  have hlog1 : Real.log (Real.log T) ≤ Real.log (15 + v) :=
    Real.log_le_log (by linarith) (log_le_lin hT0)
  have hlog2 : Real.log (15 + v) ≤ 2.7091 + 0.5 * √v := by
    have h16 : Real.log 16 ≤ 2.7726 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    have hy : 0 < (15 + v) / 16 := by positivity
    have h1 : Real.log ((15 + v) / 16) ≤ 2 * (√((15 + v) / 16) - 1) := by
      have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hy)
      rw [Real.log_sqrt hy.le] at this
      linarith
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 : √((15 + v) / 16) ≤ (3.873 + √v) / 4 := by
      rw [Real.sqrt_le_left (by positivity)]
      have h15 : (15 : ℝ) ≤ 3.873 ^ 2 := by norm_num
      have hsv := Real.sq_sqrt (show 0 ≤ v by linarith)
      have : 0 ≤ √v := Real.sqrt_nonneg _
      nlinarith
    linarith
  have hsv : 1 ≤ √v := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hv1
  have hg := exp_gamma_le
  have hg0 : 0 ≤ rexp Real.eulerMascheroniConstant := (Real.exp_pos _).le
  have h1 : rexp Real.eulerMascheroniConstant * Real.log (Real.log T) ≤
      1.948 * (2.7091 + 0.5 * √v) :=
    mul_le_mul hg (hlog1.trans hlog2) (by linarith) (by norm_num)
  have h2 : 2.50637 / Real.log (Real.log T) ≤ 1.002548 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

theorem kap1_le {T t : ℝ} (hT : 6e6 ≤ T) (ht : 0 < t) (htT : t ≤ T / 3) :
    kap1 (T ^ 3) (U1 T t) (V1 T) ≤ 0.23209 := by
  have h := zeta_term_le hT ht htT
  unfold kap1
  have hpi := Real.pi_gt_d6
  have : 2 / π ^ 2 ≤ 0.20265 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e : zeta3 * √(T ^ 3 / V1 T) / U1 T t = (8 * zeta3 * √(T ^ 3 / V1 T) / U1 T t) / 8 := by ring
  rw [e]; linarith

/-- `log c ≤ 2 log(X/c)` when `c ≤ 1.0015 t`, `t ≤ T/3`, `X ≥ 9T√t`. -/
theorem log_le_two_log_div {T t c X : ℝ} (ht0 : 0 < t) (htT : t ≤ T / 3) (hc0 : 0 < c)
    (hc : c ≤ 1.0015 * t) (hX : 9 * (T * √t) ≤ X) : Real.log c ≤ 2 * Real.log (X / c) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le (by have := Real.sqrt_pos.2 ht0; positivity) hX
  rw [← Real.log_rpow (by positivity)]
  refine Real.log_le_log hc0 ?_
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, div_pow, le_div_iff₀ (by positivity)]
  have h1 : (9 * (T * √t)) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hX 2
  have hst := Real.sq_sqrt ht0.le
  have h2 : c * c ^ 2 ≤ 1.0015 ^ 3 * t ^ 3 := by
    have := pow_le_pow_left₀ hc0.le hc 3
    nlinarith
  have h3 : (9 * (T * √t)) ^ 2 = 81 * T ^ 2 * t := by rw [mul_pow, mul_pow, hst]; ring
  have h : t * t ≤ T * T := by nlinarith
  have h4 : 1.0015 ^ 3 * t ^ 3 ≤ 81 * T ^ 2 * t := by
    nlinarith [mul_le_mul_of_nonneg_left h ht0.le]
  linarith

/-- With `r = T^{1/4}`: `r ≥ 49.47`, `√T = r²`, `T = r⁴`. -/
theorem fourth_root_facts {T : ℝ} (hT : 6e6 ≤ T) :
    49.47 ≤ √(√T) ∧ √T = √(√T) ^ 2 ∧ T = √(√T) ^ 4 := by
  have hT0 : 0 ≤ T := by linarith
  have h1 : √T = √(√T) ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  have h2 : T = √(√T) ^ 4 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, ← h1, Real.sq_sqrt hT0]
  refine ⟨?_, h1, h2⟩
  rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _), Real.le_sqrt (by norm_num) hT0]
  norm_num; linarith

set_option maxHeartbeats 1600000 in
/-- **[B, (6.60), (6.61)], lower-order terms** of `typeII_637`/`typeII_640` at the parameters
of (6.49): at most `3.2 x^{5/6}` (cf. [B]'s `2.73908 x^{5/6}` in (6.62)). Here `c ∈ [t, 1.0015 t]`
(`c = 2q` resp. `δ₀q(1 + ε₁)`). -/
theorem typeII_rest_le {T t c : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (ht2 : 2 ≤ t) (htT : t ≤ T / 3)
    (hct : t ≤ c) (hc : c ≤ 1.0015 * t) (hq : 1 ≤ q) (hqT : (q : ℝ) ≤ T) :
    4 * √(kap1 (T ^ 3) (U1 T t) (V1 T) * q * T ^ 3 / (2 * Nat.totient q)) *
        (2 * √(T ^ 3 / U1 T t) + √(Real.log c) * (2 * rexp 1 * √c +
          4 * √(T ^ 3 / U1 T t / Real.log (T ^ 3 / U1 T t / c)))) +
      8 * 1.4262 * T ^ 3 * √(kap1 (T ^ 3) (U1 T t) (V1 T) * (1 / 2 + 1 / U1 T t)) / √(V1 T) ≤
      3.2 * (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨hr, hsT, hTr⟩ := fourth_root_facts hT
  set r := √(√T) with hr_def
  have hr0 : 0 < r := by linarith
  have hκ := kap1_le hT ht0 htT
  have hκ0 : 0 ≤ kap1 (T ^ 3) (U1 T t) (V1 T) := by unfold kap1; have := zeta3_nonneg; positivity
  have hU := U1_ge hT ht0 htT
  have hU0 : 0 < (U1 T t : ℝ) := lt_of_lt_of_le (by positivity) hU
  have hV := V1_ge hT0
  have hV0 : 0 < (V1 T : ℝ) := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  -- `q/φ(q) ≤ Ϝ(T) ≤ 7.2539 √v`, `v = T/6e6`.
  have hF : (q : ℝ) / Nat.totient q ≤ 7.2539 * √(T / 6e6) := by
    have h1 := Prelim.div_totient_lt hq (by linarith) hqT
    have h2 := F_le hT
    have hsv : 1 ≤ √(T / 6e6) := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ (by norm_num)]; linarith)
    linarith
  have hsTv : 2449.48 * √(T / 6e6) ≤ √T := by
    rw [Real.sqrt_div' _ (by norm_num), mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    have : 2449.48 ≤ √6e6 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have := Real.sqrt_nonneg T
    nlinarith
  -- `x/U ≤ 5.1963 r⁶`, so `√(x/U) ≤ 2.2796 r³`.
  have hxU : T ^ 3 / U1 T t ≤ 5.1963 * r ^ 6 := by
    have h1 := div_U1_le hT ht0 htT
    have h2 : √t ≤ √T / √3 := by
      rw [← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 3)]; exact Real.sqrt_le_sqrt (by linarith)
    have h3 : 1 / √3 ≤ 0.57736 := by
      rw [div_le_iff₀ (by positivity)]
      have : 1.73205 ≤ √3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      nlinarith
    have : T * √t ≤ T * √T * 0.57736 := by
      calc T * √t ≤ T * (√T / √3) := by gcongr
        _ = T * √T * (1 / √3) := by ring
        _ ≤ T * √T * 0.57736 := by gcongr
    have e : T * √T = r ^ 6 := by rw [hsT]; nth_rw 1 [hTr]; ring
    nlinarith
  have hA : √(T ^ 3 / U1 T t) ≤ 2.2796 * r ^ 3 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (2.2796 * r ^ 3) ^ 2 = 5.19657616 * r ^ 6 := by ring
    have : 0 ≤ r ^ 6 := by positivity
    linarith
  -- `log c ≤ 2 log(x/U/c)`.
  have hxU1 : 9 * (T * √t) ≤ T ^ 3 / U1 T t := by
    rw [le_div_iff₀ hU0]
    have := U1_le (T := T) ht0
    have hst : 0 < √t := Real.sqrt_pos.2 ht0
    calc 9 * (T * √t) * (U1 T t : ℝ) ≤ 9 * (T * √t) * (T ^ 2 / (9 * √t)) := by gcongr
      _ = T ^ 3 := by field_simp
  have hst2 : t ≤ √t ^ 3 := by
    have := Real.sq_sqrt ht0.le
    have h2 : 1 ≤ √t := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    nlinarith
  have hlogc : 0 < Real.log c := Real.log_pos (by linarith)
  have hratio : Real.log c ≤ 2 * Real.log (T ^ 3 / U1 T t / c) :=
    log_le_two_log_div ht0 htT hc0 hc hxU1
  have hlogxUc : 0 < Real.log (T ^ 3 / U1 T t / c) := by linarith
  have hB1 : √(Real.log c) * (4 * √(T ^ 3 / U1 T t / Real.log (T ^ 3 / U1 T t / c))) ≤
      4 * 1.41422 * √(T ^ 3 / U1 T t) := by
    have e : √(Real.log c) * √(T ^ 3 / U1 T t / Real.log (T ^ 3 / U1 T t / c)) =
        √(T ^ 3 / U1 T t) * √(Real.log c / Real.log (T ^ 3 / U1 T t / c)) := by
      rw [← Real.sqrt_mul hlogc.le, ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp
    have h2 : √(Real.log c / Real.log (T ^ 3 / U1 T t / c)) ≤ 1.41422 := by
      rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ hlogxUc]
      exact hratio.trans (mul_le_mul_of_nonneg_right (by norm_num) hlogxUc.le)
    calc √(Real.log c) * (4 * √(T ^ 3 / U1 T t / Real.log (T ^ 3 / U1 T t / c)))
        = 4 * (√(T ^ 3 / U1 T t) * √(Real.log c / Real.log (T ^ 3 / U1 T t / c))) := by
          rw [← e]; ring
      _ ≤ 4 * (√(T ^ 3 / U1 T t) * 1.41422) := by gcongr
      _ = _ := by ring
  -- `√(c log c) ≤ 0.0997 r³`.
  have hB2 : √(Real.log c) * (2 * rexp 1 * √c) ≤ 2 * rexp 1 * (0.0997 * r ^ 3) := by
    have e : √(Real.log c) * (2 * rexp 1 * √c) = 2 * rexp 1 * √(c * Real.log c) := by
      rw [Real.sqrt_mul hc0.le]; ring
    rw [e]
    gcongr
    rw [Real.sqrt_le_left (by positivity)]
    have hcT : c ≤ 0.3339 * r ^ 4 := by rw [← hTr]; linarith
    have hlc : Real.log c ≤ 1.4717 * r := by
      have h1 : Real.log c ≤ Real.log T := Real.log_le_log hc0 (by linarith)
      have h2 : Real.log T = 4 * Real.log r := by
        rw [hTr, Real.log_pow]; push_cast; ring
      have h3 := log_le_div_exp hr0
      have h4 : (2.718 : ℝ) ≤ rexp 1 := by have := Real.exp_one_gt_d9; linarith
      have h5 : r / rexp 1 ≤ r / 2.718 := div_le_div_of_nonneg_left hr0.le (by norm_num) h4
      have h6 : r / 2.718 ≤ 0.36792 * r := by rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    have h7 : c * Real.log c ≤ 0.3339 * r ^ 4 * (1.4717 * r) :=
      mul_le_mul hcT hlc hlogc.le (by positivity)
    have h8 : 0.3339 * r ^ 4 * (1.4717 * r) ≤ (0.0997 * r ^ 3) ^ 2 := by
      have e1 : (0.0997 * r ^ 3) ^ 2 = (0.00994009 * r) * r ^ 5 := by ring
      have e2 : 0.3339 * r ^ 4 * (1.4717 * r) = 0.49140063 * r ^ 5 := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have he : rexp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have hbracket : 2 * √(T ^ 3 / U1 T t) + √(Real.log c) * (2 * rexp 1 * √c +
      4 * √(T ^ 3 / U1 T t / Real.log (T ^ 3 / U1 T t / c))) ≤ 17.998 * r ^ 3 := by
    rw [mul_add]
    have : 2 * rexp 1 * (0.0997 * r ^ 3) ≤ 2 * 2.7182818286 * (0.0997 * r ^ 3) := by gcongr
    have : 0 ≤ r ^ 3 := by positivity
    linarith only [hA, hB1, hB2, this, ‹2 * rexp 1 * (0.0997 * r ^ 3) ≤ 2 * 2.7182818286 * (0.0997 * r ^ 3)›]
  -- The prefactor: `√(κ₁ q x/(2φ)) ≤ 0.34066 √(q/φ) r⁶`.
  have hpre : √(kap1 (T ^ 3) (U1 T t) (V1 T) * q * T ^ 3 / (2 * Nat.totient q)) ≤
      0.34066 * √((q : ℝ) / Nat.totient q) * r ^ 6 := by
    have e : kap1 (T ^ 3) (U1 T t) (V1 T) * q * T ^ 3 / (2 * Nat.totient q) =
        (kap1 (T ^ 3) (U1 T t) (V1 T) / 2) * ((q : ℝ) / Nat.totient q) * (r ^ 6) ^ 2 := by
      rw [show (r ^ 6) ^ 2 = (r ^ 4) ^ 3 by ring, ← hTr]; field_simp
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    gcongr
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  -- `√(q/φ) ≤ 0.055055 r`.
  have hsF : √((q : ℝ) / Nat.totient q) ≤ 0.055055 * r := by
    rw [Real.sqrt_le_left (by positivity)]
    have : 7.2539 * √(T / 6e6) ≤ (0.055055 * r) ^ 2 := by
      have e1 : (0.055055 * r) ^ 2 = 0.003031053025 * r ^ 2 := by ring
      rw [e1, ← hsT]
      have := Real.sqrt_nonneg (T / 6e6)
      linarith
    linarith
  have hT2 : 4 * √(kap1 (T ^ 3) (U1 T t) (V1 T) * q * T ^ 3 / (2 * Nat.totient q)) *
      (2 * √(T ^ 3 / U1 T t) + √(Real.log c) * (2 * rexp 1 * √c +
        4 * √(T ^ 3 / U1 T t / Real.log (T ^ 3 / U1 T t / c)))) ≤ 1.36 * r ^ 10 := by
    have hb0 : 0 ≤ 2 * √(T ^ 3 / U1 T t) + √(Real.log c) * (2 * rexp 1 * √c +
        4 * √(T ^ 3 / U1 T t / Real.log (T ^ 3 / U1 T t / c))) := by positivity
    calc _ ≤ 4 * (0.34066 * (0.055055 * r) * r ^ 6) * (17.998 * r ^ 3) := by
          gcongr
          · exact hpre.trans (by gcongr)
      _ = (4 * 0.34066 * 0.055055 * 17.998) * r ^ 10 := by ring
      _ ≤ 1.36 * r ^ 10 := by
          have : 0 < r ^ 10 := pow_pos hr0 10
          exact mul_le_mul_of_nonneg_right (by norm_num) this.le
  -- `T3 ≤ 1.84 x^{5/6}`.
  have hT3 : 8 * 1.4262 * T ^ 3 * √(kap1 (T ^ 3) (U1 T t) (V1 T) * (1 / 2 + 1 / U1 T t)) /
      √(V1 T) ≤ 1.84 * r ^ 10 := by
    have h1 : √(kap1 (T ^ 3) (U1 T t) (V1 T) * (1 / 2 + 1 / U1 T t)) ≤ 0.34068 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have : 1 / (U1 T t : ℝ) ≤ 1e-6 := by
        rw [div_le_iff₀ hU0]
        have : 0 < r ^ 6 := by positivity
        have e : T * √T = r ^ 6 := by rw [hsT]; nth_rw 1 [hTr]; ring
        nlinarith
      have : kap1 (T ^ 3) (U1 T t) (V1 T) * (1 / 2 + 1 / U1 T t) ≤ 0.23209 * (1 / 2 + 1e-6) :=
        mul_le_mul hκ (by linarith) (by positivity) (by norm_num)
      linarith
    have h2 : 2.1213 * r ^ 2 ≤ √(V1 T) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      have : (2.1213 * r ^ 2) ^ 2 = 4.49991369 * T := by rw [mul_pow, ← pow_mul, hTr]; ring
      rw [this]; linarith
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) h2)]
    calc 8 * 1.4262 * T ^ 3 * √(kap1 (T ^ 3) (U1 T t) (V1 T) * (1 / 2 + 1 / U1 T t))
        ≤ 8 * 1.4262 * T ^ 3 * 0.34068 := by gcongr
      _ = 8 * 1.4262 * 0.34068 * r ^ 12 := by rw [hTr]; ring
      _ ≤ 1.84 * r ^ 10 * (2.1213 * r ^ 2) := by
          have e : 1.84 * r ^ 10 * (2.1213 * r ^ 2) = (1.84 * 2.1213) * r ^ 12 := by ring
          rw [e]; exact mul_le_mul_of_nonneg_right (by norm_num) (pow_pos hr0 12).le
      _ ≤ 1.84 * r ^ 10 * √(V1 T) := by gcongr
  have e : T ^ 2 * √T = r ^ 10 := by rw [hsT, hTr]; ring
  rw [e]; linarith

end TernaryGoldbach.MinorArcs
