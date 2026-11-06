import TernaryGoldbach.MinorArcs.TypeIITotalGen
import TernaryGoldbach.MinorArcs.S1Lemma

/-!
# [H, §6.3.1]: the first choice of parameters — tools

* `zeta_three_halves_le`: `ζ(3/2) ≤ 2.77` (so `zeta3 ≤ 27`);
* `typeII_main_le`: the main term of (6.37)/(6.40) at the parameters of (6.49) is at most
  `√(C_{x,t}(log t + 0.002) + log(4t)/2) · √(0.30214 log t + 0.7468)` ([H, (6.60), (6.61)]),
  where `C_{x,t} = log(1 + log 4t/(2 log(9x^{1/3}/(2.004 t))))`.

We write `T = x^{1/3}`.
-/

open Real Finset

namespace TernaryGoldbach.MinorArcs

/-- `n^{-3/2} ≤ 2/√(n-1) - 2/√n` for `n ≥ 2`. -/
theorem rpow_neg_three_halves_le {n : ℝ} (hn : 2 ≤ n) :
    1 / n ^ (3 / 2 : ℝ) ≤ 2 / √(n - 1) - 2 / √n := by
  rw [rpow_three_halves n (by linarith)]
  have ha : 0 < √(n - 1) := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < √n := Real.sqrt_pos.2 (by linarith)
  have hab : √(n - 1) ≤ √n := Real.sqrt_le_sqrt (by linarith)
  have ha2 : √(n - 1) ^ 2 = n - 1 := Real.sq_sqrt (by linarith)
  have hb2 : √n ^ 2 = n := Real.sq_sqrt (by linarith)
  rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hn' : n * √n = √n ^ 3 := by rw [pow_succ, hb2]
  rw [hn']
  -- `√(n-1)√n ≤ 2√n³ (√n - √(n-1))`, i.e. `√(n-1)√n (√n + √(n-1)) ≤ 2 √n³`.
  have key : √(n - 1) * √n * (√n + √(n - 1)) ≤ 2 * √n ^ 3 := by nlinarith
  have hdiff : (√n - √(n - 1)) * (√n + √(n - 1)) = 1 := by nlinarith
  nlinarith [mul_pos ha hb]

/-- `ζ(3/2) ≤ 2.77` (`1 + 2^{-3/2} + √2 = 2.7678…`, by telescoping). -/
theorem zeta_three_halves_le : (riemannZeta (3 / 2)).re ≤ 2.77 := by
  rw [zeta_three_halves_eq]
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ (3 / 2 : ℝ)
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [f]; positivity
  have h2 : f 2 = 1 / (2 * √2) := by
    simp only [f]; push_cast; rw [rpow_three_halves 2 (by norm_num)]
  have hs2 : √2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2' : 1.4142 < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  -- `∑_{n < N} f n + 2/√(N-1) ≤ 1 + f 2 + √2` for `N ≥ 3`.
  have key : ∀ N : ℕ, 3 ≤ N → ∑ n ∈ range N, f n + 2 / √((N : ℝ) - 1) ≤ 1 + f 2 + √2 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [sum_range_succ, sum_range_zero, f]
      norm_num
    | succ N hN ih =>
      rw [sum_range_succ]
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
      have := rpow_neg_three_halves_le hN2
      push_cast
      have e : ((N : ℝ) + 1 - 1) = N := by ring
      rw [e]
      simp only [f] at this ih ⊢
      linarith
  have hbound : ∀ N, ∑ n ∈ range N, f n ≤ 1 + f 2 + √2 := by
    intro N
    rcases lt_or_ge N 3 with h | h
    · refine (sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h.le) fun n _ _ => hf0 n).trans ?_
      simp only [sum_range_succ, sum_range_zero, f]; norm_num
    · have := key N h
      have : 0 ≤ 2 / √((N : ℝ) - 1) := by positivity
      linarith
  refine (Real.tsum_le_of_sum_range_le hf0 hbound).trans ?_
  rw [h2]
  have : 1 / (2 * √2) ≤ 0.3536 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

theorem zeta3_le : zeta3 ≤ 27 := by
  unfold zeta3
  have h0 := zeta_three_halves_nonneg
  have h1 := zeta_three_halves_le
  have : (riemannZeta (3 / 2)).re ^ 3 ≤ 2.77 ^ 3 := pow_le_pow_left₀ h0 h1 3
  norm_num at this ⊢
  linarith

/-- `log T ≤ 15 + T/(6·10⁶)` (tangent line at `6·10⁶`, and `log(6·10⁶) ≤ 16`). -/
theorem log_le_lin {T : ℝ} (hT : 0 < T) : Real.log T ≤ 15 + T / 6e6 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < T / 6e6 by positivity)
  rw [Real.log_div hT.ne' (by norm_num)] at h1
  have h2 : Real.log 6e6 ≤ 16 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (6e6 : ℝ) ≤ 2.7182818283 ^ 16 := by norm_num
      _ ≤ rexp 1 ^ 16 := pow_le_pow_left₀ (by norm_num) this.le 16
      _ = rexp 16 := by rw [← Real.exp_nat_mul]; norm_num
  linarith

/-- `C_{x,t} = log(1 + log 4t/(2 log(9T/(2.004 t))))` with `T = x^{1/3}` [H, (6.64)]. -/
noncomputable def Cxt (T t : ℝ) : ℝ := Real.log (1 + Real.log (4 * t) / (2 * Real.log (9 * T / (2.004 * t))))

theorem div_one_add_le_log {z : ℝ} (hz : 0 ≤ z) : z / (1 + z) ≤ Real.log (1 + z) := by
  have h := Real.add_one_le_exp (-(z / (1 + z)))
  have hpos : 0 < 1 + z := by linarith
  rw [Real.le_log_iff_exp_le hpos]
  have e1 : -(z / (1 + z)) + 1 = 1 / (1 + z) := by field_simp; ring
  rw [e1] at h
  have : rexp (z / (1 + z)) * rexp (-(z / (1 + z))) = 1 := by
    rw [← Real.exp_add]; simp
  have hexp := Real.exp_pos (z / (1 + z))
  have h2 : rexp (z / (1 + z)) * (1 / (1 + z)) ≤ rexp (z / (1 + z)) * rexp (-(z / (1 + z))) :=
    mul_le_mul_of_nonneg_left h hexp.le
  rw [this] at h2
  rw [mul_one_div, div_le_one hpos] at h2
  exact h2

/-- `-log(1 - 1/T) ≤ 2/T` for `T ≥ 2`. -/
theorem neg_log_one_sub_inv_le {T : ℝ} (hT : 2 ≤ T) : -Real.log (1 - 1 / T) ≤ 2 / T := by
  have hT0 : 0 < T := by linarith
  have hpos : 0 < 1 - 1 / T := by
    have : 1 / T ≤ 1 / 2 := by rw [div_le_div_iff₀ hT0 (by norm_num)]; linarith
    linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - 1 / T) by positivity)
  rw [one_div (1 - 1 / T), Real.log_inv] at h
  have hT1 : T - 1 ≠ 0 := by linarith
  have e : (1 - 1 / T)⁻¹ - 1 = 1 / (T - 1) := by field_simp; ring
  rw [e] at h
  have : 1 / (T - 1) ≤ 2 / T := by
    rw [div_le_div_iff₀ (by linarith) hT0]; linarith
  linarith

/-- `log(x/UV) ≤ log(4t)/2 + 2/T` when `UV ≥ (1 - 1/T) x/(2√t)`. -/
theorem log_div_UV_le {x T t U V : ℝ} (hT : 2 ≤ T) (ht0 : 0 < t) (hx0 : 0 < x)
    (hUV0 : 0 < U * V) (hUV1 : (1 - 1 / T) * (x / (2 * √t)) ≤ U * V) :
    Real.log (x / (U * V)) ≤ Real.log (4 * t) / 2 + 2 / T := by
  have hT0 : 0 < T := by linarith
  have hpos : 0 < 1 - 1 / T := by
    have : 1 / T ≤ 1 / 2 := by rw [div_le_div_iff₀ hT0 (by norm_num)]; linarith
    linarith
  have hst : 0 < √t := Real.sqrt_pos.2 ht0
  have hxuv : x / (U * V) ≤ 2 * √t / (1 - 1 / T) := by
    rw [div_le_div_iff₀ hUV0 hpos]
    have := mul_le_mul_of_nonneg_left hUV1 (show (0 : ℝ) ≤ 2 * √t by positivity)
    have e : 2 * √t * ((1 - 1 / T) * (x / (2 * √t))) = x * (1 - 1 / T) := by field_simp
    linarith
  have hlog : Real.log (2 * √t / (1 - 1 / T)) = Real.log (4 * t) / 2 - Real.log (1 - 1 / T) := by
    rw [Real.log_div (by positivity) hpos.ne']
    congr 1
    rw [show 4 * t = (2 * √t) ^ 2 by rw [mul_pow, Real.sq_sqrt ht0.le]; norm_num,
      Real.log_pow]; push_cast; ring
  have := neg_log_one_sub_inv_le hT
  calc Real.log (x / (U * V)) ≤ Real.log (2 * √t / (1 - 1 / T)) :=
        Real.log_le_log (by positivity) hxuv
    _ ≤ _ := by rw [hlog]; linarith

/-- `log(9T/(2.004t)) ≤ 16 + T/6e6` for `t ≥ 2`. -/
theorem logL_le {T t : ℝ} (hT : 0 < T) (ht : 2 ≤ t) :
    Real.log (9 * T / (2.004 * t)) ≤ 16 + T / 6e6 := by
  have h1 := log_le_lin hT
  have : Real.log (9 * T / (2.004 * t)) ≤ Real.log T + 1 := by
    rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add, Real.exp_log hT]
    have : (2.7 : ℝ) ≤ rexp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [div_le_iff₀ (by positivity)]
    have h2 : T * 2.7 * (2.004 * 2) ≤ T * rexp 1 * (2.004 * t) := by gcongr
    nlinarith
  linarith

/-- `log(V/c) ≥ log(9T/(2.004t)) + 0.00048` for `V ≥ 9T/2 - 1`, `c ≤ 1.0015t`. -/
theorem logVc_ge {T t c V : ℝ} (hT : 6e6 ≤ T) (ht0 : 0 < t) (hc0 : 0 < c) (hc : c ≤ 1.0015 * t)
    (hV1 : 9 * T / 2 - 1 ≤ V) :
    Real.log (9 * T / (2.004 * t)) + 0.00048 ≤ Real.log (V / c) := by
  have hT0 : 0 < T := by linarith
  have h1 : 1.00049 * (9 * T / (2.004 * t)) ≤ V / c := by
    rw [le_div_iff₀ hc0]
    have : 1.00049 * (9 * T / (2.004 * t)) * c ≤ 1.00049 * (9 * T / (2.004 * t)) * (1.0015 * t) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have e : 1.00049 * (9 * T / (2.004 * t)) * (1.0015 * t) = 1.00049 * 1.0015 / 2.004 * 9 * T := by
      field_simp
    nlinarith
  have h2 : Real.log (1.00049 * (9 * T / (2.004 * t))) =
      Real.log 1.00049 + Real.log (9 * T / (2.004 * t)) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have h3 : 0.00048 ≤ Real.log 1.00049 := by
    have := div_one_add_le_log (show (0 : ℝ) ≤ 0.00049 by norm_num)
    norm_num at this ⊢; linarith
  calc Real.log (9 * T / (2.004 * t)) + 0.00048 ≤ Real.log (1.00049 * (9 * T / (2.004 * t))) := by
        rw [h2]; linarith
    _ ≤ _ := Real.log_le_log (by positivity) h1

/-- `2/T ≤ 0.0005 · z/(1+z)` when `z ≥ 1/(16 + T/6e6)`, `T ≥ 6e6`. -/
theorem two_div_le_of_z {T z : ℝ} (hT : 6e6 ≤ T) (hz : 1 / (16 + T / 6e6) ≤ z) :
    2 / T ≤ 0.0005 * (z / (1 + z)) := by
  have hT0 : 0 < T := by linarith
  set A := 16 + T / 6e6 with hA
  have hA0 : 0 < A := by positivity
  have hw : 0 < 1 / A := by positivity
  have hz0 : 0 < z := lt_of_lt_of_le hw hz
  have hmono : (1 / A) / (1 + 1 / A) ≤ z / (1 + z) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have e : (1 / A) / (1 + 1 / A) = 1 / (A + 1) := by field_simp
  rw [e] at hmono
  have : 2 / T ≤ 0.0005 * (1 / (A + 1)) := by
    rw [div_le_iff₀ hT0, show 0.0005 * (1 / (A + 1)) * T = 0.0005 * T / (A + 1) by ring,
      le_div_iff₀ (by positivity), hA]
    nlinarith
  nlinarith

/-- `log 4t ≥ 2` for `t ≥ 2`. -/
theorem two_le_log_four_mul {t : ℝ} (ht : 2 ≤ t) : 2 ≤ Real.log (4 * t) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h := Real.exp_one_lt_d9
  calc rexp 2 = rexp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 2
    _ ≤ 4 * t := by nlinarith

/-- `log(9T/(2.004t)) ≥ 2` for `t ≤ T/3`. -/
theorem two_le_logL {T t : ℝ} (ht : 0 < t) (htT : t ≤ T / 3) :
    2 ≤ Real.log (9 * T / (2.004 * t)) := by
  have hT : 0 < T := by linarith
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h := Real.exp_one_lt_d9
  have : rexp 2 ≤ 7.39 := by
    calc rexp 2 = rexp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 2
      _ ≤ 7.39 := by norm_num
  refine this.trans ?_
  rw [le_div_iff₀ (by positivity)]; nlinarith

/-- **The Type II main term at the parameters of [H, (6.49)]** ([H, (6.60), (6.61)], first
lines). Here `T = x^{1/3} ≥ 6·10⁶`, `2 ≤ t ≤ T/3` (`t = δ₀q`), `t ≤ c ≤ 1.0015 t` (`c = 2q`, resp.
`c = δ₀q(1+ε₁)`), `V ∈ [9T/2 - 1, 9T/2]`, `UV ∈ [(1 - 1/T) x/(2√t), x]`. -/
theorem typeII_main_le {x T t c U V : ℝ} (hT : 6e6 ≤ T) (hx : x = T ^ 3) (ht2 : 2 ≤ t)
    (htT : t ≤ T / 3) (hct : t ≤ c) (hc : c ≤ 1.0015 * t) (hU : 0 < U) (hV1 : 9 * T / 2 - 1 ≤ V)
    (hUV1 : (1 - 1 / T) * (x / (2 * √t)) ≤ U * V) (hUV2 : U * V ≤ x)
    (hζ : 8 * zeta3 * √(x / V) / U ≤ 0.2355) :
    √((Real.log (x / (U * V)) + Real.log c *
        (Real.log (Real.log (x / U / c)) - Real.log (Real.log (V / c)))) *
        (0.60428 * Real.log (x / (U * V)) + 0.0924 + 8 * zeta3 * √(x / V) / U)) ≤
      √(Cxt T t * (Real.log t + 0.002) + Real.log (4 * t) / 2) *
        √(0.30214 * Real.log t + 0.7468) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hc0 : 0 < c := by linarith
  have hx0 : 0 < x := by rw [hx]; positivity
  have hV0 : 0 < V := by linarith
  have hUV0 : 0 < U * V := by positivity
  set Λ₀ := Real.log (x / (U * V)) with hΛ₀
  have hΛ0 : 0 ≤ Λ₀ := Real.log_nonneg (by rw [le_div_iff₀ hUV0]; linarith)
  have hΛ1 : Λ₀ ≤ Real.log (4 * t) / 2 + 2 / T := log_div_UV_le (by linarith) ht0 hx0 hUV0 hUV1
  set L := Real.log (9 * T / (2.004 * t)) with hL
  have hL1 : 2 ≤ L := two_le_logL ht0 htT
  have hL2 : L ≤ 16 + T / 6e6 := logL_le hT0 ht2
  have hVc : L + 0.00048 ≤ Real.log (V / c) := logVc_ge hT ht0 hc0 hc hV1
  have hlogVc : 0 < Real.log (V / c) := by linarith
  have hid : Real.log (Real.log (x / U / c)) - Real.log (Real.log (V / c)) =
      Real.log (1 + Λ₀ / Real.log (V / c)) := by
    have e : Real.log (x / U / c) = Real.log (V / c) + Λ₀ := by
      rw [hΛ₀, ← Real.log_mul (by positivity) (by positivity)]
      congr 1; field_simp
    rw [e, ← Real.log_div (by positivity) hlogVc.ne']
    congr 1; field_simp
  have h4t : 2 ≤ Real.log (4 * t) := two_le_log_four_mul ht2
  have hratio : Λ₀ / Real.log (V / c) ≤ Real.log (4 * t) / (2 * L) := by
    rw [div_le_div_iff₀ hlogVc (by linarith)]
    have h1 : 4 * L / T ≤ 0.00048 * Real.log (4 * t) := by
      rw [div_le_iff₀ hT0]
      nlinarith
    have e : (Real.log (4 * t) / 2 + 2 / T) * (2 * L) = Real.log (4 * t) * L + 4 * L / T := by
      field_simp; ring
    have h2 := mul_le_mul_of_nonneg_right hΛ1 (show 0 ≤ 2 * L by linarith)
    have h3 := mul_le_mul_of_nonneg_left hVc (show 0 ≤ Real.log (4 * t) by linarith)
    nlinarith
  have hC : Real.log (1 + Λ₀ / Real.log (V / c)) ≤ Cxt T t := by
    unfold Cxt
    exact Real.log_le_log (by positivity) (by rw [← hL]; linarith)
  have hC0 : 0 ≤ Real.log (1 + Λ₀ / Real.log (V / c)) := Real.log_nonneg (by
    have : 0 ≤ Λ₀ / Real.log (V / c) := div_nonneg hΛ0 hlogVc.le
    linarith)
  have hCt0 : 0 ≤ Cxt T t := hC0.trans hC
  have hCge : 2 / T ≤ 0.0005 * Cxt T t := by
    have hz0 : 0 ≤ Real.log (4 * t) / (2 * L) := by positivity
    have hzlow : 1 / (16 + T / 6e6) ≤ Real.log (4 * t) / (2 * L) :=
      calc 1 / (16 + T / 6e6) ≤ 1 / L := one_div_le_one_div_of_le (by linarith) hL2
        _ = 2 / (2 * L) := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right h4t (by linarith)
    have h1 := two_div_le_of_z hT hzlow
    have h2 : Real.log (4 * t) / (2 * L) / (1 + Real.log (4 * t) / (2 * L)) ≤ Cxt T t := by
      unfold Cxt; rw [← hL]; exact div_one_add_le_log hz0
    linarith
  have hlogc : Real.log c ≤ Real.log t + 0.0015 := by
    have h1 : Real.log c ≤ Real.log (1.0015 * t) := Real.log_le_log hc0 hc
    rw [Real.log_mul (by norm_num) ht0.ne'] at h1
    have : Real.log 1.0015 ≤ 0.0015 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.0015 by norm_num)
      linarith
    linarith
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hA : Λ₀ + Real.log c * (Real.log (Real.log (x / U / c)) - Real.log (Real.log (V / c))) ≤
      Cxt T t * (Real.log t + 0.002) + Real.log (4 * t) / 2 := by
    rw [hid]
    have h1 : Real.log c * Real.log (1 + Λ₀ / Real.log (V / c)) ≤ (Real.log t + 0.0015) * Cxt T t :=
      mul_le_mul hlogc hC hC0 (by linarith)
    nlinarith
  have hB : 0.60428 * Λ₀ + 0.0924 + 8 * zeta3 * √(x / V) / U ≤ 0.30214 * Real.log t + 0.7468 := by
    have hl4 : Real.log (4 * t) = 2 * Real.log 2 + Real.log t := by
      rw [Real.log_mul (by norm_num) ht0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have := Real.log_two_lt_d9
    have : 2 / T ≤ 1e-6 := by rw [div_le_iff₀ hT0]; linarith
    nlinarith
  have hB0 : 0 ≤ 0.60428 * Λ₀ + 0.0924 + 8 * zeta3 * √(x / V) / U := by
    have := zeta3_nonneg; positivity
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt (mul_le_mul hA hB hB0 (by positivity))

end TernaryGoldbach.MinorArcs
