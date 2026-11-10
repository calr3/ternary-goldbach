import TernaryGoldbach.Prelim.MertensProduct
import TernaryGoldbach.MinorArcs.FirstChoiceFinal
import TernaryGoldbach.MinorArcs.SecondNumerics

/-!
# The "bridge" case of [H, §6.3.2]

Case (c) of `second_case_split`: the new approximation `a'/q'` has `q' ≤ y`, `|δ'| ≤ 8y/q'`, so it
is an approximation for `Q = (3/4)x^{2/3}`, and `δ₀'q' ∈ [2y(1 - y/Q), 2y]`. The first case of
Theorem 3.1.1 (`theorem_3_1_1_first`) then gives `|S| ≤ 1.434 x^{5/6} (log T)^{3/2}`
(`T = x^{1/3}`), i.e. `|S| ≤ 0.276 x^{5/6} (log x)^{3/2}`, with room to spare.
-/

open Real

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 S)

theorem exp_one_sq_ge : (7.389 : ℝ) ≤ rexp 1 ^ 2 := by
  have he := Real.exp_one_gt_d9
  nlinarith

/-- `log log (T/6) ≥ 2.50637` for `T ≥ 6·10⁶`. -/
theorem loglog_T6_ge {T : ℝ} (hT : 6e6 ≤ T) : 2.50637 ≤ Real.log (Real.log (T / 6)) := by
  -- `exp 12.3 ≤ 10⁶ ≤ T/6` and `exp 2.50637 ≤ 12.3`.
  have he := Real.exp_one_lt_d9
  have h1 : rexp 12.3 ≤ 1e6 := by
    have e : rexp 12.3 = rexp 1 ^ 12 * rexp 0.3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h3 : rexp 0.3 ≤ 1.36 := by
      have h := Real.exp_bound' (x := 0.3) (by norm_num) (by norm_num) (n := 3) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h; linarith
    have h12 : rexp 1 ^ 12 ≤ 2.7182818286 ^ 12 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 12
    rw [e]
    calc rexp 1 ^ 12 * rexp 0.3 ≤ 2.7182818286 ^ 12 * 1.36 :=
          mul_le_mul h12 h3 (Real.exp_pos _).le (by positivity)
      _ ≤ 1e6 := by norm_num
  have h2 : rexp 2.50637 ≤ 12.3 := by
    have e : rexp 2.50637 = rexp 1 ^ 2 * rexp 0.50637 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h3 : rexp 0.50637 ≤ 1.6594 := by
      have h := Real.exp_bound' (x := 0.50637) (by norm_num) (by norm_num) (n := 5) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h; linarith
    have h12 : rexp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 2
    rw [e]
    calc rexp 1 ^ 2 * rexp 0.50637 ≤ 2.7182818286 ^ 2 * 1.6594 :=
          mul_le_mul h12 h3 (Real.exp_pos _).le (by positivity)
      _ ≤ 12.3 := by norm_num
  have hl : 12.3 ≤ Real.log (T / 6) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  rw [Real.le_log_iff_exp_le (by linarith)]; linarith

variable [Fact TernaryGoldbach.PlattGRH] in
/-- `q/φ(q) ≤ 1.948 log log T + 1` for `q ≤ T/6`, `T ≥ 6·10⁶` (Lemma C.2.2). -/
theorem div_totient_le_loglog {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 6e6 ≤ T) (hqT : (q : ℝ) ≤ T / 6) :
    (q : ℝ) / Nat.totient q ≤ 1.948 * Real.log (Real.log T) + 1 := by
  have h1 := Prelim.div_totient_lt hq (by linarith) hqT
  have hll := loglog_T6_ge hT
  have hg := exp_gamma_le
  have hl6 : 0 < Real.log (T / 6) := Real.log_pos (by linarith)
  have hmono : Real.log (Real.log (T / 6)) ≤ Real.log (Real.log T) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by linarith) (by linarith))
  have h2 : 2.50637 / Real.log (Real.log (T / 6)) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hll
  have h3 : rexp eulerMascheroniConstant * Real.log (Real.log (T / 6)) ≤
      1.948 * Real.log (Real.log T) :=
    mul_le_mul hg hmono (by linarith) (by norm_num)
  linarith

/-- `C_{x,t} ≤ log log T - 1.06` for `2 ≤ t ≤ T/3`, `T ≥ 6·10⁶`. -/
theorem Cxt_le_loglog {T t : ℝ} (hT : 6e6 ≤ T) (ht2 : 2 ≤ t) (htT : t ≤ T / 3) :
    Cxt T t ≤ Real.log (Real.log T) - 1.06 := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hL := fifteen_six_le_log hT
  have h2 := two_le_logL ht0 htT
  have h4 : Real.log (4 * t) ≤ Real.log T + 0.29 := by
    have : Real.log (4 * t) ≤ Real.log (4 / 3 * T) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at this
    have h43 : Real.log (4 / 3) ≤ 0.29 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (x := 0.29) (by norm_num) 4
      norm_num [Finset.sum_range_succ, Nat.factorial] at h; linarith
    linarith
  have h4' : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hin : 1 + Real.log (4 * t) / (2 * Real.log (9 * T / (2.004 * t))) ≤ Real.log T / (29 / 10) := by
    have : Real.log (4 * t) / (2 * Real.log (9 * T / (2.004 * t))) ≤ Real.log (4 * t) / 4 :=
      div_le_div_of_nonneg_left h4' (by norm_num) (by linarith)
    linarith
  have hpos : 0 < 1 + Real.log (4 * t) / (2 * Real.log (9 * T / (2.004 * t))) := by positivity
  unfold Cxt
  refine (Real.log_le_log hpos hin).trans (le_of_eq_of_le (Real.log_div (by linarith) (by norm_num))
    ?_)
  have : 1.06 ≤ Real.log (29 / 10) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h := Real.exp_bound' (x := 0.06) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have e : rexp 1.06 = rexp 1 * rexp 0.06 := by rw [← Real.exp_add]; norm_num
    have := Real.exp_one_lt_d9
    rw [e]; nlinarith [Real.exp_pos 0.06, Real.exp_pos 1]
  linarith

/-- The final numerical inequality of the bridge case (main part), in `L = log T ≥ 15.6`. -/
theorem bridge_numeric_main {L : ℝ} (hL : 15.6 ≤ L) :
    ((0.27125 * (Real.log L - 1.06) + 0.41415) * L + 0.8764) *
        √(3.0001 * (1.948 * Real.log L + 1)) + (4.38 + 2.5 + 3.8) ≤ 1.434 * (L * √L) := by
  have hsq := sqrt_ge_of_log hL
  have h39 := sqrt_fifteen_six_ge
  have hl15 := log_fifteen_six_le
  have hmono : Real.log 15.6 ≤ Real.log L := Real.log_le_log (by norm_num) hL
  set s := Real.log L
  set d := s - Real.log 15.6
  have hd : 0 ≤ d := sub_nonneg.2 hmono
  have hs : s ≤ 2.75 + d := by simp only [d]; linarith
  have hs0 : 2.7 ≤ s := by
    have : Real.log 15.6 ≥ 2.7 := by
      rw [ge_iff_le, Real.le_log_iff_exp_le (by norm_num)]
      have e : rexp 2.7 = rexp 1 ^ 2 * rexp 0.7 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h := Real.exp_bound' (x := 0.7) (by norm_num) (by norm_num) (n := 5) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      have he := Real.exp_one_lt_d9
      have h12 : rexp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 2
      rw [e]; nlinarith [Real.exp_pos 0.7]
    linarith
  set B := 3.0001 * (1.948 * s + 1)
  have hB : 0 ≤ B := by positivity
  -- AM–GM: `√B ≤ B/8.74 + 2.185`.
  have hsB : √B ≤ B * (100 / 874) + 2.185 := by
    have h : 8.74 * √B ≤ B + 19.0969 := by nlinarith [Real.sq_sqrt hB, sq_nonneg (√B - 4.37)]
    linarith
  set A := 0.27125 * (s - 1.06) + 0.41415 + 0.0562
  have hA : 0 ≤ 0.27125 * (s - 1.06) + 0.41415 := by nlinarith
  have hN : ((0.27125 * (s - 1.06) + 0.41415) * L + 0.8764) * √B ≤
      L * (A * (B * (100 / 874) + 2.185)) := by
    have h1 : 0.8764 ≤ 0.0562 * L := by linarith
    have h2 : 0 ≤ √B := Real.sqrt_nonneg _
    have hA' : 0 ≤ A := by simp only [A]; linarith
    calc ((0.27125 * (s - 1.06) + 0.41415) * L + 0.8764) * √B
        ≤ ((0.27125 * (s - 1.06) + 0.41415) * L + 0.0562 * L) * √B := by gcongr
      _ = L * (A * √B) := by simp only [A]; ring
      _ ≤ _ := by gcongr
  have hc : 4.38 + 2.5 + 3.8 ≤ L * 0.69 := by linarith
  -- Monotonicity in `s`, then a polynomial inequality in `d`.
  have hmon : A * (B * (100 / 874) + 2.185) ≤ (0.27125 * (2.75 + d - 1.06) + 0.41415 + 0.0562) *
      (3.0001 * (1.948 * (2.75 + d) + 1) * (100 / 874) + 2.185) := by
    have h1 : A ≤ 0.27125 * (2.75 + d - 1.06) + 0.41415 + 0.0562 := by simp only [A]; linarith
    have h2 : B * (100 / 874) + 2.185 ≤ 3.0001 * (1.948 * (2.75 + d) + 1) * (100 / 874) + 2.185 := by
      simp only [B]; nlinarith
    exact mul_le_mul h1 h2 (by positivity) (by nlinarith)
  have hpoly : (0.27125 * (2.75 + d - 1.06) + 0.41415 + 0.0562) *
      (3.0001 * (1.948 * (2.75 + d) + 1) * (100 / 874) + 2.185) + 0.69 ≤
      1.434 * (3.9496 * (1 + d / 2 + d ^ 2 / 8)) := by
    nlinarith [mul_nonneg hd hd]
  have hR : 1.434 * (3.9496 * (1 + d / 2 + d ^ 2 / 8)) ≤ 1.434 * √L := by
    have : 3.9496 * (1 + d / 2 + d ^ 2 / 8) ≤ √15.6 * (1 + d / 2 + d ^ 2 / 8) :=
      mul_le_mul_of_nonneg_right h39 (by positivity)
    linarith
  have hL0 : 0 ≤ L := by linarith
  have key : A * (B * (100 / 874) + 2.185) + 0.69 ≤ 1.434 * √L := by linarith
  nlinarith [mul_le_mul_of_nonneg_left key hL0]

/-- The third term of the bridge bound, divided by `√T`. -/
theorem bridge_numeric_third {T : ℝ} (hT : 6e6 ≤ T) :
    6.0002 * ((1.948 * Real.log (Real.log T) + 1) * (13 / 4 * Real.log T + 7.82) +
      13.66 * Real.log T + 37.55) ≤ 2.5 * √T := by
  have hT0 : 0 < T := by linarith
  have hsT : √T = rexp (Real.log T / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hT0]; ring_nf
  set L := Real.log T
  have hL := fifteen_six_le_log hT
  -- `log L ≤ L/e ≤ 0.3679 L`.
  have hlog : Real.log L ≤ 0.3679 * L := by
    have h := Real.log_le_sub_one_of_pos (show 0 < L / rexp 1 by positivity)
    rw [Real.log_div (by linarith) (Real.exp_pos 1).ne', Real.log_exp] at h
    have he := Real.exp_one_gt_d9
    have : L / rexp 1 ≤ 0.3679 * L := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
    linarith
  -- `√T = exp(L/2) ≥ exp(7.8)(1 + d/2 + d²/8)`, `d = L - 15.6`.
  have h78 : (2400 : ℝ) ≤ rexp 7.8 := by
    have e : rexp 7.8 = rexp 1 ^ 7 * rexp 0.8 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h := Real.sum_le_exp_of_nonneg (x := 0.8) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have he := Real.exp_one_gt_d9
    have h7 : (2.7182818283 : ℝ) ^ 7 ≤ rexp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) he.le 7
    rw [e]; nlinarith [Real.exp_pos 0.8]
  have hgrow := exp_half_ge (s := L) (s₀ := 15.6) hL
  have e2 : rexp (15.6 / 2) = rexp 7.8 := by norm_num
  rw [e2] at hgrow
  set d := L - 15.6
  have hd : 0 ≤ d := by simp only [d]; linarith
  have hLd : L = 15.6 + d := by simp only [d]; ring
  have hY : (1.948 * Real.log L + 1) * (13 / 4 * L + 7.82) ≤ (1.948 * (0.3679 * L) + 1) *
      (13 / 4 * L + 7.82) := by
    have : 0 ≤ 13 / 4 * L + 7.82 := by linarith
    nlinarith
  rw [hsT]
  have hq : 0 ≤ 1 + d / 2 + d ^ 2 / 8 := by positivity
  have hexp : 2400 * (1 + d / 2 + d ^ 2 / 8) ≤ rexp (L / 2) :=
    (mul_le_mul_of_nonneg_right h78 hq).trans hgrow
  have hP : 6.0002 * ((1.948 * (0.3679 * L) + 1) * (13 / 4 * L + 7.82) + 13.66 * L + 37.55) ≤
      2.5 * (2400 * (1 + d / 2 + d ^ 2 / 8)) := by
    rw [hLd]; nlinarith [mul_nonneg hd hd]
  linarith

set_option maxHeartbeats 1600000 in
variable [Fact TernaryGoldbach.PlattGRH] in
/-- **The bridge case** (case (c) of `second_case_split`): `|S| ≤ 1.434 T^{5/2} (log T)^{3/2}`. -/
theorem bridge_le {α T δ' : ℝ} {a' : ℤ} {q' : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ' a' q' (3 / 4 * T ^ 2)) (hq : (q' : ℝ) ≤ T / 6)
    (hlow : 2 * (T / 6) * (1 - (T / 6) / (3 / 4 * T ^ 2)) ≤ |δ'| * q' / 4) :
    ‖S eta2 (T ^ 3) α‖ ≤ 1.434 * (T ^ 2 * √T) * (Real.log T * √(Real.log T)) := by
  have key := theorem_3_1_1_first hT h hq
  obtain ⟨-, ht2, htT⟩ := first_choice_t hT h hq
  have hq1 : 1 ≤ q' := h.1
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq1
  have hφ : (0 : ℝ) < Nat.totient q' := by exact_mod_cast Nat.totient_pos.2 hq1
  set t := delta0 δ' * q' with ht
  have ht0 : 0 < t := by linarith
  -- `t ≥ T/3.0001`.
  have htlow : T / 3.0001 ≤ t := by
    have h1 : |δ'| * q' / 4 ≤ t := by
      simp only [t, delta0]
      have := le_max_right 2 (|δ'| / 4)
      nlinarith
    have h2 : T / 3.0001 ≤ 2 * (T / 6) * (1 - (T / 6) / (3 / 4 * T ^ 2)) := by
      have e : 2 * (T / 6) * (1 - (T / 6) / (3 / 4 * T ^ 2)) = T / 3 - 2 / 27 := by
        field_simp; ring
      rw [e]
      have : T / 3 - T / 3.0001 = T / 90003 := by ring
      have : (2 : ℝ) / 27 ≤ T / 90003 := by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
      linarith
    linarith
  -- `q'/φ(q') ≤ Fb`.
  set L := Real.log T
  have hL := fifteen_six_le_log hT
  have hF := div_totient_le_loglog hq1 hT hq
  set Fb := 1.948 * Real.log L + 1
  have hlogL : 2.7 ≤ Real.log L := by
    have : (2.7 : ℝ) ≤ Real.log 15.6 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have e : rexp 2.7 = rexp 1 ^ 2 * rexp 0.7 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h := Real.exp_bound' (x := 0.7) (by norm_num) (by norm_num) (n := 5) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      have he := Real.exp_one_lt_d9
      have h12 : rexp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 2
      rw [e]; nlinarith [Real.exp_pos 0.7]
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 15.6) hL]
  have hFb : 0 < Fb := by positivity
  -- `log t ≤ L`, `log t ≥ 0`.
  have hlt : Real.log t ≤ L := Real.log_le_log ht0 (by linarith)
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  -- The coefficient of the main term.
  have hC := Cxt_le_loglog hT ht2 htT
  have hC0 := Cxt_nonneg ht2 htT
  set N := (0.27125 * Cxt T t + 0.41415) * Real.log t + 0.8764
  have hN : N ≤ (0.27125 * (Real.log L - 1.06) + 0.41415) * L + 0.8764 := by
    simp only [N]
    have h1 : 0.27125 * Cxt T t + 0.41415 ≤ 0.27125 * (Real.log L - 1.06) + 0.41415 := by linarith
    have h2 : 0 ≤ 0.27125 * Cxt T t + 0.41415 := by positivity
    nlinarith
  have hN0 : 0 ≤ N := by positivity
  -- `√(δ₀ φ) ≥ √T / √(3.0001 Fb)`.
  have hden : T / (3.0001 * Fb) ≤ delta0 δ' * Nat.totient q' := by
    have e : delta0 δ' * Nat.totient q' = t / ((q' : ℝ) / Nat.totient q') := by
      simp only [t]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : T * ((q' : ℝ) / Nat.totient q') ≤ T * Fb := mul_le_mul_of_nonneg_left hF hT0.le
    have hT3t : T ≤ 3.0001 * t := by rw [div_le_iff₀ (by norm_num)] at htlow; linarith
    have : T * Fb ≤ 3.0001 * t * Fb := mul_le_mul_of_nonneg_right hT3t hFb.le
    linarith
  have hsT : 0 < √T := Real.sqrt_pos.2 hT0
  have hT3 : T ^ 3 = T ^ 2 * √T * √T := by rw [mul_assoc, Real.mul_self_sqrt hT0.le]; ring
  have t1 : N / √(delta0 δ' * Nat.totient q') * T ^ 3 ≤ N * √(3.0001 * Fb) * (T ^ 2 * √T) := by
    have h1 : √(T / (3.0001 * Fb)) ≤ √(delta0 δ' * Nat.totient q') := Real.sqrt_le_sqrt hden
    have h2 : √(T / (3.0001 * Fb)) = √T / √(3.0001 * Fb) := Real.sqrt_div' _ (by positivity)
    have hp : 0 < √(3.0001 * Fb) := Real.sqrt_pos.2 (by positivity)
    rw [h2] at h1
    rw [div_mul_eq_mul_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) h1)]
    calc N * T ^ 3 = N * √(3.0001 * Fb) * (T ^ 2 * √T) * (√T / √(3.0001 * Fb)) := by
          rw [hT3]; field_simp
      _ ≤ _ := by gcongr
  have t2 : 2.526 * T ^ 3 / √t ≤ 4.38 * (T ^ 2 * √T) := by
    have h1 : √(T / 3.0001) ≤ √t := Real.sqrt_le_sqrt htlow
    have h2 : √(T / 3.0001) = √T / √3.0001 := Real.sqrt_div' _ (by norm_num)
    have h3 : √3.0001 ≤ 1.73209 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [h2] at h1
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) h1)]
    calc 2.526 * T ^ 3 = 2.526 * √3.0001 * (T ^ 2 * √T) * (√T / √3.0001) := by
          rw [hT3]; field_simp
      _ ≤ 4.38 * (T ^ 2 * √T) * (√T / √3.0001) := by gcongr; nlinarith
      _ ≤ _ := by gcongr
  have t3 : 2 * T ^ 3 / t * ((q' : ℝ) / Nat.totient q' * (13 / 4 * Real.log t + 7.82) +
      13.66 * Real.log t + 37.55) ≤ 2.5 * (T ^ 2 * √T) := by
    have h1 : 2 * T ^ 3 / t ≤ 6.0002 * T ^ 2 := by
      rw [div_le_iff₀ ht0]
      have : T ≤ 3.0001 * t := by rw [div_le_iff₀ (by norm_num)] at htlow; linarith
      nlinarith [sq_nonneg T]
    have h2 : (q' : ℝ) / Nat.totient q' * (13 / 4 * Real.log t + 7.82) + 13.66 * Real.log t +
        37.55 ≤ Fb * (13 / 4 * L + 7.82) + 13.66 * L + 37.55 := by
      have : (q' : ℝ) / Nat.totient q' * (13 / 4 * Real.log t + 7.82) ≤ Fb * (13 / 4 * L + 7.82) :=
        mul_le_mul hF (by linarith) (by positivity) hFb.le
      linarith
    have h3 := bridge_numeric_third hT
    have hpos : 0 ≤ (q' : ℝ) / Nat.totient q' * (13 / 4 * Real.log t + 7.82) +
        13.66 * Real.log t + 37.55 := by positivity
    calc 2 * T ^ 3 / t * ((q' : ℝ) / Nat.totient q' * (13 / 4 * Real.log t + 7.82) +
          13.66 * Real.log t + 37.55)
        ≤ 6.0002 * T ^ 2 * (Fb * (13 / 4 * L + 7.82) + 13.66 * L + 37.55) :=
          mul_le_mul h1 h2 hpos (by positivity)
      _ = T ^ 2 * (6.0002 * (Fb * (13 / 4 * L + 7.82) + 13.66 * L + 37.55)) := by ring
      _ ≤ T ^ 2 * (2.5 * √T) := by gcongr
      _ = _ := by ring
  have hmain : ((0.27125 * (Real.log L - 1.06) + 0.41415) * L + 0.8764) * √(3.0001 * Fb) +
      (4.38 + 2.5 + 3.8) ≤ 1.434 * (L * √L) := bridge_numeric_main hL
  have hP : 0 < T ^ 2 * √T := by positivity
  have hfin : N * √(3.0001 * Fb) ≤ 1.434 * (L * √L) - (4.38 + 2.5 + 3.8) := by
    have : N * √(3.0001 * Fb) ≤ ((0.27125 * (Real.log L - 1.06) + 0.41415) * L + 0.8764) *
        √(3.0001 * Fb) := mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg _)
    linarith
  refine key.trans ?_
  have t4 : 3.8 * (T ^ 2 * √T) = 3.8 * (T ^ 2 * √T) := rfl
  nlinarith [mul_le_mul_of_nonneg_right hfin hP.le]

end TernaryGoldbach.MinorArcs
