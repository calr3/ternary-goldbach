import TernaryGoldbach.Prelim.Mcheck

/-!
# `|m̌(x) − 1| ≤ 0.00303` for `x ≥ 2·10⁵`

From `abs_mcheck_sub_one_le`: `|m̌(x) − 1| ≤ (1 − γ)|m(x) − M(x)/x| + (1 + ∫₁ˣ |M(u)| du/u)/x`, with
* `|m(x)| ≤ 0.03/log x` for `x ≥ 11815` (Ramaré's bound, [H, (2.21)]);
* on `[2·10⁵, 10⁹)`: `|M(n)| ≤ 0.571 √n` (RSBounds' (M)) and `∑_{t < 2·10⁵} |M(t)|/t ≤ 131` (kernel);
* beyond `10⁹`: RSBounds' `|N(n)| ≤ 0.017 n` (`N(n) = ∑_{k ≤ n} μ(k) log k`), its bound
  `|M(n)| ≤ |C₀| + |N(n)|/log n + ∑_{10⁹ ≤ k < n} |N(k)| (1/log k − 1/log(k+1))` with `|C₀| ≤ 1743`,
  and `∑_{t < 10⁹} |M(t)| log(1 + 1/t) ≤ 36113`.

These inputs are the fields of `McheckBigInputs`; `McheckRSBounds.lean` supplies them.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

local notation "γ" => Real.eulerMascheroniConstant

/-- `N(n) = ∑_{k ≤ n} μ(k) log k`. -/
noncomputable def nfun (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, (μ k : ℝ) * Real.log k

/-- `∑_{a ≤ k < b} |N(k)| (1/log k − 1/log(k+1))`. -/
noncomputable def iint (a b : ℕ) : ℝ :=
  ∑ k ∈ Ico a b, |nfun k| * (1 / Real.log k - 1 / Real.log (k + 1))

/-- `S(x) = ∑_{t < x} |M(t)| log(1 + 1/t)`. -/
noncomputable def sfun (x : ℕ) : ℝ := ∑ t ∈ Ico 1 x, |mertR t| * Real.log (1 + 1 / (t : ℝ))

/-- The inputs for `x ≥ 2·10⁵`. -/
structure McheckBigInputs : Prop where
  /-- Ramaré's `|m(x)| ≤ 0.03/log x` for `x ≥ 11815`. -/
  ramare : ∀ x : ℝ, 11815 ≤ x → |msumR x| ≤ 0.03 / Real.log x
  /-- RSBounds' (M): `|M(n)| ≤ 0.571 √n` for `33 ≤ n ≤ 10⁹`. -/
  mertSqrt : ∀ n : ℕ, 33 ≤ n → n ≤ 10 ^ 9 → |mertR n| ≤ 0.571 * Real.sqrt n
  /-- RSBounds: `|N(n)| ≤ 0.017 n` for `n ≥ 10⁹`. -/
  nBound : ∀ n : ℕ, 10 ^ 9 ≤ n → |nfun n| ≤ 0.017 * n
  /-- RSBounds: `|M(n)| ≤ 1743 + |N(n)|/log n + I(10⁹, n)` for `n ≥ 10⁹`. -/
  mOfN : ∀ n : ℕ, 10 ^ 9 ≤ n → |mertR n| ≤ 1743 + |nfun n| / Real.log n + iint (10 ^ 9) n
  /-- RSBounds: `S(10⁹) ≤ 36113`. -/
  sX0 : sfun (10 ^ 9) ≤ 36113
  /-- Kernel: `∑_{t < 2·10⁵} |M(t)|/t ≤ 131`. -/
  sX1 : ∑ t ∈ Ico (1 : ℕ) 200000, |mertR t| / (t : ℝ) ≤ 131

/-! ### Elementary inequalities -/

theorem log_one_add_inv_le {t : ℝ} (ht : 0 < t) : Real.log (1 + 1 / t) ≤ 1 / t := by
  have := Real.log_le_sub_one_of_pos (x := 1 + 1 / t) (by positivity)
  linarith

theorem inv_sqrt_le_two_mul_sub {t : ℝ} (ht : 1 ≤ t) :
    1 / Real.sqrt t ≤ 2 * (Real.sqrt t - Real.sqrt (t - 1)) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (t - 1) ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
  have hs10 : 0 ≤ Real.sqrt (t - 1) := Real.sqrt_nonneg _
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
  have hsq1 : Real.sqrt (t - 1) ^ 2 = t - 1 := Real.sq_sqrt (by linarith)
  rw [div_le_iff₀ hs]
  nlinarith

theorem sum_sqrt_log_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ t ∈ Ico a b, Real.sqrt t * Real.log (1 + 1 / (t : ℝ)) ≤
      2 * (Real.sqrt ((b : ℝ) - 1) - Real.sqrt ((a : ℝ) - 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb]
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast ha.trans hb
    have hb0 : (0 : ℝ) < b := by linarith
    have hs : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.2 hb0
    have h1 : Real.sqrt b * Real.log (1 + 1 / (b : ℝ)) ≤ 1 / Real.sqrt b := by
      calc Real.sqrt b * Real.log (1 + 1 / (b : ℝ)) ≤ Real.sqrt b * (1 / b) :=
            mul_le_mul_of_nonneg_left (log_one_add_inv_le hb0) hs.le
        _ = 1 / Real.sqrt b := by rw [mul_one_div, Real.sqrt_div_self']
    have h2 := inv_sqrt_le_two_mul_sub hb1
    push_cast
    rw [show (b : ℝ) + 1 - 1 = b by ring]
    linarith

/-- `k (1/log k − 1/log(k+1)) ≤ 1/log² k` for `k ≥ 2`. -/
theorem mul_inv_log_sub_le {k : ℝ} (hk : 2 ≤ k) :
    k * (1 / Real.log k - 1 / Real.log (k + 1)) ≤ 1 / Real.log k ^ 2 := by
  have hk0 : 0 < k := by linarith
  have hl : 0 < Real.log k := Real.log_pos (by linarith)
  have hl1 : Real.log k ≤ Real.log (k + 1) := Real.log_le_log hk0 (by linarith)
  have hl1' : 0 < Real.log (k + 1) := by linarith
  have hd : Real.log (k + 1) - Real.log k ≤ 1 / k := by
    have := log_one_add_inv_le hk0
    rw [show 1 + 1 / k = (k + 1) / k by field_simp, Real.log_div (by linarith) hk0.ne'] at this
    exact this
  have e : 1 / Real.log k - 1 / Real.log (k + 1) =
      (Real.log (k + 1) - Real.log k) / (Real.log k * Real.log (k + 1)) := by
    field_simp
  rw [e]
  calc k * ((Real.log (k + 1) - Real.log k) / (Real.log k * Real.log (k + 1)))
      ≤ k * ((1 / k) / (Real.log k * Real.log k)) := by
        gcongr
    _ = 1 / Real.log k ^ 2 := by field_simp

theorem log_ge_of_exp_le {a x : ℝ} (h : Real.exp a ≤ x) : a ≤ Real.log x := by
  rw [← Real.log_exp a]; exact Real.log_le_log (Real.exp_pos a) h

theorem exp_le_of_pow {n : ℕ} {x : ℝ} (h : (2.7182818286 : ℝ) ^ n ≤ x) : Real.exp n ≤ x := by
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  calc Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ 2.7182818286 ^ n := pow_le_pow_left₀ (Real.exp_pos 1).le he n
    _ ≤ x := h

theorem twelve_le_log {x : ℝ} (hx : 200000 ≤ x) : 12 ≤ Real.log x := by
  have h := log_ge_of_exp_le (a := ((12 : ℕ) : ℝ))
    (exp_le_of_pow (le_trans (by norm_num) hx))
  exact_mod_cast h

theorem twenty_le_log {x : ℝ} (hx : 10 ^ 9 ≤ x) : 20 ≤ Real.log x := by
  have h := log_ge_of_exp_le (a := ((20 : ℕ) : ℝ))
    (exp_le_of_pow (le_trans (by norm_num) hx))
  exact_mod_cast h

/-- `b/s − a/s² ≤ b²/(4a)`. -/
theorem div_sub_div_sq_le {a b s : ℝ} (ha : 0 < a) (hs : 0 < s) : b / s - a / s ^ 2 ≤ b ^ 2 / (4 * a) := by
  rw [div_sub_div _ _ hs.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (b * s - 2 * a), sq_nonneg s, mul_pos ha hs]

/-! ### The bound -/

theorem mertAbsInt_eq (x : ℝ) : mertAbsInt x = sfun ⌊x⌋₊ + |mertR x| * Real.log (x / ⌊x⌋₊) := by
  rw [mertAbsInt, sfun]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj1 := (mem_Ico.1 hj).1
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [add_div, div_self hj0]

theorem mertR_floor (x : ℝ) : mertR x = mertR (⌊x⌋₊ : ℝ) := by
  rw [mertR, mertR, Nat.floor_natCast]

theorem sfun_le_sum_div (n : ℕ) : sfun n ≤ ∑ t ∈ Ico (1 : ℕ) n, |mertR t| / (t : ℝ) := by
  refine sum_le_sum fun t ht => ?_
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Ico.1 ht).1
  calc |mertR t| * Real.log (1 + 1 / (t : ℝ)) ≤ |mertR t| * (1 / t) :=
        mul_le_mul_of_nonneg_left (log_one_add_inv_le ht0) (abs_nonneg _)
    _ = |mertR t| / t := by ring

theorem abs_mertR_mul_log_le {x c : ℝ} (hx : 1 ≤ x) (hM : |mertR x| ≤ c * ⌊x⌋₊) :
    |mertR x| * Real.log (x / ⌊x⌋₊) ≤ c := by
  have hN1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hx : ((1 : ℕ) : ℝ) ≤ x)
  have hN0 : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have hlog : Real.log (x / ⌊x⌋₊) ≤ 1 / ⌊x⌋₊ := by
    have h1 := Real.log_le_sub_one_of_pos (x := x / ⌊x⌋₊) (by positivity)
    have h2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h3 : x / ⌊x⌋₊ - 1 ≤ 1 / ⌊x⌋₊ := by
      rw [div_sub_one hN0.ne', div_le_div_iff_of_pos_right hN0]; linarith
    linarith
  have hlog0 : 0 ≤ Real.log (x / ⌊x⌋₊) :=
    Real.log_nonneg (by rw [le_div_iff₀ hN0, one_mul]; exact Nat.floor_le (by linarith))
  calc |mertR x| * Real.log (x / ⌊x⌋₊) ≤ c * ⌊x⌋₊ * (1 / ⌊x⌋₊) :=
        mul_le_mul hM hlog hlog0 ((abs_nonneg _).trans hM)
    _ = c := by field_simp

/-- `|M(n)| ≤ 0.0009 n` for `n ≥ 10⁹`. -/
theorem abs_mertR_le_big (h : McheckBigInputs) {n : ℕ} (hn : 10 ^ 9 ≤ n) :
    |mertR n| ≤ 0.0009 * n := by
  have hn' : (10 : ℝ) ^ 9 ≤ n := by exact_mod_cast hn
  have hlog := twenty_le_log hn'
  have hN := h.nBound n hn
  have h1 : |nfun n| / Real.log n ≤ 0.00085 * n := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [abs_nonneg (nfun n)]
  have h2 : iint (10 ^ 9) n ≤ 0.0000425 * n := by
    calc iint (10 ^ 9) n ≤ ∑ k ∈ Ico (10 ^ 9) n, (0.017 / 400 : ℝ) := by
          refine sum_le_sum fun k hk => ?_
          have hk9 : 10 ^ 9 ≤ k := (mem_Ico.1 hk).1
          have hk' : (10 : ℝ) ^ 9 ≤ k := by exact_mod_cast hk9
          have hlk := twenty_le_log hk'
          have hd0 : 0 ≤ 1 / Real.log k - 1 / Real.log (k + 1) := by
            rw [sub_nonneg]
            exact one_div_le_one_div_of_le (by linarith)
              (Real.log_le_log (by linarith) (by linarith))
          have hm := mul_inv_log_sub_le (k := k) (by linarith)
          have hsq : 1 / Real.log k ^ 2 ≤ 1 / 400 :=
            one_div_le_one_div_of_le (by norm_num) (by nlinarith)
          calc |nfun k| * (1 / Real.log k - 1 / Real.log (k + 1))
              ≤ (0.017 * k) * (1 / Real.log k - 1 / Real.log (k + 1)) :=
                mul_le_mul_of_nonneg_right (h.nBound k hk9) hd0
            _ = 0.017 * (k * (1 / Real.log k - 1 / Real.log (k + 1))) := by ring
            _ ≤ 0.017 * (1 / 400) := by
                exact mul_le_mul_of_nonneg_left (hm.trans hsq) (by norm_num)
            _ = 0.017 / 400 := by ring
      _ = (0.017 / 400 : ℝ) * (n - 10 ^ 9 : ℕ) := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]; ring
      _ ≤ 0.0000425 * n := by
          rw [Nat.cast_sub hn]; push_cast; nlinarith
  have := h.mOfN n hn
  linarith

theorem abs_mcheck_sub_one_le_mid (h : McheckBigInputs) {x : ℝ} (hx : 200000 ≤ x)
    (hx9 : x < 10 ^ 9) : |mcheck x - 1| ≤ 0.00303 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set N := ⌊x⌋₊ with hN
  have hN2 : 200000 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN9 : N ≤ 10 ^ 9 := by
    have : (N : ℝ) < 10 ^ 9 := lt_of_le_of_lt hNx hx9
    exact_mod_cast this.le
  have hN2' : (200000 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  -- `m` and `M`
  have hm : |msumR x| ≤ 0.0025 := by
    have h1 := h.ramare x (by linarith)
    have h2 := twelve_le_log hx
    have h3 : 0.03 / Real.log x ≤ 0.03 / 12 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
    linarith
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hsN : Real.sqrt N ≤ s := Real.sqrt_le_sqrt hNx
  have hMx : |mertR x| ≤ 0.571 * s := by
    rw [mertR_floor]; exact (h.mertSqrt N (by omega) hN9).trans (by nlinarith [Real.sqrt_nonneg (N : ℝ)])
  -- the integral of `|M|`
  have hS : sfun N ≤ 131 + 1.142 * (s - Real.sqrt 199999) := by
    rw [sfun, ← Finset.sum_Ico_consecutive _ (show 1 ≤ 200000 by norm_num) hN2]
    have h1 : ∑ t ∈ Ico (1 : ℕ) 200000, |mertR (t : ℝ)| * Real.log (1 + 1 / (t : ℝ)) ≤ 131 := by
      have := (sfun_le_sum_div 200000).trans h.sX1
      rwa [sfun] at this
    have h2 : ∑ t ∈ Ico 200000 N, |mertR (t : ℝ)| * Real.log (1 + 1 / (t : ℝ)) ≤
        0.571 * ∑ t ∈ Ico 200000 N, Real.sqrt (t : ℝ) * Real.log (1 + 1 / (t : ℝ)) := by
      rw [mul_sum]
      refine sum_le_sum fun t ht => ?_
      obtain ⟨ht1, ht2⟩ := mem_Ico.1 ht
      have ht1' : (200000 : ℝ) ≤ t := by exact_mod_cast ht1
      have ht0 : (0 : ℝ) < t := by linarith
      have hinv : 0 ≤ 1 / (t : ℝ) := by positivity
      have hl : 0 ≤ Real.log (1 + 1 / (t : ℝ)) := Real.log_nonneg (by linarith)
      have := h.mertSqrt t (by omega) (by omega)
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right this hl
    have h3 := sum_sqrt_log_le (a := 200000) (b := N) (by norm_num) hN2
    have h4 : Real.sqrt ((N : ℝ) - 1) ≤ s := Real.sqrt_le_sqrt (by linarith)
    have h5 : Real.sqrt (((200000 : ℕ) : ℝ) - 1) = Real.sqrt 199999 := by norm_num
    rw [h5] at h3
    linarith
  have hTail : |mertR x| * Real.log (x / N) ≤ 1 := by
    refine abs_mertR_mul_log_le hx1 ((?_ : |mertR x| ≤ 1 * N))
    rw [mertR_floor]
    refine (h.mertSqrt N (by omega) hN9).trans ?_
    have h1 : Real.sqrt N ≤ N := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    nlinarith
  have hI : mertAbsInt x ≤ 132 + 1.142 * (s - Real.sqrt 199999) := by
    rw [mertAbsInt_eq]; linarith
  -- assemble
  have hγ : 1 - γ ≤ 1 / 2 := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ0 : 0 ≤ 1 - γ := by linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hsq : (447.2 : ℝ) ≤ Real.sqrt 199999 := Real.le_sqrt_of_sq_le (by norm_num)
  have hmM : |msumR x - mertR x / x| ≤ 0.0025 + 0.571 / s := by
    refine (abs_sub _ _).trans (add_le_add hm ?_)
    rw [abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 hs0]
    nlinarith [hMx, hs0.le, hs2]
  have hmain := abs_mcheck_sub_one_le hx1
  have hA : (1 - γ) * |msumR x - mertR x / x| ≤ 1 / 2 * (0.0025 + 0.571 / s) :=
    mul_le_mul hγ hmM (abs_nonneg _) (by norm_num)
  have hnum : 1 + mertAbsInt x ≤ 1.142 * s - (1.142 * 447.2 - 133) := by nlinarith
  have hB : (1 + mertAbsInt x) / x ≤ 1.142 / s - (1.142 * 447.2 - 133) / s ^ 2 := by
    calc (1 + mertAbsInt x) / x ≤ (1.142 * s - (1.142 * 447.2 - 133)) / x :=
          div_le_div_of_nonneg_right hnum hx0.le
      _ = 1.142 / s - (1.142 * 447.2 - 133) / s ^ 2 := by
          rw [← hs2]; field_simp
  have hAMGM := div_sub_div_sq_le (a := 1.142 * 447.2 - 133) (b := 1.142 + 0.2855) (by norm_num) hs0
  have e : 1 / 2 * (0.0025 + 0.571 / s) + (1.142 / s - (1.142 * 447.2 - 133) / s ^ 2) =
      0.00125 + ((1.142 + 0.2855) / s - (1.142 * 447.2 - 133) / s ^ 2) := by ring
  have hfin : (0.00125 : ℝ) + (1.142 + 0.2855) ^ 2 / (4 * (1.142 * 447.2 - 133)) ≤ 0.00303 := by
    norm_num
  linarith

theorem abs_mcheck_sub_one_le_large (h : McheckBigInputs) {x : ℝ} (hx9 : 10 ^ 9 ≤ x) :
    |mcheck x - 1| ≤ 0.00303 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set N := ⌊x⌋₊ with hN
  have hN9 : 10 ^ 9 ≤ N := Nat.le_floor (by exact_mod_cast hx9)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hm : |msumR x| ≤ 0.0015 := by
    have h1 := h.ramare x (by linarith)
    have h2 := twenty_le_log hx9
    have h3 : 0.03 / Real.log x ≤ 0.03 / 20 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
    linarith
  have hMN : |mertR x| ≤ 0.0009 * N := by rw [mertR_floor]; exact abs_mertR_le_big h hN9
  have hMx : |mertR x| ≤ 0.0009 * x := hMN.trans (by nlinarith)
  have hS : sfun N ≤ 36113 + 0.0009 * x := by
    rw [sfun, ← Finset.sum_Ico_consecutive _ (show 1 ≤ 10 ^ 9 by norm_num) hN9]
    have h1 : ∑ t ∈ Ico (1 : ℕ) (10 ^ 9), |mertR (t : ℝ)| * Real.log (1 + 1 / (t : ℝ)) ≤ 36113 := by
      have := h.sX0
      rwa [sfun] at this
    have h2 : ∑ t ∈ Ico (10 ^ 9) N, |mertR (t : ℝ)| * Real.log (1 + 1 / (t : ℝ)) ≤
        ∑ t ∈ Ico (10 ^ 9) N, (0.0009 : ℝ) := by
      refine sum_le_sum fun t ht => ?_
      have ht9 := (mem_Ico.1 ht).1
      have ht9' : (10 : ℝ) ^ 9 ≤ t := by exact_mod_cast ht9
      have ht0 : (0 : ℝ) < t := by linarith
      have hinv : 0 ≤ 1 / (t : ℝ) := by positivity
      calc |mertR t| * Real.log (1 + 1 / (t : ℝ)) ≤ (0.0009 * t) * (1 / t) :=
            mul_le_mul (abs_mertR_le_big h ht9) (log_one_add_inv_le ht0)
              (Real.log_nonneg (by linarith)) (by positivity)
        _ = 0.0009 := by field_simp
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hN9] at h2
    push_cast at h2
    refine (add_le_add h1 h2).trans ?_
    nlinarith
  have hTail : |mertR x| * Real.log (x / N) ≤ 0.0009 := abs_mertR_mul_log_le hx1 hMN
  have hI : mertAbsInt x ≤ 36114 + 0.0009 * x := by rw [mertAbsInt_eq]; linarith
  have hγ : 1 - γ ≤ 1 / 2 := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hmM : |msumR x - mertR x / x| ≤ 0.0015 + 0.0009 := by
    refine (abs_sub _ _).trans (add_le_add hm ?_)
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; linarith
  have hA : (1 - γ) * |msumR x - mertR x / x| ≤ 1 / 2 * (0.0015 + 0.0009) :=
    mul_le_mul hγ hmM (abs_nonneg _) (by norm_num)
  have hB : (1 + mertAbsInt x) / x ≤ 0.00094 := by
    rw [div_le_iff₀ hx0]; nlinarith
  have hmain := abs_mcheck_sub_one_le hx1
  linarith

/-- **`|m̌(x) − 1| ≤ 0.00303` for `x ≥ 2·10⁵`.** -/
theorem abs_mcheck_sub_one_le_big (h : McheckBigInputs) {x : ℝ} (hx : 200000 ≤ x) :
    |mcheck x - 1| ≤ 0.00303 := by
  rcases lt_or_ge x (10 ^ 9) with hx9 | hx9
  · exact abs_mcheck_sub_one_le_mid h hx hx9
  · exact abs_mcheck_sub_one_le_large h hx9

end TernaryGoldbach.Prelim
