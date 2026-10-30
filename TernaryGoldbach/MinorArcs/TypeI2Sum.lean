import TernaryGoldbach.MinorArcs.TypeI2Total
import TernaryGoldbach.MinorArcs.GcdSums

/-!
# Type I totals [B, §6.2.2]: summing over `v` ((6.9)–(6.13))

We bound the sum over `v` in `typeI2_le_sum` explicitly for the case `|δ| ≤ 1/2c₂`.
-/

open Real Finset
open ArithmeticFunction (vonMangoldt)
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

/-- `d/φ(d) ≤ n/φ(n)` for `d | n`. -/
theorem div_totient_le_of_dvd {d n : ℕ} (h : d ∣ n) (hn : n ≠ 0) :
    (d : ℝ) / Nat.totient d ≤ n / Nat.totient n := by
  have hd : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.1 h)
  have hφd : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hd)
  have hφn : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)
  rw [div_le_div_iff₀ hφd hφn]
  have hf : ∀ p ∈ n.primeFactors, 0 ≤ 1 - (p : ℚ)⁻¹ ∧ 1 - (p : ℚ)⁻¹ ≤ 1 := by
    intro p hp
    have : (1 : ℚ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact ⟨sub_nonneg.2 (inv_le_one_of_one_le₀ this), by
      have : (0 : ℚ) ≤ (p : ℚ)⁻¹ := by positivity
      linarith⟩
  have key : (d : ℚ) * Nat.totient n ≤ n * Nat.totient d := by
    rw [Nat.totient_eq_mul_prod_factors n, Nat.totient_eq_mul_prod_factors d,
      ← prod_sdiff (Nat.primeFactors_mono h hn)]
    have h1 : ∏ p ∈ n.primeFactors \ d.primeFactors, (1 - (p : ℚ)⁻¹) ≤ 1 :=
      prod_le_one₀ (fun p hp => (hf p (mem_sdiff.1 hp).1).1) (fun p hp => (hf p (mem_sdiff.1 hp).1).2)
    have h0 : 0 ≤ ∏ p ∈ d.primeFactors, (1 - (p : ℚ)⁻¹) :=
      prod_nonneg fun p hp => (hf p (Nat.primeFactors_mono h hn hp)).1
    have : (0 : ℚ) ≤ d * n := by positivity
    nlinarith [mul_nonneg (mul_nonneg this h0) (sub_nonneg.2 h1)]
  exact_mod_cast key

/-- `muBound` is antitone in `q` (along divisors) and monotone in `M`. -/
theorem muBound_anti {M₀ M : ℝ} {q' q : ℕ} (hM0 : 0 < M₀) (hM : M₀ ≤ M) (hq' : 1 ≤ q')
    (hqq : q' ∣ q) (hq : 1 ≤ q) : muBound M q' ≤ muBound M₀ q := by
  have hq'q : (q' : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hqq
  have hq'0 : (0 : ℝ) < q' := by exact_mod_cast hq'
  unfold muBound
  by_cases h : 2 * (q : ℝ) ^ 2 < M₀
  · have h' : 2 * (q' : ℝ) ^ 2 < M := by nlinarith
    rw [if_pos h, if_pos h']
    refine min_le_min le_rfl ?_
    have hlog : 0 < Real.log (M₀ / (2 * q ^ 2)) :=
      Real.log_pos (by rw [one_lt_div (by positivity)]; exact h)
    have hrat := div_totient_le_of_dvd (Nat.mul_dvd_mul_left 2 hqq) (by omega)
    push_cast at hrat
    refine div_le_div₀ (by positivity) (by linarith) hlog (Real.log_le_log (by positivity) ?_)
    exact div_le_div₀ (by linarith) hM (by positivity) (by nlinarith)
  · rw [if_neg h]; split_ifs
    · exact min_le_left _ _
    · exact le_rfl

/-- `t log⁺(A/t) ≤ A/e`. -/
theorem mul_logPlus_div_le {t A : ℝ} (ht : 0 < t) (hA : 0 ≤ A) :
    t * logPlus (A / t) ≤ A / rexp 1 := by
  unfold logPlus
  rcases le_total (Real.log (A / t)) 0 with h | h
  · rw [max_eq_right h]; simp; positivity
  · rw [max_eq_left h]
    rcases hA.lt_or_eq with hA | rfl
    · have hy : 0 < A / t := by positivity
      have h1 := Real.log_le_sub_one_of_pos (show 0 < A / t / rexp 1 by positivity)
      rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
      calc t * Real.log (A / t) ≤ t * (A / t / rexp 1) := mul_le_mul_of_nonneg_left (by linarith) ht.le
        _ = A / rexp 1 := by field_simp
    · simp

/-- `s log⁺(A/s) ≤ t log⁺(A/t) + t/e` for `0 < s ≤ t`. -/
theorem mul_logPlus_mono {s t A : ℝ} (hs : 0 < s) (hst : s ≤ t) (hA : 0 ≤ A) :
    s * logPlus (A / s) ≤ t * logPlus (A / t) + t / rexp 1 := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h3 := mul_logPlus_div_le hs ht.le
  have hsplit : logPlus (A / s) ≤ logPlus (A / t) + logPlus (t / s) := by
    rcases hA.lt_or_eq with hA | rfl
    · unfold logPlus
      have : Real.log (A / s) = Real.log (A / t) + Real.log (t / s) := by
        rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
      rw [this]
      exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
        (add_nonneg (le_max_right _ _) (le_max_right _ _))
    · simp [logPlus]
  calc s * logPlus (A / s) ≤ s * (logPlus (A / t) + logPlus (t / s)) :=
        mul_le_mul_of_nonneg_left hsplit hs.le
    _ = s * logPlus (A / t) + s * logPlus (t / s) := by ring
    _ ≤ t * logPlus (A / t) + t / rexp 1 := add_le_add
        (mul_le_mul_of_nonneg_right hst (logPlus_nonneg _)) h3

theorem cast_div_gcd (q v : ℕ) (hq : 1 ≤ q) :
    ((q / Nat.gcd q v : ℕ) : ℝ) = q / Nat.gcd q v := by
  rw [Nat.cast_div (Nat.gcd_dvd_left q v)]
  exact_mod_cast (Nat.gcd_pos_of_pos_left v hq).ne'

theorem one_le_div_gcd (q v : ℕ) (hq : 1 ≤ q) : 1 ≤ q / Nat.gcd q v :=
  (Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left v hq)).2
    (by rw [one_mul]; exact Nat.le_of_dvd hq (Nat.gcd_dvd_left q v))

/-- [B, (6.6)], per `v`: (4.30) for `x/v`, `q_v = q/(q,v)`. Here `M₀ = min(Q/2V, U)`. -/
theorem bound_4_30_v_le {x δ Q U V : ℝ} {q v : ℕ} (hq : 1 ≤ q) (hx : 0 < x)
    (hδQ : |δ| * q * Q ≤ x) (hU : 0 < U) (hQ : 0 < Q) (hv : 1 ≤ v) (hvV : (v : ℝ) ≤ V) :
    bound_4_30 (x / v) δ (q / Nat.gcd q v) U ≤
      x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q * (Nat.gcd q v / v) +
        c₀ * (1 / 8 - 1 / (2 * π ^ 2)) / x * (U ^ 2 / q * v * Nat.gcd q v + (2 * U + q) * v) := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hV : 0 < V := lt_of_lt_of_le hv0 hvV
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hg1 : (1 : ℝ) ≤ Nat.gcd q v := by exact_mod_cast Nat.gcd_pos_of_pos_left v hq
  have hqv1 := one_le_div_gcd q v hq
  have hqv := cast_div_gcd q v hq
  have hM0 : 0 < min (Q / (2 * V)) U := lt_min (by positivity) hU
  -- `M_v ≥ M₀`.
  have hM : min (Q / (2 * V)) U ≤ Mof (x / v) δ (q / Nat.gcd q v) U := by
    unfold Mof
    split_ifs with hδ
    · exact min_le_right _ _
    · refine min_le_min ?_ le_rfl
      have hδp : 0 < |δ| := abs_pos.2 hδ
      rw [hqv]
      have hgq : (q : ℝ) / Nat.gcd q v ≤ q := div_le_self hq0.le hg1
      have h1 : Q / V ≤ x / v / (|δ| * (q / Nat.gcd q v)) := by
        rw [div_le_div_iff₀ hV (by positivity)]
        calc Q * (|δ| * (q / Nat.gcd q v)) ≤ Q * (|δ| * q) := by gcongr
          _ = |δ| * q * Q := by ring
          _ ≤ x := hδQ
          _ = x / v * v := by field_simp
          _ ≤ x / v * V := by gcongr
      calc Q / (2 * V) = Q / V / 2 := by ring
        _ ≤ _ := by gcongr
  have hmu := (abs_muSum_one_le hqv1 (lt_of_lt_of_le hM0 hM)).trans (muBound_anti hM0 hM hqv1
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q v)) hq)
  have hmi : 0 ≤ minInv c₀ (π * δ) := by
    unfold minInv; split_ifs
    · norm_num
    · exact le_min zero_le_one (div_nonneg (by norm_num [c₀]) (sq_nonneg _))
  have hpi : 0 ≤ 1 / 8 - 1 / (2 * π ^ 2) := by
    have := Real.pi_gt_three
    have := Real.pi_pos
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  unfold bound_4_30
  rw [hqv]
  have e1 : x / v / (2 * (q / Nat.gcd q v)) = x / (2 * q) * (Nat.gcd q v / v) := by
    field_simp
  have e2 : c₀ * (q / Nat.gcd q v) / (x / v) * (1 / 8 - 1 / (2 * π ^ 2)) *
      (U / (q / Nat.gcd q v) + 1) ^ 2 = c₀ * (1 / 8 - 1 / (2 * π ^ 2)) / x *
        (U ^ 2 / q * v * Nat.gcd q v + 2 * U * v + q / Nat.gcd q v * v) := by
    field_simp; ring
  rw [e1, e2]
  have hc : 0 ≤ c₀ * (1 / 8 - 1 / (2 * π ^ 2)) / x := by
    have : (0 : ℝ) < c₀ := by norm_num [c₀]
    positivity
  have hgq : (q : ℝ) / Nat.gcd q v * v ≤ q * v :=
    mul_le_mul_of_nonneg_right (div_le_self hq0.le hg1) hv0.le
  have h1 : x / (2 * q) * (Nat.gcd q v / v) * minInv c₀ (π * δ) *
      |muSum (Mof (x / v) δ (q / Nat.gcd q v) U) (q / Nat.gcd q v) (2 * (q / Nat.gcd q v))
        fun _ => 1| ≤
      x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q * (Nat.gcd q v / v) := by
    have : 0 ≤ x / (2 * q) * (Nat.gcd q v / v) * minInv c₀ (π * δ) := by positivity
    calc _ ≤ x / (2 * q) * (Nat.gcd q v / v) * minInv c₀ (π * δ) *
          muBound (min (Q / (2 * V)) U) q := mul_le_mul_of_nonneg_left hmu this
      _ = _ := by ring
  have h2 := mul_le_mul_of_nonneg_left (show U ^ 2 / q * v * Nat.gcd q v + 2 * U * v +
    q / Nat.gcd q v * v ≤ U ^ 2 / q * v * Nat.gcd q v + (2 * U + q) * v by nlinarith) hc
  linarith

/-- `c₊ = 1 + |η₂'|₁/(x/UV)` [B, (6.7)]. -/
noncomputable def cPlus (x U V : ℝ) : ℝ := 1 + eta2'L1 / (x / (U * V))

/-- The coefficient of `UV` in (6.13): `2√(c₀c₊)/π + 3c₊/(2ec₂)`. -/
noncomputable def coefUV (c : ℝ) : ℝ := 2 * √(c₀ * c) / π + 3 * c / (2 * c₂ * rexp 1)

/-- Our coefficient of `Q` in (6.13) (before the factor `1.0004`):
`√(c₀c₊)/π (log⁺(2U/q) + 1/e) + (2|η₂'|₁/π) max(1, log(c₀e³q²V/4π|η₂'|₁x))`
`+ 2√(3c₀c₊)/π + 3c₊/2c₂ + 55c₀c₂/6π²`. -/
noncomputable def coefQ (x : ℝ) (q : ℕ) (U V c : ℝ) : ℝ :=
  √(c₀ * c) / π * (logPlus (2 * U / q) + 1 / rexp 1) +
    2 * eta2'L1 / π * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 * V / (4 * π * eta2'L1 * x))) +
    (2 * √(3 * c₀ * c) / π + 3 * c / (2 * c₂) + 55 * c₀ * c₂ / (6 * π ^ 2))

/-- [B, (6.7)], per `v`: (4.31) for `x/v`, `q_v = q/(q,v)`. -/
theorem bound_4_31_v_le {x U V : ℝ} {q v : ℕ} (hq : 1 ≤ q) (hx : 0 < x) (hU : 0 < U)
    (hv : 1 ≤ v) (hvV : (v : ℝ) ≤ V) :
    bound_4_31 (x / v) (q / Nat.gcd q v) U ≤
      coefUV (cPlus x U V) * U + coefQ x q U V (cPlus x U V) * q := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hV : 0 < V := lt_of_lt_of_le hv0 hvV
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hg1 : (1 : ℝ) ≤ Nat.gcd q v := by exact_mod_cast Nat.gcd_pos_of_pos_left v hq
  have hqv := cast_div_gcd q v hq
  have hqv1 : (1 : ℝ) ≤ ((q / Nat.gcd q v : ℕ) : ℝ) := by exact_mod_cast one_le_div_gcd q v hq
  have hqvq : ((q / Nat.gcd q v : ℕ) : ℝ) ≤ q := by rw [hqv]; exact div_le_self hq0.le hg1
  have hL := eta2'L1_pos
  have hc0 : (0 : ℝ) < c₀ := by norm_num [c₀]
  have hc2 := c₂_pos
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  set c₁ := 1 + eta2'L1 / (x / v / U) with hc₁
  set c := cPlus x U V with hc
  have hc1 : 1 ≤ c₁ := by
    have : 0 ≤ eta2'L1 / (x / v / U) := by positivity
    linarith
  have hcc : c₁ ≤ c := by
    simp only [hc₁, hc, cPlus]
    have e1 : eta2'L1 / (x / v / U) = eta2'L1 * U * v / x := by field_simp
    have e2 : eta2'L1 / (x / (U * V)) = eta2'L1 * U * V / x := by field_simp
    rw [e1, e2]; gcongr
  have hcpos : 0 ≤ c := by linarith
  set s := ((q / Nat.gcd q v : ℕ) : ℝ) with hs
  have hs0 : 0 < s := by linarith
  unfold bound_4_31
  simp only []
  rw [← hc₁]
  -- The five terms.
  have hsq : √(c₀ * c₁) ≤ √(c₀ * c) := Real.sqrt_le_sqrt (by gcongr)
  have hsq3 : √(3 * c₀ * c₁) ≤ √(3 * c₀ * c) := Real.sqrt_le_sqrt (by gcongr)
  have t1 : 2 * √(c₀ * c₁) / π * U ≤ 2 * √(c₀ * c) / π * U := by gcongr
  have t2 : 3 * c₁ / 2 * (x / v / s) * logPlus (U / (c₂ * (x / v) / s)) ≤
      3 * c / (2 * c₂ * rexp 1) * U := by
    have e : U / (c₂ * (x / v) / s) = (U / c₂) / (x / v / s) := by field_simp
    rw [e]
    have := mul_logPlus_div_le (show 0 < x / v / s by positivity) (show 0 ≤ U / c₂ by positivity)
    calc 3 * c₁ / 2 * (x / v / s) * logPlus (U / c₂ / (x / v / s))
        = 3 * c₁ / 2 * ((x / v / s) * logPlus (U / c₂ / (x / v / s))) := by ring
      _ ≤ 3 * c / 2 * (U / c₂ / rexp 1) := by
          gcongr
          exact mul_nonneg (by positivity) (logPlus_nonneg _)
      _ = 3 * c / (2 * c₂ * rexp 1) * U := by field_simp
  have t3 : √(c₀ * c₁) / π * s * logPlus (U / (s / 2)) ≤
      √(c₀ * c) / π * (logPlus (2 * U / q) + 1 / rexp 1) * q := by
    have e : U / (s / 2) = 2 * U / s := by field_simp
    rw [e]
    have := mul_logPlus_mono hs0 hqvq (show 0 ≤ 2 * U by positivity)
    calc √(c₀ * c₁) / π * s * logPlus (2 * U / s) = √(c₀ * c₁) / π * (s * logPlus (2 * U / s)) := by
          ring
      _ ≤ √(c₀ * c) / π * (q * logPlus (2 * U / q) + q / rexp 1) := by
          gcongr
          exact mul_nonneg hs0.le (logPlus_nonneg _)
      _ = _ := by ring
  have t4 : 2 * eta2'L1 / π * s * max 1 (Real.log (c₀ * rexp 3 * s ^ 2 / (4 * π * eta2'L1 * (x / v))))
      ≤ 2 * eta2'L1 / π * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 * V / (4 * π * eta2'L1 * x))) * q := by
    have harg : c₀ * rexp 3 * s ^ 2 / (4 * π * eta2'L1 * (x / v)) ≤
        c₀ * rexp 3 * q ^ 2 * V / (4 * π * eta2'L1 * x) := by
      rw [show c₀ * rexp 3 * s ^ 2 / (4 * π * eta2'L1 * (x / v)) =
        c₀ * rexp 3 * s ^ 2 * v / (4 * π * eta2'L1 * x) by field_simp]
      gcongr
    have hm : max 1 (Real.log (c₀ * rexp 3 * s ^ 2 / (4 * π * eta2'L1 * (x / v)))) ≤
        max 1 (Real.log (c₀ * rexp 3 * q ^ 2 * V / (4 * π * eta2'L1 * x))) :=
      max_le_max le_rfl (Real.log_le_log (by positivity) harg)
    have : 0 ≤ max 1 (Real.log (c₀ * rexp 3 * s ^ 2 / (4 * π * eta2'L1 * (x / v)))) :=
      zero_le_one.trans (le_max_left _ _)
    calc _ = 2 * eta2'L1 / π * (s * max 1 (Real.log (c₀ * rexp 3 * s ^ 2 /
          (4 * π * eta2'L1 * (x / v))))) := by ring
      _ ≤ 2 * eta2'L1 / π * (q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 * V /
          (4 * π * eta2'L1 * x)))) := by gcongr
      _ = _ := by ring
  have t5 : (2 * √(3 * c₀ * c₁) / π + 3 * c₁ / (2 * c₂) + 55 * c₀ * c₂ / (6 * π ^ 2)) * s ≤
      (2 * √(3 * c₀ * c) / π + 3 * c / (2 * c₂) + 55 * c₀ * c₂ / (6 * π ^ 2)) * q := by
    gcongr
  unfold coefUV coefQ
  nlinarith [t1, t2, t3, t4, t5]

theorem muBound_nonneg (U : ℝ) {q : ℕ} (hq : 1 ≤ q) : 0 ≤ muBound U q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  unfold muBound
  split_ifs with h
  · refine le_min zero_le_one (div_nonneg (by positivity) (Real.log_nonneg ?_))
    rw [le_div_iff₀ (by positivity)]
    linarith
  · exact zero_le_one

theorem coefUV_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ coefUV c := by
  unfold coefUV
  have := c₂_pos; have := Real.pi_pos
  positivity

theorem coefQ_nonneg (x : ℝ) (q : ℕ) (U V : ℝ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ coefQ x q U V c := by
  unfold coefQ
  have := c₂_pos; have := Real.pi_pos; have := eta2'L1_pos
  have h1 : 0 ≤ max 1 (Real.log (c₀ * rexp 3 * q ^ 2 * V / (4 * π * eta2'L1 * x))) :=
    zero_le_one.trans (le_max_left _ _)
  have h2 := logPlus_nonneg (2 * U / q)
  have : (0 : ℝ) < c₀ := by norm_num [c₀]
  positivity

/-- **[B, (6.12) + (6.13)]**, our version, for `|δ| ≤ 1/2c₂` and `qV ≤ Q`:
`|S_{I,2}| ≤ (x/2q) min(1, c₀/(πδ)²) μ log(Vq)`
`+ (c₀(1/8 - 1/2π²)/x) ((U²/q)(0.5004V² + Vq log q) + 0.5004 (2U + q) V²)`
`+ 1.0004 (2√(c₀c₊)/π + 3c₊/2ec₂) UV + 1.0004 C_Q Q`,
with `μ = min(1, (4/5)(2q/φ(2q))/log(M₀/2q²))` (`muBound`), `M₀ = min(Q/2V, U)`,
`c₊ = 1 + 8 log 2/(x/UV)` and `C_Q = coefQ`.  Compared with [B], the term `U²V log V`
is replaced by `U²V log q`, and `√(c₀c₊)/π · Q log(U/(q/2))` becomes
`√(c₀c₊)/π · Q (log⁺(2U/q) + 1/e)` (no assumption `Q ≤ 2UV/e`). -/
theorem typeI2_le_small {α x δ Q U V : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q) (hx : 0 < x)
    (hqV : q * V ≤ Q) (hQV : 16 * V ≤ Q) (hU : 1 ≤ U) (hV : 2e6 ≤ V) (hUV : U * V ≤ x)
    (hδ : |δ| ≤ 1 / (2 * c₂)) :
    ‖typeI2 α x U V‖ ≤
      x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q * Real.log (V * q) +
        c₀ * (1 / 8 - 1 / (2 * π ^ 2)) / x *
          (U ^ 2 / q * (0.5004 * V ^ 2 + V * q * Real.log q) + (2 * U + q) * (0.5004 * V ^ 2)) +
        1.0004 * coefUV (cPlus x U V) * (U * V) + 1.0004 * coefQ x q U V (cPlus x U V) * Q := by
  have hsum := (typeI2_le_sum h hx hqV hQV hU (by linarith) hUV).1 hδ
  refine hsum.trans ?_
  obtain ⟨hq, -, -, hδQ', -⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hV0 : 0 < V := by linarith
  have hQ : 0 < Q := by linarith
  have hU0 : 0 < U := by linarith
  have hδQ : |δ| * q * Q ≤ x := by
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity), one_mul] at hδQ'
    linarith
  set N := ⌊V⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNV : (N : ℝ) ≤ V := Nat.floor_le hV0.le
  set A := x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q with hA
  set K := c₀ * (1 / 8 - 1 / (2 * π ^ 2)) / x with hK
  set c := cPlus x U V with hc
  set C := coefUV c * U + coefQ x q U V c * q with hC
  have hc0 : 0 ≤ c := by
    simp only [hc, cPlus]; have := eta2'L1_pos; positivity
  have hmi : 0 ≤ minInv c₀ (π * δ) := by
    unfold minInv; split_ifs
    · norm_num
    · exact le_min zero_le_one (div_nonneg (by norm_num [c₀]) (sq_nonneg _))
  have hA0 : 0 ≤ A := by
    have := muBound_nonneg (min (Q / (2 * V)) U) hq; positivity
  have hK0 : 0 ≤ K := by
    have := Real.pi_gt_three; have := Real.pi_pos
    have : 0 ≤ 1 / 8 - 1 / (2 * π ^ 2) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have : (0 : ℝ) < c₀ := by norm_num [c₀]
    positivity
  have hC0 : 0 ≤ C := by
    have := coefUV_nonneg hc0; have := coefQ_nonneg x q U V hc0; positivity
  -- Per-`v` bound.
  set F : ℕ → ℝ := fun v => A * (1 / v * Nat.gcd q v) +
    K * (U ^ 2 / q * (v * Nat.gcd q v) + (2 * U + q) * v) + C with hF
  have hF0 : ∀ v, 0 ≤ F v := fun v => by simp only [hF]; positivity
  have step1 : (∑ v ∈ Icc 1 N, if Odd v then (Λ v : ℝ) * (bound_4_30 (x / v) δ (q / Nat.gcd q v) U +
      bound_4_31 (x / v) (q / Nat.gcd q v) U) else 0) ≤ ∑ v ∈ Icc 1 N, (Λ v : ℝ) * F v := by
    refine sum_le_sum fun v hv => ?_
    have hv1 := (mem_Icc.1 hv).1
    have hvV : (v : ℝ) ≤ V := (Nat.cast_le.2 (mem_Icc.1 hv).2).trans hNV
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := v)
    split_ifs
    · refine mul_le_mul_of_nonneg_left ?_ hΛ
      have h30 := bound_4_30_v_le (δ := δ) hq hx hδQ hU0 hQ hv1 hvV
      have h31 := bound_4_31_v_le hq hx hU0 hv1 hvV (V := V)
      simp only [hF, hA, hK, hC, hc]
      have : x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q *
          (Nat.gcd q v / v) = x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q *
          (1 / v * Nat.gcd q v) := by ring
      have : U ^ 2 / q * v * Nat.gcd q v = U ^ 2 / q * (v * Nat.gcd q v) := by ring
      linarith
    · exact mul_nonneg hΛ (hF0 v)
  have e : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * F v =
      A * ∑ v ∈ Icc 1 N, (Λ v : ℝ) * (1 / v) * Nat.gcd q v +
        K * U ^ 2 / q * ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v * Nat.gcd q v +
        K * (2 * U + q) * ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v + C * ∑ v ∈ Icc 1 N, (Λ v : ℝ) := by
    rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib,
      ← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    simp only [hF]; ring
  rw [e] at step1
  refine step1.trans ?_
  -- The sums over `v`.
  have s1 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * (1 / v) * Nat.gcd q v ≤ Real.log (V * q) := by
    refine (sum_vonMangoldt_gcd_div_le hq hN1).trans ?_
    rw [Real.log_mul hV0.ne' hq0.ne']
    have : Real.log N ≤ Real.log V :=
      Real.log_le_log (by exact_mod_cast hN1) hNV
    linarith
  have s3 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v ≤ 0.5004 * V ^ 2 := by
    have := Prelim.sum_vonMangoldt_mul_lt' (y := V) (by norm_num; linarith)
    rw [← hN] at this; linarith
  have s2 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v * Nat.gcd q v ≤ 0.5004 * V ^ 2 + V * q * Real.log q := by
    refine (sum_vonMangoldt_mul_gcd_le hq (N := N)).trans ?_
    have : (N : ℝ) * q * Real.log q ≤ V * q * Real.log q := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
      gcongr
    linarith
  have s4 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) ≤ 1.0004 * V := by
    have := Prelim.sum_vonMangoldt_le_10004 (y := V) (by linarith)
    rwa [← hN] at this
  have hKU : 0 ≤ K * U ^ 2 / q := by positivity
  have hK2 : 0 ≤ K * (2 * U + q) := by positivity
  have b1 := mul_le_mul_of_nonneg_left s1 hA0
  have b2 := mul_le_mul_of_nonneg_left s2 hKU
  have b3 := mul_le_mul_of_nonneg_left s3 hK2
  have b4 := mul_le_mul_of_nonneg_left s4 hC0
  have hQq : coefQ x q U V c * q * V ≤ coefQ x q U V c * Q := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hqV (coefQ_nonneg x q U V hc0)
  have hlast : C * (1.0004 * V) ≤ 1.0004 * coefUV c * (U * V) + 1.0004 * coefQ x q U V c * Q := by
    simp only [hC]; nlinarith
  have hfin : K * U ^ 2 / q * (0.5004 * V ^ 2 + V * q * Real.log q) +
      K * (2 * U + q) * (0.5004 * V ^ 2) = K * (U ^ 2 / q * (0.5004 * V ^ 2 + V * q * Real.log q) +
        (2 * U + q) * (0.5004 * V ^ 2)) := by ring
  linarith

end TernaryGoldbach.MinorArcs
