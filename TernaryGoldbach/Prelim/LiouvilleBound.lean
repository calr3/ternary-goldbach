import TernaryGoldbach.Prelim.MoebiusBound
import TernaryGoldbach.Prelim.Liouville
import TernaryGoldbach.Prelim.SmallLiouville
import TernaryGoldbach.Prelim.SmallCGrid
import TernaryGoldbach.Prelim.SmallMoebius

/-!
# `|ℓ(z)| ≤ 0.99/log z`, `|ℓ_q(x)| ≤ 0.99 (q/φ(q))/log(x/q)`
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- `|∑_{n≤k} λ(n)/n| log(k+1) ≤ 0.99` for `1 ≤ k ≤ 10⁵` (maximum `0.7831` at `k = 10`), checked by
the kernel (`Prelim/SmallLiouville.lean`). -/
theorem liouville_small (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 10 ^ 5) :
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  TernaryGoldbach.Prelim.SmallLiou.liouville_kernel k h1 h2

/-- `|∑_{n≤y} μ(n)/n| ≤ √2/√y` for `1 ≤ y < 11815` (kernel, `Prelim/SmallMoebius.lean`). -/
theorem m_sqrt {y : ℝ} (h1 : 1 ≤ y) (h2 : y < 11815) :
    |∑ n ∈ Icc 1 ⌊y⌋₊, (μ n : ℝ) / n| ≤ √2 / √y := by
  have hy0 : 0 < y := by linarith
  have hk1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hk2 : ⌊y⌋₊ < 11815 := (Nat.floor_lt hy0.le).2 (by norm_num; linarith)
  refine (SmallMoeb.moebius_sqrt_kernel _ hk1 hk2).trans ?_
  rw [← Real.sqrt_div (by norm_num)]
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (by norm_num) hy0 (Nat.lt_floor_add_one y).le

/-- **[H, (2.24)]** on our checked range: `|∑_{n ≤ x} μ(n)/n| ≤ √(2/x)` for `0 < x < 11815`
([H] cites Helfgott's computation for `x ≤ 10¹²`). -/
theorem abs_sum_moebius_div_le_sqrt {x : ℝ} (hx : 0 < x) (hx' : x < 11815) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ √(2 / x) := by
  rcases lt_or_ge x 1 with h | h
  · have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.2 h
    rw [this]; simp only [Finset.Icc_self, Icc_eq_empty_of_lt zero_lt_one, sum_empty, abs_zero]
    positivity
  · rw [Real.sqrt_div (by norm_num)]; exact m_sqrt h hx'

theorem abs_ls_le (z : ℝ) :
    |ls z| ≤ ∑ u ∈ Icc 1 (Nat.sqrt ⌊z⌋₊),
      |∑ n ∈ Icc 1 ⌊z / (u * u : ℕ)⌋₊, (μ n : ℝ) / n| / (u * u : ℕ) := by
  rw [← lqs_one, lqs_eq]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun u hu => ?_))
  have hu0 : u ≠ 0 := by have := (mem_Icc.1 hu).1; omega
  rw [chiq_apply, if_pos ⟨hu0, Nat.coprime_one_right u⟩, mqs_one, abs_mul, abs_div, abs_one,
    Nat.abs_cast]
  ring

/-- `u ≤ √⌊z⌋` gives `1 ≤ z/u²`. -/
theorem one_le_div_sq {z : ℝ} {u : ℕ} (hz : 0 ≤ z) (hu : u ∈ Icc 1 (Nat.sqrt ⌊z⌋₊)) :
    1 ≤ z / (u * u : ℕ) ∧ (0 : ℝ) < (u * u : ℕ) := by
  obtain ⟨h1, h2⟩ := mem_Icc.1 hu
  have hpos : (0 : ℝ) < (u * u : ℕ) := by exact_mod_cast Nat.mul_pos h1 h1
  refine ⟨?_, hpos⟩
  rw [le_div_iff₀ hpos, one_mul]
  have : u * u ≤ ⌊z⌋₊ := Nat.le_sqrt.1 h2
  exact (Nat.cast_le.2 this).trans (Nat.floor_le hz)

theorem sum_inv_sq_le (N : ℕ) : ∑ u ∈ Icc 1 N, (1 : ℝ) / (u * u : ℕ) ≤ 5 / 3 := by
  have key : ∀ N : ℕ, 1 ≤ N → ∑ u ∈ Icc 1 N, (1 : ℝ) / (u * u : ℕ) ≤ 5 / 3 - 1 / (N + 1 / 2) := by
    intro N hN
    induction N with
    | zero => omega
    | succ N ih =>
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; norm_num
      rw [sum_Icc_succ_top (by omega)]
      have := ih h0
      have hN0 : (0 : ℝ) < N := by exact_mod_cast h0
      have e : (1 : ℝ) / ((N + 1) * (N + 1) : ℕ) ≤ 1 / (N + 1 / 2) - 1 / ((N + 1 : ℕ) + 1 / 2) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; norm_num
  · have := key N h0
    have : (0 : ℝ) ≤ 1 / (N + 1 / 2) := by positivity
    linarith

theorem log_three_le : Real.log 3 ≤ 1.1363 := by
  have h1 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h2 : 1 - (4 / 3 : ℝ)⁻¹ ≤ Real.log (4 / 3) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), h1] at h2
  have := Real.log_two_lt_d9
  norm_num at h2; linarith

theorem sum_log_div_sq_le (N : ℕ) : ∑ u ∈ Icc 1 N, Real.log u / (u * u : ℕ) ≤ 1.0117 := by
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_le
  have hl3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set g : ℝ → ℝ := fun t => (Real.log t + 1) / t with hg
  have key : ∀ N : ℕ, 3 ≤ N → ∑ u ∈ Icc 1 N, Real.log u / (u * u : ℕ) ≤
      Real.log 2 / 4 + Real.log 3 / 9 + g 3 - g N := by
    intro N hN
    induction N with
    | zero => omega
    | succ N ih =>
      rcases Nat.lt_or_ge N 3 with h | h
      · have : N = 2 := by omega
        subst this
        simp only [hg]
        rw [show Icc 1 (2 + 1) = {1, 2, 3} by rfl]
        simp; ring_nf; linarith
      rw [sum_Icc_succ_top (by omega)]
      have := ih h
      have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h
      have hN0 : (0 : ℝ) < N := by linarith
      -- `log(N+1)/(N+1)² ≤ g(N) − g(N+1)`
      have hlog : Real.log (N + 1) ≤ Real.log N + 1 / N := by
        have := Real.log_le_sub_one_of_pos (x := (N + 1) / N) (by positivity)
        rw [Real.log_div (by positivity) hN0.ne'] at this
        have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
        linarith
      have hanti : Real.log (N + 1) / (N + 1) ≤ Real.log N / N := by
        have he : Real.exp 1 ≤ (N : ℝ) := by
          have := Real.exp_one_lt_d9; linarith
        exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (by linarith))
          (by linarith)
      have step : Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1) * (N + 1) : ℕ) ≤ g N - g (N + 1 : ℕ) := by
        simp only [hg]
        push_cast
        have hN1 : (0 : ℝ) < N + 1 := by linarith
        have a1 : Real.log (N + 1) / ((N + 1) * (N + 1)) ≤ Real.log N / N / (N + 1) := by
          rw [show Real.log (N + 1) / ((N + 1) * (N + 1)) = Real.log (N + 1) / (N + 1) / (N + 1) by
            field_simp]
          exact div_le_div_of_nonneg_right hanti hN1.le
        have a2 : Real.log N / N / (N + 1) ≤ (Real.log N + 1) / N - (Real.log (N + 1) + 1) / (N + 1) := by
          have : (Real.log N + 1) / N - (Real.log (N + 1) + 1) / (N + 1) ≥
              (Real.log N + 1) / N - (Real.log N + 1 / N + 1) / (N + 1) := by
            have := div_le_div_of_nonneg_right (by linarith : Real.log (N + 1) + 1 ≤ Real.log N + 1 / N + 1) hN1.le
            linarith
          have e : (Real.log N + 1) / N - (Real.log N + 1 / N + 1) / (N + 1) = Real.log N / N / (N + 1) := by
            field_simp; ring
          linarith
        linarith
      push_cast at step this ⊢
      linarith
  rcases Nat.lt_or_ge N 3 with h | h
  · interval_cases N
    · norm_num
    · norm_num
    · rw [show Icc 1 2 = {1, 2} by rfl]; simp; linarith
  · have := key N h
    have hgN : 0 ≤ g N := by
      simp only [hg]
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      have := Real.log_nonneg this
      positivity
    simp only [hg] at this
    have : g 3 = (Real.log 3 + 1) / 3 := rfl
    linarith

theorem harm_le {N : ℕ} (hN : 1 ≤ N) : ∑ u ∈ Icc 1 N, (1 : ℝ) / u ≤ 1 + Real.log N := by
  have hs : Icc 1 N = insert 1 (Ioc 1 N) := by
    ext n; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
  rw [hs, sum_insert (by simp)]
  have h := sum_inv_le_log (a := 1) (b := N) le_rfl hN
  push_cast at h ⊢; simp only [Real.log_one, sub_zero] at h
  linarith

theorem sqrt_floor_le {z : ℝ} (hz : 0 ≤ z) : (Nat.sqrt ⌊z⌋₊ : ℝ) ≤ √z := by
  apply Real.le_sqrt_of_sq_le
  have h1 : Nat.sqrt ⌊z⌋₊ * Nat.sqrt ⌊z⌋₊ ≤ ⌊z⌋₊ := Nat.sqrt_le _
  have : ((Nat.sqrt ⌊z⌋₊ * Nat.sqrt ⌊z⌋₊ : ℕ) : ℝ) ≤ z := (Nat.cast_le.2 h1).trans (Nat.floor_le hz)
  push_cast at this; nlinarith

/-- The term bound `|m(z/u²)|/u² ≤ √2/(u√z)` when `z/u² < 11815`. -/
theorem term_sqrt_le {z : ℝ} (hz : 0 < z) {u : ℕ} (hu : u ∈ Icc 1 (Nat.sqrt ⌊z⌋₊))
    (hlt : z / (u * u : ℕ) < 11815) :
    |∑ n ∈ Icc 1 ⌊z / (u * u : ℕ)⌋₊, (μ n : ℝ) / n| / (u * u : ℕ) ≤ √2 / √z * (1 / u) := by
  obtain ⟨h1, hpos⟩ := one_le_div_sq hz.le hu
  have hm := m_sqrt h1 hlt
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (mem_Icc.1 hu).1
  have hsq : √(z / (u * u : ℕ)) = √z / u := by
    push_cast
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul_self hu0.le]
  rw [hsq] at hm
  have hsz : 0 < √z := Real.sqrt_pos.2 hz
  calc |∑ n ∈ Icc 1 ⌊z / (u * u : ℕ)⌋₊, (μ n : ℝ) / n| / (u * u : ℕ)
      ≤ (√2 / (√z / u)) / (u * u : ℕ) := div_le_div_of_nonneg_right hm hpos.le
    _ = √2 / √z * (1 / u) := by push_cast; field_simp

theorem log_le_of_le_two_pow {y : ℝ} (hy : 0 < y) {k : ℕ} (h : y ≤ 2 ^ k) :
    Real.log y ≤ k * 0.6931471808 := by
  have := Real.log_le_log hy h
  rw [Real.log_pow] at this
  have := Real.log_two_lt_d9
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith

theorem div_sq_le {z : ℝ} (hz : 0 ≤ z) {u N : ℕ} (hu : u ∈ Icc 1 N) : z / (u * u : ℕ) ≤ z := by
  have h1 : 1 ≤ u * u := Nat.mul_pos (mem_Icc.1 hu).1 (mem_Icc.1 hu).1
  exact div_le_self hz (by exact_mod_cast h1)

/-- `∑_{u ≤ N} 1/u² ≤ π²/6 < 1.64495` (`hasSum_zeta_two`). -/
theorem sum_inv_sq_le_pi (N : ℕ) : ∑ u ∈ Icc 1 N, (1 : ℝ) / (u * u : ℕ) ≤ 1.64495 := by
  have h := sum_le_hasSum (Icc 1 N) (fun i _ => by positivity) hasSum_zeta_two
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have e : ∑ u ∈ Icc 1 N, (1 : ℝ) / (u * u : ℕ) = ∑ u ∈ Icc 1 N, (1 : ℝ) / (u : ℝ) ^ 2 :=
    sum_congr rfl fun u _ => by push_cast; ring
  rw [e]
  have : Real.pi ^ 2 / 6 ≤ 1.64495 := by nlinarith
  linarith

theorem log_11815_ge_nine : (9 : ℝ) ≤ Real.log 11815 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 9 ≤ (2.7182818286 : ℝ) ^ 9 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 9
    _ ≤ 11815 := by norm_num

/-- `log z ≤ 0.04 √z` for `z ≥ 10⁵`. -/
theorem log_le_sqrt_mid {z : ℝ} (hz : 1e5 ≤ z) : Real.log z ≤ 0.04 * √z := by
  have hz0 : 0 < z := by linarith
  have hs5 : (316.2 : ℝ) ≤ √1e5 := Real.le_sqrt_of_sq_le (by norm_num)
  have h5pos : (0 : ℝ) < √1e5 := by positivity
  set s := √z / √1e5 with hs
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ h5pos, one_mul]; exact Real.sqrt_le_sqrt hz
  have hl := Real.log_le_sub_one_of_pos (x := s) (by linarith)
  have e : Real.log z = Real.log 1e5 + 2 * Real.log s := by
    rw [hs, Real.log_div (by positivity) h5pos.ne', Real.log_sqrt hz0.le, Real.log_sqrt (by norm_num)]
    ring
  have h5 := log_le_of_le_two_pow (y := 1e5) (k := 17) (by norm_num) (by norm_num)
  have hsz : √z = √1e5 * s := by rw [hs]; field_simp
  rw [e, hsz]
  norm_num at h5
  nlinarith [mul_le_mul_of_nonneg_right hs5 (by linarith : (0 : ℝ) ≤ s)]

variable [Fact TernaryGoldbach.PlattGRH] in
/-- The term bound for `z/u² ≥ 11815` (`|m(y)| ≤ 0.14/log y`, `abs_m_le_014`). -/
theorem term_big_le {z : ℝ} (hz : 0 < z) {u N : ℕ} (hu : u ∈ Icc 1 N)
    (hge : 11815 ≤ z / (u * u : ℕ)) :
    |∑ n ∈ Icc 1 ⌊z / (u * u : ℕ)⌋₊, (μ n : ℝ) / n| / (u * u : ℕ) ≤
      0.14 / Real.log z * ((1 + 2 / 9 * Real.log u) * (1 / (u * u : ℕ))) := by
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (mem_Icc.1 hu).1
  have hpos : (0 : ℝ) < (u * u : ℕ) := by push_cast; positivity
  have hm := abs_m_le_014 hge
  set w := Real.log (z / (u * u : ℕ)) with hw
  have hw9 : 9 ≤ w := log_11815_ge_nine.trans (Real.log_le_log (by norm_num) hge)
  have hlu : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hL : Real.log z = w + 2 * Real.log u := by
    rw [hw, Real.log_div hz.ne' hpos.ne']; push_cast
    rw [Real.log_mul (by positivity) (by positivity)]; ring
  have hLpos : 0 < Real.log z := by linarith
  have key : 1 / w ≤ (1 + 2 / 9 * Real.log u) / Real.log z := by
    rw [div_le_div_iff₀ (by linarith) hLpos, hL]
    nlinarith [mul_nonneg hlu (by linarith : (0 : ℝ) ≤ w - 9)]
  calc |∑ n ∈ Icc 1 ⌊z / (u * u : ℕ)⌋₊, (μ n : ℝ) / n| / (u * u : ℕ)
      ≤ 0.14 / w / (u * u : ℕ) := div_le_div_of_nonneg_right hm hpos.le
    _ = 0.14 * (1 / w) * (1 / (u * u : ℕ)) := by ring
    _ ≤ 0.14 * ((1 + 2 / 9 * Real.log u) / Real.log z) * (1 / (u * u : ℕ)) := by gcongr
    _ = _ := by ring

variable [Fact TernaryGoldbach.PlattGRH] in
/-- `|ℓ(z)| log z ≤ 0.99` for `z ≥ 10⁵`: `|m(y)| ≤ 0.14/log y` for `z/u² ≥ 11815`, the kernel-checked
`√(2/y)` below. -/
theorem abs_ls_large {z : ℝ} (hz : 1e5 ≤ z) : |ls z| * Real.log z ≤ 0.99 := by
  have hz0 : 0 < z := by linarith
  set L := Real.log z with hLdef
  have hLpos : 0 < L := Real.log_pos (by linarith)
  set N := Nat.sqrt ⌊z⌋₊ with hN
  set U := Nat.sqrt ⌊z / 11815⌋₊ with hU
  have hU1 : 1 ≤ U := by
    rw [hU, Nat.le_sqrt]; exact Nat.le_floor (by rw [le_div_iff₀ (by norm_num)]; norm_num; linarith)
  have hUN : U ≤ N := Nat.sqrt_le_sqrt (Nat.floor_mono (div_le_self hz0.le (by norm_num)))
  set t : ℕ → ℝ := fun u => |∑ n ∈ Icc 1 ⌊z / (u * u : ℕ)⌋₊, (μ n : ℝ) / n| / (u * u : ℕ) with ht
  have h0 := abs_ls_le z
  rw [← sum_filter_add_sum_filter_not _ (fun u : ℕ => 11815 ≤ z / (u * u : ℕ))] at h0
  -- first part
  have hA : ∑ u ∈ (Icc 1 N).filter (fun u : ℕ => 11815 ≤ z / (u * u : ℕ)), t u ≤
      0.14 / L * (1.64495 + 2 / 9 * 1.0117) := by
    calc _ ≤ ∑ u ∈ (Icc 1 N).filter (fun u : ℕ => 11815 ≤ z / (u * u : ℕ)),
          0.14 / L * ((1 + 2 / 9 * Real.log u) * (1 / (u * u : ℕ))) :=
          sum_le_sum fun u hu => term_big_le hz0 (mem_filter.1 hu).1 (mem_filter.1 hu).2
      _ ≤ ∑ u ∈ Icc 1 N, 0.14 / L * ((1 + 2 / 9 * Real.log u) * (1 / (u * u : ℕ))) := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun u hu _ => ?_
          have : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast (mem_Icc.1 hu).1)
          positivity
      _ = 0.14 / L * (∑ u ∈ Icc 1 N, (1 : ℝ) / (u * u : ℕ) +
            2 / 9 * ∑ u ∈ Icc 1 N, Real.log u / (u * u : ℕ)) := by
          rw [mul_sum, ← sum_add_distrib, mul_sum]
          exact sum_congr rfl fun u _ => by ring
      _ ≤ 0.14 / L * (1.64495 + 2 / 9 * 1.0117) := by
          have := sum_inv_sq_le_pi N
          have := sum_log_div_sq_le N
          gcongr
  -- second part
  have hB : ∑ u ∈ (Icc 1 N).filter (fun u : ℕ => ¬ 11815 ≤ z / (u * u : ℕ)), t u ≤
      √2 / √z * 5.6 := by
    calc _ ≤ ∑ u ∈ (Icc 1 N).filter (fun u : ℕ => ¬ 11815 ≤ z / (u * u : ℕ)), √2 / √z * (1 / (u : ℝ)) :=
          sum_le_sum fun u hu => term_sqrt_le hz0 (mem_filter.1 hu).1 (not_le.1 (mem_filter.1 hu).2)
      _ ≤ ∑ u ∈ Ioc U N, √2 / √z * (1 / (u : ℝ)) := by
          refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun u _ _ => by positivity
          obtain ⟨hu1, hu2⟩ := mem_filter.1 hu
          refine mem_Ioc.2 ⟨?_, (mem_Icc.1 hu1).2⟩
          by_contra! hle
          apply hu2
          have h1 : u * u ≤ ⌊z / 11815⌋₊ := Nat.le_sqrt.1 hle
          have h2 : ((u * u : ℕ) : ℝ) ≤ z / 11815 :=
            (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
          have hp : (0 : ℝ) < (u * u : ℕ) := by
            have := (mem_Icc.1 hu1).1; exact_mod_cast Nat.mul_pos this this
          rw [le_div_iff₀ hp]; rw [le_div_iff₀ (by norm_num)] at h2; linarith
      _ = √2 / √z * ∑ u ∈ Ioc U N, (1 : ℝ) / u := by rw [mul_sum]
      _ ≤ √2 / √z * 5.6 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (sum_inv_le_log hU1 hUN).trans ?_
          -- `N² ≤ z < 11815 (U+1)² ≤ 47260 U²`
          have hU0 : (0 : ℝ) < U := by exact_mod_cast hU1
          have hN0 : (0 : ℝ) < N := by exact_mod_cast hU1.trans hUN
          have hNz : (N : ℝ) * N ≤ z := by
            have : ((N * N : ℕ) : ℝ) ≤ z := (Nat.cast_le.2 (Nat.sqrt_le _)).trans (Nat.floor_le hz0.le)
            push_cast at this; exact this
          have hzU : z < 11815 * ((U + 1) * (U + 1)) := by
            have h1 := Nat.lt_succ_sqrt ⌊z / 11815⌋₊
            have h2 : z / 11815 < ⌊z / 11815⌋₊ + 1 := Nat.lt_floor_add_one _
            have h3 : ((⌊z / 11815⌋₊ + 1 : ℕ) : ℝ) ≤ ((U.succ * U.succ : ℕ) : ℝ) := by exact_mod_cast h1
            push_cast at h3
            rw [div_lt_iff₀ (by norm_num)] at h2
            nlinarith
          have hNU : (N : ℝ) * N ≤ (47260 * U * U) := by
            have : (U : ℝ) + 1 ≤ 2 * U := by
              have : (1 : ℝ) ≤ U := by exact_mod_cast hU1
              linarith
            nlinarith
          have hlog : Real.log ((N : ℝ) * N) ≤ Real.log (47260 * U * U) :=
            Real.log_le_log (by positivity) hNU
          rw [Real.log_mul hN0.ne' hN0.ne', Real.log_mul (by positivity) hU0.ne',
            Real.log_mul (by norm_num) hU0.ne'] at hlog
          have h4 := log_le_of_le_two_pow (y := 47260) (k := 16) (by norm_num) (by norm_num)
          norm_num at h4
          linarith
  have hsum : |ls z| ≤ 0.14 / L * (1.64495 + 2 / 9 * 1.0117) + √2 / √z * 5.6 := by
    refine h0.trans ?_
    exact add_le_add hA hB
  have hsz : 0 < √z := Real.sqrt_pos.2 hz0
  have hlz := log_le_sqrt_mid hz
  obtain ⟨-, hs2⟩ := sqrt2_bounds
  calc |ls z| * L ≤ (0.14 / L * (1.64495 + 2 / 9 * 1.0117) + √2 / √z * 5.6) * L :=
        mul_le_mul_of_nonneg_right hsum hLpos.le
    _ = 0.14 * (1.64495 + 2 / 9 * 1.0117) + √2 * 5.6 * (L / √z) := by
        field_simp
    _ ≤ 0.14 * (1.64495 + 2 / 9 * 1.0117) + 1.414214 * 5.6 * 0.04 := by
        gcongr
        rw [div_le_iff₀ hsz]; exact hlz
    _ ≤ 0.99 := by norm_num

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **`|ℓ(z)| ≤ 0.99/log z`** for `z > 1`. -/
theorem abs_ls_mul_log_le {z : ℝ} (hz : 1 < z) : |ls z| * Real.log z ≤ 0.99 := by
  rcases lt_or_ge z 1e5 with h | h
  · have hk1 : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz.le)
    have hk2 : ⌊z⌋₊ ≤ 10 ^ 5 := by
      have := (Nat.floor_lt (by linarith)).2 (show z < ((10 ^ 5 : ℕ) : ℝ) by norm_num; linarith)
      omega
    have hax := liouville_small _ hk1 hk2
    have hl : Real.log z ≤ Real.log (⌊z⌋₊ + 1) :=
      Real.log_le_log (by linarith) (Nat.lt_floor_add_one z).le
    have hl0 : 0 ≤ Real.log z := Real.log_nonneg hz.le
    rw [ls]
    calc |∑ n ∈ Icc 1 ⌊z⌋₊, lam n / n| * Real.log z
        ≤ |∑ n ∈ Icc 1 ⌊z⌋₊, lam n / n| * Real.log (⌊z⌋₊ + 1) :=
          mul_le_mul_of_nonneg_left hl (abs_nonneg _)
      _ ≤ 0.99 := hax
  exact abs_ls_large h

/-! ### `ℓ_q` and `m_q` -/

theorem mqs_eq_sum (q : ℕ) (x : ℝ) :
    mqs q x = ∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0) := by
  rw [mqs]; refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.1 hn).1; omega
  rw [muq, pmul_apply, chiq_apply, intCoe_apply]
  by_cases h : Nat.Coprime n q
  · rw [if_pos ⟨hn0, h⟩, if_pos h, mul_one]
  · rw [if_neg (fun h' => h h'.2), if_neg h, mul_zero, zero_div]

theorem abs_mqs_le_one {q : ℕ} (hq : 1 ≤ q) (x : ℝ) : |mqs q x| ≤ 1 := by
  rw [mqs_eq_sum]; exact abs_sum_moebius_div_coprime_le_one x hq

theorem abs_lqs_le_53 {q : ℕ} (hq : 1 ≤ q) (x : ℝ) : |lqs q x| ≤ 5 / 3 := by
  rw [lqs_eq]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun u hu => ?_).trans (sum_inv_sq_le _))
  have hpos : (0 : ℝ) < (u * u : ℕ) := by
    have := (mem_Icc.1 hu).1; exact_mod_cast Nat.mul_pos this this
  rw [abs_mul, abs_div, abs_of_nonneg (chiq_nonneg q u), abs_of_pos hpos]
  have h1 := chiq_le_one q u
  have h2 := abs_mqs_le_one hq (x / (u * u : ℕ))
  have h3 := chiq_nonneg q u
  calc chiq q u / (u * u : ℕ) * |mqs q (x / (u * u : ℕ))| ≤ 1 / (u * u : ℕ) * 1 := by gcongr
    _ = 1 / (u * u : ℕ) := mul_one _

theorem sum_dq_le {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    ∑ d ∈ Icc 1 N, dq q d / d ≤ (q : ℝ) / Nat.totient q := by
  refine le_trans ?_ (sum_factored_le hq N)
  rw [sum_filter, show Icc 1 N = Ioc 0 N from rfl]
  refine sum_le_sum fun d hd => ?_
  have hd0 : d ≠ 0 := by have := (mem_Ioc.1 hd).1; omega
  rw [dq_apply]
  split_ifs with h1 h2
  · have hμ : ((μ d : ℝ)) ^ 2 ≤ 1 := by
      have : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [abs_nonneg (μ d : ℝ), sq_abs (μ d : ℝ)]
    rw [div_eq_mul_inv]
    have : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
    nlinarith
  · exfalso; apply h2
    rw [Nat.mem_factoredNumbers']
    intro p hp hpd
    exact Nat.mem_primeFactors.2 ⟨hp, hpd.trans h1.2, by omega⟩
  · rw [zero_div]; positivity
  · simp

theorem Q_ge_one {q : ℕ} (hq : 1 ≤ q) : 1 ≤ (q : ℝ) / Nat.totient q := by
  have h0 : 0 < Nat.totient q := Nat.totient_pos.2 hq
  rw [le_div_iff₀ (by exact_mod_cast h0), one_mul]
  exact_mod_cast Nat.totient_le q

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **`|ℓ_q(x)| ≤ 0.99 (q/φ(q))/log(x/q)`** for `q < x` (Lemma 2.5 and `abs_ls_mul_log_le`). -/
theorem abs_lqs_mul_log_le {q : ℕ} (hq : 1 ≤ q) {x : ℝ} (hqx : (q : ℝ) < x) :
    |lqs q x| * Real.log (x / q) ≤ 0.99 * ((q : ℝ) / Nat.totient q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 < x := by linarith
  have hyq : 0 < Real.log (x / q) := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  rw [lqs_eq_dq]
  have hterm : ∀ d ∈ Icc 1 ⌊x⌋₊, |dq q d / d * ls (x / d)| ≤
      dq q d / d * (0.99 / Real.log (x / q)) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.1 hd).1
    have hdq0 : 0 ≤ dq q d := by rw [dq_apply]; split_ifs <;> positivity
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ dq q d / d)]
    by_cases h : d ≠ 0 ∧ d ∣ q
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hdq : (d : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq h.2
      have h1 : x / q ≤ x / d := div_le_div_of_nonneg_left hx0.le hd0 hdq
      have hgt : 1 < x / d := lt_of_lt_of_le (by rw [lt_div_iff₀ hq0]; linarith) h1
      have hb := abs_ls_mul_log_le hgt
      have hl : Real.log (x / q) ≤ Real.log (x / d) := Real.log_le_log (by positivity) h1
      rw [le_div_iff₀ hyq]
      calc |ls (x / d)| * Real.log (x / q) ≤ |ls (x / d)| * Real.log (x / d) :=
            mul_le_mul_of_nonneg_left hl (abs_nonneg _)
        _ ≤ 0.99 := hb
    · have : dq q d = 0 := by rw [dq_apply, if_neg h]
      rw [this]; simp
  calc |∑ d ∈ Icc 1 ⌊x⌋₊, dq q d / d * ls (x / d)| * Real.log (x / q)
      ≤ (∑ d ∈ Icc 1 ⌊x⌋₊, dq q d / d * (0.99 / Real.log (x / q))) * Real.log (x / q) :=
        mul_le_mul_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)) hyq.le
    _ = 0.99 * ∑ d ∈ Icc 1 ⌊x⌋₊, dq q d / d := by
        rw [← sum_mul, mul_comm (∑ d ∈ Icc 1 ⌊x⌋₊, dq q d / d) _]
        field_simp
    _ ≤ 0.99 * ((q : ℝ) / Nat.totient q) := by gcongr; exact sum_dq_le hq _

/-! ### The optimisation -/

/- `betaf` (`β(a, u)`) and the grid sum `Gs` are defined in `SmallCGrid.lean`. -/

theorem betaf_nonneg (a : ℝ) (u : ℕ) : 0 ≤ betaf a u := by
  unfold betaf; split_ifs with h
  · exact le_min (by norm_num) (div_nonneg (by norm_num) (by linarith))
  · norm_num

theorem betaf_le (a : ℝ) (u : ℕ) : betaf a u ≤ 5 / 3 := by
  unfold betaf; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem betaf_anti {a y : ℝ} (hay : a ≤ y) (u : ℕ) : betaf y u ≤ betaf a u := by
  unfold betaf
  by_cases h1 : 2 * Real.log u < a
  · rw [if_pos (lt_of_lt_of_le h1 hay), if_pos h1]
    exact min_le_min le_rfl (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))
  · rw [if_neg h1]; split_ifs
    · exact min_le_left _ _
    · exact le_rfl

theorem sum_inv_sq_Ioc_le (M N : ℕ) : ∑ u ∈ Ioc M N, (1 : ℝ) / (u * u : ℕ) ≤ 1 / (M + 1 / 2) := by
  have key : ∀ k : ℕ, ∑ u ∈ Ioc M (M + k), (1 : ℝ) / (u * u : ℕ) ≤
      1 / (M + 1 / 2) - 1 / ((M + k : ℕ) + 1 / 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, sum_Ioc_succ_top (by omega)]
      have e : (1 : ℝ) / ((M + k + 1) * (M + k + 1) : ℕ) ≤
          1 / ((M + k : ℕ) + 1 / 2) - 1 / ((M + k + 1 : ℕ) + 1 / 2) := by
        push_cast
        have : (0 : ℝ) ≤ M + k := by positivity
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  rcases le_or_gt N M with h | h
  · rw [Ioc_eq_empty (by omega), sum_empty]; positivity
  · obtain ⟨k, rfl⟩ : ∃ k, N = M + k := ⟨N - M, by omega⟩
    have := key k
    have : (0 : ℝ) ≤ 1 / ((M + k : ℕ) + 1 / 2) := by positivity
    linarith

/-- Splitting the `u`-sum at `M`. -/
theorem S_split (a : ℝ) (N M : ℕ) :
    ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf a u ≤
      ∑ u ∈ Icc 1 M, |(μ u : ℝ)| / (u * u : ℕ) * betaf a u + 5 / 3 / (M + 1 / 2) := by
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun u => u ≤ M)]
  have hnn : ∀ u : ℕ, 0 ≤ |(μ u : ℝ)| / (u * u : ℕ) * betaf a u := fun u => by
    have := betaf_nonneg a u; positivity
  apply add_le_add
  · refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun u _ _ => hnn u
    obtain ⟨h1, h2⟩ := mem_filter.1 hu
    exact mem_Icc.2 ⟨(mem_Icc.1 h1).1, h2⟩
  · calc _ ≤ ∑ u ∈ Ioc M N, |(μ u : ℝ)| / (u * u : ℕ) * betaf a u := by
          refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun u _ _ => hnn u
          obtain ⟨h1, h2⟩ := mem_filter.1 hu
          exact mem_Ioc.2 ⟨by omega, (mem_Icc.1 h1).2⟩
      _ ≤ ∑ u ∈ Ioc M N, 5 / 3 * ((1 : ℝ) / (u * u : ℕ)) := by
          refine sum_le_sum fun u _ => ?_
          have hμ : |(μ u : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have hb := betaf_le a u
          have hb0 := betaf_nonneg a u
          have : (0 : ℝ) ≤ 1 / (u * u : ℕ) := by positivity
          calc |(μ u : ℝ)| / (u * u : ℕ) * betaf a u = |(μ u : ℝ)| * (1 / (u * u : ℕ)) * betaf a u := by
                ring
            _ ≤ 1 * (1 / (u * u : ℕ)) * (5 / 3) := by gcongr
            _ = 5 / 3 * ((1 : ℝ) / (u * u : ℕ)) := by ring
      _ ≤ 5 / 3 / (M + 1 / 2) := by
          rw [← mul_sum, div_eq_mul_one_div (5 / 3 : ℝ)]
          exact mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le M N) (by norm_num)

theorem Gs_nonneg (a : ℝ) : 0 ≤ Gs a := by
  unfold Gs
  have : 0 ≤ ∑ u ∈ Icc 1 3000, |(μ u : ℝ)| / (u * u : ℕ) * betaf a u :=
    sum_nonneg fun u _ => by have := betaf_nonneg a u; positivity
  positivity

/-- `y ∑_u |μ(u)|/u² β(y, u) ≤ 2.8` for `2.8 ≤ y < 80` (kernel-checked grid, `SmallCGrid.lean`). -/
theorem yS_grid {y : ℝ} (h1 : 2.8 ≤ y) (h2 : y < 80) (N : ℕ) :
    y * ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u ≤ 2.8 := by
  obtain ⟨t, ht, hay, hyb⟩ := CGrid.C_cover h1 h2
  set a : ℝ := (t.1 : ℝ) / 1000 with ha
  have hS : ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u ≤ Gs a := by
    refine (S_split y N 3000).trans ?_
    unfold Gs
    push_cast
    gcongr with u
    · exact betaf_anti hay u
  have hG := Gs_nonneg a
  have hy0 : 0 ≤ y := by linarith
  calc y * ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u ≤ y * Gs a :=
        mul_le_mul_of_nonneg_left hS hy0
    _ ≤ ((t.2.1 : ℝ) / 1000) * Gs a := mul_le_mul_of_nonneg_right hyb hG
    _ ≤ 2.8 := CGrid.grid_ok ht

/-- `y ∑_u |μ(u)|/u² β(y, u) ≤ 2.8` for `y ≥ 80` (split at `e^{y/8}`). -/
theorem yS_large {y : ℝ} (hy : 80 ≤ y) (N : ℕ) :
    y * ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u ≤ 2.8 := by
  have hy0 : 0 < y := by linarith
  set M := ⌊Real.exp (y / 8)⌋₊ with hM
  have hsplit := S_split y N M
  -- the head
  have hhead : ∑ u ∈ Icc 1 M, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u ≤ 5 / 3 * (1.32 / y) := by
    calc _ ≤ ∑ u ∈ Icc 1 M, (1 : ℝ) / (u * u : ℕ) * (1.32 / y) := by
          refine sum_le_sum fun u hu => ?_
          have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (mem_Icc.1 hu).1
          have huM : (u : ℝ) ≤ Real.exp (y / 8) :=
            (Nat.cast_le.2 (mem_Icc.1 hu).2).trans (Nat.floor_le (Real.exp_pos _).le)
          have hlog : Real.log u ≤ y / 8 := by
            rw [← Real.log_exp (y / 8)]; exact Real.log_le_log (by linarith) huM
          have hl0 : 0 ≤ Real.log u := Real.log_nonneg hu1
          have hb : betaf y u ≤ 1.32 / y := by
            unfold betaf
            rw [if_pos (by linarith)]
            refine (min_le_right _ _).trans ?_
            rw [div_le_div_iff₀ (by linarith) hy0]; nlinarith
          have hμ : |(μ u : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have hb0 := betaf_nonneg y u
          have hpos : (0 : ℝ) < (u * u : ℕ) := by push_cast; positivity
          calc |(μ u : ℝ)| / (u * u : ℕ) * betaf y u = |(μ u : ℝ)| * (1 / (u * u : ℕ)) * betaf y u := by
                ring
            _ ≤ 1 * (1 / (u * u : ℕ)) * (1.32 / y) := by gcongr
            _ = (1 : ℝ) / (u * u : ℕ) * (1.32 / y) := by ring
      _ = (∑ u ∈ Icc 1 M, (1 : ℝ) / (u * u : ℕ)) * (1.32 / y) := by rw [sum_mul]
      _ ≤ 5 / 3 * (1.32 / y) := mul_le_mul_of_nonneg_right (sum_inv_sq_le M) (by positivity)
  -- the tail
  have he10 : (22026 : ℝ) ≤ Real.exp 10 := by
    have h := Real.exp_one_gt_d9
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (22026 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h.le 10
  have hexp : 22026 * (y / 80) ≤ Real.exp (y / 8) := by
    have h1 : Real.exp (y / 8) = Real.exp 10 * Real.exp ((y - 80) / 8) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : (y - 80) / 8 + 1 ≤ Real.exp ((y - 80) / 8) := Real.add_one_le_exp _
    have h3 : y / 80 ≤ (y - 80) / 8 + 1 := by linarith
    rw [h1]
    calc 22026 * (y / 80) ≤ Real.exp 10 * ((y - 80) / 8 + 1) :=
          mul_le_mul he10 h3 (by positivity) (by positivity)
      _ ≤ Real.exp 10 * Real.exp ((y - 80) / 8) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hM1 : Real.exp (y / 8) < M + 1 := Nat.lt_floor_add_one _
  have hMy : 274 * y ≤ (M : ℝ) + 1 / 2 := by nlinarith
  have htail : y * (5 / 3 / ((M : ℝ) + 1 / 2)) ≤ 5 / 3 / 274 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  calc y * ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u
      ≤ y * (5 / 3 * (1.32 / y) + 5 / 3 / (M + 1 / 2)) :=
        mul_le_mul_of_nonneg_left (hsplit.trans (by linarith)) hy0.le
    _ = 5 / 3 * 1.32 + y * (5 / 3 / (M + 1 / 2)) := by field_simp
    _ ≤ 5 / 3 * 1.32 + 5 / 3 / 274 := by linarith
    _ ≤ 2.8 := by norm_num

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **[H, (2.22)] with constant `2.8`** (Ramaré's Liouville route, hal-02572851):
`|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ 2.8 (q/φ(q))/log(x/q)` for `1 ≤ q < x`. -/
theorem abs_mqs_le {q : ℕ} (hq : 1 ≤ q) {x : ℝ} (hqx : (q : ℝ) < x) :
    |mqs q x| ≤ 2.8 * ((q : ℝ) / Nat.totient q) / Real.log (x / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 < x := by linarith
  set y := Real.log (x / q) with hydef
  have hy : 0 < y := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  set Q := (q : ℝ) / Nat.totient q with hQ
  have hQ1 : 1 ≤ Q := Q_ge_one hq
  rw [le_div_iff₀ hy]
  rcases le_or_gt y 2.8 with hy28 | hy28
  · have := abs_mqs_le_one hq x
    nlinarith
  -- `|m_q(x)| ≤ Q ∑_u |μ(u)|/u² β(y, u)`
  set N := Nat.sqrt ⌊x⌋₊
  have hS : |mqs q x| ≤ Q * ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u := by
    rw [mqs_eq, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u hu => ?_)
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (mem_Icc.1 hu).1
    have hpos : (0 : ℝ) < (u * u : ℕ) := by push_cast; positivity
    have hχ := chiq_le_one q u
    have hχ0 := chiq_nonneg q u
    -- the `ℓ_q` factor
    have hl : |lqs q (x / (u * u : ℕ))| ≤ Q * betaf y u := by
      have h53 := abs_lqs_le_53 hq (x / (u * u : ℕ))
      unfold betaf
      split_ifs with h
      · rw [mul_min_of_nonneg _ _ (by linarith)]
        refine le_min (by nlinarith) ?_
        have hlog : Real.log (x / (u * u : ℕ) / q) = y - 2 * Real.log u := by
          rw [hydef, div_div, mul_comm ((u * u : ℕ) : ℝ), ← div_div,
            Real.log_div (by positivity) hpos.ne']
          push_cast; rw [Real.log_mul (by positivity) (by positivity)]; ring
        have hgt : (q : ℝ) < x / (u * u : ℕ) := by
          have : 0 < Real.log (x / (u * u : ℕ) / q) := by rw [hlog]; linarith
          have := (Real.log_pos_iff (by positivity)).1 this
          rwa [one_lt_div hq0] at this
        have hb := abs_lqs_mul_log_le hq hgt
        rw [hlog] at hb
        rw [mul_div_assoc', le_div_iff₀ (by linarith)]
        linarith
      · nlinarith
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hχ0, abs_of_pos hpos]
    calc |(μ u : ℝ)| * chiq q u / (u * u : ℕ) * |lqs q (x / (u * u : ℕ))|
        ≤ |(μ u : ℝ)| * 1 / (u * u : ℕ) * (Q * betaf y u) := by gcongr
      _ = Q * (|(μ u : ℝ)| / (u * u : ℕ) * betaf y u) := by ring
  have hyS : y * ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u ≤ 2.8 := by
    rcases lt_or_ge y 80 with h | h
    · exact yS_grid hy28.le h N
    · exact yS_large h N
  calc |mqs q x| * y ≤ Q * (∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u) * y :=
        mul_le_mul_of_nonneg_right hS hy.le
    _ = Q * (y * ∑ u ∈ Icc 1 N, |(μ u : ℝ)| / (u * u : ℕ) * betaf y u) := by ring
    _ ≤ Q * 2.8 := mul_le_mul_of_nonneg_left hyS (by linarith)
    _ = 2.8 * Q := by ring

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **[H, (2.22)] with constant `2.8`** (for [H]'s `4/5`, from [Ramb]), in the summatory form. -/
theorem abs_sum_moebius_div_coprime_le_log {x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqx : (q : ℝ) < x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤
      2.8 * (q / Nat.totient q) / Real.log (x / q) := by
  rw [← mqs_eq_sum]; exact abs_mqs_le hq hqx

end TernaryGoldbach.Prelim
