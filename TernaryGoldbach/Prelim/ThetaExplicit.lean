import TernaryGoldbach.Explicit.PsiAsymp
import TernaryGoldbach.Prelim.PsiTwoSided

/-!
# An explicit prime number theorem for `θ`

`|θ(n) − n| < n/log³n + ε_pl(n)·n` for `n ≥ 10¹²`, where `ε_pl(n) = 1.83·10⁻⁹` if
`780 < log n < 20000` and `0` otherwise.

Inputs: for `n ≤ 10¹⁷`, `|ψ(n) − n| ≤ c(n) √n` (`psi_two_sided`: a kernel-checked table below `10⁶`,
the Weil-window explicit formula above) and `ψ(n) − θ(n) ≤ √n (1.036 + 0.049 log n)`
(`psi_sub_theta_le_cB`), whose sum is `< n/log³n` for `n ≥ 10¹²` (`theta_mid`); above `10¹⁷`, the
explicit formula with the zero-free region (`Explicit/Psi*`).
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim

open TernaryGoldbach.Explicit (psiR psi_plateau psi_range1 psi_asymp)
open TernaryGoldbach.Helfgott (psi theta psi_sub_theta_le_sum sum_pow_le_theta)

/-- The plateau. -/
noncomputable def epl (x : ℝ) : ℝ := if 780 < Real.log x ∧ Real.log x < 20000 then 1.83e-9 else 0

theorem epl_nonneg (x : ℝ) : 0 ≤ epl x := by unfold epl; split_ifs <;> norm_num

theorem epl_le (x : ℝ) : epl x ≤ 1.83e-9 := by unfold epl; split_ifs <;> norm_num

theorem theta_eq (n : ℕ) : theta n = ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p := by
  rw [theta, sum_filter, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [Nat.not_prime_zero, if_false, zero_add]
  rw [show Icc 1 n = Ico 1 (n + 1) from rfl]
  refine sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · exact ArithmeticFunction.vonMangoldt_apply_prime hp
  · rfl

theorem psiR_nat (n : ℕ) : psiR n = psi n := by unfold psiR; rw [Nat.floor_natCast]

/-- `ψ(N) − θ(N) ≤ 2.001 log N · √N`. -/
theorem psi_sub_theta_le' {N : ℕ} (hN : 2 ≤ N) : psi N - theta N ≤ 2.001 * Real.log N * √(N : ℝ) := by
  classical
  have h1 := psi_sub_theta_le_sum N
  have h2 : ∀ k ∈ Finset.Icc 2 (Nat.log 2 N), (∑ m ∈ range (N + 1),
      if m.Prime ∧ m ^ k ≤ N then Real.log m else 0) ≤ (Nat.sqrt N : ℝ) * Real.log 4 := by
    intro k hk
    refine sum_pow_le_theta (Nat.sqrt_le_self N) fun m hm hmk => ?_
    rw [Nat.le_sqrt]
    have hk2 : 2 ≤ k := (Finset.mem_Icc.1 hk).1
    calc m * m = m ^ 2 := by ring
      _ ≤ m ^ k := Nat.pow_le_pow_right hm.pos hk2
      _ ≤ N := hmk
  have h3 := sum_le_sum h2
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at h3
  have hs : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hl4 : Real.log 4 ≤ 1.3863 := by
    have := Real.log_two_lt_d9
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hk : ((Nat.log 2 N + 1 - 2 : ℕ) : ℝ) ≤ Real.log N / Real.log 2 := by
    have hkN : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
    have : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) (by exact_mod_cast hkN)
    have h2' := Real.log_pos (by norm_num : (1:ℝ) < 2)
    rw [le_div_iff₀ h2']
    have h3 : ((Nat.log 2 N + 1 - 2 : ℕ) : ℝ) ≤ Nat.log 2 N := by
      exact_mod_cast (by omega : Nat.log 2 N + 1 - 2 ≤ Nat.log 2 N)
    have := mul_le_mul_of_nonneg_right h3 h2'.le
    linarith
  have hl2 := Real.log_two_gt_d9
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h4 : ((Nat.log 2 N + 1 - 2 : ℕ) : ℝ) * ((Nat.sqrt N : ℝ) * Real.log 4) ≤
      Real.log N / Real.log 2 * (√(N : ℝ) * 1.3863) := by
    gcongr
  have h5 : Real.log N / Real.log 2 * (√(N : ℝ) * 1.3863) ≤ 2.001 * Real.log N * √(N : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have hp := mul_nonneg hlN (Real.sqrt_nonneg (N : ℝ))
    have h6 := mul_le_mul_of_nonneg_left (show (1.3863 : ℝ) ≤ 2.001 * Real.log 2 by linarith) hp
    have e1 : Real.log N * (√(N : ℝ) * 1.3863) = Real.log N * √(N : ℝ) * 1.3863 := by ring
    have e2 : 2.001 * Real.log N * √(N : ℝ) * Real.log 2 = Real.log N * √(N : ℝ) * (2.001 * Real.log 2) := by ring
    rw [e1, e2]; linarith
  linarith

/-- `L^k e^{−cL}` is decreasing for `L ≥ k/c`. -/
theorem pow_exp_anti {k : ℕ} {c L0 L : ℝ} (hc : 0 < c) (h0 : (k : ℝ) / c ≤ L0) (hL0 : 0 < L0) (h : L0 ≤ L) :
    L ^ k * Real.exp (-(c * L)) ≤ L0 ^ k * Real.exp (-(c * L0)) := by
  set u := L / L0 - 1 with hu
  have hu0 : 0 ≤ u := by rw [hu, sub_nonneg, le_div_iff₀ hL0]; linarith
  have hLu : L = L0 * (1 + u) := by rw [hu]; field_simp; ring
  have h1 : (1 + u) ^ k ≤ Real.exp (k * u) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) k
  have h2 : (k : ℝ) * u ≤ c * (L - L0) := by
    have : L - L0 = L0 * u := by rw [hLu]; ring
    rw [this]
    have : (k : ℝ) ≤ c * L0 := by rwa [div_le_iff₀ hc, mul_comm] at h0
    nlinarith
  rw [hLu, mul_pow]
  have e : Real.exp (-(c * (L0 * (1 + u)))) = Real.exp (-(c * L0)) * Real.exp (-(c * (L0 * u))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have h3 : (1 + u) ^ k * Real.exp (-(c * (L0 * u))) ≤ 1 := by
    have : Real.exp (k * u) * Real.exp (-(c * (L0 * u))) ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]
      have : L - L0 = L0 * u := by rw [hLu]; ring
      nlinarith
    have hp : 0 ≤ Real.exp (-(c * (L0 * u))) := (Real.exp_pos _).le
    nlinarith
  have hA : 0 ≤ L0 ^ k * Real.exp (-(c * L0)) := by positivity
  calc L0 ^ k * (1 + u) ^ k * (Real.exp (-(c * L0)) * Real.exp (-(c * (L0 * u))))
      = (L0 ^ k * Real.exp (-(c * L0))) * ((1 + u) ^ k * Real.exp (-(c * (L0 * u)))) := by ring
    _ ≤ (L0 ^ k * Real.exp (-(c * L0))) * 1 := mul_le_mul_of_nonneg_left h3 hA
    _ = _ := mul_one _

theorem sqrt_eq_exp_half {x : ℝ} (hx : 0 < x) : √x = Real.exp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]; congr 1; ring

theorem theta_le_psi' (N : ℕ) : theta N ≤ psi N := by
  rw [theta, psi]
  refine sum_le_sum fun n _ => ?_
  split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]

theorem psi_eq_Icc (n : ℕ) : psi n = ∑ m ∈ Icc 1 n, (Λ m : ℝ) := by
  rw [psi, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
  simp [Finset.Ico_add_one_right_eq_Icc]

open Classical in
/-- The prime-power terms with exponent `k` are at most `θ(M)` if every prime `m` with `mᵏ ≤ N` has
`m ≤ M`. -/
theorem sum_pow_le_theta' {N k M : ℕ} (hMN : M ≤ N) (hM : ∀ m, m.Prime → m ^ k ≤ N → m ≤ M) :
    (∑ m ∈ range (N + 1), if m.Prime ∧ m ^ k ≤ N then Real.log m else 0) ≤ theta M := by
  have hfilt : (range (N + 1)).filter (· ≤ M) = range (M + 1) := by
    ext m; simp only [mem_filter, mem_range]; omega
  rw [theta, ← hfilt, sum_filter]
  refine sum_le_sum fun m _ => ?_
  by_cases hp : m.Prime
  · by_cases hk : m ^ k ≤ N
    · simp [hp, hk, hM m hp hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp only [hp, hk, and_false, ite_false, true_and]
      split_ifs <;> simp [ArithmeticFunction.vonMangoldt_apply_prime hp,
        Real.log_nonneg, hp.one_lt.le]
  · simp [hp]

variable [Fact TernaryGoldbach.RHUpTo] in
/-- `θ(M) ≤ M + c(M) √M` for `12 ≤ M ≤ 10¹⁷` (`psi_two_sided`). -/
theorem theta_le_cB {M : ℕ} (h1 : 12 ≤ M) (h2 : M ≤ 10 ^ 17) :
    theta M ≤ M + cB M * √(M : ℝ) := by
  have hb := (abs_le.1 (psi_two_sided h1 h2)).2
  rw [← psi_eq_Icc] at hb
  have := theta_le_psi' M
  linarith

/-- `c(m) √m ≤ 0.0355 m` for `1020 ≤ m ≤ 3.2·10¹⁰`. -/
theorem cB_sqrt_le {m : ℕ} (h1 : 1020 ≤ m) (h2 : m ≤ 32000000000) : cB m * √(m : ℝ) ≤ 0.0355 * m := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hss : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm0
  rcases lt_or_ge m 1000000 with h | h
  · rw [cB_small h, one_mul]
    have : (31.9 : ℝ) ≤ √(m : ℝ) := Real.le_sqrt_of_sq_le (by
      have : (1020 : ℝ) ≤ m := by exact_mod_cast h1
      linarith)
    nlinarith
  · have hc := cB_le_355 h2
    have : (1000 : ℝ) ≤ √(m : ℝ) := Real.le_sqrt_of_sq_le (by
      have : (1000000 : ℝ) ≤ m := by exact_mod_cast h
      linarith)
    have h1 := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (m : ℝ))
    nlinarith

open Classical in
variable [Fact TernaryGoldbach.RHUpTo] in
/-- **`ψ(N) − θ(N) ≤ √N (1.036 + 0.049 log N)` for `10⁹ ≤ N ≤ 10¹⁹`**: the squares contribute
`θ(⌊√N⌋)`, and every prime `m` with `m³ ≤ N` has `961 m² ≤ N`, so `m ≤ ⌊√N⌋/31`; both `θ`s are bounded
by `psi_two_sided` (`θ(m) ≤ 1.0355 m`, `cB_sqrt_le`). -/
theorem psi_sub_theta_le_cB {N : ℕ} (h1 : 10 ^ 9 ≤ N) (h2 : N ≤ 10 ^ 19) :
    psi N - theta N ≤ √(N : ℝ) * (1.036 + 0.049 * Real.log N) := by
  have hsum := psi_sub_theta_le_sum N
  set s := Nat.sqrt N with hs
  set M := s / 31 with hM
  set K := Nat.log 2 N with hK
  have hsN : s ≤ N := Nat.sqrt_le_self N
  have hs1 : 31622 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hM1 : 1020 ≤ M := by rw [hM]; omega
  have hMs : M ≤ s := Nat.div_le_self s 31
  have hK2 : 2 ≤ K := by
    rw [hK]; exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hK2, Finset.sum_insert (by simp)] at hsum
  -- the squares
  have hS2 : (∑ m ∈ range (N + 1), if m.Prime ∧ m ^ 2 ≤ N then Real.log m else 0) ≤ theta s :=
    sum_pow_le_theta' hsN fun m _ hm2 => by rw [hs, Nat.le_sqrt]; nlinarith
  -- the higher powers
  have hS3 : ∀ k ∈ Icc (2 + 1) K,
      (∑ m ∈ range (N + 1), if m.Prime ∧ m ^ k ≤ N then Real.log m else 0) ≤ theta M := by
    intro k hk
    have hk3 : 3 ≤ k := (mem_Icc.1 hk).1
    refine sum_pow_le_theta' (hMs.trans hsN) fun m hmp hmk => ?_
    have hm3 : m ^ 3 ≤ N := le_trans (Nat.pow_le_pow_right hmp.pos hk3) hmk
    have h961 : 961 * m ^ 2 ≤ N := by
      rcases le_or_gt 961 m with hm | hm
      · calc 961 * m ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_right _ hm
          _ = m ^ 3 := by ring
          _ ≤ N := hm3
      · have : m ^ 2 ≤ 960 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
    rw [hM, Nat.le_div_iff_mul_le (by norm_num), hs, Nat.le_sqrt]
    nlinarith
  have hS3' := sum_le_sum hS3
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at hS3'
  -- `psi_two_sided` at `s` and `M`
  have hs32 : s ≤ 32000000000 := by
    by_contra hc
    have := Nat.sqrt_le' N
    rw [← hs] at this
    nlinarith
  have hs17 : s ≤ 10 ^ 17 := by omega
  have hθs := theta_le_cB (M := s) (by omega) hs17
  have hθM := theta_le_cB (M := M) (by omega) (by omega)
  have hθM0 : 0 ≤ theta M := by
    rw [theta]; exact sum_nonneg fun n _ => by
      split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  set sN := √(N : ℝ) with hsNdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hssN : (s : ℝ) ≤ sN := Real.nat_sqrt_le_real_sqrt
  have hMr : (M : ℝ) ≤ sN / 31 := by
    have : (M : ℝ) ≤ (s : ℝ) / 31 := by rw [hM]; exact_mod_cast Nat.cast_div_le
    linarith
  have hs177 : (177 : ℝ) ≤ √(s : ℝ) :=
    Real.le_sqrt_of_sq_le (by have : (31622 : ℝ) ≤ s := by exact_mod_cast hs1
                              linarith)
  have hM319 : (31.9 : ℝ) ≤ √(M : ℝ) :=
    Real.le_sqrt_of_sq_le (by have : (1020 : ℝ) ≤ M := by exact_mod_cast hM1
                              linarith)
  have hsq_s : √(s : ℝ) * √(s : ℝ) = s := Real.mul_self_sqrt (Nat.cast_nonneg s)
  have hsq_M : √(M : ℝ) * √(M : ℝ) = M := Real.mul_self_sqrt (Nat.cast_nonneg M)
  have hbs := cB_sqrt_le (m := s) (by omega) hs32
  have hbM := cB_sqrt_le (m := M) (by omega) (by omega)
  -- the number of exponents
  have hKr : ((K + 1 - (2 + 1) : ℕ) : ℝ) ≤ K := by exact_mod_cast (by omega : K + 1 - (2 + 1) ≤ K)
  have hKL : (K : ℝ) * 0.6931 ≤ Real.log N := by
    have hkN : 2 ^ K ≤ N := Nat.pow_log_le_self 2 (by omega)
    have h1 : (K : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) (by exact_mod_cast hkN)
    have := Real.log_two_gt_d9
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hsN0 : 0 ≤ sN := Real.sqrt_nonneg _
  -- assemble: `ψ − θ ≤ 1.0355 √N + K · 1.0355 √N/31`
  have hA : theta s ≤ 1.0355 * sN := by nlinarith
  have hB : ((K + 1 - (2 + 1) : ℕ) : ℝ) * theta M ≤ K * (1.0355 * (sN / 31)) := by
    have h1 : theta M ≤ 1.0355 * (sN / 31) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right hKr hθM0
    have h3 := mul_le_mul_of_nonneg_left h1 hK0
    linarith
  have hC : K * (1.0355 * (sN / 31)) ≤ 0.049 * (Real.log N * sN) := by
    have := mul_le_mul_of_nonneg_left hKL hsN0
    nlinarith
  have e : sN * (1.036 + 0.049 * Real.log N) = 1.036 * sN + 0.049 * (Real.log N * sN) := by ring
  rw [e]
  linarith

/-- `L³/√x ≤ L₀³ e^{−L₀/2}` for `log x ≥ L₀ ≥ 6`. -/
theorem cube_div_sqrt_le {x L0 : ℝ} (hx : 0 < x) (h6 : 6 ≤ L0) (hL : L0 ≤ Real.log x) :
    Real.log x ^ 3 * (√x)⁻¹ ≤ L0 ^ 3 * Real.exp (-(1 / 2 * L0)) := by
  have h := pow_exp_anti (k := 3) (c := 1 / 2) (L0 := L0) (L := Real.log x) (by norm_num)
    (by push_cast; linarith) (by linarith) hL
  rw [sqrt_eq_exp_half hx, ← Real.exp_neg]
  convert h using 3; ring

theorem quart_div_sqrt_le {x L0 : ℝ} (hx : 0 < x) (h8 : 8 ≤ L0) (hL : L0 ≤ Real.log x) :
    Real.log x ^ 4 * (√x)⁻¹ ≤ L0 ^ 4 * Real.exp (-(1 / 2 * L0)) := by
  have h := pow_exp_anti (k := 4) (c := 1 / 2) (L0 := L0) (L := Real.log x) (by norm_num)
    (by push_cast; linarith) (by linarith) hL
  rw [sqrt_eq_exp_half hx, ← Real.exp_neg]
  convert h using 3; ring

/-- `e^{−L₀/2} = 1/√x₀` for `L₀ = log x₀`. -/
theorem exp_neg_half_log {x0 : ℝ} (hx0 : 0 < x0) : Real.exp (-(1 / 2 * Real.log x0)) = (√x0)⁻¹ := by
  rw [sqrt_eq_exp_half hx0, ← Real.exp_neg]; congr 1; ring

theorem log_1e10_le : Real.log 1e10 ≤ 23.03 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 23 (u := 0.03) (by norm_num) 4
  have e : ((23 : ℕ) : ℝ) + 0.03 = 23.03 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_2e8_le : Real.log 2e8 ≤ 19.12 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 19 (u := 0.12) (by norm_num) 5
  have e : ((19 : ℕ) : ℝ) + 0.12 = 19.12 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_1e9_le : Real.log 1e9 ≤ 20.73 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 20 (u := 0.73) (by norm_num) 8
  have e : ((20 : ℕ) : ℝ) + 0.73 = 20.73 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_1e17_le : Real.log 1e17 ≤ 39.15 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 39 (u := 0.15) (by norm_num) 8
  have e : ((39 : ℕ) : ℝ) + 0.15 = 39.15 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_1e19_le : Real.log 1e19 ≤ 43.75 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 43 (u := 0.75) (by norm_num) 8
  have e : ((43 : ℕ) : ℝ) + 0.75 = 43.75 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_ge_of_le {x c : ℝ} (hx : 0 < x) (h : Real.exp c ≤ x) : c ≤ Real.log x :=
  (Real.le_log_iff_exp_le hx).2 h

theorem log_1e12_le : Real.log 1e12 ≤ 27.632 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 27 (u := 0.632) (by norm_num) 8
  have e : ((27 : ℕ) : ℝ) + 0.632 = 27.632 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_32e11_le : Real.log 3.2e12 ≤ 28.795 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 28 (u := 0.795) (by norm_num) 8
  have e : ((28 : ℕ) : ℝ) + 0.795 = 28.795 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_1e13_le : Real.log 1e13 ≤ 29.934 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 29 (u := 0.934) (by norm_num) 8
  have e : ((29 : ℕ) : ℝ) + 0.934 = 29.934 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `√x (c + 0.049 log x) < x/log³x` for `x ≥ x₀`, from `log³x₀/√x₀ ≤ A`, `log⁴x₀/√x₀ ≤ B`,
`cA + 0.049 B < 1`. -/
theorem sqrt_mul_lt_div_cube {x x0 c A B : ℝ} (hx0 : 0 < x0) (h8 : 8 ≤ Real.log x0) (hx : x0 ≤ x)
    (hA : Real.log x0 ^ 3 * (√x0)⁻¹ ≤ A) (hB : Real.log x0 ^ 4 * (√x0)⁻¹ ≤ B) (hc : 0 ≤ c)
    (hcAB : c * A + 0.049 * B < 1) : √x * (c + 0.049 * Real.log x) < x / Real.log x ^ 3 := by
  have hxp : 0 < x := lt_of_lt_of_le hx0 hx
  have hL0 : Real.log x0 ≤ Real.log x := Real.log_le_log hx0 hx
  have hlx : 0 < Real.log x := by linarith
  have hL3 : 0 < Real.log x ^ 3 := by positivity
  have hs0 : 0 < √x := Real.sqrt_pos.2 hxp
  have hss : √x * √x = x := Real.mul_self_sqrt hxp.le
  have hc0 := cube_div_sqrt_le hxp (by linarith) hL0
  have hq0 := quart_div_sqrt_le hxp h8 hL0
  rw [exp_neg_half_log hx0] at hc0 hq0
  have hc' := hc0.trans hA
  have hq' := hq0.trans hB
  have hL3' : Real.log x ^ 3 ≤ A * √x := by
    have := mul_le_mul_of_nonneg_right hc' hs0.le
    rwa [mul_assoc, inv_mul_cancel₀ hs0.ne', mul_one] at this
  have hL4' : Real.log x ^ 4 ≤ B * √x := by
    have := mul_le_mul_of_nonneg_right hq' hs0.le
    rwa [mul_assoc, inv_mul_cancel₀ hs0.ne', mul_one] at this
  rw [lt_div_iff₀ hL3]
  have e : √x * (c + 0.049 * Real.log x) * Real.log x ^ 3 =
      c * (√x * Real.log x ^ 3) + 0.049 * (√x * Real.log x ^ 4) := by ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL3' hs0.le) hc
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL4' hs0.le) (by norm_num : (0 : ℝ) ≤ 0.049)
  have e1 : c * (√x * (A * √x)) = c * A * x := by
    rw [show √x * (A * √x) = A * (√x * √x) by ring, hss]; ring
  have e2 : 0.049 * (√x * (B * √x)) = 0.049 * B * x := by
    rw [show √x * (B * √x) = B * (√x * √x) by ring, hss]; ring
  rw [e1] at h1; rw [e2] at h2
  nlinarith

variable [Fact TernaryGoldbach.RHUpTo] in
/-- **`|θ(n) − n| < n/log³n` on `[10¹², 10¹⁷]`**, from `psi_two_sided` and `psi_sub_theta_le_cB`. -/
theorem theta_mid {n : ℕ} (hn : 10 ^ 12 ≤ n) (h2 : n ≤ 10 ^ 17) :
    |∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p - n| < n / Real.log n ^ 3 := by
  have hB := psi_two_sided (n := n) (by omega) h2
  rw [← psi_eq_Icc] at hB
  have hD := psi_sub_theta_le_cB (N := n) (by omega) (h2.trans (by norm_num))
  have hθψ := theta_le_psi' n
  rw [← theta_eq n]
  set x : ℝ := (n : ℝ) with hx
  have hx12 : (1e12 : ℝ) ≤ x := by
    have : ((10 ^ 12 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    rw [hx]; norm_num at this ⊢; linarith
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg _
  obtain ⟨c, hc, hkey⟩ : ∃ c : ℝ, cB n ≤ c ∧ √x * (c + 1.036 + 0.049 * Real.log x) < x / Real.log x ^ 3 := by
    rcases le_or_gt n 3200000000000 with h3 | h3
    · refine ⟨42.82, cB_le_4282 (by omega) h3, ?_⟩
      have hl := log_1e12_le
      have h8 : 8 ≤ Real.log (1e12 : ℝ) := log_ge_of_le (by norm_num) (by
        have h := Real.exp_one_lt_d9
        have : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        calc Real.exp 1 ^ 8 ≤ 2.7182818286 ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 8
          _ ≤ 1e12 := by norm_num)
      have hs : √(1e12 : ℝ) = 1e6 := by
        rw [show (1e12 : ℝ) = 1e6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have h0 : 0 ≤ Real.log (1e12 : ℝ) := by linarith
      have := sqrt_mul_lt_div_cube (c := 42.82 + 1.036) (A := 0.021099) (B := 0.583) (by norm_num) h8 hx12
        (by rw [hs]; have := pow_le_pow_left₀ h0 hl 3; norm_num at this ⊢; nlinarith)
        (by rw [hs]; have := pow_le_pow_left₀ h0 hl 4; norm_num at this ⊢; nlinarith)
        (by norm_num) (by norm_num)
      exact this
    rcases le_or_gt n 10000000000000 with h4 | h4
    · refine ⟨45.08, cB_le_4508 (by omega) h4, ?_⟩
      have hx32 : (3.2e12 : ℝ) ≤ x := by
        have : ((3200000000000 : ℕ) : ℝ) ≤ n := by exact_mod_cast h3.le
        rw [hx]; norm_num at this ⊢; linarith
      have hl := log_32e11_le
      have h8 : 8 ≤ Real.log (3.2e12 : ℝ) := le_trans (by
        have h := Real.exp_one_lt_d9
        exact log_ge_of_le (by norm_num) (by
          have : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
          rw [this]
          calc Real.exp 1 ^ 8 ≤ 2.7182818286 ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 8
            _ ≤ 3.2e12 := by norm_num)) le_rfl
      have hs : (1788854 : ℝ) ≤ √(3.2e12 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
      have hsi : (√(3.2e12 : ℝ))⁻¹ ≤ 1 / 1788854 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hs
      have h0 : 0 ≤ Real.log (3.2e12 : ℝ) := by linarith
      have := sqrt_mul_lt_div_cube (c := 45.08 + 1.036) (A := 0.01335) (B := 0.3844) (by norm_num) h8 hx32
        (by have := pow_le_pow_left₀ h0 hl 3
            calc Real.log 3.2e12 ^ 3 * (√(3.2e12 : ℝ))⁻¹ ≤ 28.795 ^ 3 * (1 / 1788854) :=
                  mul_le_mul this hsi (by positivity) (by norm_num)
              _ ≤ 0.01335 := by norm_num)
        (by have := pow_le_pow_left₀ h0 hl 4
            calc Real.log 3.2e12 ^ 4 * (√(3.2e12 : ℝ))⁻¹ ≤ 28.795 ^ 4 * (1 / 1788854) :=
                  mul_le_mul this hsi (by positivity) (by norm_num)
              _ ≤ 0.3844 := by norm_num)
        (by norm_num) (by norm_num)
      exact this
    · refine ⟨72, cB_le_72 n, ?_⟩
      have hx13 : (1e13 : ℝ) ≤ x := by
        have : ((10000000000000 : ℕ) : ℝ) ≤ n := by exact_mod_cast h4.le
        rw [hx]; norm_num at this ⊢; linarith
      have hl := log_1e13_le
      have h8 : 8 ≤ Real.log (1e13 : ℝ) := log_ge_of_le (by norm_num) (by
        have h := Real.exp_one_lt_d9
        have : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        calc Real.exp 1 ^ 8 ≤ 2.7182818286 ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 8
          _ ≤ 1e13 := by norm_num)
      have hs : (3162277 : ℝ) ≤ √(1e13 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
      have hsi : (√(1e13 : ℝ))⁻¹ ≤ 1 / 3162277 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hs
      have h0 : 0 ≤ Real.log (1e13 : ℝ) := by linarith
      have := sqrt_mul_lt_div_cube (c := 72 + 1.036) (A := 0.008483) (B := 0.254) (by norm_num) h8 hx13
        (by have := pow_le_pow_left₀ h0 hl 3
            calc Real.log 1e13 ^ 3 * (√(1e13 : ℝ))⁻¹ ≤ 29.934 ^ 3 * (1 / 3162277) :=
                  mul_le_mul this hsi (by positivity) (by norm_num)
              _ ≤ 0.008483 := by norm_num)
        (by have := pow_le_pow_left₀ h0 hl 4
            calc Real.log 1e13 ^ 4 * (√(1e13 : ℝ))⁻¹ ≤ 29.934 ^ 4 * (1 / 3162277) :=
                  mul_le_mul this hsi (by positivity) (by norm_num)
              _ ≤ 0.254 := by norm_num)
        (by norm_num) (by norm_num)
      exact this
  have hcs := mul_le_mul_of_nonneg_right hc hs0
  have e : √x * (c + 1.036 + 0.049 * Real.log x) = c * √x + √x * (1.036 + 0.049 * Real.log x) := by ring
  rw [e] at hkey
  have hp : 0 ≤ √x * (1.036 + 0.049 * Real.log x) := by
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    positivity
  rw [abs_lt]
  constructor
  · have := (abs_le.1 hB).1; linarith
  · have := (abs_le.1 hB).2; linarith

set_option maxHeartbeats 1000000 in
variable [Fact TernaryGoldbach.RHUpTo] in
/-- **Explicit PNT for `θ`**: `|θ(n) − n| < n/log³n + ε_pl(n) n` for `n ≥ 10¹²`. -/
theorem theta_explicit {n : ℕ} (hn : 1000000000000 ≤ n) :
    |∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p - n| < n / Real.log n ^ 3 + epl n * n := by
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = n := ⟨_, rfl⟩
  rw [← hxdef]
  have hx0 : 0 < x := by rw [hxdef]; exact_mod_cast (by omega : 0 < n)
  have hepl : 0 ≤ epl x * x := mul_nonneg (epl_nonneg x) hx0.le
  have hlx : 0 < Real.log x := Real.log_pos (by rw [hxdef]; exact_mod_cast (by omega : 1 < n))
  have hL3 : 0 < Real.log x ^ 3 := by positivity
  set θ := ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p with hθ
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hsinv : x * (√x)⁻¹ = √x := by
    calc x * (√x)⁻¹ = √x * √x * (√x)⁻¹ := by rw [hss]
      _ = √x := by field_simp
  rcases le_or_gt n (10 ^ 17) with h2 | h2
  · have h := theta_mid (n := n) (by omega) h2
    rw [← hxdef] at h
    exact lt_of_lt_of_le h (by linarith)
  -- above `10¹⁷`
  have hx19 : (1e17 : ℝ) < x := by
    rw [hxdef]
    have : ((10 ^ 17 : ℕ) : ℝ) < n := by exact_mod_cast h2
    norm_num at this ⊢; linarith
  have hψ : psiR x = psi n := by rw [hxdef]; exact psiR_nat n
  have hθt : θ = theta n := (theta_eq n).symm
  have hdiff := psi_sub_theta_le' (N := n) (by omega)
  have hθψ := theta_le_psi' n
  rw [← hxdef] at hdiff
  set L := Real.log x with hLdef
  have hL19 : Real.log 1e17 ≤ L := Real.log_le_log (by norm_num) hx19.le
  have h19 := log_1e17_le
  have hl19ge : (39.1 : ℝ) ≤ Real.log 1e17 := log_ge_of_le (by norm_num) (by
      have h1 := Real.exp_one_lt_d9
      have h2 := Real.exp_bound' (x := 0.1) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h2
      have e : Real.exp 39.1 = Real.exp 1 ^ 39 * Real.exp 0.1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      have h3 : Real.exp 1 ^ 39 ≤ 2.7182818286 ^ 39 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 39
      nlinarith [Real.exp_pos 0.1, pow_pos (Real.exp_pos 1) 39])
  have hL43 : 39.1 ≤ L := by linarith
  have hsx : √x = Real.exp (L / 2) := sqrt_eq_exp_half hx0
  -- `|θ − x| ≤ |ψ − x| + 2.001 L √x`
  have htri : |θ - x| ≤ |psiR x - x| + 2.001 * L * √x := by
    rw [hθt]
    have : |theta n - x| ≤ |psi n - x| + (psi n - theta n) := by
      rw [abs_le]; constructor <;> cases abs_cases (psi n - x) <;> linarith
    rw [hψ]; linarith
  have hsL3 : √x * L ^ 3 = x * (L ^ 3 * (√x)⁻¹) := by
    rw [← hsinv]; field_simp; exact (Real.sq_sqrt hx0.le).symm
  have hsL4 : √x * L ^ 4 = x * (L ^ 4 * (√x)⁻¹) := by
    rw [← hsinv]; field_simp; exact (Real.sq_sqrt hx0.le).symm
  have hinv : (√x)⁻¹ = Real.exp (-(1 / 2 * L)) := by
    rw [hsx, ← Real.exp_neg]; congr 1; ring
  rcases le_or_gt L 780 with h3 | h3
  · -- the explicit formula up to `e^{780}`: below `x/L³`
    have hP := psi_plateau hx19.le
    have hA : |θ - x| ≤ 1.82e-9 * x + 1600 * √x + 4.2e10 + 2.001 * L * √x := by linarith
    have hbig : (1.82e-9 * x + 1600 * √x + 4.2e10 + 2.001 * L * √x) * L ^ 3 < x := by
      have e : (1.82e-9 * x + 1600 * √x + 4.2e10 + 2.001 * L * √x) * L ^ 3 =
          1.82e-9 * x * L ^ 3 + 1600 * (√x * L ^ 3) + 4.2e10 * L ^ 3 + 2.001 * (√x * L ^ 4) := by ring
      rw [e, hsL3, hsL4]
      rcases le_or_gt L 100 with h4 | h4
      · have hc := cube_div_sqrt_le hx0 (by linarith) hL19
        have hq := quart_div_sqrt_le hx0 (by linarith) hL19
        rw [exp_neg_half_log (by norm_num)] at hc hq
        have hs19 : (3.16e8 : ℝ) ≤ √(1e17 : ℝ) := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        have hinv19 : (√(1e17 : ℝ))⁻¹ ≤ 3.1646e-9 := by
          have : (√(1e17 : ℝ))⁻¹ ≤ (3.16e8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs19
          exact this.trans (by norm_num)
        have hl0 : 0 ≤ Real.log 1e17 := by linarith
        have hc' : L ^ 3 * (√x)⁻¹ ≤ 1.9e-4 := by
          refine hc.trans ?_
          have : Real.log 1e17 ^ 3 ≤ 39.15 ^ 3 := pow_le_pow_left₀ hl0 h19 3
          have := mul_le_mul this hinv19 (by positivity) (by norm_num)
          norm_num at this ⊢; linarith
        have hq' : L ^ 4 * (√x)⁻¹ ≤ 7.44e-3 := by
          refine hq.trans ?_
          have : Real.log 1e17 ^ 4 ≤ 39.15 ^ 4 := pow_le_pow_left₀ hl0 h19 4
          have := mul_le_mul this hinv19 (by positivity) (by norm_num)
          norm_num at this ⊢; linarith
        have hL3b : L ^ 3 ≤ 1e6 := by
          have := pow_le_pow_left₀ (by linarith) h4 3; norm_num at this ⊢; linarith
        have h5 := mul_le_mul_of_nonneg_left hc' hx0.le
        have h6 := mul_le_mul_of_nonneg_left hq' hx0.le
        have h7 : 1.82e-9 * x * L ^ 3 ≤ 1.82e-3 * x := by nlinarith
        have h8 : 4.2e10 * L ^ 3 ≤ 0.42 * x := by nlinarith
        linarith
      · have h100 : (100 : ℝ) ≤ L := h4.le
        have hc := pow_exp_anti (k := 3) (c := 1 / 2) (L0 := 100) (L := L) (by norm_num) (by norm_num)
          (by norm_num) h100
        have hq := pow_exp_anti (k := 4) (c := 1 / 2) (L0 := 100) (L := L) (by norm_num) (by norm_num)
          (by norm_num) h100
        have he50 : Real.exp (-(1 / 2 * 100 : ℝ)) ≤ 2e-22 := by
          rw [show -(1 / 2 * 100 : ℝ) = -50 by norm_num, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          have := TernaryGoldbach.Explicit.exp_nat_ge' 50
          norm_num at this ⊢; linarith
        have hc' : L ^ 3 * (√x)⁻¹ ≤ 2e-16 := by
          rw [hinv]; refine hc.trans ?_; nlinarith [Real.exp_pos (-(1 / 2 * 100 : ℝ))]
        have hq' : L ^ 4 * (√x)⁻¹ ≤ 2e-14 := by
          rw [hinv]; refine hq.trans ?_; nlinarith [Real.exp_pos (-(1 / 2 * 100 : ℝ))]
        have hL3b : L ^ 3 ≤ 4.7456e8 := by
          have := pow_le_pow_left₀ (by linarith) h3 3; norm_num at this ⊢; linarith
        have hxbig : (1e30 : ℝ) ≤ x := by
          have h := TernaryGoldbach.Explicit.exp_nat_ge' 70
          have h2' : Real.exp ((70 : ℕ) : ℝ) ≤ Real.exp L := Real.exp_le_exp.2 (by push_cast; linarith)
          rw [hLdef, Real.exp_log hx0] at h2'
          have : (1e30 : ℝ) ≤ 2.7182818283 ^ 70 := by norm_num
          exact this.trans (h.trans h2')
        have h5 := mul_le_mul_of_nonneg_left hc' hx0.le
        have h6 := mul_le_mul_of_nonneg_left hq' hx0.le
        have h7 : 1.82e-9 * x * L ^ 3 ≤ 0.8638 * x := by nlinarith
        have h8 : 4.2e10 * L ^ 3 ≤ 1e-8 * x := by nlinarith
        linarith
    have : |θ - x| < x / L ^ 3 := by
      rw [lt_div_iff₀ (by positivity)]
      calc |θ - x| * L ^ 3 ≤ (1.82e-9 * x + 1600 * √x + 4.2e10 + 2.001 * L * √x) * L ^ 3 :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ < x := hbig
    linarith
  -- above `e^{780}`
  have hs30 : (1e30 : ℝ) ≤ √x := by
    rw [hsx]
    have h := TernaryGoldbach.Explicit.exp_nat_ge' 70
    have h2' : Real.exp ((70 : ℕ) : ℝ) ≤ Real.exp (L / 2) := Real.exp_le_exp.2 (by push_cast; linarith)
    have : (1e30 : ℝ) ≤ 2.7182818283 ^ 70 := by norm_num
    exact this.trans (h.trans h2')
  have hsmall : ∀ c : ℝ, 0 ≤ c → c * √x ≤ c * 1e-30 * x := by
    intro c hc
    have : c * √x * 1e30 ≤ c * √x * √x := mul_le_mul_of_nonneg_left hs30 (by positivity)
    rw [mul_assoc c √x √x, hss] at this
    nlinarith
  have hx60 : (1e60 : ℝ) ≤ x := by nlinarith
  rcases lt_or_ge L 20000 with h5 | h5
  · -- the plateau
    have hepl : epl x = 1.83e-9 := by unfold epl; rw [if_pos ⟨h3, h5⟩]
    have hP := psi_plateau hx19.le
    have h1' : 2.001 * L * √x ≤ 40020 * √x := by
      have := mul_le_mul_of_nonneg_right (show 2.001 * L ≤ 40020 by linarith) hs0.le; linarith
    have h2' := hsmall 55020 (by norm_num)
    have : |θ - x| ≤ 1.83e-9 * x := by nlinarith
    rw [hepl]
    have : 0 < x / L ^ 3 := by positivity
    linarith
  rcases lt_or_ge L 35000 with h6 | h6
  · -- `e^{20000} ≤ x < e^{35000}`
    have hxe : Real.exp 20000 ≤ x := by
      rw [show x = Real.exp L by rw [hLdef, Real.exp_log hx0]]; exact Real.exp_le_exp.2 h5
    have hR := psi_range1 hxe
    have h1' : 2.001 * L * √x ≤ 70035 * √x := by
      have := mul_le_mul_of_nonneg_right (show 2.001 * L ≤ 70035 by linarith) hs0.le; linarith
    have h2' := hsmall 70035 (by norm_num)
    have hL3' : L ^ 3 < 4.2875e13 := by
      have := pow_lt_pow_left₀ h6 (by linarith) (by norm_num : (3 : ℕ) ≠ 0); norm_num at this ⊢; linarith
    have : |θ - x| < x / L ^ 3 := by
      rw [lt_div_iff₀ (by positivity)]
      have hθ' : |θ - x| ≤ 2.11e-14 * x := by nlinarith
      calc |θ - x| * L ^ 3 ≤ 2.11e-14 * x * L ^ 3 := mul_le_mul_of_nonneg_right hθ' (by positivity)
        _ < 2.11e-14 * x * 4.2875e13 := by
            apply mul_lt_mul_of_pos_left hL3' (by positivity)
        _ ≤ x := by nlinarith
    linarith
  · -- `x ≥ e^{35000}`
    have hxe : Real.exp 35000 ≤ x := by
      rw [show x = Real.exp L by rw [hLdef, Real.exp_log hx0]]; exact Real.exp_le_exp.2 h6
    have hA := psi_asymp hxe
    have hsb := TernaryGoldbach.Explicit.sqrt_big hxe
    rw [← hLdef] at hA hsb
    have hL3pos : 0 < L ^ 3 := by positivity
    have h1' : 2.001 * L * √x ≤ 0.1 * x / L ^ 3 := by
      rw [le_div_iff₀ hL3pos]
      have : 20.01 * L ^ 4 ≤ √x := by
        have : 20.01 * L ^ 4 ≤ 1e20 * L ^ 7 := by
          have h1 : (1 : ℝ) ≤ L ^ 3 := by
            have := pow_le_pow_left₀ (by norm_num) h6 3; norm_num at this ⊢; linarith
          have : L ^ 7 = L ^ 4 * L ^ 3 := by ring
          rw [this]; nlinarith [pow_pos (by linarith : (0:ℝ) < L) 4]
        linarith
      have e : 2.001 * L * √x * L ^ 3 = 2.001 * L ^ 4 * √x := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right this hs0.le
      rw [hss] at this
      nlinarith
    have : |θ - x| < x / L ^ 3 := by
      have : |θ - x| ≤ 0.3 * x / L ^ 3 := by
        have e : 0.2 * x / L ^ 3 + 0.1 * x / L ^ 3 = 0.3 * x / L ^ 3 := by ring
        linarith
      have h2 : 0.3 * x / L ^ 3 < x / L ^ 3 := by
        apply div_lt_div_of_pos_right _ hL3pos; linarith
      linarith
    linarith

/-! ## Sums of the plateau term -/

/-- `ε_pl(n) = 0` once `log n ≥ 20000`. -/
theorem epl_eq_zero {x : ℝ} (h : 20000 ≤ Real.log x) : epl x = 0 := by
  unfold epl; rw [if_neg]; push Not; intro _; exact h

theorem epl_ne_zero {x : ℝ} (h : epl x ≠ 0) : 780 < Real.log x ∧ Real.log x < 20000 := by
  unfold epl at h; split_ifs at h with hh
  · exact hh
  · exact absurd rfl h

/-- `Σ_{a<n<b} ε_pl(n)/(n+1) ≤ 1.83·10⁻⁹ (20000.0001 − max(780, log(a+1)))`, and `= 0` if
`log(a+1) ≥ 20000`. -/
theorem sum_epl_div_le (a b : ℕ) :
    ∑ n ∈ Ioo a b, epl n / ((n : ℝ) + 1) ≤ if Real.log ((a : ℝ) + 1) < 20000 then
      1.83e-9 * (20000.0001 - max 780 (Real.log ((a : ℝ) + 1))) else 0 := by
  split_ifs with ha
  · -- telescoping over `[max(e^{780}, a+1), e^{20000}]`
    set m1 := max ⌈Real.exp 780⌉₊ (a + 1) with hm1
    set m2 := ⌊Real.exp 20000⌋₊ + 1 with hm2
    have hterm : ∀ n ∈ Ioo a b, epl n / ((n : ℝ) + 1) ≤
        if n ∈ Ico m1 m2 then 1.83e-9 * (Real.log ((n : ℝ) + 1) - Real.log n) else 0 := by
      intro n hnab
      by_cases h0 : epl (n : ℝ) = 0
      · rw [h0, zero_div]; split_ifs
        · have : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
            rcases Nat.eq_zero_or_pos n with rfl | hn
            · simp
            · exact Real.log_le_log (by exact_mod_cast hn) (by linarith)
          nlinarith
        · exact le_rfl
      obtain ⟨hl1, hl2⟩ := epl_ne_zero h0
      have hn0 : (0 : ℝ) < n := by
        by_contra hc; push Not at hc
        have : (n : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg n)
        rw [this, Real.log_zero] at hl1; linarith
      have hmem : n ∈ Ico m1 m2 := by
        rw [Finset.mem_Ico]; constructor
        · rw [hm1, max_le_iff, Nat.ceil_le]
          refine ⟨?_, (Finset.mem_Ioo.1 hnab).1⟩
          have := (Real.lt_log_iff_exp_lt hn0).1 hl1; linarith
        · rw [hm2, Nat.lt_succ_iff]
          apply Nat.le_floor
          have := (Real.log_lt_iff_lt_exp hn0).1 hl2; linarith
      rw [if_pos hmem, epl, if_pos ⟨hl1, hl2⟩]
      have h1 : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
        have := Real.one_sub_inv_le_log_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
        rw [Real.log_div (by positivity) hn0.ne'] at this
        have e : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / (n + 1) := by field_simp; ring
        linarith
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_filter]
    have hsub : (Ioo a b).filter (· ∈ Ico m1 m2) ⊆ Ico m1 m2 := fun n hn => (mem_filter.1 hn).2
    have hnn : ∀ n ∈ Ico m1 m2, 0 ≤ 1.83e-9 * (Real.log ((n : ℝ) + 1) - Real.log n) := by
      intro n hn
      have hn1 : 1 ≤ m1 := le_trans (by omega) (le_max_right _ _)
      have hn0 : (0 : ℝ) < n := by
        have := (Finset.mem_Ico.1 hn).1; exact_mod_cast (by omega : 0 < n)
      have : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
      nlinarith
    refine (sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hnn n hn).trans ?_
    rw [← mul_sum]
    have hm12 : m1 ≤ m2 := by
      rw [hm1, hm2, max_le_iff, Nat.ceil_le]
      constructor
      · have := Nat.lt_floor_add_one (Real.exp 20000)
        have : Real.exp 780 ≤ Real.exp 20000 := Real.exp_le_exp.2 (by norm_num)
        push_cast; linarith
      · have h1 : ((a : ℝ) + 1) < Real.exp 20000 := (Real.log_lt_iff_lt_exp (by positivity)).1 ha
        have : a + 1 ≤ ⌊Real.exp 20000⌋₊ := Nat.le_floor (by push_cast; linarith)
        omega
    have htel : ∑ n ∈ Ico m1 m2, (Real.log ((n : ℝ) + 1) - Real.log n) = Real.log m2 - Real.log m1 := by
      rw [Finset.sum_Ico_eq_sum_range]
      have := Finset.sum_range_sub (fun k : ℕ => Real.log ((m1 + k : ℕ) : ℝ)) (m2 - m1)
      rw [show m1 + (m2 - m1) = m2 by omega, show m1 + 0 = m1 by omega] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring_nf
    rw [htel]
    have hm1pos : (0 : ℝ) < m1 := by
      have : 1 ≤ m1 := le_trans (by omega) (le_max_right _ _)
      exact_mod_cast this
    have h1 : max 780 (Real.log ((a : ℝ) + 1)) ≤ Real.log m1 := by
      refine max_le ?_ ?_
      · rw [Real.le_log_iff_exp_le hm1pos]
        exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
      · exact Real.log_le_log (by positivity) (by exact_mod_cast le_max_right _ _)
    have h2 : Real.log m2 ≤ 20000.0001 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      rw [hm2]; push_cast
      have := Nat.floor_le (Real.exp_pos 20000).le
      have he : Real.exp 20000 + 1 ≤ Real.exp 20000.0001 := by
        rw [show (20000.0001 : ℝ) = 20000 + 0.0001 by norm_num, Real.exp_add]
        have h3 := Real.add_one_le_exp (0.0001 : ℝ)
        have h4 : (1 : ℝ) ≤ 0.0001 * Real.exp 20000 := by
          have := Real.add_one_le_exp (20000 : ℝ); nlinarith
        nlinarith [Real.exp_pos (20000 : ℝ)]
      linarith
    nlinarith
  · -- above `e^{20000}` the plateau is empty
    refine (sum_eq_zero fun n hn => ?_).le
    have hn := (Finset.mem_Ioo.1 hn).1
    push Not at ha
    have : 20000 ≤ Real.log (n : ℝ) := by
      refine ha.trans (Real.log_le_log (by positivity) ?_)
      exact_mod_cast hn
    rw [epl_eq_zero this, zero_div]

/-- `Σ_{a<n<b} ε_pl(n)/(n+1) ≤ 3.52·10⁻⁵`. -/
theorem sum_epl_div_le_const (a b : ℕ) : ∑ n ∈ Ioo a b, epl n / ((n : ℝ) + 1) ≤ 3.52e-5 := by
  refine (sum_epl_div_le a b).trans ?_
  split_ifs
  · generalize hm : max 780 (Real.log ((a : ℝ) + 1)) = m
    have : 780 ≤ m := hm ▸ le_max_left _ _
    nlinarith
  · norm_num

theorem epl_mul_log_le (x : ℝ) : epl x * Real.log x ≤ 3.66e-5 := by
  unfold epl; split_ifs with h
  · nlinarith [h.1, h.2]
  · rw [zero_mul]; norm_num

end TernaryGoldbach.Prelim
