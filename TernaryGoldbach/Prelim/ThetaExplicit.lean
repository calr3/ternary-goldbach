import TernaryGoldbach.Explicit.PsiAsymp

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# An explicit prime number theorem for `θ` (replacing Dusart's bound)

`|θ(n) − n| < n/log³n + ε_pl(n)·n` for `n ≥ 10⁹`, where `ε_pl(n) = 2.2·10⁻¹¹` if
`3400 < log n < 20000` and `0` otherwise.

Inputs: for `n ≤ 10¹⁹`, Büthe's `|ψ(n) − n| ≤ 0.94 √n` (numerical axiom `buthe_psi`) and
`ψ(n) − θ(n) ≤ √n (1.0054 + 0.048 log n)` (`psi_sub_theta_le_buthe`: Büthe at `⌊√n⌋` and `⌊√n⌋/31`), whose
sum is `< n/log³n` for `n ≥ 10⁹`; above `10¹⁹`, the explicit formula with the zero-free region
(`Explicit/Psi*`).
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim

open TernaryGoldbach.Explicit (psiR psi_plateau psi_range1 psi_asymp)
open TernaryGoldbach.Helfgott (psi theta psi_sub_theta_le_sum sum_pow_le_theta)

omit [Fact TernaryGoldbach.RHUpTo] in
/-- **Numerical hypothesis** ([Büthe 2018], *An analytic method for bounding ψ(x)*, Math. Comp. 87 (2018),
1991–2009, arXiv:1511.02032, Thm 2, (1.5)): `|x − ψ(x)| ≤ 0.94 √x` for `11 < x ≤ 10¹⁹`; we use it at
integers `12 ≤ n ≤ 10¹⁹`. (Büthe's bounds (1.6)–(1.7) for `θ` are not used: the `θ` bounds here are
derived from this one.) -/
theorem buthe_psi [h : Fact ButhePsi] (n : ℕ) (h1 : 12 ≤ n) (h2 : n ≤ 10 ^ 19) :
    |∑ m ∈ Icc 1 n, (Λ m : ℝ) - n| ≤ 0.94 * √(n : ℝ) :=
  h.out n h1 h2

variable [Fact TernaryGoldbach.ButhePsi]

/-- The plateau. -/
noncomputable def epl (x : ℝ) : ℝ := if 3400 < Real.log x ∧ Real.log x < 20000 then 2.2e-11 else 0

theorem epl_nonneg (x : ℝ) : 0 ≤ epl x := by unfold epl; split_ifs <;> norm_num

theorem epl_le (x : ℝ) : epl x ≤ 2.2e-11 := by unfold epl; split_ifs <;> norm_num

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

/-- `θ(M) ≤ M + 0.94 √M` for `12 ≤ M ≤ 10¹⁹` (Büthe's bound for `ψ`). -/
theorem theta_le_buthe {M : ℕ} (h1 : 12 ≤ M) (h2 : M ≤ 10 ^ 19) :
    theta M ≤ M + 0.94 * √(M : ℝ) := by
  have hb := (abs_le.1 (buthe_psi M h1 h2)).2
  rw [← psi_eq_Icc] at hb
  have := theta_le_psi' M
  linarith

open Classical in
/-- **`ψ(N) − θ(N) ≤ √N (1.0054 + 0.048 log N)` for `10⁹ ≤ N ≤ 10¹⁹`**: the squares contribute
`θ(⌊√N⌋)`, and every prime `m` with `m³ ≤ N` has `961 m² ≤ N`, so `m ≤ ⌊√N⌋/31`; both `θ`s are bounded
by Büthe's bound for `ψ`. -/
theorem psi_sub_theta_le_buthe {N : ℕ} (h1 : 10 ^ 9 ≤ N) (h2 : N ≤ 10 ^ 19) :
    psi N - theta N ≤ √(N : ℝ) * (1.0054 + 0.048 * Real.log N) := by
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
  -- Büthe at `s` and `M`
  have hθs := theta_le_buthe (M := s) (by omega) (by omega)
  have hθM := theta_le_buthe (M := M) (by omega) (by omega)
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
  have hbs : 0.94 * √(s : ℝ) ≤ 0.00532 * s := by nlinarith
  have hbM : 0.94 * √(M : ℝ) ≤ 0.02947 * M := by nlinarith
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
  -- assemble: `ψ − θ ≤ 1.00532 √N + K · 1.02947 √N/31`
  have hA : theta s ≤ 1.00532 * sN := by linarith
  have hB : ((K + 1 - (2 + 1) : ℕ) : ℝ) * theta M ≤ K * (1.02947 * (sN / 31)) := by
    have h1 : theta M ≤ 1.02947 * (sN / 31) := by linarith
    have h2 := mul_le_mul_of_nonneg_right hKr hθM0
    have h3 := mul_le_mul_of_nonneg_left h1 hK0
    linarith
  have hC : K * (1.02947 * (sN / 31)) ≤ 0.048 * (Real.log N * sN) := by
    have := mul_le_mul_of_nonneg_left hKL hsN0
    nlinarith
  have e : sN * (1.0054 + 0.048 * Real.log N) = 1.0054 * sN + 0.048 * (Real.log N * sN) := by ring
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

theorem log_1e19_le : Real.log 1e19 ≤ 43.75 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 43 (u := 0.75) (by norm_num) 8
  have e : ((43 : ℕ) : ℝ) + 0.75 = 43.75 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_ge_of_le {x c : ℝ} (hx : 0 < x) (h : Real.exp c ≤ x) : c ≤ Real.log x :=
  (Real.le_log_iff_exp_le hx).2 h

set_option maxHeartbeats 1000000 in
/-- **Explicit PNT for `θ`** (replaces Dusart): `|θ(n) − n| < n/log³n + ε_pl(n) n` for `n ≥ 10⁹`. -/
theorem theta_explicit {n : ℕ} (hn : 1000000000 ≤ n) :
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
  rcases le_or_gt n (10 ^ 19) with h2 | h2
  · -- Büthe's bound for `ψ`, and `ψ − θ ≤ √x (1.0054 + 0.048 log x)`
    have hB := buthe_psi n (by omega) h2
    rw [← psi_eq_Icc] at hB
    have hD := psi_sub_theta_le_buthe (N := n) hn h2
    have hθψ := theta_le_psi' n
    have hθt : θ = theta n := (theta_eq n).symm
    rw [← hxdef] at hB hD
    have hx9 : (1e9 : ℝ) ≤ x := by
      rw [hxdef]
      have : ((1000000000 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      norm_num at this ⊢; linarith
    have hL0 : Real.log 1e9 ≤ Real.log x := Real.log_le_log (by norm_num) hx9
    have h8 : 8 ≤ Real.log 1e9 := log_ge_of_le (by norm_num) (by
      have h := Real.exp_one_lt_d9
      have : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 8 ≤ 2.7182818286 ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 8
        _ ≤ 1e9 := by norm_num)
    have hc := cube_div_sqrt_le hx0 (by linarith) hL0
    have hq := quart_div_sqrt_le hx0 h8 hL0
    rw [exp_neg_half_log (by norm_num)] at hc hq
    have hs9 : (31622 : ℝ) ≤ √(1e9 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
    have hl9 := log_1e9_le
    have hl0 : 0 ≤ Real.log 1e9 := by linarith
    have h4 : (√(1e9 : ℝ))⁻¹ ≤ 1 / 31622 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hs9
    have hc' : Real.log x ^ 3 * (√x)⁻¹ ≤ 0.2818 := by
      refine hc.trans ?_
      have h3 : Real.log 1e9 ^ 3 ≤ 20.73 ^ 3 := pow_le_pow_left₀ hl0 hl9 3
      calc Real.log 1e9 ^ 3 * (√(1e9 : ℝ))⁻¹ ≤ 20.73 ^ 3 * (1 / 31622) :=
            mul_le_mul h3 h4 (by positivity) (by norm_num)
        _ ≤ 0.2818 := by norm_num
    have hq' : Real.log x ^ 4 * (√x)⁻¹ ≤ 5.84 := by
      refine hq.trans ?_
      have h3 : Real.log 1e9 ^ 4 ≤ 20.73 ^ 4 := pow_le_pow_left₀ hl0 hl9 4
      calc Real.log 1e9 ^ 4 * (√(1e9 : ℝ))⁻¹ ≤ 20.73 ^ 4 * (1 / 31622) :=
            mul_le_mul h3 h4 (by positivity) (by norm_num)
        _ ≤ 5.84 := by norm_num
    have hL3' : Real.log x ^ 3 ≤ 0.2818 * √x := by
      have := mul_le_mul_of_nonneg_right hc' hs0.le
      rwa [mul_assoc, inv_mul_cancel₀ hs0.ne', mul_one] at this
    have hL4' : Real.log x ^ 4 ≤ 5.84 * √x := by
      have := mul_le_mul_of_nonneg_right hq' hs0.le
      rwa [mul_assoc, inv_mul_cancel₀ hs0.ne', mul_one] at this
    -- `√x (1.9454 + 0.048 L) < x/L³`
    have hkey : √x * (1.9454 + 0.048 * Real.log x) * Real.log x ^ 3 < x := by
      have e : √x * (1.9454 + 0.048 * Real.log x) * Real.log x ^ 3 =
          1.9454 * (√x * Real.log x ^ 3) + 0.048 * (√x * Real.log x ^ 4) := by ring
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left hL3' hs0.le
      have h2 := mul_le_mul_of_nonneg_left hL4' hs0.le
      have e1 : √x * (0.2818 * √x) = 0.2818 * x := by
        rw [show √x * (0.2818 * √x) = 0.2818 * (√x * √x) by ring, hss]
      have e2 : √x * (5.84 * √x) = 5.84 * x := by
        rw [show √x * (5.84 * √x) = 5.84 * (√x * √x) by ring, hss]
      rw [e1] at h1; rw [e2] at h2
      linarith
    have hlt : √x * (1.9454 + 0.048 * Real.log x) < x / Real.log x ^ 3 := by
      rw [lt_div_iff₀ hL3]; exact hkey
    have hpos : 0 ≤ √x * (1.0054 + 0.048 * Real.log x) := by positivity
    have e3 : 0.94 * √x + √x * (1.0054 + 0.048 * Real.log x) = √x * (1.9454 + 0.048 * Real.log x) := by
      ring
    rw [hθt, abs_lt]
    constructor <;> linarith [(abs_le.1 hB).1, (abs_le.1 hB).2]
  -- above `10¹⁹`
  have hx19 : (1e19 : ℝ) < x := by
    rw [hxdef]
    have : ((10 ^ 19 : ℕ) : ℝ) < n := by exact_mod_cast h2
    norm_num at this ⊢; linarith
  have hψ : psiR x = psi n := by rw [hxdef]; exact psiR_nat n
  have hθt : θ = theta n := (theta_eq n).symm
  have hdiff := psi_sub_theta_le' (N := n) (by omega)
  have hθψ := theta_le_psi' n
  rw [← hxdef] at hdiff
  set L := Real.log x with hLdef
  have hL19 : Real.log 1e19 ≤ L := Real.log_le_log (by norm_num) hx19.le
  have h19 := log_1e19_le
  have hl19ge : (43.7 : ℝ) ≤ Real.log 1e19 := log_ge_of_le (by norm_num) (by
      have h1 := Real.exp_one_lt_d9
      have h2 := Real.exp_bound' (x := 0.7) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h2
      have e : Real.exp 43.7 = Real.exp 1 ^ 43 * Real.exp 0.7 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      have h3 : Real.exp 1 ^ 43 ≤ 2.7182818286 ^ 43 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 43
      nlinarith [Real.exp_pos 0.7, pow_pos (Real.exp_pos 1) 43])
  have hL43 : 43.7 ≤ L := by linarith
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
  rcases le_or_gt L 3400 with h3 | h3
  · -- the explicit formula up to `e^{3400}`: below `x/L³`
    have hP := psi_plateau hx19.le
    have hA : |θ - x| ≤ 2.15e-11 * x + 15000 * √x + 4.2e10 + 2.001 * L * √x := by linarith
    have hbig : (2.15e-11 * x + 15000 * √x + 4.2e10 + 2.001 * L * √x) * L ^ 3 < x := by
      have e : (2.15e-11 * x + 15000 * √x + 4.2e10 + 2.001 * L * √x) * L ^ 3 =
          2.15e-11 * x * L ^ 3 + 15000 * (√x * L ^ 3) + 4.2e10 * L ^ 3 + 2.001 * (√x * L ^ 4) := by ring
      rw [e, hsL3, hsL4]
      rcases le_or_gt L 100 with h4 | h4
      · have hc := cube_div_sqrt_le hx0 (by linarith) hL19
        have hq := quart_div_sqrt_le hx0 (by linarith) hL19
        rw [exp_neg_half_log (by norm_num)] at hc hq
        have hs19 : (3.16e9 : ℝ) ≤ √(1e19 : ℝ) := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        have hinv19 : (√(1e19 : ℝ))⁻¹ ≤ 3.1646e-10 := by
          have : (√(1e19 : ℝ))⁻¹ ≤ (3.16e9 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs19
          exact this.trans (by norm_num)
        have hl0 : 0 ≤ Real.log 1e19 := by linarith
        have hc' : L ^ 3 * (√x)⁻¹ ≤ 2.651e-5 := by
          refine hc.trans ?_
          have : Real.log 1e19 ^ 3 ≤ 43.75 ^ 3 := pow_le_pow_left₀ hl0 h19 3
          have := mul_le_mul this hinv19 (by positivity) (by norm_num)
          norm_num at this ⊢; linarith
        have hq' : L ^ 4 * (√x)⁻¹ ≤ 1.16e-3 := by
          refine hq.trans ?_
          have : Real.log 1e19 ^ 4 ≤ 43.75 ^ 4 := pow_le_pow_left₀ hl0 h19 4
          have := mul_le_mul this hinv19 (by positivity) (by norm_num)
          norm_num at this ⊢; linarith
        have hL3b : L ^ 3 ≤ 1e6 := by
          have := pow_le_pow_left₀ (by linarith) h4 3; norm_num at this ⊢; linarith
        have h5 := mul_le_mul_of_nonneg_left hc' hx0.le
        have h6 := mul_le_mul_of_nonneg_left hq' hx0.le
        have h7 : 2.15e-11 * x * L ^ 3 ≤ 2.15e-5 * x := by nlinarith
        have h8 : 4.2e10 * L ^ 3 ≤ 4.2e-3 * x := by nlinarith
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
        have hL3b : L ^ 3 ≤ 3.9305e10 := by
          have := pow_le_pow_left₀ (by linarith) h3 3; norm_num at this ⊢; linarith
        have hxbig : (1e30 : ℝ) ≤ x := by
          have h := TernaryGoldbach.Explicit.exp_nat_ge' 70
          have h2' : Real.exp ((70 : ℕ) : ℝ) ≤ Real.exp L := Real.exp_le_exp.2 (by push_cast; linarith)
          rw [hLdef, Real.exp_log hx0] at h2'
          have : (1e30 : ℝ) ≤ 2.7182818283 ^ 70 := by norm_num
          exact this.trans (h.trans h2')
        have h5 := mul_le_mul_of_nonneg_left hc' hx0.le
        have h6 := mul_le_mul_of_nonneg_left hq' hx0.le
        have h7 : 2.15e-11 * x * L ^ 3 ≤ 0.846 * x := by nlinarith
        have h8 : 4.2e10 * L ^ 3 ≤ 1e-8 * x := by nlinarith
        linarith
    have : |θ - x| < x / L ^ 3 := by
      rw [lt_div_iff₀ (by positivity)]
      calc |θ - x| * L ^ 3 ≤ (2.15e-11 * x + 15000 * √x + 4.2e10 + 2.001 * L * √x) * L ^ 3 :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ < x := hbig
    linarith
  -- above `e^{3400}`
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
    have hepl : epl x = 2.2e-11 := by unfold epl; rw [if_pos ⟨h3, h5⟩]
    have hP := psi_plateau hx19.le
    have h1' : 2.001 * L * √x ≤ 40020 * √x := by
      have := mul_le_mul_of_nonneg_right (show 2.001 * L ≤ 40020 by linarith) hs0.le; linarith
    have h2' := hsmall 55020 (by norm_num)
    have : |θ - x| ≤ 2.2e-11 * x := by nlinarith
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

theorem epl_ne_zero {x : ℝ} (h : epl x ≠ 0) : 3400 < Real.log x ∧ Real.log x < 20000 := by
  unfold epl at h; split_ifs at h with hh
  · exact hh
  · exact absurd rfl h

/-- `Σ_{a<n<b} ε_pl(n)/(n+1) ≤ 3.66·10⁻⁷`, and `= 0` if `log(a+1) ≥ 20000`. -/
theorem sum_epl_div_le (a b : ℕ) :
    ∑ n ∈ Ioo a b, epl n / ((n : ℝ) + 1) ≤ if Real.log ((a : ℝ) + 1) < 20000 then 3.66e-7 else 0 := by
  split_ifs with ha
  · -- telescoping over `[e^{3400}, e^{20000}]`
    set m1 := ⌈Real.exp 3400⌉₊ with hm1
    set m2 := ⌊Real.exp 20000⌋₊ + 1 with hm2
    have hterm : ∀ n ∈ Ioo a b, epl n / ((n : ℝ) + 1) ≤
        if n ∈ Ico m1 m2 then 2.2e-11 * (Real.log ((n : ℝ) + 1) - Real.log n) else 0 := by
      intro n _
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
        · rw [hm1, Nat.ceil_le]
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
    have hnn : ∀ n ∈ Ico m1 m2, 0 ≤ 2.2e-11 * (Real.log ((n : ℝ) + 1) - Real.log n) := by
      intro n hn
      have hn1 : 1 ≤ m1 := by rw [hm1, Nat.one_le_ceil_iff]; exact Real.exp_pos _
      have hn0 : (0 : ℝ) < n := by
        have := (Finset.mem_Ico.1 hn).1; exact_mod_cast (by omega : 0 < n)
      have : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
      nlinarith
    refine (sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hnn n hn).trans ?_
    rw [← mul_sum]
    have hm12 : m1 ≤ m2 := by
      rw [hm1, hm2, Nat.ceil_le]
      have := Nat.lt_floor_add_one (Real.exp 20000)
      have : Real.exp 3400 ≤ Real.exp 20000 := Real.exp_le_exp.2 (by norm_num)
      push_cast; linarith
    have htel : ∑ n ∈ Ico m1 m2, (Real.log ((n : ℝ) + 1) - Real.log n) = Real.log m2 - Real.log m1 := by
      rw [Finset.sum_Ico_eq_sum_range]
      have := Finset.sum_range_sub (fun k : ℕ => Real.log ((m1 + k : ℕ) : ℝ)) (m2 - m1)
      rw [show m1 + (m2 - m1) = m2 by omega, show m1 + 0 = m1 by omega] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring_nf
    rw [htel]
    have hm1pos : (0 : ℝ) < m1 := by
      have : 1 ≤ m1 := by rw [hm1, Nat.one_le_ceil_iff]; exact Real.exp_pos _
      exact_mod_cast this
    have h1 : 3400 ≤ Real.log m1 := by
      rw [Real.le_log_iff_exp_le hm1pos]; exact Nat.le_ceil _
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

/-- The plateau mass beyond `M`: `3.7·10⁻⁷` if `log M < 20000`, else `0`. -/
noncomputable def Pth (M : ℝ) : ℝ := if Real.log M < 20000 then 3.7e-7 else 0

theorem Pth_nonneg (M : ℝ) : 0 ≤ Pth M := by unfold Pth; split_ifs <;> norm_num

theorem Pth_le (M : ℝ) : Pth M ≤ 3.7e-7 := by unfold Pth; split_ifs <;> norm_num

theorem Pth_mul_log_le {M : ℝ} (hM : 1 ≤ M) : Pth M * Real.log M ≤ 0.0074 := by
  unfold Pth; split_ifs with h
  · have := Real.log_nonneg hM; nlinarith
  · rw [zero_mul]; norm_num

/-- `Σ_{M<n<N} ε_pl(n)/(n+1) + ε_pl(N) + ε_pl(M) ≤ P(M)`. -/
theorem epl_total_le {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ∑ n ∈ Ioo M N, epl n / ((n : ℝ) + 1) + epl N + epl M ≤ Pth M := by
  have hS := sum_epl_div_le M N
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  by_cases h : Real.log (M : ℝ) < 20000
  · have hS' : ∑ n ∈ Ioo M N, epl n / ((n : ℝ) + 1) ≤ 3.66e-7 := hS.trans (by split_ifs <;> norm_num)
    have := epl_le (N : ℝ); have := epl_le (M : ℝ)
    unfold Pth; rw [if_pos h]; linarith
  · push Not at h
    have h1 : ¬ Real.log ((M : ℝ) + 1) < 20000 := by
      push Not; exact h.trans (Real.log_le_log hM0 (by linarith))
    rw [if_neg h1] at hS
    have hN : 20000 ≤ Real.log (N : ℝ) := h.trans (Real.log_le_log hM0 hMN')
    unfold Pth; rw [if_neg (not_lt.2 h), epl_eq_zero hN, epl_eq_zero h]; linarith

theorem epl_mul_log_le (x : ℝ) : epl x * Real.log x ≤ 4.4e-7 := by
  unfold epl; split_ifs with h
  · nlinarith [h.1, h.2]
  · rw [zero_mul]; norm_num

end TernaryGoldbach.Prelim
