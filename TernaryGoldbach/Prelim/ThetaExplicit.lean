import TernaryGoldbach.Explicit.PsiAsymp

/-!
# An explicit prime number theorem for `θ` (replacing Dusart's bound)

`|θ(n) − n| < n/log³n + ε_pl(n)·n` for `n ≥ 89 967 803`, where `ε_pl(n) = 2.2·10⁻¹¹` if
`3400 < log n < 20000` and `0` otherwise.

Inputs: the finite check `theta_cube_small` (`n ≤ 10¹⁰`, `scripts/theta_cube_check.py`), [Büthe 2018] for
`n ≤ 10¹⁹` (numerical axiom), and the explicit formula with the zero-free region (`Explicit/Psi*`) above.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim

open TernaryGoldbach.Explicit (psiR psi_plateau psi_range1 psi_asymp)
open TernaryGoldbach.Helfgott (psi theta psi_sub_theta_le_sum sum_pow_le_theta)

/-- **Numerical axiom** (`scripts/theta_cube_check.py`; maximum of `|θ(n) − n| log³ n/n` is `0.99934` at
`n = 89 967 810`): `|θ(n) − n| < n/log³ n` for `89 967 803 ≤ n ≤ 10¹⁰`. -/
axiom theta_cube_small (n : ℕ) (h1 : 89967803 ≤ n) (h2 : n ≤ 10 ^ 10) :
    |∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p - n| < n / Real.log n ^ 3

/-- **Numerical axiom** ([Büthe 2018], *An analytic method for bounding ψ(x)*, Math. Comp. 87 (2018),
1991–2009, arXiv:1511.02032, Thm 2): `0.05 √x < x − θ(x) ≤ 1.95 √x` for `1423 ≤ x ≤ 10¹⁹`; we use
`|θ(n) − n| ≤ 1.95 √n`. -/
axiom buthe_theta (n : ℕ) (h1 : 1423 ≤ n) (h2 : n ≤ 10 ^ 19) :
    |∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p - n| ≤ 1.95 * √(n : ℝ)

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

theorem log_1e19_le : Real.log 1e19 ≤ 43.75 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 43 (u := 0.75) (by norm_num) 8
  have e : ((43 : ℕ) : ℝ) + 0.75 = 43.75 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_ge_of_le {x c : ℝ} (hx : 0 < x) (h : Real.exp c ≤ x) : c ≤ Real.log x :=
  (Real.le_log_iff_exp_le hx).2 h

set_option maxHeartbeats 1000000 in
/-- **Explicit PNT for `θ`** (replaces Dusart): `|θ(n) − n| < n/log³n + ε_pl(n) n` for `n ≥ 89 967 803`. -/
theorem theta_explicit {n : ℕ} (hn : 89967803 ≤ n) :
    |∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p - n| < n / Real.log n ^ 3 + epl n * n := by
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = n := ⟨_, rfl⟩
  rw [← hxdef]
  have hx0 : 0 < x := by rw [hxdef]; exact_mod_cast (by omega : 0 < n)
  have hepl : 0 ≤ epl x * x := mul_nonneg (epl_nonneg x) hx0.le
  have hlx : 0 < Real.log x := Real.log_pos (by rw [hxdef]; exact_mod_cast (by omega : 1 < n))
  have hL3 : 0 < Real.log x ^ 3 := by positivity
  rcases le_or_gt n (10 ^ 10) with h1 | h1
  · have := theta_cube_small n hn h1
    rw [← hxdef] at this; linarith
  set θ := ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p with hθ
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hsinv : x * (√x)⁻¹ = √x := by
    calc x * (√x)⁻¹ = √x * √x * (√x)⁻¹ := by rw [hss]
      _ = √x := by field_simp
  rcases le_or_gt n (10 ^ 19) with h2 | h2
  · -- Büthe
    have hB := buthe_theta n (by omega) h2
    rw [← hxdef] at hB
    have hx10 : (1e10 : ℝ) ≤ x := by
      rw [hxdef]
      have : ((10 ^ 10 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1.le
      norm_num at this ⊢; linarith
    have hL0 : Real.log 1e10 ≤ Real.log x := Real.log_le_log (by norm_num) hx10
    have h6 : 6 ≤ Real.log 1e10 := log_ge_of_le (by norm_num) (by
      have := TernaryGoldbach.Explicit.exp_split_ge' 6 (u := 0) le_rfl 1
      have h := Real.exp_one_lt_d9
      have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 6 ≤ 2.7182818286 ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 6
        _ ≤ 1e10 := by norm_num)
    have hc := cube_div_sqrt_le hx0 h6 hL0
    rw [exp_neg_half_log (by norm_num), show √(1e10 : ℝ) = 1e5 by
      rw [show (1e10 : ℝ) = 1e5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hc
    have hl10 := log_1e10_le
    have hl0 : 0 ≤ Real.log 1e10 := by linarith
    have hc' : Real.log x ^ 3 * (√x)⁻¹ ≤ 0.1222 := by
      refine hc.trans ?_
      have : Real.log 1e10 ^ 3 ≤ 23.03 ^ 3 := pow_le_pow_left₀ hl0 hl10 3
      norm_num at this ⊢; linarith
    -- `1.95 √x < x/L³`
    have hkey : 1.95 * √x * Real.log x ^ 3 < x := by
      have : Real.log x ^ 3 ≤ 0.1222 * √x := by
        have := mul_le_mul_of_nonneg_right hc' hs0.le
        rwa [mul_assoc, inv_mul_cancel₀ hs0.ne', mul_one] at this
      nlinarith
    have : 1.95 * √x < x / Real.log x ^ 3 := by rw [lt_div_iff₀ hL3]; exact hkey
    linarith
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

end TernaryGoldbach.Prelim
