import TernaryGoldbach.Helfgott.Inputs
import TernaryGoldbach.Prelim.ThetaExplicit

/-!
# The small cases `5 < n ≤ 10²⁷` from binary Goldbach and bounds for `θ`

For odd `n ≤ 2.8·10¹⁷ + 3`, `n = 3 + (n − 3)` and binary Goldbach up to `2.8·10¹⁷` (`binary_goldbach_input`,
[OeSHP14] go to `4·10¹⁸` and double-checked `3·10¹⁷`) applies. For odd `2.8·10¹⁷ + 3 < n ≤ 10²⁷` there is a
prime `p` with `n − 2.8·10¹⁷ < p ≤ n − 4`, since `−1.413·10¹⁷ ≤ θ(m) − m ≤ 1.373·10¹⁷` for
`1423 ≤ m ≤ 10²⁷` (`theta_bound`): [Büthe 2018] (`buthe_theta`) below `10¹⁹`, and the explicit formula
(`psi_plateau`, from `rh_upto`) with `ψ − θ ≤ 2.001 log m √m` above. Then `n − p` is even and at most
`2.8·10¹⁷`.

This replaces the Helfgott–Platt prime ladder [HP13], whose gaps are `≤ 4·10¹⁸`.
-/

open Finset Real

namespace TernaryGoldbach.Helfgott

open TernaryGoldbach.Prelim (buthe_theta theta_eq psi_sub_theta_le' theta_le_psi' psiR_nat)
open TernaryGoldbach.Explicit (psi_plateau)

/-- `θ(n) = ∑_{p ≤ n} log p`. -/
noncomputable def th (n : ℕ) : ℝ := ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p

theorem th_mono {a b : ℕ} (h : a ≤ b) : th a ≤ th b := by
  unfold th
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => Real.log_natCast_nonneg p
  simp only [mem_filter, mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans h⟩, hp.2⟩

/-- A prime in `(a, b]` if `θ(a) < θ(b)`. -/
theorem exists_prime_of_th_lt {a b : ℕ} (h : th a < th b) : ∃ p, p.Prime ∧ a < p ∧ p ≤ b := by
  by_contra hne
  push Not at hne
  have : th b ≤ th a := by
    unfold th
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => Real.log_natCast_nonneg p
    simp only [mem_filter, mem_Icc] at hp ⊢
    refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
    by_contra hpa
    exact absurd hp.1.2 (not_le.2 (hne p hp.2 (by omega)))
  linarith

theorem sqrt_le_of_sq {x c : ℝ} (hc : 0 ≤ c) (h : x ≤ c ^ 2) : √x ≤ c := by
  rw [Real.sqrt_le_left hc]; exact h

theorem log_1e27_le : Real.log (10 ^ 27 : ℝ) ≤ 63 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have e : Real.exp 63 = Real.exp 1 ^ 63 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (10 ^ 27 : ℝ) ≤ (2.7182818283 : ℝ) ^ 63 := by norm_num
    _ ≤ Real.exp 1 ^ 63 := pow_le_pow_left₀ (by norm_num) h1.le 63

/-- **`−1.413·10¹⁷ ≤ θ(n) − n ≤ 1.373·10¹⁷` for `1423 ≤ n ≤ 10²⁷`**. -/
theorem theta_bound {n : ℕ} (h1 : 1423 ≤ n) (h2 : n ≤ 10 ^ 27) :
    -1.413e17 ≤ th n - n ∧ th n - n ≤ 1.373e17 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt n (10 ^ 19) with h | h
  · have hB := abs_le.1 (buthe_theta n h1 h)
    have hs : √(n : ℝ) ≤ 4e9 :=
      sqrt_le_of_sq (by norm_num) ((Nat.cast_le.2 h).trans_eq' (by norm_num) |>.trans (by norm_num))
    unfold th
    constructor <;> nlinarith
  · have hn19 : (1e19 : ℝ) ≤ n := by
      have : (10 ^ 19 : ℝ) ≤ n := by exact_mod_cast h.le
      norm_num at this ⊢; exact this
    have hn27 : (n : ℝ) ≤ 10 ^ 27 := by exact_mod_cast h2
    have hP := abs_le.1 (psi_plateau hn19)
    rw [psiR_nat] at hP
    have hT : th n = theta n := by rw [theta_eq]; rfl
    have hle := theta_le_psi' n
    have hge := psi_sub_theta_le' (N := n) (by omega)
    have hs : √(n : ℝ) ≤ 3.1623e13 := sqrt_le_of_sq (by norm_num) (hn27.trans (by norm_num))
    have hl : Real.log n ≤ 63 :=
      (Real.log_le_log (by linarith) hn27).trans log_1e27_le
    have hs0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hls : Real.log n * √(n : ℝ) ≤ 63 * 3.1623e13 := mul_le_mul hl hs hs0 (by norm_num)
    rw [hT]
    constructor <;> nlinarith

/-- **Ternary Goldbach for odd `5 < n ≤ 10²⁷`**. -/
theorem ternaryGoldbachUpTo_1e27 : TernaryGoldbachUpTo (10 ^ 27) := by
  intro n hn h5 hle
  have hBG := binary_goldbach_input
  by_cases hsmall : n ≤ 28 * 10 ^ 16 + 3
  · -- `n = 3 + (n − 3)`
    have hev : Even (n - 3) := Nat.Odd.sub_odd hn (by decide)
    obtain ⟨p, q, hp, hq, hpq⟩ := hBG (n - 3) hev (by obtain ⟨k, hk⟩ := hn; omega) (by omega)
    exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩
  · -- a prime `p ∈ (n − 2.8·10¹⁷, n − 4]`
    push Not at hsmall
    set a := n - 28 * 10 ^ 16 with ha
    set b := n - 4 with hb
    have hab : (b : ℝ) - a = 28 * 10 ^ 16 - 4 := by
      rw [ha, hb, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have hb1 : 1423 ≤ b := by omega
    have hb2 : b ≤ 10 ^ 27 := by omega
    have hbb := (theta_bound hb1 hb2).1
    have hlt : th a < th b := by
      rcases le_or_gt 1423 a with h | h
      · have haa := (theta_bound h (by omega)).2
        linarith
      · have h1 : th a ≤ th 1423 := th_mono h.le
        have h2 : |th 1423 - ((1423 : ℕ) : ℝ)| ≤ 1.95 * √((1423 : ℕ) : ℝ) :=
          buthe_theta 1423 le_rfl (by norm_num)
        have hs : √((1423 : ℕ) : ℝ) ≤ 38 := sqrt_le_of_sq (by norm_num) (by norm_num)
        have h3 : th 1423 ≤ 1500 := by
          have := (abs_le.1 h2).2
          have e : ((1423 : ℕ) : ℝ) = 1423 := by norm_num
          rw [e] at this hs
          linarith
        have hbR : (28 * 10 ^ 16 : ℝ) ≤ b := by exact_mod_cast (show 28 * 10 ^ 16 ≤ b by omega)
        linarith
    obtain ⟨p, hp, hap, hpb⟩ := exists_prime_of_th_lt hlt
    have hp2 : p ≠ 2 := by omega
    have hpo : Odd p := hp.odd_of_ne_two hp2
    have hev : Even (n - p) := Nat.Odd.sub_odd hn hpo
    obtain ⟨q, r, hq, hr, hqr⟩ := hBG (n - p) hev (by omega) (by omega)
    exact ⟨p, q, r, hp, hq, hr, by omega⟩

end TernaryGoldbach.Helfgott
