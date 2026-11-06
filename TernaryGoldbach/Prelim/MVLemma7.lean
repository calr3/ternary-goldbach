import TernaryGoldbach.Prelim.MVLemma8
import TernaryGoldbach.Prelim.SmallProdAp
import TernaryGoldbach.Prelim.SmallG
import TernaryGoldbach.Prelim.SmallW
import TernaryGoldbach.Prelim.Ramare

/-!
# [MV73, Lemma 7]: `G(r) = ∑_{s ≤ r} μ(s)²/φ(s) ≥ log r + 1.07` for `r ≥ 6`

For `r ≥ 21400` this follows from Ramaré's estimate `G(r) = log r + c_E + O*(7.284 r^{−1/3})`
(`Prelim.ramare_Gq`, [H, (12.12)]); for `6 ≤ r < 21400` it is checked by the kernel
(`SmallG.lemma7_small`).

The file also proves the asymptotic `|G(N) − log N − κ| ≤ (2 + 3/e + γ) P N^{−1/3}` from the
Euler product of `h = F ∗ μ`, `F(n) = n μ(n)²/φ(n)` (Rankin's trick, `P = ∑ |h(d)| d^{−2/3} ≤ 9.32`;
`GS_asymp`). The main theorems do not use it.
-/

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim.MV

/-- `F(n) = n μ(n)²/φ(n)`. -/
noncomputable def Fm : ArithmeticFunction ℝ :=
  ⟨fun n => if Squarefree n then (n : ℝ) / Nat.totient n else 0, by simp⟩

theorem Fm_apply (n : ℕ) : Fm n = if Squarefree n then (n : ℝ) / Nat.totient n else 0 := rfl

theorem isMultiplicative_Fm : IsMultiplicative Fm := by
  refine ⟨by simp [Fm_apply], fun {m n} hmn => ?_⟩
  simp only [Fm_apply, Nat.squarefree_mul_iff, Nat.totient_mul hmn]
  by_cases hm : Squarefree m
  · by_cases hn : Squarefree n
    · rw [if_pos ⟨hmn, hm, hn⟩, if_pos hm, if_pos hn]; push_cast; field_simp
    · rw [if_neg (fun h => hn h.2.2), if_neg hn, mul_zero]
  · rw [if_neg (fun h => hm h.2.1), if_neg hm, zero_mul]

/-- `h = F ∗ μ`. -/
noncomputable def hm : ArithmeticFunction ℝ := Fm * (μ : ArithmeticFunction ℝ)

theorem isMultiplicative_hm : IsMultiplicative hm :=
  isMultiplicative_Fm.mul isMultiplicative_moebius.intCast

theorem Fm_eq_hm_mul_zeta : Fm = hm * (ζ : ArithmeticFunction ℝ) := by
  rw [hm, mul_assoc, coe_moebius_mul_coe_zeta, mul_one]

/-- `F(p^k) = ∑_{i ≤ k} h(p^i)`. -/
theorem Fm_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Fm (p ^ k) = ∑ i ∈ range (k + 1), hm (p ^ i) := by
  rw [Fm_eq_hm_mul_zeta, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]

theorem Fm_prime {p : ℕ} (hp : p.Prime) : Fm p = p / (p - 1) := by
  rw [Fm_apply, if_pos hp.squarefree, Nat.totient_prime hp, Nat.cast_sub hp.one_le]; simp

theorem Fm_prime_pow_ge_two {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 2 ≤ k) : Fm (p ^ k) = 0 := by
  rw [Fm_apply, if_neg]
  intro h
  have := h p (by
    rw [show p ^ k = p * p * p ^ (k - 2) by
      rw [← pow_two, ← pow_add]; congr 1; omega]
    exact dvd_mul_right _ _)
  exact hp.not_isUnit (Nat.isUnit_iff.2 (Nat.isUnit_iff.1 this))

theorem hm_one : hm 1 = 1 := isMultiplicative_hm.map_one

theorem hm_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    hm (p ^ (k + 1)) = Fm (p ^ (k + 1)) - Fm (p ^ k) := by
  rw [Fm_prime_pow hp (k + 1), Fm_prime_pow hp k, sum_range_succ]; ring

theorem hm_prime {p : ℕ} (hp : p.Prime) : hm p = 1 / (p - 1) := by
  have h := hm_prime_pow_succ hp 0
  simp only [zero_add, pow_one, pow_zero] at h
  rw [Fm_prime hp] at h
  have h1 : Fm 1 = 1 := isMultiplicative_Fm.map_one
  rw [h, h1]
  have : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  field_simp; ring

theorem hm_prime_sq {p : ℕ} (hp : p.Prime) : hm (p ^ 2) = -(p / (p - 1)) := by
  have h := hm_prime_pow_succ hp 1
  rw [pow_one, Fm_prime_pow_ge_two hp le_rfl, Fm_prime hp] at h
  rw [h]; ring

theorem hm_prime_pow_ge_three {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 3 ≤ k) : hm (p ^ k) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hm_prime_pow_succ hp j, Fm_prime_pow_ge_two hp (by omega), Fm_prime_pow_ge_two hp (by omega)]
  ring

/-! ### The convolution identity -/

/-- `d ↦ h(d)/d`. -/
noncomputable def hd : ArithmeticFunction ℝ := ⟨fun d => hm d / d, by simp⟩

/-- `m ↦ 1/m`. -/
noncomputable def recip : ArithmeticFunction ℝ := ⟨fun m => 1 / m, by simp⟩

theorem hd_mul_recip (n : ℕ) (hn : 0 < n) : (hd * recip) n = gS n := by
  rw [mul_apply]
  have h1 : ∀ x ∈ n.divisorsAntidiagonal, hd x.1 * recip x.2 = hm x.1 / n := by
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.1 hx
    simp only [hd, recip, coe_mk]
    have h1 : (x.1 : ℝ) ≠ 0 := by
      have := hx'.1; intro h; apply hx'.2; rw [← this]; simp [Nat.cast_eq_zero.1 h]
    have h2 : (x.2 : ℝ) ≠ 0 := by
      have := hx'.1; intro h; apply hx'.2; rw [← this]; simp [Nat.cast_eq_zero.1 h]
    rw [← hx'.1]; push_cast; field_simp
  rw [sum_congr rfl h1, ← sum_div, Nat.sum_divisorsAntidiagonal (fun a _ => hm a)]
  have h2 : ∑ i ∈ n.divisors, hm i = Fm n := by
    rw [Fm_eq_hm_mul_zeta, coe_mul_zeta_apply]
  rw [h2, Fm_apply, gS]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  split_ifs
  · field_simp
  · simp

/-- `H(m) = ∑_{i ≤ m} 1/i`. -/
noncomputable def Hs (m : ℕ) : ℝ := ∑ i ∈ Ioc 0 m, 1 / (i : ℝ)

/-- **`G(N) = ∑_{d ≤ N} (h(d)/d) H(N/d)`**. -/
theorem GS_eq (N : ℕ) : GS N = ∑ d ∈ Ioc 0 N, hm d / d * Hs (N / d) := by
  have h := sum_Ioc_mul_eq_sum_sum hd recip N
  rw [GS, show Icc 1 N = Ioc 0 N from rfl]
  rw [sum_congr rfl fun n hn => (hd_mul_recip n (mem_Ioc.1 hn).1).symm, h]
  rfl

/-! ### The harmonic sums -/

theorem Hs_eq_harmonic (m : ℕ) : Hs m = (harmonic m : ℝ) := by
  rw [harmonic_eq_sum_Icc, Hs]; push_cast
  exact sum_congr rfl fun i _ => by rw [one_div]

/-- `|H(M) − log y − γ| ≤ 1/M` for `M ≤ y < M + 1`, `M ≥ 1`. -/
theorem Hs_sub_log {M : ℕ} (hM : 1 ≤ M) {y : ℝ} (hy1 : (M : ℝ) ≤ y) (hy2 : y < M + 1) :
    |Hs M - Real.log y - eulerMascheroniConstant| ≤ 1 / M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant M
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' M
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq', show M ≠ 0 by omega,
    if_false] at h1 h2
  rw [← Hs_eq_harmonic] at h1 h2
  have hl1 : Real.log M ≤ Real.log y := Real.log_le_log hM0 hy1
  have hl2 : Real.log y ≤ Real.log (M + 1) := Real.log_le_log (by linarith) hy2.le
  have hd : Real.log (M + 1) - Real.log M ≤ 1 / M := by
    rw [← Real.log_div (by positivity) hM0.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp; ring
  rw [abs_le]; constructor <;> linarith

/-- For `1 ≤ d ≤ N`: `|H(N/d) − log(N/d) − γ| ≤ 2d/N`. -/
theorem Hs_div_sub_log {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    |Hs (N / d) - Real.log ((N : ℝ) / d) - eulerMascheroniConstant| ≤ 2 * d / N := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hM : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).2 hdN
  have hfl : (N / d : ℕ) = ⌊(N : ℝ) / d⌋₊ := (Nat.floor_div_eq_div N d).symm
  have hy1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by rw [hfl]; exact Nat.floor_le (by positivity)
  have hy2 : (N : ℝ) / d < (N / d : ℕ) + 1 := by rw [hfl]; exact Nat.lt_floor_add_one _
  refine (Hs_sub_log hM hy1 hy2).trans ?_
  have hM0 : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast hM
  -- `N/d < 2 (N/d : ℕ)` since `N/d ≥ 1`
  have hMy : (N : ℝ) / d ≤ 2 * (N / d : ℕ) := by
    have : (1 : ℝ) ≤ (N / d : ℕ) := by exact_mod_cast hM
    linarith
  rw [div_le_div_iff₀ hM0 hN0]
  rw [div_le_iff₀ hd0] at hMy
  nlinarith

/-! ### Rankin's trick: `∑ |h(d)| d^{−2/3} ≤ 9.215` -/

/-- `f(d) = |h(d)| d^{−2/3}`. -/
noncomputable def fR (d : ℕ) : ℝ := |hm d| * (d : ℝ) ^ (-(2 / 3) : ℝ)

theorem fR_nonneg (d : ℕ) : 0 ≤ fR d := by unfold fR; positivity

theorem fR_one : fR 1 = 1 := by simp [fR, hm_one]

theorem fR_mul {m n : ℕ} (h : m.Coprime n) : fR (m * n) = fR m * fR n := by
  simp only [fR, isMultiplicative_hm.map_mul_of_coprime h, abs_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

/-- `a_p = (p^{−2/3} + p^{−1/3})/(p − 1)`. -/
noncomputable def ap (p : ℕ) : ℝ := ((p : ℝ) ^ (-(2 / 3) : ℝ) + (p : ℝ) ^ (-(1 / 3) : ℝ)) / (p - 1)

theorem tsum_fR_prime_pow {p : ℕ} (hp : p.Prime) : ∑' e, fR (p ^ e) = 1 + ap p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rw [tsum_eq_sum (s := range 3) fun e he => by
    simp only [mem_range, not_lt] at he
    simp [fR, hm_prime_pow_ge_three hp he]]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, fR_one, pow_one]
  simp only [fR, hm_prime hp, hm_prime_sq hp, ap]
  have hpm : (0 : ℝ) < p - 1 := by linarith
  rw [abs_of_pos (by positivity), abs_neg, abs_of_pos (by positivity)]
  have hsq : (((p ^ 2 : ℕ) : ℝ)) ^ (-(2 / 3) : ℝ) = (p : ℝ) * (p : ℝ) ^ (-(1 / 3) : ℝ) / p ^ (2 : ℝ) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    have : (p : ℝ) * (p : ℝ) ^ (-(1 / 3) : ℝ) / p ^ (2 : ℝ) = (p : ℝ) ^ ((1 : ℝ) + -(1 / 3) - 2) := by
      rw [Real.rpow_sub hp0, Real.rpow_add hp0, Real.rpow_one]
    rw [this]; norm_num
  rw [hsq, show ((p : ℝ) ^ (2 : ℝ)) = p * p by rw [Real.rpow_two]; ring]
  field_simp
  ring

/-- `∏_{p < 10⁴} (1 + (p^{−2/3} + p^{−1/3})/(p − 1)) ≤ 7.99` (value `7.98552`; kernel-checked,
`Prelim/SmallProdAp.lean`). -/
theorem prod_ap_le : ∏ p ∈ Nat.primesBelow 10000, (1 + ap p) ≤ 7.99 := by
  unfold ap; exact Small.prod_ap_le'

/-- `∑_{P₀ ≤ n < M} n^{−s} ≤ (P₀ − 1)^{1−s}/(s − 1)`. -/
theorem sum_rpow_neg_le {s : ℝ} (hs : 1 < s) {P0 : ℕ} (hP0 : 2 ≤ P0) (M : ℕ) :
    ∑ n ∈ Ico P0 M, (n : ℝ) ^ (-s) ≤ ((P0 : ℝ) - 1) ^ (1 - s) / (s - 1) := by
  have ha : (0 : ℝ) < (P0 : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P0 := by exact_mod_cast hP0
    linarith
  rcases le_or_gt M P0 with hM | hM
  · rw [Ico_eq_empty (by omega), sum_empty]; positivity
  -- shift and compare with the integral
  have hshift : ∑ n ∈ Ico P0 M, (n : ℝ) ^ (-s) = ∑ i ∈ Ico (P0 - 1) (M - 1), ((i + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [show ∑ i ∈ Ico (P0 - 1) (M - 1), ((i + 1 : ℕ) : ℝ) ^ (-s) =
        ∑ n ∈ Ico (P0 - 1 + 1) (M - 1 + 1), (n : ℝ) ^ (-s) from
      sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-s)) _ _ 1,
      show P0 - 1 + 1 = P0 by omega, show M - 1 + 1 = M by omega]
  rw [hshift]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc ((P0 - 1 : ℕ) : ℝ) ((M - 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := by
      have := hx.1; rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hint := hanti.sum_le_integral_Ico (by omega : P0 - 1 ≤ M - 1)
  refine hint.trans ?_
  have hb : (0 : ℝ) < ((M - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast
    have : (P0 : ℝ) + 1 ≤ M := by exact_mod_cast hM
    linarith
  have ha' : ((P0 - 1 : ℕ) : ℝ) = (P0 : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.mem_uIcc]; push Not; constructor <;> intro h <;> linarith [h]⟩), ha']
  rw [show -s + 1 = 1 - s by ring]
  have hb0 : 0 ≤ ((M - 1 : ℕ) : ℝ) ^ (1 - s) := by positivity
  have hs1 : (1 : ℝ) - s ≠ 0 := by linarith
  have hs2 : s - 1 ≠ 0 := by linarith
  have e : (((M - 1 : ℕ) : ℝ) ^ (1 - s) - ((P0 : ℝ) - 1) ^ (1 - s)) / (1 - s) =
      (((P0 : ℝ) - 1) ^ (1 - s) - ((M - 1 : ℕ) : ℝ) ^ (1 - s)) / (s - 1) := by
    field_simp; ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem ap_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ ap n := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold ap; apply div_nonneg (by positivity); linarith

/-- `9999^{−1/3} ≤ 1/21.54`. -/
theorem rpow_9999_le : (9999 : ℝ) ^ (-(1 / 3) : ℝ) ≤ 1 / 21.54 := by
  have h1 : (21.54 : ℝ) ≤ (9999 : ℝ) ^ ((1 / 3) : ℝ) := by
    have : (21.54 : ℝ) = ((21.54 : ℝ) ^ (3 : ℕ)) ^ ((1 / 3) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
  rw [Real.rpow_neg (by norm_num), ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h1

/-- The tail `∑_{10⁴ ≤ n < M} a_n ≤ 0.1426`. -/
theorem tail_ap_le (M : ℕ) : ∑ n ∈ Ico 10000 M, ap n ≤ 0.1426 := by
  have hb : ∀ n ∈ Ico 10000 M, ap n ≤ 10000 / 9999 *
      ((n : ℝ) ^ (-(5 / 3) : ℝ) + (n : ℝ) ^ (-(4 / 3) : ℝ)) := by
    intro n hn
    have hn' : (10000 : ℝ) ≤ n := by exact_mod_cast (mem_Ico.1 hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    have e1 : (n : ℝ) ^ (-(5 / 3) : ℝ) = (n : ℝ) ^ (-(2 / 3) : ℝ) / n := by
      rw [eq_div_iff hn0.ne', ← Real.rpow_add_one hn0.ne']; norm_num
    have e2 : (n : ℝ) ^ (-(4 / 3) : ℝ) = (n : ℝ) ^ (-(1 / 3) : ℝ) / n := by
      rw [eq_div_iff hn0.ne', ← Real.rpow_add_one hn0.ne']; norm_num
    rw [e1, e2, ap]
    have hpos : 0 ≤ (n : ℝ) ^ (-(2 / 3) : ℝ) + (n : ℝ) ^ (-(1 / 3) : ℝ) := by positivity
    rw [show 10000 / 9999 * ((n : ℝ) ^ (-(2 / 3) : ℝ) / n + (n : ℝ) ^ (-(1 / 3) : ℝ) / n) =
      ((n : ℝ) ^ (-(2 / 3) : ℝ) + (n : ℝ) ^ (-(1 / 3) : ℝ)) * (10000 / (9999 * n)) by field_simp]
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hpos
    rw [div_le_div_iff₀ (by linarith) (by positivity)]; linarith
  refine (sum_le_sum hb).trans ?_
  rw [← mul_sum, sum_add_distrib]
  have h53 := sum_rpow_neg_le (s := 5 / 3) (by norm_num) (P0 := 10000) (by norm_num) M
  have h43 := sum_rpow_neg_le (s := 4 / 3) (by norm_num) (P0 := 10000) (by norm_num) M
  have hr := rpow_9999_le
  have hr0 : 0 ≤ (9999 : ℝ) ^ (-(1 / 3) : ℝ) := by positivity
  have e53 : ((10000 : ℕ) : ℝ) - 1 = 9999 := by norm_num
  rw [e53] at h53 h43
  have h1 : (9999 : ℝ) ^ ((1 : ℝ) - 5 / 3) = ((9999 : ℝ) ^ (-(1 / 3) : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h2 : (9999 : ℝ) ^ ((1 : ℝ) - 4 / 3) = (9999 : ℝ) ^ (-(1 / 3) : ℝ) := by norm_num
  rw [h1] at h53; rw [h2] at h43
  have hsq : ((9999 : ℝ) ^ (-(1 / 3) : ℝ)) ^ 2 ≤ (1 / 21.54) ^ 2 := pow_le_pow_left₀ hr0 hr 2
  have hs : 0 ≤ ∑ n ∈ Ico 10000 M, (n : ℝ) ^ (-(5 / 3) : ℝ) + ∑ n ∈ Ico 10000 M, (n : ℝ) ^ (-(4 / 3) : ℝ) :=
    add_nonneg (sum_nonneg fun _ _ => by positivity) (sum_nonneg fun _ _ => by positivity)
  norm_num at h53 h43 hsq ⊢
  nlinarith

/-- `∏_{p < N} (1 + a_p) ≤ 9.32`. -/
theorem prod_ap_le_all (N : ℕ) : ∏ p ∈ Nat.primesBelow N, (1 + ap p) ≤ 9.32 := by
  have hone : ∀ p ∈ Nat.primesBelow N, 1 ≤ 1 + ap p := fun p hp =>
    le_add_of_nonneg_right (ap_nonneg (Nat.mem_primesBelow.1 hp).2.two_le)
  rw [← prod_filter_mul_prod_filter_not (Nat.primesBelow N) (· < 10000)]
  have hA : ∏ p ∈ (Nat.primesBelow N).filter (· < 10000), (1 + ap p) ≤ 7.99 := by
    refine le_trans (prod_le_prod_of_subset_of_one_le₀ ?_ ?_ ?_) prod_ap_le
    · intro p hp
      simp only [mem_filter, Nat.mem_primesBelow] at hp ⊢; exact ⟨hp.2, hp.1.2⟩
    · intro p hp
      have := ap_nonneg (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le; linarith
    · intro p hp _
      exact le_add_of_nonneg_right (ap_nonneg (Nat.mem_primesBelow.1 hp).2.two_le)
  have hB : ∏ p ∈ (Nat.primesBelow N).filter (fun p => ¬ p < 10000), (1 + ap p) ≤
      Real.exp 0.1426 := by
    calc ∏ p ∈ (Nat.primesBelow N).filter (fun p => ¬ p < 10000), (1 + ap p)
        ≤ ∏ p ∈ (Nat.primesBelow N).filter (fun p => ¬ p < 10000), Real.exp (ap p) :=
          prod_le_prod₀ (fun p hp => by
            have := ap_nonneg (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le; linarith)
            fun p _ => by linarith [Real.add_one_le_exp (ap p)]
      _ = Real.exp (∑ p ∈ (Nat.primesBelow N).filter (fun p => ¬ p < 10000), ap p) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp 0.1426 := by
          refine Real.exp_le_exp.2 (le_trans (sum_le_sum_of_subset_of_nonneg ?_ ?_) (tail_ap_le N))
          · intro p hp
            simp only [mem_filter, Nat.mem_primesBelow, not_lt] at hp
            exact mem_Ico.2 ⟨hp.2, hp.1.1⟩
          · intro n hn _
            exact ap_nonneg (by have := (mem_Ico.1 hn).1; omega)
  have he : Real.exp 0.1426 ≤ 1 / (1 - 0.1426) :=
    Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have hA0 : 0 ≤ ∏ p ∈ (Nat.primesBelow N).filter (· < 10000), (1 + ap p) :=
    prod_nonneg fun p hp => by
      have := ap_nonneg (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le; linarith
  have hB0 : 0 ≤ ∏ p ∈ (Nat.primesBelow N).filter (fun p => ¬ p < 10000), (1 + ap p) :=
    prod_nonneg fun p hp => by
      have := ap_nonneg (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le; linarith
  calc _ ≤ 7.99 * Real.exp 0.1426 := mul_le_mul hA hB hB0 (by norm_num)
    _ ≤ 7.99 * (1 / (1 - 0.1426)) := by gcongr
    _ ≤ 9.32 := by norm_num

/-- `P = 9.32`: `∑_{d < N} |h(d)| d^{−2/3} ≤ 9.32`. -/
theorem sum_fR_le (N : ℕ) : ∑ d ∈ range N, fR d ≤ 9.32 := by
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖fR (p ^ n)‖) := by
    intro p hp
    refine summable_of_ne_finset_zero (s := range 3) fun e he => ?_
    simp only [mem_range, not_lt] at he
    simp [fR, hm_prime_pow_ge_three hp he]
  obtain ⟨-, hHas⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    fR_one (fun h => fR_mul h) hsum N
  have hval : ∏ p ∈ N.primesBelow, ∑' e, fR (p ^ e) = ∏ p ∈ N.primesBelow, (1 + ap p) :=
    prod_congr rfl fun p hp => tsum_fR_prime_pow (Nat.mem_primesBelow.1 hp).2
  rw [hval] at hHas
  -- the finite sum is part of the smooth-number sum
  have hsub : ∑ d ∈ range N, fR d = ∑ x ∈ (range N).subtype (· ∈ N.smoothNumbers), fR x := by
    rw [sum_subtype_eq_sum_filter, ← sum_filter_add_sum_filter_not (range N) (· ∈ N.smoothNumbers)]
    have : ∑ x ∈ (range N).filter (fun x => x ∉ N.smoothNumbers), fR x = 0 := by
      refine sum_eq_zero fun d hd => ?_
      simp only [mem_filter, mem_range, Nat.mem_smoothNumbers, not_and, not_forall] at hd
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · subst h0; simp [fR]
      · exfalso
        obtain ⟨p, hp, hpN⟩ := hd.2 hpos.ne'
        exact hpN (lt_of_le_of_lt (Nat.le_of_mem_primeFactorsList hp) hd.1)
    rw [this, add_zero]
  rw [hsub]
  exact (sum_le_hasSum (f := fun m : N.smoothNumbers => fR m) _ (fun x _ => fR_nonneg x) hHas).trans
    (prod_ap_le_all N)

theorem summable_fR : Summable fR :=
  summable_of_sum_range_le fR_nonneg sum_fR_le

theorem tsum_fR_le : ∑' d, fR d ≤ 9.32 :=
  Real.tsum_le_of_sum_range_le fR_nonneg sum_fR_le

/-! ### `∑ h(d)/d = 1` and the asymptotic formula -/

theorem hm_zero : hm 0 = 0 := by simp

theorem abs_hd_le (d : ℕ) : |hm d / d| ≤ fR d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp [fR]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < d), fR, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)

theorem summable_hd : Summable fun d : ℕ => hm d / d :=
  Summable.of_norm_bounded summable_fR fun d => by rw [Real.norm_eq_abs]; exact abs_hd_le d

/-- `log d ≤ (3/e) d^{1/3}`. -/
theorem log_le_rpow_third {x : ℝ} (hx : 0 < x) : Real.log x ≤ 3 / Real.exp 1 * x ^ ((1 / 3) : ℝ) := by
  have h3 : 0 < x ^ ((1 / 3) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos (x := x ^ ((1 / 3) : ℝ) / Real.exp 1) (by positivity)
  rw [Real.log_div h3.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_rpow hx] at h
  have : 3 / Real.exp 1 * x ^ ((1 / 3) : ℝ) = 3 * (x ^ ((1 / 3) : ℝ) / Real.exp 1) := by ring
  rw [this]; linarith

theorem abs_hlog_le (d : ℕ) : |hm d * Real.log d / d| ≤ 3 / Real.exp 1 * fR d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp [fR]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast h
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h
  have hlog0 : 0 ≤ Real.log d := Real.log_nonneg hd1
  rw [abs_div, abs_mul, abs_of_nonneg hlog0, abs_of_pos hd0, fR]
  have hl := log_le_rpow_third hd0
  have e : (d : ℝ) ^ (-(2 / 3) : ℝ) = (d : ℝ) ^ ((1 / 3) : ℝ) / d := by
    rw [eq_div_iff hd0.ne', ← Real.rpow_add_one hd0.ne']; norm_num
  rw [e]
  have : |hm d| * Real.log d / d ≤ |hm d| * (3 / Real.exp 1 * (d : ℝ) ^ ((1 / 3) : ℝ)) / d :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (abs_nonneg _)) hd0.le
  refine this.trans (le_of_eq ?_); ring

theorem summable_hlog : Summable fun d : ℕ => hm d * Real.log d / d :=
  Summable.of_norm_bounded (summable_fR.mul_left (3 / Real.exp 1)) fun d => by
    rw [Real.norm_eq_abs]; exact abs_hlog_le d

/-- **`∑ h(d)/d = 1`** (Euler product: each local factor is `1 + h(p)/p + h(p²)/p² = 1`). -/
theorem tsum_hd : ∑' d : ℕ, hm d / d = 1 := by
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → hm (m * n) / ((m * n : ℕ) : ℝ) =
      hm m / m * (hm n / n) := by
    intro m n h
    rw [isMultiplicative_hm.map_mul_of_coprime h]; push_cast; ring
  have h := EulerProduct.eulerProduct_tprod (f := fun d : ℕ => hm d / d) (by simp [hm_one]) hmul
    summable_hd.norm (by simp)
  rw [← h]
  have hfac : ∀ p : Nat.Primes, ∑' e : ℕ, hm ((p : ℕ) ^ e) / ((p : ℕ) ^ e : ℕ) = 1 := by
    intro p
    have hp := p.2
    have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hp.one_lt
    rw [tsum_eq_sum (s := range 3) fun e he => by
      simp only [mem_range, not_lt] at he
      simp [hm_prime_pow_ge_three hp he]]
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, hm_one, pow_one,
      hm_prime hp, hm_prime_sq hp]
    have : ((p : ℕ) : ℝ) - 1 ≠ 0 := by linarith
    push_cast
    field_simp; ring
  simp only [hfac, tprod_one]

/-- `A = ∑ h(d) log d / d` and `κ = γ − A`. -/
noncomputable def kappa : ℝ := eulerMascheroniConstant - ∑' d : ℕ, hm d * Real.log d / d

/-- The tail `∑_{d > N} f(d)` is at most `P`. -/
theorem tsum_fR_tail_le (N : ℕ) : ∑' i, fR (i + N) ≤ 9.32 := by
  have h := summable_fR.sum_add_tsum_nat_add N
  have h0 : 0 ≤ ∑ i ∈ range N, fR i := sum_nonneg fun i _ => fR_nonneg i
  linarith [tsum_fR_le]

/-- (i) The harmonic-sum errors: `|∑_{d≤N} (h(d)/d)(H(N/d) − log(N/d) − γ)| ≤ 2 P N^{−1/3}`. -/
theorem harmonic_err_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ d ∈ Ioc 0 N, hm d / d * (Hs (N / d) - Real.log ((N : ℝ) / d) - eulerMascheroniConstant)| ≤
      2 * 9.32 * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNm0 : 0 < (N : ℝ) ^ (-(1 / 3) : ℝ) := by positivity
  have hpt : ∀ d ∈ Ioc 0 N, |hm d / d * (Hs (N / d) - Real.log ((N : ℝ) / d) - eulerMascheroniConstant)|
      ≤ fR d * (2 * (N : ℝ) ^ (-(1 / 3) : ℝ)) := by
    intro d hd
    have hd1 := (mem_Ioc.1 hd).1
    have hdN := (mem_Ioc.1 hd).2
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hH := Hs_div_sub_log hd1 hdN
    have h23 : (d : ℝ) ^ ((2 / 3) : ℝ) ≤ (N : ℝ) ^ ((2 / 3) : ℝ) :=
      Real.rpow_le_rpow hd0.le (by exact_mod_cast hdN) (by norm_num)
    have e1 : |hm d| = fR d * (d : ℝ) ^ ((2 / 3) : ℝ) := by
      rw [fR, mul_assoc, ← Real.rpow_add hd0]; norm_num
    have e2 : (N : ℝ) ^ ((2 / 3) : ℝ) = (N : ℝ) ^ (-(1 / 3) : ℝ) * N := by
      rw [← Real.rpow_add_one hN0.ne']; norm_num
    have hkey : |hm d| ≤ fR d * (N : ℝ) ^ (-(1 / 3) : ℝ) * N := by
      rw [e1, mul_assoc, ← e2]; exact mul_le_mul_of_nonneg_left h23 (fR_nonneg d)
    rw [abs_mul, abs_div, abs_of_pos hd0]
    calc |hm d| / d * |Hs (N / d) - Real.log ((N : ℝ) / d) - eulerMascheroniConstant|
        ≤ |hm d| / d * (2 * d / N) := mul_le_mul_of_nonneg_left hH (by positivity)
      _ = 2 * |hm d| / N := by field_simp
      _ ≤ 2 * (fR d * (N : ℝ) ^ (-(1 / 3) : ℝ) * N) / N := by
          gcongr
      _ = fR d * (2 * (N : ℝ) ^ (-(1 / 3) : ℝ)) := by field_simp
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hpt).trans ?_)
  rw [← sum_mul]
  have hs : ∑ d ∈ Ioc 0 N, fR d ≤ 9.32 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => fR_nonneg i) (sum_fR_le (N + 1))
    intro d hd; simp only [mem_Ioc, mem_range] at hd ⊢; omega
  have := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ (-(1 / 3) : ℝ))
  linarith

/-- `∑_{d ∈ (0, N]} f(d) = ∑_{d < N + 1} f(d)` when `f(0) = 0`. -/
theorem sum_Ioc_eq_range (N : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    ∑ d ∈ Ioc 0 N, f d = ∑ d ∈ range (N + 1), f d := by
  rw [range_eq_Ico, show Ico 0 (N + 1) = insert 0 (Ioc 0 N) by ext x; simp,
    sum_insert (by simp), hf0, zero_add]

/-- (ii) The main term:
`∑_{d≤N} (h(d)/d)(log N − log d + γ) = log N + κ − ∑_{d>N} (h(d)/d)(log N + γ − log d)`. -/
theorem main_term_eq (N : ℕ) :
    ∑ d ∈ Ioc 0 N, hm d / d * (Real.log N - Real.log d + eulerMascheroniConstant) =
      Real.log N + kappa - ∑' i, hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) *
        (Real.log N + eulerMascheroniConstant - Real.log ((i + (N + 1) : ℕ) : ℝ)) := by
  set γ := eulerMascheroniConstant
  have hsu := summable_hd
  have hsv := summable_hlog
  have hsplit_u := hsu.sum_add_tsum_nat_add (N + 1)
  have hsplit_v := hsv.sum_add_tsum_nat_add (N + 1)
  have e1 : ∑ d ∈ Ioc 0 N, hm d / d * (Real.log N - Real.log d + γ) =
      (Real.log N + γ) * ∑ d ∈ Ioc 0 N, hm d / (d : ℝ) -
        ∑ d ∈ Ioc 0 N, hm d * Real.log d / (d : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by ring
  have e2 : ∑ d ∈ Ioc 0 N, hm d / (d : ℝ) =
      1 - ∑' i, hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) := by
    rw [sum_Ioc_eq_range N (fun d => hm d / (d : ℝ)) (by simp), ← tsum_hd]; linarith
  have e3 : ∑ d ∈ Ioc 0 N, hm d * Real.log d / (d : ℝ) =
      (∑' d : ℕ, hm d * Real.log d / d) -
        ∑' i, hm (i + (N + 1)) * Real.log ((i + (N + 1) : ℕ) : ℝ) / ((i + (N + 1) : ℕ) : ℝ) := by
    rw [sum_Ioc_eq_range N (fun d => hm d * Real.log d / (d : ℝ)) (by simp)]; linarith
  have hsu' := (summable_nat_add_iff (N + 1)).2 hsu
  have hsv' := (summable_nat_add_iff (N + 1)).2 hsv
  have e4 : ∑' i, hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) *
        (Real.log N + γ - Real.log ((i + (N + 1) : ℕ) : ℝ)) =
      (Real.log N + γ) * ∑' i, hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) -
        ∑' i, hm (i + (N + 1)) * Real.log ((i + (N + 1) : ℕ) : ℝ) / ((i + (N + 1) : ℕ) : ℝ) := by
    rw [← tsum_mul_left, ← (hsu'.mul_left _).tsum_sub hsv']
    exact tsum_congr fun i => by ring
  rw [e1, e2, e3, e4, kappa]; ring

/-- A pointwise bound for the tail: for `d > N ≥ 1`,
`|(h(d)/d)(log N + γ − log d)| ≤ (3/e + γ) N^{−1/3} f(d)`. -/
theorem tail_term_le {N d : ℕ} (hN : 1 ≤ N) (hdN : N < d) :
    |hm d / d * (Real.log N + eulerMascheroniConstant - Real.log d)| ≤
      (3 / Real.exp 1 + eulerMascheroniConstant) * (N : ℝ) ^ (-(1 / 3) : ℝ) * fR d := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le N) hdN)
  have hdN' : (N : ℝ) < d := by exact_mod_cast hdN
  have hγ0 : 0 < eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  have hr : 1 ≤ (d : ℝ) / N := by rw [le_div_iff₀ hN0]; linarith
  set t := ((d : ℝ) / N) ^ ((1 / 3) : ℝ) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hr (by norm_num)
  have hl0 : 0 ≤ Real.log ((d : ℝ) / N) := Real.log_nonneg hr
  have hl : Real.log ((d : ℝ) / N) ≤ 3 / Real.exp 1 * t := log_le_rpow_third (by positivity)
  have hγt : eulerMascheroniConstant ≤ eulerMascheroniConstant * t := le_mul_of_one_le_right hγ0.le ht1
  have he : 0 ≤ 3 / Real.exp 1 * t := by positivity
  have hlog : |Real.log N + eulerMascheroniConstant - Real.log d| ≤
      (3 / Real.exp 1 + eulerMascheroniConstant) * t := by
    have e : Real.log N + eulerMascheroniConstant - Real.log d =
        eulerMascheroniConstant - Real.log ((d : ℝ) / N) := by
      rw [Real.log_div hd0.ne' hN0.ne']; ring
    rw [e, abs_le]
    constructor <;> nlinarith only [hl0, hl, hγt, he, hγ0]
  have hfR : |hm d / d| * t = fR d * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
    rw [abs_div, abs_of_pos hd0, fR, ht, Real.div_rpow hd0.le hN0.le]
    have e1 : (d : ℝ) ^ (-(2 / 3) : ℝ) = (d : ℝ) ^ ((1 / 3) : ℝ) / d := by
      rw [eq_div_iff hd0.ne', ← Real.rpow_add_one hd0.ne']; norm_num
    have e2 : (N : ℝ) ^ (-(1 / 3) : ℝ) = 1 / (N : ℝ) ^ ((1 / 3) : ℝ) := by
      rw [Real.rpow_neg hN0.le, inv_eq_one_div]
    have : (N : ℝ) ^ ((1 / 3) : ℝ) ≠ 0 := by positivity
    rw [e1, e2]; field_simp
  rw [abs_mul]
  calc |hm d / d| * |Real.log N + eulerMascheroniConstant - Real.log d|
      ≤ |hm d / d| * ((3 / Real.exp 1 + eulerMascheroniConstant) * t) :=
        mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    _ = (3 / Real.exp 1 + eulerMascheroniConstant) * (|hm d / d| * t) := by ring
    _ = _ := by rw [hfR]; ring

/-- (iii) The tail: `|∑_{d>N} (h(d)/d)(log N + γ − log d)| ≤ (3/e + γ) P N^{−1/3}`. -/
theorem tail_le {N : ℕ} (hN : 1 ≤ N) :
    |∑' i, hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) *
        (Real.log N + eulerMascheroniConstant - Real.log ((i + (N + 1) : ℕ) : ℝ))| ≤
      (3 / Real.exp 1 + eulerMascheroniConstant) * 9.32 * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
  set c := (3 / Real.exp 1 + eulerMascheroniConstant) * (N : ℝ) ^ (-(1 / 3) : ℝ)
  have hc : 0 ≤ c := by
    have := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) Real.one_half_lt_eulerMascheroniConstant
    positivity
  have hpt : ∀ i : ℕ, |hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) *
      (Real.log N + eulerMascheroniConstant - Real.log ((i + (N + 1) : ℕ) : ℝ))| ≤
      c * fR (i + (N + 1)) := fun i => tail_term_le hN (by omega)
  have hsfR := (summable_nat_add_iff (N + 1)).2 summable_fR
  have hsabs := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpt (hsfR.mul_left c)
  calc _ ≤ ∑' i, |hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) *
          (Real.log N + eulerMascheroniConstant - Real.log ((i + (N + 1) : ℕ) : ℝ))| := by
        have := norm_tsum_le_tsum_norm (f := fun i : ℕ => hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) *
          (Real.log N + eulerMascheroniConstant - Real.log ((i + (N + 1) : ℕ) : ℝ)))
          (by simpa only [Real.norm_eq_abs] using hsabs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' i, c * fR (i + (N + 1)) := hsabs.tsum_le_tsum hpt (hsfR.mul_left c)
    _ = c * ∑' i, fR (i + (N + 1)) := tsum_mul_left
    _ ≤ c * 9.32 := mul_le_mul_of_nonneg_left (tsum_fR_tail_le (N + 1)) hc
    _ = _ := by ring

/-- **`|G(N) − log N − κ| ≤ (2 + 3/e + γ) P N^{−1/3}`**, `P = 9.32`. -/
theorem GS_asymp {N : ℕ} (hN : 1 ≤ N) :
    |GS N - Real.log N - kappa| ≤
      (2 + 3 / Real.exp 1 + eulerMascheroniConstant) * 9.32 * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hG : GS N = ∑ d ∈ Ioc 0 N, hm d / d * (Real.log N - Real.log d + eulerMascheroniConstant) +
      ∑ d ∈ Ioc 0 N, hm d / d * (Hs (N / d) - Real.log ((N : ℝ) / d) - eulerMascheroniConstant) := by
    rw [GS_eq, ← sum_add_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
    rw [Real.log_div hN0.ne' hd0.ne']; ring
  rw [hG, main_term_eq N]
  have h1 := harmonic_err_le hN
  have h2 := tail_le hN
  set E1 := ∑ d ∈ Ioc 0 N, hm d / d * (Hs (N / d) - Real.log ((N : ℝ) / d) - eulerMascheroniConstant)
  set E2 := ∑' i, hm (i + (N + 1)) / ((i + (N + 1) : ℕ) : ℝ) *
    (Real.log N + eulerMascheroniConstant - Real.log ((i + (N + 1) : ℕ) : ℝ))
  have e : Real.log N + kappa - E2 + E1 - Real.log N - kappa = E1 - E2 := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

/-! ### Lemma 7 and Lemma 8 -/

/-- `G(r)` as Ramaré's `G_1(r)`. -/
theorem GS_eq_GqP (r : ℕ) : GS r = TernaryGoldbach.Prelim.GqP 1 r := by
  unfold GS TernaryGoldbach.Prelim.GqP
  rw [Nat.floor_natCast, filter_true_of_mem (fun x _ => Nat.coprime_one_right x)]
  refine sum_congr rfl fun n _ => ?_
  unfold gS
  have h := ArithmeticFunction.moebius_sq (n := n)
  have h' : ((μ n : ℝ)) ^ 2 = if Squarefree n then 1 else 0 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this; rw [this]
  rw [h']; split_ifs <;> simp

/-- **[MV73, Lemma 7]**: `G(r) ≥ log r + 1.07` for `r ≥ 6`. -/
theorem lemma7 (r : ℕ) (h6 : 6 ≤ r) : Real.log r + 1.07 ≤ GS r := by
  rcases lt_or_ge r 21400 with hr | hr
  · exact TernaryGoldbach.Prelim.SmallG.lemma7_small r h6 hr
  obtain ⟨c, hc1, -, hram⟩ := TernaryGoldbach.Prelim.ramare_Gq
  have hr' : (21400 : ℝ) ≤ r := by exact_mod_cast hr
  have h := (abs_le.1 (hram 1 le_rfl r (by linarith))).1
  have hS : TernaryGoldbach.Prelim.SqP 1 = 0 := by simp [TernaryGoldbach.Prelim.SqP]
  have hf : TernaryGoldbach.Prelim.f1qP 1 = 1 := by simp [TernaryGoldbach.Prelim.f1qP]
  rw [hS, hf] at h
  simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul, mul_one, add_zero] at h
  -- `r^{−1/3} ≤ 1/27.75`
  have h3 : (27.75 : ℝ) ≤ (r : ℝ) ^ (1 / 3 : ℝ) := by
    calc (27.75 : ℝ) = ((27.75 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (r : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
  have h4 : (r : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 / 27.75 := by
    rw [Real.rpow_neg (by positivity), ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  rw [GS_eq_GqP]
  nlinarith

/-- **[MV73, Lemma 8]** (with kernel checks for `R < 1000`): for `R ≥ 2`,
`∑_{r ≤ R} (1 + r/R)⁻¹ μ(r)²/φ(r) > log R + 0.25068`. -/
theorem lemma8 {R : ℝ} (hR : 2 ≤ R) : Real.log R + 0.25068 ≤ WR R := by
  rcases lt_or_ge R 6 with h | h
  · exact (lemma8_tiny hR h).le
  rcases lt_or_ge R 1000 with h' | h'
  · exact (TernaryGoldbach.Prelim.SmallW.lemma8_mid h h').le
  · exact lemma8_large lemma7 h'

end TernaryGoldbach.Prelim.MV
