import Mathlib

/-!
# [B, (2.20)]: `|∑_{n ≤ x, (n, q) = 1} μ(n)/n| ≤ 1`

The elementary proof. Let `f(d) = μ(d)·[(d, q) = 1]` and `g = f ∗ 1`. Then `g(n) ∈ {0, 1}`
(it is multiplicative, and `g(p^k) = 1 + f(p)`), and `g(n) = 0` for `n ≥ 2` coprime to `q`
(where `g = μ ∗ 1`). With `N = ⌊x⌋`, `∑_{n ≤ N} g(n) = ∑_{n ≤ N} f(n) ⌊N/n⌋`, so
`N · ∑ f(n)/n = ∑_{n ≤ N} (g(n) + f(n) {N/n})`, and each term lies in `[-1, 1]`.
-/

open Finset
open ArithmeticFunction (moebius IsMultiplicative)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim

/-- `μ(n)·[(n, q) = 1]`. -/
def muCop (q : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n.Coprime q then μ n else 0, by simp⟩

theorem muCop_apply (q n : ℕ) : muCop q n = if n.Coprime q then μ n else 0 := rfl

theorem isMultiplicative_muCop (q : ℕ) : IsMultiplicative (muCop q) := by
  refine ⟨by simp [muCop_apply], fun {m n} hmn => ?_⟩
  simp only [muCop_apply, Nat.coprime_mul_iff_left]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
  split_ifs <;> simp_all

/-- `g = muCop q ∗ 1`. -/
noncomputable def gCop (q : ℕ) : ArithmeticFunction ℤ := muCop q * (ζ : ArithmeticFunction ℤ)

theorem isMultiplicative_gCop (q : ℕ) : IsMultiplicative (gCop q) :=
  (isMultiplicative_muCop q).mul ArithmeticFunction.isMultiplicative_zeta.natCast

theorem gCop_prime_pow (q : ℕ) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    gCop q (p ^ k) = 1 + muCop q p := by
  rw [gCop, ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
    sum_range_succ']
  have hterm : ∀ i ∈ range k, muCop q (p ^ (i + 1)) = if i = 0 then muCop q p else 0 := by
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · simp only [muCop_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega : i + 1 ≠ 0)]
      simp [show i ≠ 0 by omega]
  rw [sum_congr rfl hterm, sum_ite_eq' (range k) 0, if_pos (mem_range.2 hk)]
  simp [muCop_apply, add_comm]

theorem gCop_zero_or_one (q n : ℕ) : gCop q n = 0 ∨ gCop q n = 1 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => left; simp
  | one => right; exact (isMultiplicative_gCop q).map_one
  | prime_pow p k hp hk =>
    rw [gCop_prime_pow q hp hk, muCop_apply]
    split_ifs
    · left; rw [ArithmeticFunction.moebius_apply_prime hp]; ring
    · right; ring
  | coprime a b _ _ hab ha hb =>
    rw [(isMultiplicative_gCop q).map_mul_of_coprime hab]
    rcases ha with h | h <;> rcases hb with h' | h' <;> simp [h, h']

theorem gCop_of_coprime {q n : ℕ} (hn : n.Coprime q) : gCop q n = if n = 1 then 1 else 0 := by
  have h : gCop q n = (μ * (ζ : ArithmeticFunction ℤ)) n := by
    rw [gCop, ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_mul_zeta_apply]
    refine sum_congr rfl fun d hd => ?_
    rw [muCop_apply, if_pos (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd) hn)]
  rw [h, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- **[B, (2.20)]** (Granville–Ramaré [GR96, Lemma 10.2]):
`|∑_{n ≤ x, (n, q) = 1} μ(n)/n| ≤ 1` for all `x` and all `q ≥ 1`. -/
theorem abs_sum_moebius_div_coprime_le_one (x : ℝ) {q : ℕ} (_hq : 1 ≤ q) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤ 1 := by
  set N := ⌊x⌋₊
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hIcc : Icc 1 N = Ioc 0 N := Finset.Icc_succ_left_eq_Ioc 0 N
  -- `fr n = N/n - ⌊N/n⌋`.
  set fr : ℕ → ℝ := fun n => (N : ℝ) / n - ((N / n : ℕ) : ℝ) with hfr
  have hfr_bd : ∀ n ∈ Ioc 0 N, 0 ≤ fr n ∧ fr n < 1 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
    have hdm := Nat.div_add_mod N n
    have hmod := Nat.mod_lt N (mem_Ioc.1 hn).1
    have hN' : (N : ℝ) = n * ((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) := by exact_mod_cast hdm.symm
    have hmod' : ((N % n : ℕ) : ℝ) < n := by exact_mod_cast hmod
    have : fr n = ((N % n : ℕ) : ℝ) / n := by
      simp only [hfr]; rw [hN']; field_simp; ring
    rw [this]
    exact ⟨by positivity, (div_lt_one hn0).2 hmod'⟩
  have hfr1 : fr 1 = 0 := by simp [hfr]
  -- The identity `∑ g = ∑ f ⌊N/n⌋`.
  have hid : ∑ n ∈ Ioc 0 N, (gCop q n : ℝ) = ∑ n ∈ Ioc 0 N, (muCop q n : ℝ) * ((N / n : ℕ) : ℝ) := by
    have := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (muCop q) N
    rw [← gCop] at this
    have h := congrArg (Int.cast : ℤ → ℝ) this
    push_cast at h
    exact h
  -- `N · S = ∑ (g n + f n · fr n)`.
  have hS : (N : ℝ) * ∑ n ∈ Icc 1 N, (if Nat.Coprime n q then (μ n : ℝ) / n else 0) =
      ∑ n ∈ Ioc 0 N, ((gCop q n : ℝ) + (muCop q n : ℝ) * fr n) := by
    rw [sum_add_distrib, hid, ← sum_add_distrib, hIcc, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.1 hn).1.ne'
    simp only [hfr, muCop_apply]
    split_ifs <;> push_cast <;> field_simp <;> ring
  -- Each term is in `[-1, 1]`.
  have hterm : ∀ n ∈ Ioc 0 N, |(gCop q n : ℝ) + (muCop q n : ℝ) * fr n| ≤ 1 := by
    intro n hn
    obtain ⟨h0, h1⟩ := hfr_bd n hn
    by_cases hc : n.Coprime q
    · by_cases hn1 : n = 1
      · subst hn1; rw [hfr1]; simp [(isMultiplicative_gCop q).map_one]
      · rw [gCop_of_coprime hc, if_neg hn1, muCop_apply, if_pos hc]
        have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        push_cast
        rw [zero_add, abs_mul, abs_of_nonneg h0]
        nlinarith [abs_nonneg (μ n : ℝ)]
    · rw [muCop_apply, if_neg hc]
      rcases gCop_zero_or_one q n with h | h <;> simp [h]
  have hbound : |(N : ℝ) * ∑ n ∈ Icc 1 N, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤ N := by
    rw [hS]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum hterm).trans ?_
    simp
  rw [abs_mul, abs_of_pos hNr] at hbound
  exact le_of_mul_le_mul_left (by linarith) hNr

end TernaryGoldbach.Prelim
