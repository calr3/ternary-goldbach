import TernaryGoldbach.Prelim.MoebiusLog
import TernaryGoldbach.Prelim.Mcheck

/-!
# [H, (2.23)]: from the coprime sum to the plain one

`m̌(x) = ∑_{n ≤ x} μ(n)/n · log(x/n)`. Ramaré's reduction ([Ramb, Lemma 1.9, Cor. 1.10]):
`μ · 1_{(·,q)=1} = c_q * μ`, where `c_q` is the indicator of the `q`-factored numbers (those whose
prime factors all divide `q`; `MoebiusLog.cq`). Hence

  `∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n) = ∑_{a ≤ x, a q-factored} m̌(x/a)/a`,

and, since `∑_{a q-factored} 1/a = q/φ(q)`, a bound `|m̌(y)| ≤ C` for all `y ≥ 1` gives
`|∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n)| ≤ C q/φ(q)`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim

/-- Summing over the divisor pairs of each `n ≤ N` is summing over the pairs `(a, k)` with
`a k ≤ N`. -/
theorem sum_Ioc_sum_divisorsAntidiagonal (F : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ a ∈ Ioc 0 N, ∑ k ∈ Ioc 0 (N / a), F a k := by
  have h1 : ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, F x.1 x.2 := by
    trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, F x.1 x.2
    · refine sum_congr rfl fun n hn => ?_
      simp only [mem_Ioc] at hn
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
    · simp_rw [sum_filter]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => (by simp_all)
  rw [h1, sum_filter, sum_product]
  refine sum_congr rfl fun a ha => ?_
  have ha0 : 0 < a := (mem_Ioc.1 ha).1
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hk0, _⟩, hk⟩
    exact ⟨hk0, (Nat.le_div_iff_mul_le ha0).2 (by rwa [mul_comm])⟩
  · rintro ⟨hk0, hk⟩
    have := (Nat.le_div_iff_mul_le ha0).1 hk
    refine ⟨⟨hk0, le_trans hk (Nat.div_le_self _ _)⟩, by rwa [mul_comm]⟩

/-- `c_q` is the indicator of the `q`-factored numbers. -/
theorem cq_apply_eq {q k : ℕ} (hq : q ≠ 0) (hk : k ≠ 0) :
    cq q k = if k ∈ Nat.factoredNumbers q.primeFactors then 1 else 0 := by
  rcases cq_cases hq hk with ⟨h, hm⟩ | h
  · rw [h, ite_eq_left hm]
  · rw [h]
    split_ifs with hm
    · exfalso
      rw [(cq_mult q).multiplicative_factorization (cq q) hk, Finsupp.prod] at h
      obtain ⟨p, hp, hp0⟩ := prod_eq_zero_iff.1 h
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
      have hpk : p ∣ k := Nat.dvd_of_mem_primeFactors (by simpa using hp)
      rw [cq_prime_pow hpp (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp))] at hp0
      have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors ((Nat.mem_factoredNumbers'.1 hm) p hpp hpk)
      exact one_ne_zero (by rwa [ite_eq_left hpq] at hp0)
    · rfl

/-- `μ_q = c_q * μ`. -/
theorem cq_mul_moebius (q : ℕ) : cq q * (μ : ArithmeticFunction ℝ) = muq q := by
  rw [cq, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

/-- **The reduction** [Ramb, Lemma 1.9]: `∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n) =
∑_{a ≤ x} c_q(a)/a · m̌(x/a)`. -/
theorem sum_coprime_log_eq (x : ℝ) (q : ℕ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0) =
      ∑ a ∈ Icc 1 ⌊x⌋₊, cq q a / a * mcheck (x / a) := by
  set N := ⌊x⌋₊
  have hIcc : ∀ m, Icc 1 m = Ioc 0 m := fun m => rfl
  set F : ℕ → ℕ → ℝ := fun a k => cq q a / a * ((μ k : ℝ) / k * Real.log (x / a / k)) with hF
  -- each term on the left is a sum over the divisor pairs of `n`
  have hL : ∀ n ∈ Ioc 0 N, (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0) =
      ∑ y ∈ n.divisorsAntidiagonal, F y.1 y.2 := by
    intro n hn
    have hn0 : n ≠ 0 := (mem_Ioc.1 hn).1.ne'
    have hterm : ∀ y ∈ n.divisorsAntidiagonal,
        F y.1 y.2 = cq q y.1 * (μ y.2 : ℝ) * (Real.log (x / n) / n) := by
      intro y hy
      obtain ⟨hyn, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
      have h1 : (y.1 : ℝ) ≠ 0 := by
        have : y.1 ≠ 0 := fun h => hn0 (by rw [← hyn, h, zero_mul])
        exact_mod_cast this
      have h2 : (y.2 : ℝ) ≠ 0 := by
        have : y.2 ≠ 0 := fun h => hn0 (by rw [← hyn, h, mul_zero])
        exact_mod_cast this
      have hn : (n : ℝ) = y.1 * y.2 := by exact_mod_cast hyn.symm
      simp only [hF]
      rw [hn, div_div]
      field_simp
    rw [sum_congr rfl hterm, ← sum_mul]
    have hconv : ∑ y ∈ n.divisorsAntidiagonal, cq q y.1 * (μ y.2 : ℝ) = muq q n := by
      rw [← cq_mul_moebius, mul_apply]
      rfl
    rw [hconv]
    simp only [muq, pmul_apply, intCoe_apply, chiq_apply, ne_eq, hn0, not_false_eq_true, true_and]
    split_ifs <;> ring
  rw [hIcc, sum_congr rfl hL, sum_Ioc_sum_divisorsAntidiagonal F N]
  refine sum_congr rfl fun a ha => ?_
  rw [mcheck, Nat.floor_div_natCast, hIcc, mul_sum]

/-- **[H, (2.23)] from a bound on `m̌`** [Ramb, Cor. 1.10]: if `|m̌(y)| ≤ C` for all `y ≥ 1`, then
`|∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n)| ≤ C q/φ(q)`. -/
theorem abs_sum_coprime_log_le_of_mcheck {C : ℝ} (hC : ∀ y : ℝ, 1 ≤ y → |mcheck y| ≤ C)
    {x : ℝ} (hx : 0 < x) {q : ℕ} (hq : 1 ≤ q) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0)| ≤
      C * (q / Nat.totient q) := by
  set N := ⌊x⌋₊
  have hq0 : q ≠ 0 := by omega
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1 le_rfl)
  rw [sum_coprime_log_eq x q]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ a ∈ Icc 1 N, |cq q a / a * mcheck (x / a)| ≤
      C * (if a ∈ Nat.factoredNumbers q.primeFactors then (a : ℝ)⁻¹ else 0) := by
    intro a ha
    have ha1 : 1 ≤ a := (mem_Icc.1 ha).1
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hy : 1 ≤ x / a := by
      rw [le_div_iff₀ ha0, one_mul]
      exact le_trans (by exact_mod_cast (mem_Icc.1 ha).2) (Nat.floor_le hx.le)
    rw [cq_apply_eq hq0 (by omega)]
    split_ifs
    · rw [abs_mul, one_div, abs_inv, abs_of_pos ha0, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _ hy) (by positivity)
    · simp
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  rw [← sum_filter]
  exact sum_factored_le hq N

end TernaryGoldbach.Prelim
