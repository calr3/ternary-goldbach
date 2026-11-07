import TernaryGoldbach.Prelim.LambdaMu

/-!
# Sums of `Λ(v)·(q,v)` [H, §6.2.2]

The elementary bounds behind [H, (6.9)] and the bound for `∑ Λ(v) v (v,q)` in §6.2.2:
* `∑_{v ≤ N} Λ(v)(q,v)/v ≤ log N + log q` (so `∑ Λ(v)/(v q_v) ≤ log(Nq)/q`, (6.9));
* `∑_{v ≤ N} Λ(v) v (q,v) ≤ ∑_{v ≤ N} Λ(v) v + N q log q`.

We write `(q,v) = ∑_{d | (q,v)} φ(d)`; for `d = p^j > 1`, the `v = p^α` divisible by `d`
give a geometric series, and `φ(p^j) ∑_{α ≥ j} log p/p^α = log p = Λ(d)`.
-/

open Real Finset
open ArithmeticFunction (vonMangoldt)
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

/-- `∑_{v ∈ s} f(v)(q,v) = ∑_{d | q} φ(d) ∑_{v ∈ s, d | v} f(v)`. -/
theorem sum_mul_gcd_eq {q : ℕ} (hq : q ≠ 0) (s : Finset ℕ) (f : ℕ → ℝ) :
    ∑ v ∈ s, f v * (Nat.gcd q v : ℝ) =
      ∑ d ∈ q.divisors, (Nat.totient d : ℝ) * ∑ v ∈ s with d ∣ v, f v := by
  have h1 : ∀ v, (Nat.gcd q v : ℝ) = ∑ d ∈ q.divisors, if d ∣ v then (Nat.totient d : ℝ) else 0 := by
    intro v
    have hg : Nat.gcd q v ≠ 0 := Nat.gcd_ne_zero_left hq
    rw [← sum_filter, ← Nat.sum_totient (Nat.gcd q v)]
    push_cast
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    tauto
  simp_rw [h1, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_filter]
  refine sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

/-- Only the prime powers `v = p^α`, `j ≤ α`, contribute to `∑_{v ≤ N, p^j | v} Λ(v) g(v)`. -/
theorem sum_vonMangoldt_pow_dvd_le {p j N : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) :
    ∑ v ∈ Icc 1 N with p ^ j ∣ v, (Λ v : ℝ) * g v ≤
      Real.log p * ∑ α ∈ Icc j (Nat.log p N), g (p ^ α) := by
  rw [← sum_filter_ne_zero]
  have hsub : {v ∈ {v ∈ Icc 1 N | p ^ j ∣ v} | (Λ v : ℝ) * g v ≠ 0} ⊆
      (Icc j (Nat.log p N)).image (p ^ ·) := by
    intro v hv
    simp only [mem_filter, mem_Icc] at hv
    obtain ⟨⟨⟨hv1, hvN⟩, hdv⟩, hne⟩ := hv
    have hΛ : (Λ v : ℝ) ≠ 0 := left_ne_zero_of_mul hne
    obtain ⟨r, k, hr, hk, rfl⟩ := isPrimePow_nat_iff _ |>.1
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).1
      (hp.dvd_of_dvd_pow ((dvd_pow_self p (by omega)).trans hdv))
    subst hpr
    refine mem_image.2 ⟨k, mem_Icc.2 ⟨(Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdv,
      Nat.le_log_of_pow_le hp.one_lt hvN⟩, rfl⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub fun v _ _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hg v)).trans (le_of_eq ?_)
  rw [sum_image (fun a _ b _ h => Nat.pow_right_injective hp.two_le h), mul_sum]
  refine sum_congr rfl fun α hα => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by have := (mem_Icc.1 hα).1; omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- For `d ≠ 1` that is not a prime power, no `v` with `Λ(v) ≠ 0` is divisible by `d`. -/
theorem sum_vonMangoldt_dvd_eq_zero {d : ℕ} (hd : d ≠ 1) (hpp : ¬IsPrimePow d) (s : Finset ℕ)
    (g : ℕ → ℝ) : ∑ v ∈ s with d ∣ v, (Λ v : ℝ) * g v = 0 := by
  refine sum_eq_zero fun v hv => ?_
  have hdv := (mem_filter.1 hv).2
  by_cases h : IsPrimePow v
  · exact absurd (h.dvd hdv hd) hpp
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 h, zero_mul]

/-- `φ(d) ∑_{v ≤ N, d | v} Λ(v)/v ≤ Λ(d)` for `d ≠ 1`. -/
theorem totient_mul_sum_vonMangoldt_div_le {d : ℕ} (hd : d ≠ 1) (N : ℕ) :
    (Nat.totient d : ℝ) * ∑ v ∈ Icc 1 N with d ∣ v, (Λ v : ℝ) * (1 / v) ≤ Λ d := by
  by_cases hpp : IsPrimePow d
  · obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hS := sum_vonMangoldt_pow_dvd_le hp hj (fun v => 1 / (v : ℝ)) (fun n => by positivity) (N := N)
    have hgeo : ∑ α ∈ Icc j (Nat.log p N), 1 / ((p ^ α : ℕ) : ℝ) ≤ (p : ℝ)⁻¹ ^ j / (1 - (p : ℝ)⁻¹) := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      convert geom_sum_Ico_le_of_lt_one (x := (p : ℝ)⁻¹) (m := j) (n := Nat.log p N + 1)
        (by positivity) (inv_lt_one_of_one_lt₀ hp1) using 1
      refine sum_congr rfl fun α _ => ?_
      push_cast; rw [inv_pow, one_div]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.totient_prime_pow hp hj]
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    have hphi : (0 : ℝ) ≤ ((p ^ (j - 1) * (p - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((p ^ (j - 1) * (p - 1) : ℕ) : ℝ) * ∑ v ∈ Icc 1 N with p ^ j ∣ v, (Λ v : ℝ) * (1 / v)
        ≤ ((p ^ (j - 1) * (p - 1) : ℕ) : ℝ) * (Real.log p * ((p : ℝ)⁻¹ ^ j / (1 - (p : ℝ)⁻¹))) :=
          mul_le_mul_of_nonneg_left (hS.trans (mul_le_mul_of_nonneg_left hgeo hlog)) hphi
      _ = Real.log p := by
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
          obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          rw [Nat.add_sub_cancel, inv_pow, pow_succ]
          have hp' : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp
  · rw [sum_vonMangoldt_dvd_eq_zero hd hpp, mul_zero,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]

/-- `φ(d) ∑_{v ≤ N, d | v} Λ(v) v ≤ Λ(d) d N` for `d ≠ 1`. -/
theorem totient_mul_sum_vonMangoldt_mul_le {d : ℕ} (hd : d ≠ 1) (N : ℕ) :
    (Nat.totient d : ℝ) * ∑ v ∈ Icc 1 N with d ∣ v, (Λ v : ℝ) * v ≤ Λ d * d * N := by
  by_cases hpp : IsPrimePow d
  · obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hS := sum_vonMangoldt_pow_dvd_le hp hj (fun v => (v : ℝ)) (fun n => by positivity) (N := N)
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.totient_prime_pow hp hj]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    set K := Nat.log p N
    have hgeo : ∑ α ∈ Icc j K, ((p ^ α : ℕ) : ℝ) ≤ p * N / (p - 1) := by
      have hsub : Icc j K ⊆ range (K + 1) := fun α hα => by
        simp only [mem_Icc] at hα; simp only [mem_range]; omega
      refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
      push_cast
      rw [geom_sum_eq hp1.ne', le_div_iff₀ (by linarith), div_mul_cancel₀ _ (by linarith)]
      have hK : ((p ^ K : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.pow_log_le_self p hN.ne'
      push_cast at hK
      rw [pow_succ]; nlinarith
    calc ((p ^ (j - 1) * (p - 1) : ℕ) : ℝ) * ∑ v ∈ Icc 1 N with p ^ j ∣ v, (Λ v : ℝ) * v
        ≤ ((p ^ (j - 1) * (p - 1) : ℕ) : ℝ) * (Real.log p * (p * N / (p - 1))) :=
          mul_le_mul_of_nonneg_left (hS.trans (mul_le_mul_of_nonneg_left hgeo hlog))
            (Nat.cast_nonneg _)
      _ = Real.log p * ((p ^ j : ℕ) : ℝ) * N := by
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
          obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          have hp' : (p : ℝ) - 1 ≠ 0 := by linarith
          rw [Nat.add_sub_cancel]
          push_cast
          field_simp
          ring
  · rw [sum_vonMangoldt_dvd_eq_zero hd hpp, mul_zero,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]; simp

/-- The `d = 1` term of `sum_mul_gcd_eq`. -/
theorem sum_mul_gcd_split {q : ℕ} (hq : q ≠ 0) (s : Finset ℕ) (f : ℕ → ℝ) :
    ∑ v ∈ s, f v * (Nat.gcd q v : ℝ) =
      ∑ v ∈ s, f v + ∑ d ∈ q.divisors.erase 1, (Nat.totient d : ℝ) * ∑ v ∈ s with d ∣ v, f v := by
  rw [sum_mul_gcd_eq hq, ← add_sum_erase _ _ (Nat.one_mem_divisors.2 hq)]
  simp

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **[H, (6.9)]**: `∑_{v ≤ N} Λ(v)(q,v)/v ≤ log N + log q`. -/
theorem sum_vonMangoldt_gcd_div_le {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) :
    ∑ v ∈ Icc 1 N, (Λ v : ℝ) * (1 / v) * Nat.gcd q v ≤ Real.log N + Real.log q := by
  rw [sum_mul_gcd_split (by omega)]
  have h1 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * (1 / v) ≤ Real.log N := by
    have := Prelim.sum_vonMangoldt_div_le_log (x := N) (by exact_mod_cast hN)
    simpa [Nat.floor_natCast, div_eq_mul_inv] using this
  have h2 : ∑ d ∈ q.divisors.erase 1, (Nat.totient d : ℝ) *
      ∑ v ∈ Icc 1 N with d ∣ v, (Λ v : ℝ) * (1 / v) ≤ Real.log q := by
    calc _ ≤ ∑ d ∈ q.divisors.erase 1, (Λ d : ℝ) :=
          sum_le_sum fun d hd => totient_mul_sum_vonMangoldt_div_le (ne_of_mem_erase hd) N
      _ ≤ ∑ d ∈ q.divisors, (Λ d : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ =>
            ArithmeticFunction.vonMangoldt_nonneg
      _ = Real.log q := ArithmeticFunction.vonMangoldt_sum
  linarith

/-- [H, §6.2.2]: `∑_{v ≤ N} Λ(v) v (q,v) ≤ ∑_{v ≤ N} Λ(v) v + N q log q`. -/
theorem sum_vonMangoldt_mul_gcd_le {q N : ℕ} (hq : 1 ≤ q) :
    ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v * Nat.gcd q v ≤
      ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v + N * q * Real.log q := by
  rw [sum_mul_gcd_split (by omega)]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h2 : ∑ d ∈ q.divisors.erase 1, (Nat.totient d : ℝ) *
      ∑ v ∈ Icc 1 N with d ∣ v, (Λ v : ℝ) * v ≤ N * q * Real.log q := by
    calc _ ≤ ∑ d ∈ q.divisors.erase 1, (Λ d : ℝ) * d * N :=
          sum_le_sum fun d hd => totient_mul_sum_vonMangoldt_mul_le (ne_of_mem_erase hd) N
      _ ≤ ∑ d ∈ q.divisors.erase 1, (Λ d : ℝ) * q * N := by
          refine sum_le_sum fun d hd => ?_
          have : (d : ℝ) ≤ q := by exact_mod_cast Nat.divisor_le (mem_of_mem_erase hd)
          have := ArithmeticFunction.vonMangoldt_nonneg (n := d)
          have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          gcongr
      _ ≤ ∑ d ∈ q.divisors, (Λ d : ℝ) * q * N :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by
            have := ArithmeticFunction.vonMangoldt_nonneg (n := ‹ℕ›); positivity
      _ = N * q * Real.log q := by
          rw [← sum_mul, ← sum_mul, ArithmeticFunction.vonMangoldt_sum]; ring
  linarith

/-- (6.9) for a subset `s ⊆ [1, N]`: `∑_{v ∈ s} Λ(v)(q,v)/v ≤ ∑_{v ∈ s} Λ(v)/v + log q`. -/
theorem sum_vonMangoldt_gcd_div_subset_le {q N : ℕ} (hq : 1 ≤ q) {s : Finset ℕ}
    (hs : s ⊆ Icc 1 N) :
    ∑ v ∈ s, (Λ v : ℝ) * (1 / v) * Nat.gcd q v ≤ ∑ v ∈ s, (Λ v : ℝ) * (1 / v) + Real.log q := by
  rw [sum_mul_gcd_split (by omega)]
  have h2 : ∑ d ∈ q.divisors.erase 1, (Nat.totient d : ℝ) *
      ∑ v ∈ s with d ∣ v, (Λ v : ℝ) * (1 / v) ≤ Real.log q := by
    calc _ ≤ ∑ d ∈ q.divisors.erase 1, (Λ d : ℝ) := by
          refine sum_le_sum fun d hd => le_trans ?_
            (totient_mul_sum_vonMangoldt_div_le (ne_of_mem_erase hd) N)
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hs) fun v _ _ =>
            mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      _ ≤ ∑ d ∈ q.divisors, (Λ d : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ =>
            ArithmeticFunction.vonMangoldt_nonneg
      _ = Real.log q := ArithmeticFunction.vonMangoldt_sum
  linarith

end TernaryGoldbach.MinorArcs
