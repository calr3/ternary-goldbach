import TernaryGoldbach.Prelim.RamareFo

/-!
# Local data of `h_d` at a prime

For a prime `p`: `h_d(p^e) = 0` for `e ≥ 3`, and with `S₀ = ∑_e h_d(p^e)`, `S₁ = ∑_e e h_d(p^e)`,
`W = ∑_e |h_d(p^e)| p^{e/3}`:

| | `S₀` | `S₁` | `W` |
|---|---|---|---|
| `p = 2 ∤ d` | `2` | `1` | `1 + 2^{1/3}` |
| `p = 2 ∣ d` | `1` | `0` | `1` |
| odd `p ∤ d` | `1` | `−1/(p(p−1))` | `1 + (p^{1/3} + p^{2/3})/(p(p−1))` |
| odd `p ∣ d` | `1 − 1/p` | `−1/p` | `1 + p^{−2/3}` |
-/

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.RamPf

/-- `h_d(p) = [p ∤ d]/(p − 1) − [p odd]/p`. -/
theorem hD_p' {d p : ℕ} (hp : p.Prime) :
    hD d p = (if p ∣ d then 0 else 1 / ((p : ℝ) - 1)) + (if p = 2 then 0 else -1 / (p : ℝ)) := by
  rw [hD_p hp, gD_p hp, wO_p hp]

theorem hD_p2' {d p : ℕ} (hp : p.Prime) :
    hD d (p ^ 2) = (if p ∣ d then 0 else 1 / ((p : ℝ) - 1)) * (if p = 2 then 0 else -1 / (p : ℝ)) := by
  rw [hD_p2 hp, gD_p hp, wO_p hp]

/-- The local sum `∑_e h_d(p^e)` (support `e ≤ 2`). -/
noncomputable def S0 (d p : ℕ) : ℝ := 1 + hD d p + hD d (p ^ 2)

/-- `∑_e e h_d(p^e)`. -/
noncomputable def S1 (d p : ℕ) : ℝ := hD d p + 2 * hD d (p ^ 2)

theorem hD_pow_eq {d p : ℕ} (hp : p.Prime) (e : ℕ) :
    hD d (p ^ e) = if e = 0 then 1 else if e = 1 then hD d p else if e = 2 then hD d (p ^ 2) else 0 := by
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ 3 ≤ e by omega) with h | h | h | h
  · subst h; simp [(isMult_hD d).map_one]
  · subst h; simp
  · subst h; simp
  · rw [hD_pk hp h, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem hasSum_local {d p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) :
    HasSum (fun e => c e * hD d (p ^ e)) (c 0 + c 1 * hD d p + c 2 * hD d (p ^ 2)) := by
  have h : HasSum (fun e => c e * hD d (p ^ e)) (∑ e ∈ range 3, c e * hD d (p ^ e)) :=
    hasSum_sum_of_ne_finset_zero (fun e he => by
      rw [mem_range, not_lt] at he
      rw [hD_pk hp he, mul_zero])
  convert h using 1
  simp [sum_range_succ, (isMult_hD d).map_one]

theorem S0_eq {d p : ℕ} (hp : p.Prime) :
    S0 d p = if p = 2 then (if p ∣ d then 1 else 2) else (if p ∣ d then 1 - 1 / (p : ℝ) else 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [S0, hD_p' hp, hD_p2' hp]
  by_cases h2 : p = 2
  · subst h2; by_cases hd2 : 2 ∣ d <;> simp [hd2] <;> norm_num
  · by_cases hpd : p ∣ d <;> simp [h2, hpd]
    · ring
    · have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring

theorem S1_eq {d p : ℕ} (hp : p.Prime) :
    S1 d p = if p = 2 then (if p ∣ d then 0 else 1) else
      (if p ∣ d then -1 / (p : ℝ) else -1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [S1, hD_p' hp, hD_p2' hp]
  by_cases h2 : p = 2
  · subst h2; by_cases hd2 : 2 ∣ d <;> simp [hd2] <;> norm_num
  · by_cases hpd : p ∣ d <;> simp [h2, hpd]
    · have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp; ring

/-! ### The weight `|h_d(a)| a^{1/3}` -/

/-- `w_d(a) = |h_d(a)| a^{1/3}`. -/
noncomputable def wD (d a : ℕ) : ℝ := |hD d a| * (a : ℝ) ^ ((1 : ℝ) / 3)

theorem wD_nonneg (d a : ℕ) : 0 ≤ wD d a := mul_nonneg (abs_nonneg _) (by positivity)

theorem wD_one (d : ℕ) : wD d 1 = 1 := by simp [wD, (isMult_hD d).map_one]

theorem wD_mul (d : ℕ) {m n : ℕ} (h : m.Coprime n) : wD d (m * n) = wD d m * wD d n := by
  rw [wD, wD, wD, (isMult_hD d).map_mul_of_coprime h, abs_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- `W = ∑_e w_d(p^e) = 1 + |h(p)| p^{1/3} + |h(p²)| p^{2/3}`. -/
theorem hasSum_wD {d p : ℕ} (hp : p.Prime) :
    HasSum (fun e => wD d (p ^ e))
      (1 + |hD d p| * (p : ℝ) ^ ((1 : ℝ) / 3) + |hD d (p ^ 2)| * ((p ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) := by
  have h : HasSum (fun e => wD d (p ^ e)) (∑ e ∈ range 3, wD d (p ^ e)) :=
    hasSum_sum_of_ne_finset_zero (fun e he => by
      rw [mem_range, not_lt] at he
      rw [wD, hD_pk hp he, abs_zero, zero_mul])
  convert h using 1
  simp [sum_range_succ, wD, (isMult_hD d).map_one]

/-- `∑_{a ≤ A} f(a) ≤ ∏_{p ≤ A} ∑_e f(p^e)` for non-negative multiplicative `f`. -/
theorem sum_le_euler' {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (h1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖f (p ^ e)‖)) (A : ℕ) :
    ∑ n ∈ Icc 1 A, f n ≤ ∏ p ∈ Nat.primesBelow (A + 1), ∑' e, f (p ^ e) := by
  obtain ⟨-, hHas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum h1 hmul hsum (A + 1)
  have hsub : ∑ n ∈ Icc 1 A, f n = ∑ x ∈ (Icc 1 A).subtype (· ∈ (A + 1).smoothNumbers), f x := by
    rw [sum_subtype_eq_sum_filter, filter_true_of_mem]
    intro n hn
    rw [Nat.mem_smoothNumbers]
    refine ⟨by have := (mem_Icc.1 hn).1; omega, fun p hp => ?_⟩
    have := Nat.le_of_mem_primeFactorsList hp; have := (mem_Icc.1 hn).2; omega
  rw [hsub]
  exact sum_le_hasSum _ (fun x _ => hf0 x) hHas

end TernaryGoldbach.Prelim.RamPf
