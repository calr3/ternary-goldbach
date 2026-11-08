import TernaryGoldbach.Prelim.EOneRanges
import TernaryGoldbach.Prelim.MoebiusCDE

/-!
# Sums over `n` for the part `n ≤ x/Y` of the identity

For a range `u ≤ x/n < v` of `u = x/n` (`n ∈ (⌊x/v⌋, ⌊x/u⌋]`), uniformly in `x > 0`:
* `∑ 1/(n √(x/n)) ≤ 2/√u − 2/√v + 2√v/x` (`sum_sqrt_piece`);
* `∑ 1/n ≤ log(v/u) + 2v/x` (`sum_inv_piece`), for `1 ≤ u`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim

/-- `1/√(m+1) ≤ 2(√(m+1) − √m)`. -/
theorem inv_sqrt_step (m : ℕ) : (1 : ℝ) / √((m + 1 : ℕ) : ℝ) ≤ 2 * (√((m + 1 : ℕ) : ℝ) - √(m : ℝ)) := by
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hs1 : 0 < √((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hm1
  have hs0 : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
  have hle : √(m : ℝ) ≤ √((m + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
  have hsq1 := Real.mul_self_sqrt hm1.le
  have hsq0 := Real.mul_self_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  rw [div_le_iff₀ hs1]
  have e : ((m + 1 : ℕ) : ℝ) = m + 1 := by push_cast; ring
  nlinarith

/-- `∑_{a < n ≤ b} 1/√n ≤ 2(√b − √a)` for `a ≤ b`. -/
theorem sum_inv_sqrt_Ioc {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, (1 : ℝ) / √(n : ℝ) ≤ 2 * (√(b : ℝ) - √(a : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 by ring, sum_Ioc_succ_top (by omega)]
    have := ih (by omega)
    have := inv_sqrt_step (a + k)
    linarith

/-- **The `√` piece**: `∑_{⌊x/v⌋ < n ≤ ⌊x/u⌋} 1/(n √(x/n)) ≤ 2/√u − 2/√v + 2√v/x`. -/
theorem sum_sqrt_piece {x u v : ℝ} (hx : 0 < x) (hu : 0 < u) (huv : u ≤ v) :
    ∑ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, (1 : ℝ) / (n * √(x / n)) ≤ 2 / √u - 2 / √v + 2 * √v / x := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have e : ∀ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, (1 : ℝ) / (n * √(x / n)) = 1 / √x * (1 / √(n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := (mem_Ioc.1 hn).1; omega : 0 < n)
    rw [Real.sqrt_div hx.le]
    have hsn := Real.mul_self_sqrt hn0.le
    have hsn0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    field_simp
    nlinarith [hsn]
  rw [sum_congr rfl e, ← mul_sum]
  have h1 := sum_inv_sqrt_Ioc (a := ⌊x / v⌋₊) (b := ⌊x / u⌋₊)
    (Nat.floor_mono (div_le_div_of_nonneg_left hx.le hu huv))
  have hb : √((⌊x / u⌋₊ : ℕ) : ℝ) ≤ √x / √u := by
    rw [← Real.sqrt_div' x hu.le]; exact Real.sqrt_le_sqrt (Nat.floor_le (by positivity))
  -- `√⌊x/v⌋ ≥ √(x/v) − √(v/x)`
  have ha : √x / √v - √v / √x ≤ √((⌊x / v⌋₊ : ℕ) : ℝ) := by
    rcases lt_or_ge x v with hxv | hxv
    · have : √x / √v - √v / √x ≤ 0 := by
        rw [sub_nonpos, div_le_div_iff₀ (Real.sqrt_pos.2 hv) hsx]
        rw [Real.mul_self_sqrt hx.le, Real.mul_self_sqrt hv.le]; linarith
      exact this.trans (Real.sqrt_nonneg _)
    · set y := x / v with hy
      have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hv]; linarith
      have hfl : y - 1 ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by have := Nat.lt_floor_add_one y; linarith
      have hsy : √x / √v = √y := by rw [hy, Real.sqrt_div' x hv.le]
      have hsy' : √v / √x = 1 / √y := by
        rw [hy, Real.sqrt_div' x hv.le, one_div_div]
      rw [hsy, hsy']
      have hy0 : 0 < √y := Real.sqrt_pos.2 (by linarith)
      have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ y by linarith)
      have hy10 : (0 : ℝ) ≤ y - 1 := by linarith
      refine le_trans ?_ (Real.sqrt_le_sqrt hfl)
      rcases le_or_gt (√y - 1 / √y) 0 with hneg | hpos
      · exact hneg.trans (Real.sqrt_nonneg _)
      · rw [Real.le_sqrt hpos.le hy10]
        have e2 : (√y - 1 / √y) ^ 2 = y - 2 + 1 / y := by
          have h1' : √y * (1 / √y) = 1 := mul_one_div_cancel hy0.ne'
          have h2' : (1 / √y) ^ 2 = 1 / y := by rw [div_pow, one_pow, Real.sq_sqrt (by linarith)]
          calc (√y - 1 / √y) ^ 2 = √y ^ 2 - 2 * (√y * (1 / √y)) + (1 / √y) ^ 2 := by ring
            _ = y - 2 + 1 / y := by rw [Real.sq_sqrt (by linarith), h1', h2']; ring
        rw [e2]
        have : 1 / y ≤ 1 := by rw [div_le_one (by linarith)]; exact hy1
        linarith
  have h2 : ∑ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, (1 : ℝ) / √(n : ℝ) ≤ 2 * (√x / √u - (√x / √v - √v / √x)) := by
    linarith
  calc 1 / √x * ∑ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, (1 : ℝ) / √(n : ℝ)
      ≤ 1 / √x * (2 * (√x / √u - (√x / √v - √v / √x))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 / √u - 2 / √v + 2 * √v / x := by
        have hsxx := Real.mul_self_sqrt hx.le
        have e3 : 2 * √v / x = 2 * √v / (√x * √x) := by rw [hsxx]
        rw [e3]
        have hu' : 0 < √u := Real.sqrt_pos.2 hu
        have hv' : 0 < √v := Real.sqrt_pos.2 hv
        field_simp
        ring

/-- **The constant piece**: `∑_{⌊x/v⌋ < n ≤ ⌊x/u⌋} 1/n ≤ log(v/u) + 2v/x` for `1 ≤ u ≤ v`. -/
theorem sum_inv_piece {x u v : ℝ} (hx : 0 < x) (hu : 1 ≤ u) (huv : u ≤ v) :
    ∑ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, (1 : ℝ) / n ≤ Real.log (v / u) + 2 * v / x := by
  have hu0 : 0 < u := by linarith
  have hv : 0 < v := by linarith
  have hlv : 0 ≤ Real.log (v / u) := Real.log_nonneg (by rw [le_div_iff₀ hu0]; linarith)
  rcases le_or_gt ⌊x / u⌋₊ ⌊x / v⌋₊ with h | h
  · rw [Ioc_eq_empty (by omega), sum_empty]; positivity
  rcases Nat.eq_zero_or_pos ⌊x / v⌋₊ with h0 | h0
  · -- `x < v`
    rw [h0]
    have hxv : x < v := by
      by_contra hc; push Not at hc
      have : 1 ≤ ⌊x / v⌋₊ := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hv]; linarith)
      omega
    have hb1 : 1 ≤ ⌊x / u⌋₊ := by omega
    have hsum := sum_inv_le_log (a := 1) (b := ⌊x / u⌋₊) le_rfl hb1
    rw [show Ioc 0 ⌊x / u⌋₊ = insert 1 (Ioc 1 ⌊x / u⌋₊) by ext n; simp; omega,
      sum_insert (by simp)]
    have hl : Real.log ((⌊x / u⌋₊ : ℕ) : ℝ) ≤ Real.log (v / u) :=
      Real.log_le_log (by exact_mod_cast hb1) ((Nat.floor_le (by positivity)).trans
        (div_le_div_of_nonneg_right hxv.le hu0.le))
    have h2 : (1 : ℝ) ≤ 2 * v / x := by rw [le_div_iff₀ hx]; linarith
    simp only [Nat.cast_one, div_one, Real.log_one, sub_zero] at hsum ⊢
    linarith
  · have hsum := sum_inv_le_log h0 h.le
    have hb : Real.log ((⌊x / u⌋₊ : ℕ) : ℝ) ≤ Real.log (x / u) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x / u⌋₊)) (Nat.floor_le (by positivity))
    set a := ⌊x / v⌋₊ with ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast h0
    have hay : x / v - 1 < a := by have := Nat.lt_floor_add_one (x / v); linarith
    have hay' : (a : ℝ) ≤ x / v := Nat.floor_le (by positivity)
    -- `log(x/v) − log a ≤ 1/a ≤ 2v/x`
    have hl1 : Real.log (x / v) - Real.log a ≤ 1 / a := by
      rw [← Real.log_div (by positivity) ha0.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < x / v / a by positivity)
      have e : x / v / a - 1 = (x / v - a) / a := by field_simp
      rw [e] at this
      calc Real.log (x / v / a) ≤ (x / v - a) / a := this
        _ ≤ 1 / a := div_le_div_of_nonneg_right (by linarith) ha0.le
    have hl2 : 1 / (a : ℝ) ≤ 2 * v / x := by
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast h0
      have hxa : x < 2 * v * a := by
        have : x / v < a + 1 := by linarith
        rw [div_lt_iff₀ hv] at this
        nlinarith
      rw [div_le_div_iff₀ ha0 hx]
      linarith
    have e2 : Real.log (x / u) = Real.log (v / u) + Real.log (x / v) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    linarith

/-- `1/n ≤ 2 log((n + 1)/n)`. -/
theorem inv_le_two_log (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / n ≤ 2 * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn0.ne']
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < ((n + 1 : ℕ) : ℝ) / n by positivity)
  have e : 1 - (((n + 1 : ℕ) : ℝ) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by push_cast; field_simp; ring
  rw [e] at h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) / n ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    rw [mul_one_div, div_le_div_iff₀ hn0 (by positivity)]; linarith
  linarith

/-- **The `1/log²` piece**: `∑_{a < n ≤ b} 1/(n log²(x/n)) ≤ 2/log(x/(b+1))` if `x/(b+1) > 1`. -/
theorem sum_log2_piece {x : ℝ} (hx : 0 < x) {a b : ℕ} (hab : a ≤ b) (hb : (b + 1 : ℝ) < x) :
    ∑ n ∈ Ioc a b, (1 : ℝ) / (n * Real.log (x / n) ^ 2) ≤ 2 / Real.log (x / (b + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  induction k with
  | zero =>
    simp only [add_zero, Ioc_self, sum_empty]
    have : 0 < Real.log (x / (a + 1)) := Real.log_pos (by rw [lt_div_iff₀ (by positivity)]; simpa using hb)
    positivity
  | succ k ih =>
    have hb' : ((a + k : ℕ) : ℝ) + 1 < x := by push_cast at hb ⊢; linarith
    have ih' := ih (by omega) (by exact_mod_cast hb')
    rw [show a + (k + 1) = (a + k) + 1 by ring, sum_Ioc_succ_top (by omega)]
    set m := a + k + 1 with hm
    have hm1 : 1 ≤ m := by omega
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    set A := Real.log x
    have hl : ∀ t : ℝ, 0 < t → Real.log (x / t) = A - Real.log t := fun t ht => Real.log_div hx.ne' ht.ne'
    have hmc : (m : ℝ) = a + k + 1 := by rw [hm]; push_cast; ring
    have hmx : (m : ℝ) + 1 < x := by push_cast at hb; linarith
    have hpos1 : 0 < A - Real.log ((m : ℝ) + 1) := by
      rw [← hl _ (by positivity)]; exact Real.log_pos (by rw [lt_div_iff₀ (by positivity)]; linarith)
    have hlm : Real.log m ≤ Real.log ((m : ℝ) + 1) := Real.log_le_log hm0 (by linarith)
    have hpos0 : 0 < A - Real.log m := by linarith
    rw [hl _ hm0]
    rw [show ((a + k : ℕ) : ℝ) + 1 = (m : ℝ) by push_cast [hm]; ring] at ih'
    rw [show ((m : ℕ) : ℝ) + 1 = (m : ℝ) + 1 from rfl, hl _ (by positivity)]
    rw [hl _ hm0] at ih'
    -- the new term
    have hi := inv_le_two_log m hm1
    push_cast at hi
    set d := Real.log ((m : ℝ) + 1) - Real.log m with hd
    have hd0 : 0 ≤ d := by linarith
    have key : (1 : ℝ) / (m * (A - Real.log m) ^ 2) ≤
        2 / (A - Real.log ((m : ℝ) + 1)) - 2 / (A - Real.log m) := by
      rw [div_sub_div _ _ hpos1.ne' hpos0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 1 / (m : ℝ) ≤ 2 * d := hi
      have h2 : (1 : ℝ) ≤ 2 * d * m := by rw [div_le_iff₀ hm0] at h1; linarith
      have e : 2 * (A - Real.log m) - (A - Real.log ((m : ℝ) + 1)) * 2 = 2 * d := by rw [hd]; ring
      rw [e]
      have h3 : (A - Real.log ((m : ℝ) + 1)) * (A - Real.log m) ≤ (A - Real.log m) ^ 2 := by nlinarith
      nlinarith [mul_pos hpos1 hpos0]
    linarith

/-- **The `1/log³` piece**: `∑_{a < n ≤ b} 1/(n log³(x/n)) ≤ 1/log²(x/(b+1))` if `x/(b+1) > 1`. -/
theorem sum_log3_piece {x : ℝ} (hx : 0 < x) {a b : ℕ} (hab : a ≤ b) (hb : (b + 1 : ℝ) < x) :
    ∑ n ∈ Ioc a b, (1 : ℝ) / (n * Real.log (x / n) ^ 3) ≤ 1 / Real.log (x / (b + 1)) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  induction k with
  | zero =>
    simp only [add_zero, Ioc_self, sum_empty]
    positivity
  | succ k ih =>
    have hb' : ((a + k : ℕ) : ℝ) + 1 < x := by push_cast at hb ⊢; linarith
    have ih' := ih (by omega) (by exact_mod_cast hb')
    rw [show a + (k + 1) = (a + k) + 1 by ring, sum_Ioc_succ_top (by omega)]
    set m := a + k + 1 with hm
    have hm1 : 1 ≤ m := by omega
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    set A := Real.log x
    have hl : ∀ t : ℝ, 0 < t → Real.log (x / t) = A - Real.log t := fun t ht => Real.log_div hx.ne' ht.ne'
    have hmc : (m : ℝ) = a + k + 1 := by rw [hm]; push_cast; ring
    have hmx : (m : ℝ) + 1 < x := by push_cast at hb; linarith
    have hpos1 : 0 < A - Real.log ((m : ℝ) + 1) := by
      rw [← hl _ (by positivity)]; exact Real.log_pos (by rw [lt_div_iff₀ (by positivity)]; linarith)
    have hlm : Real.log m ≤ Real.log ((m : ℝ) + 1) := Real.log_le_log hm0 (by linarith)
    have hpos0 : 0 < A - Real.log m := by linarith
    rw [hl _ hm0]
    rw [show ((a + k : ℕ) : ℝ) + 1 = (m : ℝ) by push_cast [hm]; ring] at ih'
    rw [show ((m : ℕ) : ℝ) + 1 = (m : ℝ) + 1 from rfl, hl _ (by positivity)]
    rw [hl _ hm0] at ih'
    have hi := inv_le_two_log m hm1
    push_cast at hi
    set d := Real.log ((m : ℝ) + 1) - Real.log m with hd
    have hd0 : 0 ≤ d := by linarith
    set p := A - Real.log m
    set q := A - Real.log ((m : ℝ) + 1)
    have hpq : p - q = d := by simp only [p, q, hd]; ring
    have key : (1 : ℝ) / (m * p ^ 3) ≤ 1 / q ^ 2 - 1 / p ^ 2 := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 1 / (m : ℝ) ≤ 2 * d := hi
      have h2 : (1 : ℝ) ≤ 2 * d * m := by rw [div_le_iff₀ hm0] at h1; linarith
      have hqp : q ≤ p := by linarith
      have e : 1 * p ^ 2 - q ^ 2 * 1 = (p - q) * (p + q) := by ring
      rw [e, hpq]
      -- `q² p² ≤ m p³ d (p + q)` from `1 ≤ 2dm` and `2 q² ≤ p(p + q)`
      have h4 : 2 * q ^ 2 ≤ p * (p + q) := by nlinarith
      have h6 : (1 / 2 : ℝ) * (p ^ 3 * (p + q)) ≤ d * m * (p ^ 3 * (p + q)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h7 : q ^ 2 * p ^ 2 ≤ 1 / 2 * (p ^ 3 * (p + q)) := by
        have := mul_le_mul_of_nonneg_left h4 (sq_nonneg p)
        nlinarith
      have e2 : d * (p + q) * (m * p ^ 3) = d * m * (p ^ 3 * (p + q)) := by ring
      rw [e2]; linarith
    linarith

end TernaryGoldbach.Prelim
