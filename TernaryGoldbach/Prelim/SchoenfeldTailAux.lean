import TernaryGoldbach.Prelim.SchoenfeldJ
import TernaryGoldbach.Prelim.SchoenfeldCell
import TernaryGoldbach.Prelim.SmallMertens
import TernaryGoldbach.Explicit.LogNumerics

/-!
# Auxiliary bounds for the induction beyond the cells

* `rho_C5`: `|ρ(v)| ≤ 0.00985 v/log v` for `v ≥ 10¹²` (`theta_explicit` and `ψ − θ < 1.4262 √v`);
* `sum_inv_log_sq_le`: `∑_{a ≤ n < b} 1/log²n ≤ 1.013 (b/log²b − a/log²a)` for `log a ≥ 160`;
* `sum_inv_log_le`: `∑_{a ≤ n < b} 1/log n ≤ b/(log b − 2) − a/(log a − 2)` for `log a ≥ 6`;
* `log_floor_ge`: `log ⌊x⌋ ≥ log x − 2/x` for `x ≥ 2`;
* `sum_Lambda_div_Ioc`: `∑_{a < k ≤ b} Λ(k)/k ≤ log b − log(a+1) + log(3/√2)`.
-/

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim.Sch

theorem log_floor_ge {x : ℝ} (hx : 2 ≤ x) : Real.log x - 2 / x ≤ Real.log ⌊x⌋₊ := by
  have hx0 : 0 < x := by linarith
  have hf1 : x - 1 < ⌊x⌋₊ := by have := Nat.lt_floor_add_one x; linarith
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hf0 : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (x := (⌊x⌋₊ : ℝ) / x) (by positivity)
  rw [Real.log_div hf0.ne' hx0.ne', inv_div] at h
  have h2 : 1 - x / ⌊x⌋₊ ≥ -(2 / x) := by
    rw [ge_iff_le, neg_le, neg_sub, sub_le_iff_le_add, div_le_iff₀ hf0]
    have : 2 / x * ⌊x⌋₊ ≥ 2 / x * (x - 1) := mul_le_mul_of_nonneg_left hf1.le (by positivity)
    have e : 2 / x * (x - 1) = 2 - 2 / x := by field_simp
    have h3 : (1 : ℝ) ≤ 2 - 2 / x := by rw [le_sub_iff_add_le, ← le_sub_iff_add_le']; rw [div_le_iff₀ hx0]; linarith
    nlinarith
  linarith

/-- `∑_{a < k ≤ b} Λ(k)/k ≤ log b − log(a+1) + log(3/√2)`. -/
theorem sum_Lambda_div_Ioc [Fact TernaryGoldbach.PlattGRH] {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Ioc a b, (Λ k : ℝ) / k ≤ Real.log b - Real.log ((a : ℝ) + 1) + Real.log (3 / √2) := by
  have h1 := sum_vonMangoldt_div_le_log (x := (b : ℝ)) (by exact_mod_cast (le_trans ha hab))
  rw [Nat.floor_natCast] at h1
  have h2 := mertens_lower_nat ha
  have e : ∑ k ∈ Icc 1 b, (Λ k : ℝ) / k = ∑ k ∈ Icc 1 a, (Λ k : ℝ) / k + ∑ k ∈ Ioc a b, (Λ k : ℝ) / k := by
    rw [show Icc 1 b = Ioc 0 b by ext; simp; omega, show Icc 1 a = Ioc 0 a by ext; simp; omega,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  push_cast at h2
  linarith

/-- One step: `1/log²n ≤ λ((n+1)/log²(n+1) − n/log²n)` for `log n ≥ 160`. -/
theorem inv_log_sq_step {n : ℕ} (hn : 160 ≤ Real.log n) :
    1 / Real.log n ^ 2 ≤ 1.013 * (((n : ℝ) + 1) / Real.log ((n : ℝ) + 1) ^ 2 - n / Real.log n ^ 2) := by
  set l := Real.log n
  set l' := Real.log ((n : ℝ) + 1)
  have hn1 : (1 : ℝ) ≤ n := by
    by_contra h; push_neg at h
    have : Real.log n ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hll : l ≤ l' := Real.log_le_log hn0 (by linarith)
  have hl' : l' ≤ l + 1 / n := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    rw [Real.log_div (by linarith) hn0.ne'] at this
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  -- `n ≥ 160` suffices for the crude bounds on `1/n`
  have hn160 : (160 : ℝ) ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  have hin : 1 / (n : ℝ) ≤ 1 / 160 := one_div_le_one_div_of_le (by norm_num) hn160
  have hin0 : 0 < 1 / (n : ℝ) := by positivity
  have hl0 : 0 < l := by linarith
  have hl'0 : 0 < l' := by linarith
  -- `(n+1) l² − n l'² ≥ l² − 2l − 1/n`
  have hnum : ((n : ℝ) + 1) * l ^ 2 - n * l' ^ 2 ≥ l ^ 2 - 2 * l - 1 / n := by
    have h1 : (n : ℝ) * l' ^ 2 ≤ n * (l + 1 / n) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl'0.le hl' 2) hn0.le
    have e : (n : ℝ) * (l + 1 / n) ^ 2 = n * l ^ 2 + 2 * l + 1 / n := by field_simp; ring
    nlinarith
  have hsq : l' ^ 2 ≤ l ^ 2 + 2 * l / n + 1 / n ^ 2 := by
    have := pow_le_pow_left₀ hl'0.le hl' 2
    have e : (l + 1 / n) ^ 2 = l ^ 2 + 2 * l / n + 1 / n ^ 2 := by field_simp; ring
    linarith
  -- reduce to `l'² ≤ λ ((n+1) l² − n l'²)`
  have key : l' ^ 2 ≤ 1.013 * (((n : ℝ) + 1) * l ^ 2 - n * l' ^ 2) := by
    have h2 : 2 * l / n ≤ 2 * l / 160 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]; nlinarith
    have h3 : 1 / (n : ℝ) ^ 2 ≤ 1 / 160 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have e : ((n : ℝ) + 1) / l' ^ 2 - n / l ^ 2 = (((n : ℝ) + 1) * l ^ 2 - n * l' ^ 2) / (l' ^ 2 * l ^ 2) := by
    field_simp
  rw [e, mul_div_assoc', le_div_iff₀ (by positivity)]
  have e2 : 1 / l ^ 2 * (l' ^ 2 * l ^ 2) = l' ^ 2 := by field_simp
  rw [e2]; exact key

/-- `∑_{a ≤ n < b} 1/log²n ≤ 1.013 (b/log²b − a/log²a)` for `log a ≥ 160`. -/
theorem sum_inv_log_sq_le {a : ℕ} (ha : 160 ≤ Real.log a) :
    ∀ b, a ≤ b → ∑ n ∈ Ico a b, 1 / Real.log n ^ 2 ≤
      1.013 * ((b : ℝ) / Real.log b ^ 2 - a / Real.log a ^ 2) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    have hb : 160 ≤ Real.log b := by
      refine le_trans ha (Real.log_le_log ?_ (by exact_mod_cast hab))
      by_contra h; push_neg at h
      have : (a : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [this, Real.log_zero] at ha; linarith
    have := inv_log_sq_step hb
    push_cast
    linarith

/-- One step: `1/log n ≤ (n+1)/(log(n+1) − 2) − n/(log n − 2)` for `log n ≥ 6`. -/
theorem inv_log_step {n : ℕ} (hn : 6 ≤ Real.log n) :
    1 / Real.log n ≤ ((n : ℝ) + 1) / (Real.log ((n : ℝ) + 1) - 2) - n / (Real.log n - 2) := by
  set l := Real.log n
  set l' := Real.log ((n : ℝ) + 1)
  have hn1 : (1 : ℝ) ≤ n := by
    by_contra h; push_neg at h
    have : Real.log n ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hll : l ≤ l' := Real.log_le_log hn0 (by linarith)
  have hl' : l' ≤ l + 1 / n := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    rw [Real.log_div (by linarith) hn0.ne'] at this
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have hn6 : (6 : ℝ) ≤ n := by have := Real.log_le_sub_one_of_pos hn0; linarith
  have hnl : l' * n ≤ l * n + 1 := by
    have := mul_le_mul_of_nonneg_right hl' hn0.le
    have e : (l + 1 / n) * n = l * n + 1 := by field_simp
    linarith
  rw [div_sub_div _ _ (by linarith) (by linarith), le_div_iff₀ (by nlinarith)]
  rw [one_div, inv_mul_eq_div, div_le_iff₀ (by linarith)]
  -- `(l − 2)(l' − 2) ≤ l ((n+1)(l − 2) − n (l' − 2))`
  have h1 : ((n : ℝ) + 1) * (l - 2) - (l' - 2) * n ≥ l - 3 := by nlinarith
  have h2 : (l - 2) * (l' - 2) ≤ l * (l - 3) := by nlinarith
  nlinarith

/-- `∑_{a ≤ n < b} 1/log n ≤ b/(log b − 2) − a/(log a − 2)` for `log a ≥ 6`. -/
theorem sum_inv_log_le {a : ℕ} (ha : 6 ≤ Real.log a) :
    ∀ b, a ≤ b → ∑ n ∈ Ico a b, 1 / Real.log n ≤ (b : ℝ) / (Real.log b - 2) - a / (Real.log a - 2) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    have hb : 6 ≤ Real.log b := by
      refine le_trans ha (Real.log_le_log ?_ (by exact_mod_cast hab))
      by_contra h; push_neg at h
      have : (a : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [this, Real.log_zero] at ha; linarith
    have := inv_log_step hb
    push_cast
    linarith

variable [Fact TernaryGoldbach.PlattGRH]

/-- `|ρ(v)| ≤ v/log³v + ε_pl(v) v + 1.4262 √v` for `v ≥ 10¹²`. -/
theorem rho_le_epl {v : ℕ} (hv : 1000000000000 ≤ v) :
    |ρn v| ≤ v / Real.log v ^ 3 + epl v * v + 1.4262 * √(v : ℝ) := by
  rw [rho_eq]
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  have ht := theta_explicit hv
  have hnp := sum_vonMangoldt_nonprime_lt (y := (v : ℝ)) hv0
  rw [Nat.floor_natCast] at hnp
  have hsplit : psiN v = ∑ p ∈ (Icc 1 v).filter Nat.Prime, Real.log p +
      ∑ n ∈ Icc 1 v, (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ)) := by
    unfold psiN
    rw [Finset.sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hp]
  have hnp0 : 0 ≤ ∑ n ∈ Icc 1 v, (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ)) :=
    sum_nonneg fun n _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  rw [hsplit]
  rw [abs_lt] at ht
  rw [abs_le]; constructor <;> linarith

theorem log_1e12_ge : (27.63 : ℝ) ≤ Real.log (1000000000000 : ℕ) := by
  have := Small.le_log_of_chk (cN := 2763) (cD := 100) (L := 1000000000000) (by norm_num) (by norm_num)
    (by decide +kernel)
  norm_num at this ⊢; linarith

/-- **`|ρ(v)| ≤ 0.00985 v/log v`** for `v ≥ 10¹²`. -/
theorem rho_C5 {v : ℕ} (hv : 1000000000000 ≤ v) : |ρn v| ≤ 0.00985 * v / Real.log v := by
  have h := rho_le_epl hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  set L := Real.log v with hL
  have hL0 : 27.63 ≤ L := le_trans log_1e12_ge (Real.log_le_log (by norm_num) (by exact_mod_cast hv))
  have hLp : 0 < L := by linarith
  -- `log v / √v ≤ 4/s`, `s = √√v`
  set s := √(√(v : ℝ)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (Real.sqrt_pos.2 hv0)
  have hss : s ^ 2 = √(v : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsv : s ^ 4 = v := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hss, Real.sq_sqrt hv0.le]
  have hLs : L ≤ 4 * s := by
    have : Real.log v = 4 * Real.log s := by
      rw [← hsv, Real.log_pow]; push_cast; ring
    rw [hL, this]
    have := Real.log_le_sub_one_of_pos hs0; linarith
  have hs1000 : 1000 ≤ s := by
    have h4 : (1000 : ℝ) ^ 4 ≤ s ^ 4 := by rw [hsv]; norm_num; exact hv
    exact le_of_pow_le_pow_left₀ (by norm_num) hs0.le h4
  -- the bound divided by `v / L`
  have hsq : 1.4262 * √(v : ℝ) ≤ (1.4262 * 4 / s) * (v / L) := by
    rw [← hss, ← hsv]
    rw [show 1.4262 * 4 / s * (s ^ 4 / L) = 1.4262 * s ^ 2 * (4 * s / L) by field_simp]
    have : 1 ≤ 4 * s / L := by rw [le_div_iff₀ hLp]; linarith
    nlinarith [sq_nonneg s]
  have hcube : (v : ℝ) / L ^ 3 = (1 / L ^ 2) * (v / L) := by field_simp
  have hepl : epl v * v = (epl v * L) * (v / L) := by field_simp
  have hvL : 0 ≤ (v : ℝ) / L := by positivity
  have key : 1 / L ^ 2 + epl v * L + 1.4262 * 4 / s ≤ 0.00985 := by
    unfold epl
    split_ifs with he
    · obtain ⟨h1, h2⟩ := he
      rw [← hL] at h1 h2
      -- `s ≥ e^30`
      have hse : Real.exp 30 ≤ s := by
        have : Real.log s = L / 4 := by
          have : Real.log v = 4 * Real.log s := by rw [← hsv, Real.log_pow]; push_cast; ring
          rw [hL] at *; linarith
        rw [← Real.exp_log hs0, this]; exact Real.exp_le_exp.2 (by linarith)
      have he30 : (1e12 : ℝ) ≤ Real.exp 30 := by
        have := TernaryGoldbach.Explicit.exp_nat_ge' 30; push_cast at this
        have : (1e12 : ℝ) ≤ 2.7182818283 ^ 30 := by norm_num
        linarith
      have h3 : 1.4262 * 4 / s ≤ 1e-11 := by
        rw [div_le_iff₀ hs0]; nlinarith
      rcases le_or_gt L 19000 with h4 | h4
      · have : 1 / L ^ 2 ≤ 1 / 14400 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
        nlinarith
      · have : 1 / L ^ 2 ≤ 1 / 361000000 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
        nlinarith
    · have : 1 / L ^ 2 ≤ 1 / 763 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
      have h3 : 1.4262 * 4 / s ≤ 1.4262 * 4 / 1000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs1000
      norm_num at h3 this ⊢; linarith
  calc |ρn v| ≤ v / L ^ 3 + epl v * v + 1.4262 * √(v : ℝ) := h
    _ ≤ (1 / L ^ 2 + epl v * L + 1.4262 * 4 / s) * (v / L) := by rw [hcube, hepl]; nlinarith
    _ ≤ 0.00985 * (v / L) := mul_le_mul_of_nonneg_right key hvL
    _ = 0.00985 * v / L := by ring

end TernaryGoldbach.Prelim.Sch
