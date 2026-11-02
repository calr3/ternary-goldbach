import Mathlib

/-!
# Block decompositions and elementary sum bounds for [H, §4.2]
-/

open Finset Real

namespace TernaryGoldbach.MinorArcs

/-- Split `∑_{⌊a⌋ < n ≤ ⌊b⌋} G(n)` (`G ≥ 0`) into blocks `(a + jq, min(a + (j+1)q, b)]`. -/
theorem sum_Ioc_le_blocks {G : ℤ → ℝ} (hG : ∀ n, 0 ≤ G n) {q : ℕ} (hq : 1 ≤ q) :
    ∀ (J : ℕ) (a b : ℝ), b ≤ a + J * q →
      ∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, G n ≤
        ∑ j ∈ range J, ∑ n ∈ Ioc ⌊a + j * q⌋ ⌊min (a + (j + 1) * q) b⌋, G n := by
  intro J
  induction J with
  | zero =>
    intro a b hab
    simp only [CharP.cast_eq_zero, zero_mul, add_zero] at hab
    rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hab))]; simp
  | succ J ih =>
    intro a b hab
    rw [sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, zero_add, one_mul]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hih := ih (a + q) b (by push_cast at hab; linarith)
    have hrw : ∀ j : ℕ, a + q + j * q = a + ((j + 1 : ℕ) : ℝ) * q := fun j => by push_cast; ring
    have hrw2 : ∀ j : ℕ, a + q + (j + 1) * q = a + (((j + 1 : ℕ) : ℝ) + 1) * q := fun j => by
      push_cast; ring
    simp_rw [hrw, hrw2] at hih
    rcases le_or_gt b (a + q) with hb | hb
    · rw [min_eq_right hb]
      have : ∑ n ∈ Ioc ⌊a + q⌋ ⌊b⌋, G n = 0 := by
        rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hb))]; simp
      have h0 : 0 ≤ ∑ j ∈ range J, ∑ n ∈ Ioc ⌊a + ((j + 1 : ℕ) : ℝ) * q⌋
          ⌊min (a + (((j + 1 : ℕ) : ℝ) + 1) * q) b⌋, G n :=
        sum_nonneg fun _ _ => sum_nonneg fun _ _ => hG _
      linarith
    · rw [min_eq_left hb.le]
      have hsplit : ∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, G n =
          ∑ n ∈ Ioc ⌊a⌋ ⌊a + q⌋, G n + ∑ n ∈ Ioc ⌊a + q⌋ ⌊b⌋, G n := by
        rw [← sum_union (Finset.disjoint_left.2 fun n h1 h2 => by
          simp only [mem_Ioc] at h1 h2; omega)]
        congr 1
        ext n; simp only [mem_Ioc, mem_union]
        have h1 : ⌊a⌋ ≤ ⌊a + q⌋ := Int.floor_mono (by linarith)
        have h2 : ⌊a + q⌋ ≤ ⌊b⌋ := Int.floor_mono hb.le
        omega
      rw [hsplit]; linarith

/-- `∑_{j<J} 1/(R + jq) ≤ 1/R + (1/q) log(D/R)` when `R + (J-1)q ≤ D`. -/
theorem sum_inv_le {R q D : ℝ} (hR : 0 < R) (hq : 0 < q) {J : ℕ} (hJ : 1 ≤ J)
    (hD : R + (J - 1) * q ≤ D) :
    ∑ j ∈ range J, 1 / (R + j * q) ≤ 1 / R + 1 / q * Real.log (D / R) := by
  obtain ⟨K, rfl⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  rw [sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, add_zero]
  push_cast at hD
  simp only [add_sub_cancel_right] at hD
  -- Each later term is at most `(1/q) log(yⱼ/yⱼ₋₁)`.
  have hterm : ∀ j : ℕ, 1 / (R + (j + 1 : ℕ) * q) ≤
      1 / q * (Real.log (R + (j + 1 : ℕ) * q) - Real.log (R + j * q)) := by
    intro j
    have h0 : 0 < R + j * q := by positivity
    have h1 : 0 < R + (j + 1 : ℕ) * q := by positivity
    rw [← Real.log_div h1.ne' h0.ne']
    have hlog := Real.add_one_le_exp (-(q / (R + (j + 1 : ℕ) * q)))
    have hx : (R + j * q) / (R + (j + 1 : ℕ) * q) = 1 - q / (R + (j + 1 : ℕ) * q) := by
      field_simp; push_cast; ring
    have hpos : 0 < 1 - q / (R + (j + 1 : ℕ) * q) := by rw [← hx]; positivity
    have : Real.log (1 - q / (R + (j + 1 : ℕ) * q)) ≤ -(q / (R + (j + 1 : ℕ) * q)) := by
      rw [Real.log_le_iff_le_exp hpos]; linarith
    rw [← hx, Real.log_div h0.ne' h1.ne'] at this
    rw [Real.log_div h1.ne' h0.ne']
    have : q / (R + (j + 1 : ℕ) * q) ≤ Real.log (R + (j + 1 : ℕ) * q) - Real.log (R + j * q) := by
      linarith
    calc 1 / (R + (j + 1 : ℕ) * q) = 1 / q * (q / (R + (j + 1 : ℕ) * q)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have htel : ∑ j ∈ range K, (Real.log (R + (j + 1 : ℕ) * q) - Real.log (R + j * q)) =
      Real.log (R + K * q) - Real.log R := by
    have := sum_range_sub (fun j : ℕ => Real.log (R + j * q)) K
    simpa using this
  have hsum := sum_le_sum fun j (_ : j ∈ range K) => hterm j
  rw [← mul_sum, htel] at hsum
  have hlogD : Real.log (R + K * q) - Real.log R ≤ Real.log (D / R) := by
    rw [Real.log_div (by linarith [show (0:ℝ) ≤ K * q by positivity]) hR.ne']
    have := Real.log_le_log (by positivity) hD
    linarith
  have : 1 / q * (Real.log (R + K * q) - Real.log R) ≤ 1 / q * Real.log (D / R) :=
    mul_le_mul_of_nonneg_left hlogD (by positivity)
  linarith

/-- `∑_{j<J} √(1 + q/(R + jq)) ≤ √(1 + q/R) + (D - R)/q + (1/2) log(D/R)` when
`R + (J-1)q ≤ D`. -/
theorem sum_sqrt_le {R q D : ℝ} (hR : 0 < R) (hq : 0 < q) {J : ℕ} (hJ : 1 ≤ J)
    (hD : R + (J - 1) * q ≤ D) :
    ∑ j ∈ range J, √(1 + q / (R + j * q)) ≤ √(1 + q / R) + (D - R) / q + 1 / 2 * Real.log (D / R) := by
  have hinv := sum_inv_le hR hq hJ hD
  obtain ⟨K, rfl⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  rw [sum_range_succ'] at hinv ⊢
  simp only [CharP.cast_eq_zero, zero_mul, add_zero] at hinv ⊢
  push_cast at hD; simp only [add_sub_cancel_right] at hD
  have hterm : ∀ j : ℕ, √(1 + q / (R + (j + 1 : ℕ) * q)) ≤ 1 + q / 2 * (1 / (R + (j + 1 : ℕ) * q)) := by
    intro j
    have h1 : 0 < R + (j + 1 : ℕ) * q := by positivity
    rw [Real.sqrt_le_left (by positivity)]
    have : 0 ≤ q / (R + (j + 1 : ℕ) * q) := by positivity
    have e : q / 2 * (1 / (R + (j + 1 : ℕ) * q)) = q / (R + (j + 1 : ℕ) * q) / 2 := by ring
    rw [e]
    nlinarith [sq_nonneg (q / (R + (j + 1 : ℕ) * q))]
  have hsum := sum_le_sum fun j (_ : j ∈ range K) => hterm j
  rw [sum_add_distrib, ← mul_sum] at hsum
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at hsum
  have hK : (K : ℝ) ≤ (D - R) / q := by rw [le_div_iff₀ hq]; linarith
  have hinv' : ∑ j ∈ range K, 1 / (R + (j + 1 : ℕ) * q) ≤ 1 / q * Real.log (D / R) := by linarith
  have : q / 2 * ∑ j ∈ range K, 1 / (R + (j + 1 : ℕ) * q) ≤ 1 / 2 * Real.log (D / R) := by
    calc q / 2 * ∑ j ∈ range K, 1 / (R + (j + 1 : ℕ) * q)
        ≤ q / 2 * (1 / q * Real.log (D / R)) := mul_le_mul_of_nonneg_left hinv' (by positivity)
      _ = 1 / 2 * Real.log (D / R) := by field_simp
  linarith

end TernaryGoldbach.MinorArcs
