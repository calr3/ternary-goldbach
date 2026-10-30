import TernaryGoldbach.MinorArcs.TypeIProof
import TernaryGoldbach.MinorArcs.Eta2Log
import TernaryGoldbach.MinorArcs.SumTools

/-!
# Proof of [B, Lemma 4.2.3] (Type I sums with `log n`; `η = η₂`)
-/

open Real Finset
open ArithmeticFunction (moebius)
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- The inner sum of `typeILog`, for `m ≥ 1`, is `T_{m,∘}` with smoothing `η_(x/m)`. -/
theorem innerLog_eq_ToddG {α x : ℝ} (hx : 0 < x) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Icc 1 ⌊x⌋₊,
        (if Odd n then (Real.log n : ℂ) * e (α * m * n) * (eta2 (m * n / x) : ℂ) else 0) =
      ToddG (eta2log (x / m)) α x m := by
  set N := ⌊x⌋₊
  set K := (N + 1) / 2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpt : ∀ n : ℕ, (Real.log n : ℂ) * e (α * m * n) * (eta2 (m * n / x) : ℂ) =
      e (α * m * n) * (eta2log (x / m) (m * n / x) : ℂ) := by
    intro n
    rw [eta2log, show x / m * (m * n / x) = (n : ℝ) by field_simp]
    push_cast; ring
  simp_rw [hpt]
  rw [sum_Icc_odd_eq N (fun n => e (α * m * n) * (eta2log (x / m) (m * n / x) : ℂ)), ToddG]
  rw [tsum_eq_sum (s := (range K).map Nat.castEmbedding)]
  · rw [sum_map]; refine sum_congr rfl fun r _ => ?_; simp
  · intro r hr
    simp only [mem_map, mem_range, Nat.castEmbedding_apply, not_exists, not_and] at hr
    rw [eta2log, Helfgott.eta2_eq_zero, mul_zero, Complex.ofReal_zero, mul_zero]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    rcases lt_or_ge r 0 with h | h
    · left
      have : (2 * (r : ℝ) + 1) ≤ 0 := by
        have : r ≤ -1 := by omega
        have : (r : ℝ) ≤ -1 := by exact_mod_cast this
        linarith
      have : m * (2 * (r : ℝ) + 1) / x ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) this) hx.le
      linarith
    · right
      have hrK : K ≤ r.toNat := by
        by_contra hlt; push Not at hlt
        exact hr r.toNat hlt (Int.toNat_of_nonneg h)
      have hr' : ((N : ℝ) + 1) ≤ 2 * r + 1 := by
        have : (N + 1 : ℤ) ≤ 2 * r + 1 := by
          have : (K : ℤ) ≤ r := by
            have := Int.toNat_of_nonneg h; omega
          omega
        exact_mod_cast this
      have hxN : x < N + 1 := Nat.lt_floor_add_one x
      rw [le_div_iff₀ hx]
      nlinarith

theorem typeILog_eq_sum {α x : ℝ} (hx : 0 < x) (D : ℝ) :
    typeILog α x D = ∑ m ∈ Icc 1 ⌊D⌋₊,
      if Odd m then (μ m : ℂ) * ToddG (eta2log (x / m)) α x m else 0 := by
  rw [typeILog]
  refine sum_congr rfl fun m hm => ?_
  split_ifs
  · rw [innerLog_eq_ToddG hx (mem_Icc.1 hm).1]
  · rfl

/-- `‖T_{m,∘}‖` for the smoothing `η_(x/m)`, indexed by integers. -/
noncomputable def TLn (α x : ℝ) (n : ℤ) : ℝ := ‖ToddG (eta2log (x / n.toNat)) α x n.toNat‖

theorem TLn_nonneg (α x : ℝ) (n : ℤ) : 0 ≤ TLn α x n := norm_nonneg _

/-- [B, p. 67]: `|T_{m,∘}| ≤ log(x/m) · minA(x/2m + |η'|₁/2, (m/x)(c₀/2), sin²)` for `x/m ≥ 4`. -/
theorem norm_ToddL_le_minA {α x δ : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x)
    (h2α : 2 * α = a / q + δ / x + k) {m : ℕ} (hm : 1 ≤ m) (hmx : 4 * m ≤ x) {A C : ℝ}
    (hA : x / (2 * m) + eta2'L1 / 2 ≤ A) (hC : m / x * (c₀ / 2) ≤ C) :
    ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * minA A C (Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 4 ≤ x / m := by rw [le_div_iff₀ (by linarith)]; linarith
  have hL : 0 ≤ Real.log (x / m) := Real.log_nonneg (by linarith)
  have hsd := smoothData_eta2log hρ
  have hs := sin_sq_two_pi_mul h2α (m : ℝ) ⟨m, by simp⟩
  obtain ⟨h1, h2⟩ := hsd.norm_ToddG_le hx hm α
  push_cast at hs ⊢
  have h1' : ‖ToddG (eta2log (x / m)) α x m‖ ≤ Real.log (x / m) * A := by
    refine h1.trans ?_
    have : x / (2 * m) * Real.log (x / m) + eta2'L1 * Real.log (x / m) / 2 =
        Real.log (x / m) * (x / (2 * m) + eta2'L1 / 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hA hL
  unfold minA
  split_ifs with h0
  · exact h1'
  · have hne : Real.sin (2 * π * m * α) ≠ 0 := by
      intro h; apply h0; rw [← hs, h]; ring
    rw [mul_min_of_nonneg _ _ hL]
    refine le_min h1' ?_
    refine (h2 hne).2.trans ?_
    rw [hs]
    have : m / x * (c₀ * Real.log (x / m) / 2) / Real.sin (π * (a / q + δ / x) * m) ^ 2 =
        Real.log (x / m) * (m / x * (c₀ / 2) / Real.sin (π * (a / q + δ / x) * m) ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC (sq_nonneg _)) hL

/-- The second and third bounds, with the factor `log(x/m)`. -/
theorem norm_ToddL_le_min_sin {α x δ : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x)
    (h2α : 2 * α = a / q + δ / x + k) {m : ℕ} (hm : 1 ≤ m) (hmx : 4 * m ≤ x)
    (hne : Real.sin (π * (a / q + δ / x) * (m : ℤ)) ≠ 0) {A B C : ℝ}
    (hA : x / (2 * m) + eta2'L1 / 2 ≤ A) (hB : eta2'L1 / 2 ≤ B) (hC : m / x * (c₀ / 2) ≤ C) :
    ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * min A (C / Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) ∧
    ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * min (B / |Real.sin (π * (a / q + δ / x) * (m : ℤ))|)
        (C / Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 4 ≤ x / m := by rw [le_div_iff₀ (by linarith)]; linarith
  have hL : 0 ≤ Real.log (x / m) := Real.log_nonneg (by linarith)
  have hsd := smoothData_eta2log hρ
  have hs := sin_sq_two_pi_mul h2α (m : ℝ) ⟨m, by simp⟩
  push_cast at hs hne ⊢
  have habs : |Real.sin (2 * π * m * α)| = |Real.sin (π * (a / q + δ / x) * m)| := by
    rw [← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs, hs]
  have hne' : Real.sin (2 * π * m * α) ≠ 0 := by
    intro h; apply hne; rw [← abs_eq_zero, ← habs, h, abs_zero]
  obtain ⟨h1, h2⟩ := hsd.norm_ToddG_le hx hm α
  obtain ⟨h2a, h2b⟩ := h2 hne'
  have hA' : ‖ToddG (eta2log (x / m)) α x m‖ ≤ Real.log (x / m) * A := by
    refine h1.trans ?_
    have : x / (2 * m) * Real.log (x / m) + eta2'L1 * Real.log (x / m) / 2 =
        Real.log (x / m) * (x / (2 * m) + eta2'L1 / 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hA hL
  have hC' : ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * (C / Real.sin (π * (a / q + δ / x) * m) ^ 2) := by
    refine h2b.trans ?_; rw [hs]
    have : m / x * (c₀ * Real.log (x / m) / 2) / Real.sin (π * (a / q + δ / x) * m) ^ 2 =
        Real.log (x / m) * (m / x * (c₀ / 2) / Real.sin (π * (a / q + δ / x) * m) ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC (sq_nonneg _)) hL
  have hB' : ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * (B / |Real.sin (π * (a / q + δ / x) * m)|) := by
    refine h2a.trans ?_; rw [habs]
    have : eta2'L1 * Real.log (x / m) / 2 / |Real.sin (π * (a / q + δ / x) * m)| =
        Real.log (x / m) * (eta2'L1 / 2 / |Real.sin (π * (a / q + δ / x) * m)|) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hB (abs_nonneg _)) hL
  rw [mul_min_of_nonneg _ _ hL, mul_min_of_nonneg _ _ hL]
  exact ⟨le_min hA' hC', le_min hB' hC'⟩

end TernaryGoldbach.MinorArcs
