import TernaryGoldbach.Helfgott.Numerics

/-!
# Bounding the non-prime terms [H, (14.51)]

The terms of the weighted count where some `nᵢ` is even or not prime contribute at most
`3 A₊² A_* · log N · (∑_{n ≤ N, n even or non-prime} Λ(n)) · ψ(N)`, where `A₊ ≥ |η₊|`,
`A_* ≥ |η_*|` on `[0, ∞)`.  The middle sum is at most `ψ(N) - θ(N) + log 2`.

This file proves that reduction with the constants as parameters
(`repSum_sub_le_of_bounds`).  The numerical inputs are in `Helfgott/Inputs.lean`.

Proved, with no `sorry`.
-/

open Finset
open ArithmeticFunction (vonMangoldt_nonneg vonMangoldt_le_log vonMangoldt_apply_prime)
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Helfgott

/-- Chebyshev's `ψ(N) = ∑_{n ≤ N} Λ(n)`. -/
noncomputable def psi (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), Λ n

open Classical in
/-- Chebyshev's `θ(N) = ∑_{p ≤ N} log p`, written as `∑_{n ≤ N, n prime} Λ(n)`. -/
noncomputable def theta (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), if n.Prime then Λ n else 0

/-- The weighted triple convolution `∑_{n₁+n₂+n₃=N} f(n₁) g(n₂) h(n₃)`. -/
noncomputable def tri (f g h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n₁ ∈ range (N + 1), ∑ n₂ ∈ range (N + 1), ∑ n₃ ∈ range (N + 1),
    if n₁ + n₂ + n₃ = N then f n₁ * g n₂ * h n₃ else 0

theorem tri_swap23 (f g h : ℕ → ℝ) (N : ℕ) : tri f g h N = tri f h g N := by
  unfold tri
  refine sum_congr rfl fun n₁ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n₂ _ => sum_congr rfl fun n₃ _ => ?_
  rw [show n₁ + n₃ + n₂ = n₁ + n₂ + n₃ by ring, mul_right_comm]

/-- `∑_{n₁+n₂+n₃=N} f g h ≤ (∑ f)(∑ g) · sup h` for nonnegative `f, g, h`. -/
theorem tri_le {f g h : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (hh : ∀ n, 0 ≤ h n)
    {N : ℕ} {B : ℝ} (hB : ∀ n ≤ N, h n ≤ B) :
    tri f g h N ≤ (∑ n ∈ range (N + 1), f n) * (∑ n ∈ range (N + 1), g n) * B := by
  have hB0 : 0 ≤ B := (hh 0).trans (hB 0 (Nat.zero_le _))
  rw [sum_mul_sum, sum_mul]
  refine sum_le_sum fun n₁ _ => ?_
  rw [sum_mul]
  refine sum_le_sum fun n₂ _ => ?_
  rw [← sum_filter]
  calc ∑ n₃ ∈ (range (N + 1)).filter (fun n₃ => n₁ + n₂ + n₃ = N), f n₁ * g n₂ * h n₃
      ≤ ((range (N + 1)).filter (fun n₃ => n₁ + n₂ + n₃ = N)).card • (f n₁ * g n₂ * B) := by
        refine sum_le_card_nsmul _ _ _ fun n₃ hn₃ => ?_
        rw [mem_filter] at hn₃
        exact mul_le_mul_of_nonneg_left (hB n₃ (by omega)) (mul_nonneg (hf _) (hg _))
    _ ≤ 1 • (f n₁ * g n₂ * B) := by
        refine nsmul_le_nsmul_left (mul_nonneg (mul_nonneg (hf _) (hg _)) hB0) ?_
        refine card_le_one.2 fun a ha b hb => ?_
        rw [mem_filter] at ha hb
        omega
    _ = f n₁ * g n₂ * B := one_nsmul _

theorem vonMangoldt_le_log_of_le {n N : ℕ} (hN : 1 ≤ N) (hn : n ≤ N) : Λ n ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [ArithmeticFunction.map_zero]
    exact Real.log_nonneg (by exact_mod_cast hN)
  · exact vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn))

/-- "Good" summands: odd primes. -/
def Good (n : ℕ) : Prop := n.Prime ∧ Odd n

open Classical in
/-- `Λ` restricted to bad (even or non-prime) `n`. -/
noncomputable def ΛBad (n : ℕ) : ℝ := if Good n then 0 else Λ n

theorem ΛBad_nonneg (n : ℕ) : 0 ≤ ΛBad n := by
  unfold ΛBad; split_ifs <;> simp [vonMangoldt_nonneg]

theorem ΛBad_le (n : ℕ) : ΛBad n ≤ Λ n := by
  unfold ΛBad; split_ifs <;> simp [vonMangoldt_nonneg]

/-- `∑_{n ≤ N, n even or non-prime} Λ(n) ≤ ψ(N) - θ(N) + log 2`. -/
theorem sum_ΛBad_le (N : ℕ) : ∑ n ∈ range (N + 1), ΛBad n ≤ psi N - theta N + Real.log 2 := by
  classical
  have hsplit : psi N - theta N = ∑ n ∈ range (N + 1), if n.Prime then 0 else Λ n := by
    rw [psi, theta, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have hlog2 : ∑ n ∈ range (N + 1), (if n = 2 then Real.log 2 else 0) ≤ Real.log 2 := by
    rw [sum_ite_eq' (range (N + 1)) 2 (fun _ => Real.log 2)]
    split_ifs
    · exact le_rfl
    · exact Real.log_nonneg (by norm_num)
  rw [hsplit]
  refine le_trans ?_ (add_le_add le_rfl hlog2)
  rw [← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  unfold ΛBad Good
  have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hp : n.Prime
  · by_cases ho : Odd n
    · simp only [hp, ho, and_self, ite_true]
      split_ifs <;> linarith
    · have : n = 2 := (hp.eq_two_or_odd').resolve_right ho
      subst this
      simp [hp, ho, vonMangoldt_apply_prime hp]
  · simp only [hp, false_and, ite_false, ite_true]
    split_ifs <;> simp [vonMangoldt_nonneg, h2]

/-- **[H, (14.51)] with the constants as parameters.** -/
theorem repSum_sub_le_of_bounds {N : ℕ} (hN : 1 ≤ N) {Ap As : ℝ}
    (hAp : ∀ t, 0 ≤ t → |etaPlus t| ≤ Ap) (hAs : ∀ t, 0 ≤ t → |etaStar t| ≤ As) :
    repSum (fun _ => True) N - repSum Good N ≤
      3 * (Ap ^ 2 * As) * Real.log N * (psi N - theta N + Real.log 2) * psi N := by
  classical
  have hx : 0 < xOf N := div_pos (by exact_mod_cast hN) xOf_denom_bounds.1
  have hAp0 : 0 ≤ Ap := (abs_nonneg _).trans (hAp 0 le_rfl)
  have hAs0 : 0 ≤ As := (abs_nonneg _).trans (hAs 0 le_rfl)
  set A := Ap ^ 2 * As
  have hA0 : 0 ≤ A := mul_nonneg (sq_nonneg _) hAs0
  -- Pointwise comparison with `A · (T₁ + T₂ + T₃)`.
  have hpt : repSum (fun _ => True) N - repSum Good N ≤
      A * (tri ΛBad (fun n => Λ n) (fun n => Λ n) N + tri (fun n => Λ n) ΛBad (fun n => Λ n) N +
        tri (fun n => Λ n) (fun n => Λ n) ΛBad N) := by
    unfold repSum tri
    simp only [← sum_sub_distrib, ← sum_add_distrib, mul_sum]
    refine sum_le_sum fun n₁ _ => sum_le_sum fun n₂ _ => sum_le_sum fun n₃ _ => ?_
    have hΛ := fun n : ℕ => (vonMangoldt_nonneg (n := n))
    by_cases hs : n₁ + n₂ + n₃ = N
    · simp only [hs, true_and, and_true, ite_true]
      have hterm : |Λ n₁ * Λ n₂ * Λ n₃ * etaPlus (n₁ / xOf N) * etaPlus (n₂ / xOf N) *
          etaStar (n₃ / xOf N)| ≤ A * (Λ n₁ * Λ n₂ * Λ n₃) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hΛ n₁),
          abs_of_nonneg (hΛ n₂), abs_of_nonneg (hΛ n₃)]
        have h1 := hAp (n₁ / xOf N) (by positivity)
        have h2 := hAp (n₂ / xOf N) (by positivity)
        have h3 := hAs (n₃ / xOf N) (by positivity)
        have hP : 0 ≤ Λ n₁ * Λ n₂ * Λ n₃ := mul_nonneg (mul_nonneg (hΛ n₁) (hΛ n₂)) (hΛ n₃)
        calc Λ n₁ * Λ n₂ * Λ n₃ * |etaPlus (n₁ / xOf N)| * |etaPlus (n₂ / xOf N)| *
              |etaStar (n₃ / xOf N)|
            ≤ Λ n₁ * Λ n₂ * Λ n₃ * Ap * Ap * As := by gcongr
          _ = A * (Λ n₁ * Λ n₂ * Λ n₃) := by simp only [A]; ring
      have hB1 := ΛBad_nonneg n₁
      have hB2 := ΛBad_nonneg n₂
      have hB3 := ΛBad_nonneg n₃
      have hT : 0 ≤ ΛBad n₁ * Λ n₂ * Λ n₃ + Λ n₁ * ΛBad n₂ * Λ n₃ + Λ n₁ * Λ n₂ * ΛBad n₃ := by
        have := hΛ n₁; have := hΛ n₂; have := hΛ n₃; positivity
      split_ifs with hg
      · rw [sub_self]; exact mul_nonneg hA0 hT
      · rw [sub_zero]
        refine (le_abs_self _).trans (hterm.trans (mul_le_mul_of_nonneg_left ?_ hA0))
        have := hΛ n₁; have := hΛ n₂; have := hΛ n₃
        simp only [not_and_or] at hg
        rcases hg with hg | hg | hg
        · have : ΛBad n₁ = Λ n₁ := by simp [ΛBad, hg]
          rw [this]; nlinarith [mul_nonneg (mul_nonneg (hΛ n₁) hB2) (hΛ n₃),
            mul_nonneg (mul_nonneg (hΛ n₁) (hΛ n₂)) hB3]
        · have : ΛBad n₂ = Λ n₂ := by simp [ΛBad, hg]
          rw [this]; nlinarith [mul_nonneg (mul_nonneg hB1 (hΛ n₂)) (hΛ n₃),
            mul_nonneg (mul_nonneg (hΛ n₁) (hΛ n₂)) hB3]
        · have : ΛBad n₃ = Λ n₃ := by simp [ΛBad, hg]
          rw [this]; nlinarith [mul_nonneg (mul_nonneg hB1 (hΛ n₂)) (hΛ n₃),
            mul_nonneg (mul_nonneg (hΛ n₁) hB2) (hΛ n₃)]
    · simp [hs]
  -- Each `Tᵢ ≤ (∑ ΛBad) · ψ(N) · log N`.
  have hΛ0 : ∀ n, 0 ≤ (fun n => Λ n) n := fun n => vonMangoldt_nonneg
  have hlog : ∀ n ≤ N, (fun n => Λ n) n ≤ Real.log N := fun n hn =>
    vonMangoldt_le_log_of_le hN hn
  have hlogB : ∀ n ≤ N, ΛBad n ≤ Real.log N := fun n hn =>
    (ΛBad_le n).trans (vonMangoldt_le_log_of_le hN hn)
  have T1 := tri_le ΛBad_nonneg hΛ0 hΛ0 hlog
  have T2 := tri_le hΛ0 ΛBad_nonneg hΛ0 hlog
  have T3 : tri (fun n => Λ n) (fun n => Λ n) ΛBad N ≤
      (∑ n ∈ range (N + 1), Λ n) * (∑ n ∈ range (N + 1), ΛBad n) * Real.log N := by
    rw [tri_swap23]; exact tri_le hΛ0 ΛBad_nonneg hΛ0 hlog
  have hbad := sum_ΛBad_le N
  have hpsi0 : 0 ≤ psi N := sum_nonneg fun n _ => vonMangoldt_nonneg
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hsumB0 : 0 ≤ ∑ n ∈ range (N + 1), ΛBad n := sum_nonneg fun n _ => ΛBad_nonneg n
  change _ ≤ (∑ n ∈ range (N + 1), ΛBad n) * psi N * Real.log N at T1
  change _ ≤ psi N * (∑ n ∈ range (N + 1), ΛBad n) * Real.log N at T2
  change _ ≤ psi N * (∑ n ∈ range (N + 1), ΛBad n) * Real.log N at T3
  have hmono : (∑ n ∈ range (N + 1), ΛBad n) * psi N * Real.log N ≤
      (psi N - theta N + Real.log 2) * psi N * Real.log N := by gcongr
  calc repSum (fun _ => True) N - repSum Good N
      ≤ A * (3 * ((∑ n ∈ range (N + 1), ΛBad n) * psi N * Real.log N)) := by
        refine hpt.trans (mul_le_mul_of_nonneg_left ?_ hA0)
        linarith
    _ ≤ A * (3 * ((psi N - theta N + Real.log 2) * psi N * Real.log N)) := by gcongr
    _ = _ := by ring

end TernaryGoldbach.Helfgott
