import TernaryGoldbach.Prelim.EOneRanges
import TernaryGoldbach.Prelim.MoebiusCDE

/-!
# `E(u) = E₁Λ(u) + γ` on the ranges of `u ≥ 10⁶`

* `[10⁶, 9.9·10⁶]`: `|E(u)| ≤ 11.82/√u + 10⁻¹³` (`|ψ(n) − n| ≤ 2√n` below `2·10⁸`);
* `[2·10⁸, 1.58·10⁹]`: `112.7/√u + 10⁻¹³` (`cB ≤ 35.5`);
* `[1.58·10⁹, 4.9·10¹³]`: `222.6/√u + 10⁻¹³` (`cB ≤ 72`).
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens TernaryGoldbach.Explicit

theorem exp_window_le : Real.exp (3 + 0.003) ≤ 20.15 := by
  rw [Real.exp_add]
  have h1 := exp_three_le
  have h2 := exp_small_le2 (t := 0.003) (by norm_num) (by norm_num)
  nlinarith [Real.exp_pos 3, Real.exp_pos 0.003]

theorem exp_neg_window_ge : 0.997 ≤ Real.exp (-0.003) := by
  have := Real.add_one_le_exp (-0.003); linarith

variable [Fact TernaryGoldbach.PlattGRH]

/-- `|E(u)|` from a `C√n` bound for `ψ` on `[12, U]`, `u e^{3.003} ≤ U`, `u ≥ 10⁶`. -/
theorem E_sqrt_of {u C U : ℝ} (hu : 1e6 ≤ u) (hC : 0 ≤ C) (hU : u * 20.15 ≤ U)
    (hψ : ∀ n : ℕ, 12 ≤ n → (n : ℝ) ≤ U → |psiN n - n| ≤ C * √(n : ℝ)) :
    |Eg u| ≤ (3.01 * C + 5.8) / √u + 1e-13 := by
  refine E_bound_sqrt hu hC fun n h1 h2 => hψ n ?_ (h2.trans ?_)
  · have : 12 ≤ ⌊u * Real.exp (-0.003)⌋₊ := Nat.le_floor (by
      push_cast; nlinarith [exp_neg_window_ge])
    omega
  · have := exp_window_le
    nlinarith

theorem E_R1 {u : ℝ} (h1 : 1e6 ≤ u) (h2 : u ≤ 9.9e6) : |Eg u| ≤ 11.82 / √u + 1e-13 := by
  have := E_sqrt_of (C := 2) (U := 199485000) h1 (by norm_num) (by linarith)
    fun n hn1 hn2 => psi_le_two hn1 (by exact_mod_cast (show (n : ℝ) < 200000000 by linarith))
  norm_num at this ⊢; linarith

theorem E_R3 {u : ℝ} (h1 : 2e8 ≤ u) (h2 : u ≤ 1.58e9) : |Eg u| ≤ 112.7 / √u + 1e-13 := by
  have := E_sqrt_of (C := 35.5) (U := 32000000000) (by norm_num at h1 ⊢; linarith) (by norm_num)
    (by norm_num at h2 ⊢; linarith)
    fun n hn1 hn2 => by
      have hn : n ≤ 32000000000 := by exact_mod_cast hn2
      have h := psi_two_sided hn1 (by omega)
      have hc := cB_le_355 hn
      unfold psiN
      exact h.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
  have hs : 0 < √u := Real.sqrt_pos.2 (by norm_num at h1; linarith)
  have : (3.01 * 35.5 + 5.8) / √u ≤ 112.7 / √u := div_le_div_of_nonneg_right (by norm_num) hs.le
  linarith

theorem E_R4 {u : ℝ} (h1 : 1.58e9 ≤ u) (h2 : u ≤ 4.9e13) : |Eg u| ≤ 222.6 / √u + 1e-13 := by
  have := E_sqrt_of (C := 72) (U := 1e15) (by norm_num at h1 ⊢; linarith) (by norm_num)
    (by norm_num at h2 ⊢; linarith)
    fun n hn1 hn2 => by
      have hn : n ≤ 10 ^ 15 := by
        have : (n : ℝ) ≤ ((10 ^ 15 : ℕ) : ℝ) := by norm_num at hn2 ⊢; linarith
        exact_mod_cast this
      have h := psi_two_sided hn1 (le_trans hn (by norm_num))
      have hc := cB_le_72 hn
      unfold psiN
      exact h.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
  have hs : 0 < √u := Real.sqrt_pos.2 (by norm_num at h1; linarith)
  have : (3.01 * 72 + 5.8) / √u ≤ 222.6 / √u := div_le_div_of_nonneg_right (by norm_num) hs.le
  linarith

omit [Fact TernaryGoldbach.PlattGRH] in
/-- **Summation by parts with two constants**: `C₁` below `B`, `C₂ ≥ C₁` from `B` on (`M < B`):
`|E₁Λ(t) − E₁Λ(M)| ≤ 3/M + 4C₁/√M + 2C₂/√B`. -/
theorem E1_diff_two {M B : ℕ} (hM : 1 ≤ M) (hMB : M < B) {t : ℝ} (ht : (M : ℝ) ≤ t) {C₁ C₂ : ℝ}
    (h1 : 0 ≤ C₁) (h12 : C₁ ≤ C₂)
    (herr : ∀ n : ℕ, M ≤ n → n ≤ ⌊t⌋₊ → |psiN n - n| ≤ (if n < B then C₁ else C₂) * √(n : ℝ)) :
    |E₁Λ t - E₁Λ M| ≤ 3 / M + 4 * C₁ / √(M : ℝ) + 2 * C₂ / √(B : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hsM : 0 < √(M : ℝ) := Real.sqrt_pos.2 hM0
  have hsB : 0 < √(B : ℝ) := Real.sqrt_pos.2 hB0
  have hC2 : 0 ≤ C₂ := le_trans h1 h12
  set err : ℕ → ℝ := fun n => (if n < B then C₁ else C₂) * √(n : ℝ) with herrd
  have herr0 : ∀ n, 0 ≤ err n := fun n => by
    simp only [herrd]; split_ifs <;> positivity
  have h := E1_diff_gen hM ht err herr0 herr
  set N := ⌊t⌋₊ with hN
  have hMN : M ≤ N := Nat.le_floor ht
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 (by exact_mod_cast hMN)
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN0
  have hdiv : ∀ n : ℕ, 0 < n → √(n : ℝ) / n = 1 / √(n : ℝ) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs := Real.mul_self_sqrt hn0.le
    have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    field_simp; nlinarith [hs]
  -- `err(M)/M = C₁/√M`
  have hEM : err M / M = C₁ / √(M : ℝ) := by
    simp only [herrd, if_pos hMB]; rw [mul_div_assoc, hdiv M (by omega)]; ring
  -- the interior sum
  have hterm : ∀ n ∈ Ioo M N, err n / (n * (n + 1)) ≤
      C₁ * (1 / (√(n : ℝ) * (n + 1))) + (if B ≤ n then C₂ * (1 / (√(n : ℝ) * (n + 1))) else 0) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := (mem_Ioo.1 hn).1; omega : 0 < n)
    have hs := Real.mul_self_sqrt hn0.le
    have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    have e : √(n : ℝ) / (n * (n + 1)) = 1 / (√(n : ℝ) * (n + 1)) := by
      field_simp; nlinarith [hs]
    simp only [herrd]
    rw [mul_div_assoc, e]
    have hp : 0 ≤ 1 / (√(n : ℝ) * (n + 1)) := by positivity
    split_ifs with hb1 hb2 hb2
    · omega
    · linarith [mul_nonneg h1 hp]
    · nlinarith
    · omega
  have hsum1 : ∑ n ∈ Ioo M N, (1 : ℝ) / (√(n : ℝ) * (n + 1)) ≤ 2 / √(M : ℝ) := by
    rcases eq_or_lt_of_le hMN with hEq | hlt
    · rw [← hEq, Ioo_self, sum_empty]; positivity
    refine (sum_inv_sqrt_le hlt).trans ?_
    have : 2 / √((M : ℝ) + 1) ≤ 2 / √(M : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hsM (Real.sqrt_le_sqrt (by linarith))
    have : 0 ≤ 2 / √(N : ℝ) := by positivity
    linarith
  have hsum2 : ∑ n ∈ Ioo M N, (if B ≤ n then C₂ * (1 / (√(n : ℝ) * (n + 1))) else 0) ≤
      C₂ * (2 / √(B : ℝ) - (if B ≤ N then 2 / √(N : ℝ) else 0)) := by
    rw [← sum_filter]
    have hsub : (Ioo M N).filter (fun n => B ≤ n) ⊆ Ioo (B - 1) N := by
      intro n hn; simp only [mem_filter, mem_Ioo] at hn ⊢; omega
    rcases lt_or_ge (B - 1) N with hlt | hge
    · refine (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity).trans ?_
      rw [← mul_sum]
      refine mul_le_mul_of_nonneg_left ((sum_inv_sqrt_le hlt).trans (le_of_eq ?_)) hC2
      rw [show ((B - 1 : ℕ) : ℝ) + 1 = B by push_cast [Nat.cast_sub (by omega : 1 ≤ B)]; ring]
      split_ifs with hBN
      · rfl
      · push Not at hBN; omega
    · have : (Ioo M N).filter (fun n => B ≤ n) = ∅ := by
        ext n; simp only [mem_filter, mem_Ioo, Finset.notMem_empty, iff_false]; omega
      rw [this, sum_empty, if_neg (by omega), sub_zero]; positivity
  have hS := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at hS
  -- `err(N)/N`
  rcases lt_or_ge N B with hNB | hNB
  · have hEN : err N / N = C₁ / √(N : ℝ) := by
      simp only [herrd, if_pos hNB]; rw [mul_div_assoc, hdiv N (by omega)]; ring
    have hle : C₁ / √(N : ℝ) ≤ C₁ / √(M : ℝ) :=
      div_le_div_of_nonneg_left h1 hsM (Real.sqrt_le_sqrt (by exact_mod_cast hMN))
    rw [if_neg (by omega), sub_zero] at hsum2
    rw [hEN, hEM] at h
    have := mul_le_mul_of_nonneg_left hsum1 h1
    have e1 : C₁ * (2 / √(M : ℝ)) = 2 * C₁ / √(M : ℝ) := by ring
    have e2 : C₂ * (2 / √(B : ℝ)) = 2 * C₂ / √(B : ℝ) := by ring
    have e3 : 4 * C₁ / √(M : ℝ) = C₁ / √(M : ℝ) + C₁ / √(M : ℝ) + 2 * C₁ / √(M : ℝ) := by ring
    linarith
  · have hEN : err N / N = C₂ / √(N : ℝ) := by
      simp only [herrd, if_neg (show ¬ N < B by omega)]; rw [mul_div_assoc, hdiv N (by omega)]; ring
    rw [if_pos hNB] at hsum2
    rw [hEN, hEM] at h
    have := mul_le_mul_of_nonneg_left hsum1 h1
    have e1 : C₁ * (2 / √(M : ℝ)) = 2 * C₁ / √(M : ℝ) := by ring
    have e2 : C₂ * (2 / √(B : ℝ) - 2 / √(N : ℝ)) = 2 * C₂ / √(B : ℝ) - 2 * (C₂ / √(N : ℝ)) := by ring
    have hp : 0 ≤ C₂ / √(N : ℝ) := by positivity
    have hp2 : 0 ≤ C₁ / √(M : ℝ) := by positivity
    have e3 : 4 * C₁ / √(M : ℝ) = C₁ / √(M : ℝ) + 2 * C₁ / √(M : ℝ) + C₁ / √(M : ℝ) := by ring
    linarith

theorem E_R2 {u : ℝ} (h1 : 9.9e6 ≤ u) (h2 : u < 2e8) : |Eg u| ≤ 13.6 / √u + 0.00503 + 1e-13 := by
  have hu0 : 0 < u := by norm_num at h1; linarith
  have hek := exp_neg_window_ge
  have hek1 : Real.exp (-0.003) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  set M₂ := ⌊u * Real.exp (-0.003)⌋₊ with hM₂
  have hM₂ge : 0.9969 * u ≤ (M₂ : ℝ) := by
    have h1' : u * Real.exp (-0.003) < (M₂ : ℝ) + 1 := Nat.lt_floor_add_one _
    have := mul_le_mul_of_nonneg_left hek hu0.le
    norm_num at h1; nlinarith
  have hM2 : 1 ≤ M₂ := by
    have : (1 : ℝ) ≤ M₂ := by norm_num at h1; linarith
    exact_mod_cast this
  have hM₂0 : (0 : ℝ) < M₂ := by linarith
  set A0 := 3 / (M₂ : ℝ) + 4 * 2 / √(M₂ : ℝ) + 2 * 35.5 / √((200000000 : ℕ) : ℝ) with hA0
  have hE := E_bound_A (Y := u) (A0 := A0) (by norm_num at h1; linarith) (by positivity) hM2
    fun m hm1 hm2 t ht1 ht2 => by
      have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hM₂0 (by exact_mod_cast hm1)
      have hm1' : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by
        have : (M₂ : ℝ) ≤ m := by exact_mod_cast hm1
        linarith)
      have hmB : m < 200000000 := by
        have : (m : ℝ) < 200000000 := by linarith
        exact_mod_cast this
      have h := E1_diff_two (B := 200000000) hm1' hmB ht1 (C₁ := 2) (C₂ := 35.5) (by norm_num)
        (by norm_num) fun n hn1 hn2 => by
          have hn12 : 12 ≤ n := by
            have : (12 : ℝ) ≤ m := by
              have : (M₂ : ℝ) ≤ m := by exact_mod_cast hm1
              norm_num at h1; linarith
            have : 12 ≤ m := by exact_mod_cast this
            omega
          split_ifs with hnB
          · exact psi_le_two hn12 hnB
          · have hn32 : n ≤ 32000000000 := by
              have : (n : ℝ) ≤ t := le_trans (by exact_mod_cast hn2) (Nat.floor_le (by linarith))
              have := exp_window_le
              have : (n : ℝ) ≤ 32000000000 := by norm_num at h2; nlinarith
              exact_mod_cast this
            have h := psi_two_sided hn12 (by omega)
            have hc := cB_le_355 hn32
            unfold psiN
            exact h.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
      refine h.trans ?_
      have hle : (M₂ : ℝ) ≤ m := by exact_mod_cast hm1
      have k1 : 3 / (m : ℝ) ≤ 3 / M₂ := div_le_div_of_nonneg_left (by norm_num) hM₂0 hle
      have k2 : 4 * 2 / √(m : ℝ) ≤ 4 * 2 / √(M₂ : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hM₂0) (Real.sqrt_le_sqrt hle)
      rw [hA0]; linarith
  rw [← hM₂] at hE
  refine hE.trans ?_
  -- numerics
  have hsu : 0 < √u := Real.sqrt_pos.2 hu0
  have hsuu := Real.mul_self_sqrt hu0.le
  have hsM : 0.9984 * √u ≤ √(M₂ : ℝ) := by
    have h3 : √(0.9969 * u) ≤ √(M₂ : ℝ) := Real.sqrt_le_sqrt hM₂ge
    rw [Real.sqrt_mul (by norm_num)] at h3
    have : 0.9984 ≤ √(0.9969 : ℝ) := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg u]
  have hs10 : 3146 ≤ √u := by rw [Real.le_sqrt (by norm_num) hu0.le]; norm_num at h1 ⊢; linarith
  have hB : √((200000000 : ℕ) : ℝ) ≥ 14142.1 := by
    rw [ge_iff_le, Real.le_sqrt (by norm_num) (by positivity)]; norm_num
  have k1 : 4 * 2 / √(M₂ : ℝ) ≤ 8.02 / √u := by
    rw [div_le_div_iff₀ (by linarith) hsu]; nlinarith
  have k2 : 3 / (M₂ : ℝ) + 1 / M₂ ≤ 0.002 / √u := by
    rw [← add_div, div_le_div_iff₀ hM₂0 hsu]; nlinarith
  have k3 : 2 * 35.5 / √((200000000 : ℕ) : ℝ) ≤ 0.00503 := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]; nlinarith
  have k4 : 1.8e5 * u ^ (-(3 / 2) : ℝ) ≤ 0.02 / √u := by
    have e : u ^ (-(3 / 2) : ℝ) = 1 / (u * √u) := by
      rw [Real.rpow_neg hu0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hu0,
        Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
    rw [e, mul_one_div, div_le_div_iff₀ (by positivity) hsu]
    norm_num at h1; nlinarith
  have e5 : 13.6 / √u = 8.02 / √u + 5.53 / √u + 0.002 / √u + 0.02 / √u + 0.028 / √u := by ring
  have : 0 ≤ 0.028 / √u := by positivity
  rw [hA0] at *
  linarith

set_option maxHeartbeats 1000000 in
/-- The plateau range: `|E(u)| ≤ 2.51/log³u + 1.234·10⁻⁶ + 97/√u + 10⁻¹²` for `u ≥ 4.9·10¹³`
(window `a = 1/2`, `|ψ(n) − n| ≤ n/log³n + ε_pl n + 7.04√n`). -/
theorem E_R5 {u : ℝ} (h1 : 4.9e13 ≤ u) :
    |Eg u| ≤ 2.51 / Real.log u ^ 3 + 1.234e-6 + 97 / √u + 1e-12 := by
  have hu0 : 0 < u := by norm_num at h1; linarith
  have hek := exp_neg_window_ge
  set M₂ := ⌊u * Real.exp (-0.003)⌋₊ with hM₂
  have hM₂ge : 0.9969 * u ≤ (M₂ : ℝ) := by
    have h1' : u * Real.exp (-0.003) < (M₂ : ℝ) + 1 := Nat.lt_floor_add_one _
    have := mul_le_mul_of_nonneg_left hek hu0.le
    norm_num at h1; nlinarith
  have hM2big : (1e12 : ℝ) ≤ M₂ := by norm_num at h1; linarith
  have hM2 : 1 ≤ M₂ := by exact_mod_cast (show (1 : ℝ) ≤ M₂ by linarith)
  have hM₂0 : (0 : ℝ) < M₂ := by linarith
  have hLM : (31 : ℝ) ≤ Real.log M₂ := by
    have := nat_le_log (N := (M₂ : ℝ)) (k := 31) (by norm_num at h1 ⊢; nlinarith)
    exact_mod_cast this
  set L := Real.log M₂ with hL
  set A0 := 3 / (M₂ : ℝ) + 2.5062 * (1 / L ^ 3 + 4.92e-7) + 28.16 / √(M₂ : ℝ) with hA0
  have hLpos : 0 < L := by linarith
  have hE := E_bound_A_half (Y := u) (A0 := A0) (by norm_num at h1; linarith) (by positivity) hM2
    fun m hm1 hm2 t ht1 ht2 => by
      have hle : (M₂ : ℝ) ≤ m := by exact_mod_cast hm1
      have hm0 : (0 : ℝ) < m := by linarith
      have hm12 : 1000000000000 ≤ m := by
        have : (1000000000000 : ℝ) ≤ m := by norm_num at hM2big; linarith
        exact_mod_cast this
      have hLm : L ≤ Real.log m := Real.log_le_log hM₂0 hle
      set err : ℕ → ℝ := fun n => n / Real.log n ^ 3 + epl n * n + 7.04 * √(n : ℝ) with herrd
      have herr0 : ∀ n, 0 ≤ err n := fun n => by
        simp only [herrd]
        have := epl_nonneg (n : ℝ)
        have := Real.log_natCast_nonneg n
        positivity
      have h := E1_diff_gen (by omega) ht1 err herr0 fun n hn1 _ => psi_err (by omega)
      set N := ⌊t⌋₊ with hN
      have hmN : m ≤ N := Nat.le_floor ht1
      -- `err(n)/n ≤ 1/L³ + 4.92e-7 + 7.04/√m` for `n ≥ m`
      have hper : ∀ n : ℕ, m ≤ n → err n / n ≤ 1 / L ^ 3 + 4.92e-7 + 7.04 / √(m : ℝ) := by
        intro n hn
        have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hm0 (by exact_mod_cast hn)
        have hnm : (m : ℝ) ≤ n := by exact_mod_cast hn
        have hLn : L ≤ Real.log n := hLm.trans (Real.log_le_log hm0 hnm)
        have hs := Real.mul_self_sqrt hn0.le
        have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
        have e : err n / n = 1 / Real.log n ^ 3 + epl n + 7.04 / √(n : ℝ) := by
          simp only [herrd]; field_simp; ring_nf; nlinarith [hs]
        rw [e]
        have k1 : 1 / Real.log n ^ 3 ≤ 1 / L ^ 3 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hLpos.le hLn 3)
        have k2 := epl_le (n : ℝ)
        have k3 : 7.04 / √(n : ℝ) ≤ 7.04 / √(m : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hm0) (Real.sqrt_le_sqrt hnm)
        linarith
      -- the interior sum
      have hint : ∑ n ∈ Ioo m N, err n / (n * (n + 1)) ≤
          (1 / L ^ 3 + 4.92e-7) * 0.5062 + 14.08 / √(m : ℝ) := by
        have hterm : ∀ n ∈ Ioo m N, err n / (n * (n + 1)) ≤
            (1 / L ^ 3 + 4.92e-7) * (1 / ((n : ℝ) + 1)) + 7.04 * (1 / (√(n : ℝ) * (n + 1))) := by
          intro n hn
          have hn' := (mem_Ioo.1 hn).1
          have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hm0 (by exact_mod_cast hn'.le)
          have hnm : (m : ℝ) ≤ n := by exact_mod_cast hn'.le
          have hLn : L ≤ Real.log n := hLm.trans (Real.log_le_log hm0 hnm)
          have hs := Real.mul_self_sqrt hn0.le
          have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
          have e : err n / (n * (n + 1)) = (1 / Real.log n ^ 3 + epl n) * (1 / ((n : ℝ) + 1)) +
              7.04 * (1 / (√(n : ℝ) * (n + 1))) := by
            simp only [herrd]; field_simp; ring_nf; nlinarith [hs]
          rw [e]
          have k1 : 1 / Real.log n ^ 3 ≤ 1 / L ^ 3 :=
            one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hLpos.le hLn 3)
          have k2 := epl_le (n : ℝ)
          have := mul_le_mul_of_nonneg_right (add_le_add k1 k2) (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))
          linarith
        refine (sum_le_sum hterm).trans ?_
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        rcases eq_or_lt_of_le hmN with hEq | hlt
        · rw [← hEq, Ioo_self, sum_empty, sum_empty]; simp; positivity
        have s1 := sum_inv_succ_le hlt
        have s2 := sum_inv_sqrt_le hlt
        have hlogN : Real.log N - Real.log ((m : ℝ) + 1) ≤ 0.5062 := by
          have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hm0 (by exact_mod_cast hmN)
          have h3 : Real.log N ≤ Real.log t := Real.log_le_log hN0 (Nat.floor_le (by linarith))
          have h4 : Real.log t ≤ Real.log u + 0.503 := by
            have := Real.log_le_log (by linarith) ht2
            rw [Real.log_mul hu0.ne' (Real.exp_pos _).ne', Real.log_exp] at this
            linarith
          have h5 : Real.log u - Real.log ((m : ℝ) + 1) ≤ 0.0032 := by
            rw [← Real.log_div hu0.ne' (by positivity)]
            have := Real.log_le_sub_one_of_pos (show 0 < u / ((m : ℝ) + 1) by positivity)
            have h6 : u / ((m : ℝ) + 1) - 1 ≤ 0.0032 := by
              rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]; nlinarith
            linarith
          linarith
        have hs2 : 2 / √((m : ℝ) + 1) - 2 / √(N : ℝ) ≤ 2 / √(m : ℝ) := by
          have : 2 / √((m : ℝ) + 1) ≤ 2 / √(m : ℝ) :=
            div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hm0) (Real.sqrt_le_sqrt (by linarith))
          have : 0 ≤ 2 / √(N : ℝ) := by positivity
          linarith
        have hc0 : 0 ≤ 1 / L ^ 3 + 4.92e-7 := by positivity
        have k1 := mul_le_mul_of_nonneg_left (s1.trans hlogN) hc0
        have k2 := mul_le_mul_of_nonneg_left (s2.trans hs2) (by norm_num : (0 : ℝ) ≤ 7.04)
        have e : 7.04 * (2 / √(m : ℝ)) = 14.08 / √(m : ℝ) := by ring
        linarith
      have hN' := hper N hmN
      have hm' := hper m le_rfl
      refine h.trans ?_
      have k1 : 3 / (m : ℝ) ≤ 3 / M₂ := div_le_div_of_nonneg_left (by norm_num) hM₂0 hle
      have k2 : 7.04 / √(m : ℝ) ≤ 7.04 / √(M₂ : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hM₂0) (Real.sqrt_le_sqrt hle)
      have k3 : 14.08 / √(m : ℝ) ≤ 14.08 / √(M₂ : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hM₂0) (Real.sqrt_le_sqrt hle)
      have e : 28.16 / √(M₂ : ℝ) = 2 * (7.04 / √(M₂ : ℝ)) + 14.08 / √(M₂ : ℝ) := by ring
      rw [hA0]; linarith
  rw [← hM₂] at hE
  refine hE.trans ?_
  -- numerics
  have hsu : 0 < √u := Real.sqrt_pos.2 hu0
  have hsM : 0.9984 * √u ≤ √(M₂ : ℝ) := by
    have h3 : √(0.9969 * u) ≤ √(M₂ : ℝ) := Real.sqrt_le_sqrt hM₂ge
    rw [Real.sqrt_mul (by norm_num)] at h3
    have : 0.9984 ≤ √(0.9969 : ℝ) := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg u]
  have hsbig : 7e6 ≤ √u := by rw [Real.le_sqrt (by norm_num) hu0.le]; norm_num at h1 ⊢; linarith
  have hLu : L ≥ Real.log u - 0.0032 := by
    have := Real.log_le_log (by positivity) hM₂ge
    rw [Real.log_mul (by norm_num) hu0.ne'] at this
    have h7 : Real.log 0.9969 ≥ -0.0032 := by
      rw [ge_iff_le, Real.le_log_iff_exp_le (by norm_num), Real.exp_neg]
      have := Real.add_one_le_exp 0.0032
      rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    linarith
  have hlogu : 31 ≤ Real.log u := by
    have hMu : (M₂ : ℝ) ≤ u := by
      have h8 := Nat.floor_le (show 0 ≤ u * Real.exp (-0.003) by positivity)
      have h9 : Real.exp (-0.003) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
      rw [← hM₂] at h8
      nlinarith
    have := Real.log_le_log hM₂0 hMu
    linarith
  have hlu : Real.log u ≤ L + 0.0032 := by linarith
  have hL3 : 2.5062 * (1 / L ^ 3) ≤ 2.51 / Real.log u ^ 3 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (pow_pos (by linarith) 3)]
    have : Real.log u ^ 3 ≤ (L + 0.0032) ^ 3 := pow_le_pow_left₀ (by linarith) hlu 3
    nlinarith [pow_pos hLpos 2, pow_pos hLpos 3]
  have k1 : 28.16 / √(M₂ : ℝ) ≤ 28.21 / √u := by
    rw [div_le_div_iff₀ (by linarith) hsu]; nlinarith
  have hsuu := Real.mul_self_sqrt hu0.le
  have k2 : 3 / (M₂ : ℝ) + 1 / M₂ ≤ 0.001 / √u := by
    rw [← add_div, div_le_div_iff₀ hM₂0 hsu]; nlinarith
  have k4 : 5.3e6 * u ^ (-(3 / 2) : ℝ) ≤ 0.001 / √u := by
    have e : u ^ (-(3 / 2) : ℝ) = 1 / (u * √u) := by
      rw [Real.rpow_neg hu0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hu0,
        Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
    rw [e, mul_one_div, div_le_div_iff₀ (by positivity) hsu]
    norm_num at h1; nlinarith
  have e5 : 97 / √u = 28.21 / √u + 68 / √u + 0.001 / √u + 0.001 / √u + 0.788 / √u := by ring
  have : 0 ≤ 0.788 / √u := by positivity
  rw [hA0]
  linarith

/-- Beyond `e^{20001}`: `|E(u)| ≤ 4100/√u + 33/log³u + 4.1/log²u` (`E1_tendsto`). -/
theorem E_R6 {u : ℝ} (hu : 1 ≤ u) (h : 20001 ≤ Real.log u) :
    |Eg u| ≤ 4100 / √u + 33 / Real.log u ^ 3 + 4.1 / Real.log u ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hu1e : (1e12 : ℝ) ≤ u := by
    have : Real.exp 28 ≤ u := by
      rw [← Real.exp_log hu0]; exact Real.exp_le_exp.2 (by linarith)
    have h2 := exp_nat_ge' 28
    norm_num at h2 ⊢; linarith
  set n := ⌊u⌋₊ with hn
  have hn12 : 10 ^ 12 ≤ n := by
    have : ((10 ^ 12 : ℕ) : ℝ) ≤ u := by norm_num; linarith
    exact Nat.le_floor (by exact_mod_cast this)
  have hnu : (n : ℝ) ≤ u := Nat.floor_le hu0.le
  have hnu2 : u / 2 ≤ (n : ℝ) := by
    have := Nat.lt_floor_add_one u; linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hE := E1_tendsto.2 n hn12 u hnu
  have hlog2 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hlogn : Real.log u - 0.7 ≤ Real.log n := by
    have := Real.log_le_log (by linarith) hnu2
    rw [Real.log_div hu0.ne' (by norm_num)] at this; linarith
  have hlogn' : ¬ Real.log n < 20000 := by linarith
  unfold Dvar at hE
  rw [if_neg hlogn'] at hE
  unfold Eg
  refine hE.trans ?_
  set Lu := Real.log u
  have hLn0 : 0 < Lu - 0.7 := by linarith
  have hsu : 0 < √u := Real.sqrt_pos.2 hu0
  have hsn : √(u / 2) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hnu2
  have hs2 : √(u / 2) = √u / √2 := Real.sqrt_div' u (by norm_num)
  have hsq2 : √(2 : ℝ) ≤ 1.4143 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq2' : 0 < √(2 : ℝ) := by positivity
  have k1 : 1443 / √(n : ℝ) ≤ 2040.9 / √u := by
    rw [div_le_div_iff₀ (by rw [hs2] at hsn; exact lt_of_lt_of_le (by positivity) hsn) hsu]
    rw [hs2] at hsn
    have : √u ≤ 1.4143 * √(n : ℝ) := by
      rw [div_le_iff₀ hsq2'] at hsn; nlinarith
    nlinarith
  have hsuu := Real.mul_self_sqrt hu0.le
  have hsbig : 1e6 ≤ √u := by rw [Real.le_sqrt (by norm_num) hu0.le]; norm_num at hu1e ⊢; linarith
  have k2 : 13 / (n : ℝ) ≤ 0.1 / √u := by
    rw [div_le_div_iff₀ hn0 hsu]; nlinarith
  have hLnpos : 0 < Real.log n := by linarith
  have k3 : 16 / Real.log n ^ 3 ≤ 16.5 / Lu ^ 3 := by
    rw [div_le_div_iff₀ (pow_pos hLnpos 3) (pow_pos (by linarith) 3)]
    have h3 : (Lu - 0.7) ^ 3 ≤ Real.log n ^ 3 := pow_le_pow_left₀ hLn0.le hlogn 3
    have h4 : 16 * Lu ^ 3 ≤ 16.5 * (Lu - 0.7) ^ 3 := by nlinarith [sq_nonneg Lu, sq_nonneg (Lu - 0.7)]
    nlinarith
  have k4 : 2 / Real.log n ^ 2 ≤ 2.05 / Lu ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hLnpos 2) (pow_pos (by linarith) 2)]
    have h3 : (Lu - 0.7) ^ 2 ≤ Real.log n ^ 2 := pow_le_pow_left₀ hLn0.le hlogn 2
    have h4 : 2 * Lu ^ 2 ≤ 2.05 * (Lu - 0.7) ^ 2 := by nlinarith
    nlinarith
  calc 2 * (1443 / √(n : ℝ) + 13 / (n : ℝ) + 16 / Real.log n ^ 3 + 2 / Real.log n ^ 2)
      ≤ 2 * (2040.9 / √u + 0.1 / √u + 16.5 / Lu ^ 3 + 2.05 / Lu ^ 2) := by linarith
    _ = 4082 / √u + 33 / Lu ^ 3 + 4.1 / Lu ^ 2 := by ring
    _ ≤ 4100 / √u + 33 / Lu ^ 3 + 4.1 / Lu ^ 2 := by
        have : 4082 / √u ≤ 4100 / √u := div_le_div_of_nonneg_right (by norm_num) hsu.le
        linarith

end TernaryGoldbach.Prelim
