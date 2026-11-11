/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.ElMarraki
import RSBounds.Moebius003.Misc

/-!
# Proposition 8 (steps 2–3) and Corollary 9 of the note, abstractly

`step_abstract` takes Step 1 of Proposition 8 as the hypothesis
`|N(D)| ≤ |M(D)| + D·X` on the cell `[D_-, D_+)` and proves `(H_i)`. Step 2 of the note ("the first
failure") becomes strong induction on the integers of the cell, which is possible because `N` and
`M` are step functions.

`cell_m_bound` is Corollary 9.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Finset Real

/-- **Proposition 8**, steps 2 and 3. -/
theorem step_abstract (h : Inputs) {Dlo Dhi : ℕ} {ν η X I Lm : ℝ}
    (hX0 : X0 ≤ Dlo) (hlt : Dlo < Dhi)
    (hLm1 : 1 < Lm) (hLmle : Lm ≤ Real.log Dlo)
    (hI : Iint X0 Dlo ≤ I)
    (hNM : ∀ D : ℕ, Dlo ≤ D → D < Dhi → |N D| ≤ |M D| + D * X)
    (hν0 : 0 ≤ ν)
    (hν : X + (C0B + I) / Dlo ≤ ν * (1 - 1 / Lm - (1 - (Dlo : ℝ) / Dhi) / Lm ^ 2))
    (hη : ν / Lm + (C0B + I) / Dlo + ν * (1 - (Dlo : ℝ) / Dhi) / Lm ^ 2 ≤ η) :
    ∀ n : ℕ, Dlo ≤ n → n < Dhi → |N n| ≤ ν * n ∧ |M n| ≤ η * n := by
  have hC0 := abs_C0_le_C0B h
  have hDlo : (0 : ℝ) < Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < Dlo)
  have hDhi : (0 : ℝ) < Dhi := by exact_mod_cast (by omega : 0 < Dhi)
  have hLm0 : 0 < Lm := by linarith
  have hI0 : 0 ≤ Iint X0 Dlo := sum_nonneg fun n hn => mul_nonneg (abs_nonneg _)
    (inv_log_sub_nonneg (by have := (mem_Ico.1 hn).1; unfold X0 at this; omega))
  have hC0B : 0 ≤ C0B := by unfold C0B; norm_num
  set δ : ℝ := 1 - (Dlo : ℝ) / Dhi with hδ
  -- `|M(D)| ≤ C₀ + |N(D)|/L_- + I + ν (D − D_-)/L_-²`, given `|N| ≤ ν` on `[D_-, D)`
  have hMb : ∀ D : ℕ, Dlo ≤ D → D < Dhi → (∀ u, Dlo ≤ u → u < D → |N u| ≤ ν * u) →
      |M D| ≤ C0B + |N D| / Lm + I + ν * ((D : ℝ) - Dlo) / Lm ^ 2 := by
    intro D h1 h2 hN
    have hD : (0 : ℝ) < D := by linarith [(by exact_mod_cast h1 : (Dlo : ℝ) ≤ D)]
    have h3 := abs_M_le_of_N (x := D) (le_trans hX0 h1)
    rw [Iint_add hX0 h1] at h3
    have h4 := Iint_le (a := Dlo) (b := D) (by unfold X0 at hX0; omega) h1 hν0 hLm0 hLmle hN
    have h5 : |N D| / Real.log D ≤ |N D| / Lm := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) hLm0
      exact hLmle.trans (Real.log_le_log hDlo (by exact_mod_cast h1))
    linarith
  -- `D − D_- ≤ δ D`
  have hδD : ∀ D : ℕ, D < Dhi → ((D : ℝ) - Dlo) ≤ δ * D := by
    intro D hD
    have : (D : ℝ) ≤ Dhi := by exact_mod_cast hD.le
    rw [hδ, sub_mul, one_mul, div_mul_eq_mul_div, sub_le_sub_iff_left, div_le_iff₀ hDhi]
    exact mul_le_mul_of_nonneg_left this hDlo.le
  have hδ0 : 0 ≤ δ := by
    rw [hδ, sub_nonneg, div_le_one hDhi]; exact_mod_cast hlt.le
  -- Step 2: strong induction on the integers of the cell
  have hN : ∀ n : ℕ, Dlo ≤ n → n < Dhi → |N n| ≤ ν * n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h1 h2
      have hn : (Dlo : ℝ) ≤ n := by exact_mod_cast h1
      have hnpos : (0 : ℝ) < n := by linarith
      have hprev : ∀ u, Dlo ≤ u → u < n → |N u| ≤ ν * u := fun u hu1 hu2 =>
        ih u hu2 hu1 (lt_trans hu2 h2)
      have hM := hMb n h1 h2 hprev
      have hNM' := hNM n h1 h2
      have hd := hδD n h2
      -- `|N|(1 − 1/L) ≤ C₀ + I + ν δ n/L² + n X ≤ n ((C₀+I)/D_- + νδ/L² + X)`
      have hCI : C0B + I ≤ (C0B + I) / Dlo * n := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hDlo]
        exact mul_le_mul_of_nonneg_left hn (by linarith)
      have key : |N n| * (1 - 1 / Lm) ≤ n * (X + (C0B + I) / Dlo + ν * δ / Lm ^ 2) := by
        have e1 : |N n| * (1 - 1 / Lm) = |N n| - |N n| / Lm := by ring
        have e2 : ν * ((n : ℝ) - Dlo) / Lm ^ 2 ≤ ν * δ / Lm ^ 2 * n := by
          rw [div_mul_eq_mul_div, mul_assoc]
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hd hν0
        nlinarith
      have hfac : 0 < 1 - 1 / Lm := by
        rw [sub_pos, div_lt_one hLm0]; exact hLm1
      have h3 : n * (X + (C0B + I) / Dlo + ν * δ / Lm ^ 2) ≤ ν * n * (1 - 1 / Lm) := by
        have : X + (C0B + I) / Dlo + ν * δ / Lm ^ 2 ≤ ν * (1 - 1 / Lm) := by
          have e : ν * (1 - 1 / Lm - δ / Lm ^ 2) = ν * (1 - 1 / Lm) - ν * δ / Lm ^ 2 := by ring
          linarith
        nlinarith
      have := le_trans key h3
      exact le_of_mul_le_mul_right this hfac
  intro n h1 h2
  refine ⟨hN n h1 h2, ?_⟩
  -- Step 3
  have hn : (Dlo : ℝ) ≤ n := by exact_mod_cast h1
  have hnpos : (0 : ℝ) < n := by linarith
  have hM := hMb n h1 h2 (fun u hu1 hu2 => hN u hu1 (lt_trans hu2 h2))
  have hNn := hN n h1 h2
  have hd := hδD n h2
  have hCI : C0B + I ≤ (C0B + I) / Dlo * n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hDlo]
    exact mul_le_mul_of_nonneg_left hn (by linarith)
  have e1 : |N n| / Lm ≤ ν / Lm * n := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hNn hLm0.le
  have e2 : ν * ((n : ℝ) - Dlo) / Lm ^ 2 ≤ ν * δ / Lm ^ 2 * n := by
    rw [div_mul_eq_mul_div, mul_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hd hν0
  nlinarith

/-- **Corollary 9**. -/
theorem cell_m_bound (h : Inputs) {Dlo Dhi : ℕ} {η T Lp : ℝ}
    (hX0 : X0 ≤ Dlo) (hlt : Dlo < Dhi)
    (hM : ∀ n : ℕ, Dlo ≤ n → n < Dhi → |M n| ≤ η * n)
    (hT : ∑ t ∈ Ico X0 Dlo, |M t| * Real.log (1 + 1 / (t : ℝ)) ≤ T)
    (hLp : Real.log Dhi ≤ Lp) :
    ∀ n : ℕ, Dlo ≤ n → n < Dhi → |msum n| * Real.log (n + 1) ≤
      Lp * (η + max ((I0B + T) / Dlo) ((I0B + T + η * ((Dhi : ℝ) - Dlo)) / Dhi) + Lp / Dlo) := by
  intro n h1 h2
  have hDlo : (0 : ℝ) < Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < Dlo)
  have hn : (Dlo : ℝ) ≤ n := by exact_mod_cast h1
  have hnpos : (0 : ℝ) < n := by linarith
  have hnDhi : (n : ℝ) + 1 ≤ Dhi := by exact_mod_cast h2
  have hEM := el_marraki (x := n) (by unfold X0 at hX0; omega)
  have hS0 := S_X0_le h
  -- `S(n) ≤ I₀ + T + η (n − D_-)`
  have hSn : S n ≤ I0B + T + η * ((n : ℝ) - Dlo) := by
    have e : S n = S X0 + ∑ t ∈ Ico X0 Dlo, |M t| * Real.log (1 + 1 / (t : ℝ)) +
        ∑ t ∈ Ico Dlo n, |M t| * Real.log (1 + 1 / (t : ℝ)) := by
      unfold S
      rw [sum_Ico_consecutive _ (by unfold X0; omega) hX0, sum_Ico_consecutive _ (by unfold X0 at hX0; omega) h1]
    have h3 : ∑ t ∈ Ico Dlo n, |M t| * Real.log (1 + 1 / (t : ℝ)) ≤ η * ((n : ℝ) - Dlo) := by
      have hcard : ((n : ℝ) - Dlo) = ∑ t ∈ Ico Dlo n, (1 : ℝ) := by simp [Nat.cast_sub h1]
      rw [hcard, mul_sum]
      refine sum_le_sum fun t ht => ?_
      obtain ⟨ht1, ht2⟩ := mem_Ico.1 ht
      have htpos : (0 : ℝ) < t := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < t)
      have hMt := hM t ht1 (lt_trans ht2 h2)
      have hl := log_one_add_inv_le t (by unfold X0 at hX0; omega)
      have hl0 : 0 ≤ Real.log (1 + 1 / (t : ℝ)) := by
        have : 0 ≤ 1 / (t : ℝ) := by positivity
        exact Real.log_nonneg (by linarith)
      calc |M t| * Real.log (1 + 1 / (t : ℝ)) ≤ η * t * (1 / t) :=
            mul_le_mul hMt hl hl0 (le_trans (abs_nonneg _) hMt)
        _ = η * 1 := by field_simp
    linarith
  have hη0 : 0 ≤ η := by
    have := hM Dlo le_rfl hlt
    have : 0 ≤ η * Dlo := le_trans (abs_nonneg _) this
    exact nonneg_of_mul_nonneg_left this hDlo
  have hMn : |M n| / n ≤ η := by rw [div_le_iff₀ hnpos]; exact hM n h1 h2
  have hlogn : Real.log n / n ≤ Lp / Dlo := by
    have h3 : Real.log n ≤ Lp := (Real.log_le_log hnpos (by linarith)).trans hLp
    have h4 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 1 ≤ Dlo)
      linarith)
    calc Real.log n / n ≤ Lp / n := div_le_div_of_nonneg_right h3 hnpos.le
      _ ≤ Lp / Dlo := div_le_div_of_nonneg_left (le_trans h4 h3) hDlo hn
  have hmax : (I0B + T + η * ((n : ℝ) - Dlo)) / n ≤
      max ((I0B + T) / Dlo) ((I0B + T + η * ((Dhi : ℝ) - Dlo)) / Dhi) := by
    set c := I0B + T - η * Dlo
    have e1 : (I0B + T + η * ((n : ℝ) - Dlo)) / n = η + c / n := by field_simp; ring
    have e2 : (I0B + T) / Dlo = η + c / Dlo := by field_simp; ring
    have hDhi : (0 : ℝ) < Dhi := by linarith
    have e3 : (I0B + T + η * ((Dhi : ℝ) - Dlo)) / Dhi = η + c / Dhi := by field_simp; ring
    rw [e1, e2, e3]
    rcases le_or_gt 0 c with hc | hc
    · apply le_max_of_le_left
      have : c / n ≤ c / Dlo := div_le_div_of_nonneg_left hc hDlo hn
      linarith
    · apply le_max_of_le_right
      have : c / n ≤ c / Dhi := by
        rw [div_le_div_iff₀ hnpos hDhi]
        nlinarith
      linarith
  have hSn' : S n / n ≤ (I0B + T + η * ((n : ℝ) - Dlo)) / n :=
    div_le_div_of_nonneg_right hSn hnpos.le
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ Lp := (Real.log_le_log (by positivity) hnDhi).trans hLp
  have hlog10 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  calc |msum n| * Real.log (n + 1)
      ≤ (|M n| / n + S n / n + Real.log n / n) * Real.log (n + 1) :=
        mul_le_mul_of_nonneg_right hEM hlog10
    _ ≤ (η + max ((I0B + T) / Dlo) ((I0B + T + η * ((Dhi : ℝ) - Dlo)) / Dhi) + Lp / Dlo) * Lp := by
        apply mul_le_mul _ hlog1 hlog10
        · have hT0 : 0 ≤ T := le_trans (sum_nonneg fun t _ => mul_nonneg (abs_nonneg _)
            (Real.log_nonneg (by have : (0 : ℝ) ≤ 1 / (t : ℝ) := by positivity
                                 linarith))) hT
          have hLp0 : 0 ≤ Lp := le_trans hlog10 hlog1
          have h1 : 0 ≤ (I0B + T) / Dlo := div_nonneg (by unfold I0B; linarith) hDlo.le
          have h2 := le_max_left ((I0B + T) / Dlo) ((I0B + T + η * ((Dhi : ℝ) - Dlo)) / Dhi)
          have h3 : 0 ≤ Lp / Dlo := div_nonneg hLp0 hDlo.le
          linarith
        · linarith
    _ = _ := by ring

end TernaryGoldbach.RSBounds.Moebius003
