import TernaryGoldbach.Prelim.SchoenfeldInd

/-!
# A cell of Schoenfeld's induction

For a cell `[A, B)` above `X₀` (`cell_step`): if `|N(D)| ≤ |M(D)| + X D` on the cell, the weighted sum
of `|N(n)|` over `(X₀, A)` is at most `I`, and `X + (C₀ + I)/A + ν δ/L² ≤ ν (1 − 1/L)` (`L ≤ log A`,
`δ = (B − A)/B`), then `|N(D)| ≤ ν D` on the cell (induction on `D`), hence `|M(D)| ≤ η D` with
`η = ν/L + (C₀ + I)/A + ν δ/L²`, and the weighted sum over `(X₀, B)` is at most `I + ν (B − A)/L²`.
-/

open Finset

namespace TernaryGoldbach.Prelim.Sch

/-- The weight `w(n) = 1/log n − 1/log(n+1)`. -/
noncomputable def wN (n : ℕ) : ℝ := 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)

theorem wN_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ wN n := by
  unfold wN
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < Real.log n := Real.log_pos (by linarith)
  exact sub_nonneg.2 (one_div_le_one_div_of_le h1 (Real.log_le_log (by linarith) (by linarith)))

theorem n_wN_le {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (hLn : L ≤ Real.log n) :
    (n : ℝ) * wN n ≤ 1 / L ^ 2 := by
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < Real.log n := lt_of_lt_of_le hL hLn
  have h2 : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have h3 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  unfold wN
  rw [div_sub_div _ _ h1.ne' (by linarith : Real.log ((n : ℝ) + 1) ≠ 0)]
  have hp : 0 < Real.log n * Real.log ((n : ℝ) + 1) := mul_pos h1 (lt_of_lt_of_le h1 h2)
  rw [mul_div_assoc', div_le_div_iff₀ hp (pow_pos hL 2)]
  have hL2 : L ^ 2 ≤ Real.log n * Real.log ((n : ℝ) + 1) := by nlinarith
  have hn' : (n : ℝ) * (1 * Real.log ((n : ℝ) + 1) - Real.log n * 1) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ n)
    rw [mul_one_div_cancel (by positivity)] at this; linarith
  nlinarith [sq_nonneg L]

/-- **The cell step.** -/
theorem cell_step {X0 A B : ℕ} (hX0 : 1 ≤ X0) (hXA : X0 < A) (hAB : A < B) {X C0 I ν L : ℝ}
    (hL : 1 < L) (hLA : L ≤ Real.log A) (hν : 0 ≤ ν)
    (hC0 : |Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1)| ≤ C0)
    (hI : ∑ n ∈ Ioo X0 A, |Nn n| * wN n ≤ I)
    (hNM : ∀ D, A ≤ D → D < B → |Nn D| ≤ |Mn D| + X * D)
    (hcond : X + (C0 + I) / A + ν * (((B : ℝ) - A) / B) / L ^ 2 ≤ ν * (1 - 1 / L)) :
    (∀ D, A ≤ D → D < B → |Nn D| ≤ ν * D) ∧
    (∀ D, A ≤ D → D < B → |Mn D| ≤ (ν / L + (C0 + I) / A + ν * (((B : ℝ) - A) / B) / L ^ 2) * D) ∧
    ∑ n ∈ Ioo X0 B, |Nn n| * wN n ≤ I + ν * ((B : ℝ) - A) / L ^ 2 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hL0 : 0 < L := by linarith
  have hX02 : 2 ≤ A := by omega
  -- `M(D)` from `N`, given the bound below `D` in the cell
  have hM : ∀ D, A ≤ D → D < B → (∀ n, A ≤ n → n < D → |Nn n| ≤ ν * n) →
      |Mn D| ≤ C0 + |Nn D| / L + I + ν * ((D : ℝ) - A) / L ^ 2 := by
    intro D hD1 hD2 hprev
    have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have hlogD : L ≤ Real.log D := hLA.trans (Real.log_le_log hA0 (by exact_mod_cast hD1))
    have e : Mn D = (Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1)) + Nn D / Real.log D +
        ∑ n ∈ Ioo X0 D, Nn n * wN n := M_of_N hX0 D (by omega)
    have hsplit : ∑ n ∈ Ioo X0 D, Nn n * wN n =
        ∑ n ∈ Ioo X0 A, Nn n * wN n + ∑ n ∈ Ico A D, Nn n * wN n := by
      rw [show Ioo X0 D = Ioo X0 A ∪ Ico A D by ext; simp; omega, sum_union]
      exact disjoint_left.2 fun n h1 h2 => by simp at h1 h2; omega
    have hw : ∀ n ∈ Ioo X0 D, 0 ≤ wN n := fun n hn => wN_nonneg (by simp at hn; omega)
    have b1 : |∑ n ∈ Ioo X0 A, Nn n * wN n| ≤ I := by
      refine (abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_) hI)
      exact sum_congr rfl fun n hn => by
        rw [abs_mul, abs_of_nonneg (wN_nonneg (by simp at hn; omega))]
    have b2 : |∑ n ∈ Ico A D, Nn n * wN n| ≤ ν * ((D : ℝ) - A) / L ^ 2 := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ n ∈ Ico A D, |Nn n * wN n| ≤ ν / L ^ 2 := by
        intro n hn
        obtain ⟨h1, h2⟩ := mem_Ico.1 hn
        have hn2 : 2 ≤ n := by omega
        rw [abs_mul, abs_of_nonneg (wN_nonneg hn2)]
        have hLn : L ≤ Real.log n := hLA.trans (Real.log_le_log hA0 (by exact_mod_cast h1))
        have hnw := n_wN_le hn2 hL0 hLn
        have hwn := wN_nonneg hn2
        calc |Nn n| * wN n ≤ ν * n * wN n := mul_le_mul_of_nonneg_right (hprev n h1 h2) hwn
          _ = ν * (n * wN n) := by ring
          _ ≤ ν * (1 / L ^ 2) := mul_le_mul_of_nonneg_left hnw hν
          _ = ν / L ^ 2 := by ring
      refine (sum_le_sum hterm).trans ?_
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      rw [Nat.cast_sub hD1]
      apply le_of_eq; ring
    have b3 : |Nn D / Real.log D| ≤ |Nn D| / L := by
      rw [abs_div, abs_of_pos (lt_of_lt_of_le hL0 hlogD)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hL0 hlogD
    rw [e, hsplit]
    have := abs_add_le (Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1) + Nn D / Real.log D)
      (∑ n ∈ Ioo X0 A, Nn n * wN n + ∑ n ∈ Ico A D, Nn n * wN n)
    have := abs_add_le (Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1)) (Nn D / Real.log D)
    have := abs_add_le (∑ n ∈ Ioo X0 A, Nn n * wN n) (∑ n ∈ Ico A D, Nn n * wN n)
    linarith
  -- the induction
  have hδ : ∀ D, A ≤ D → D < B → ((D : ℝ) - A) ≤ (((B : ℝ) - A) / B) * D := by
    intro D h1 h2
    have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    have h1' : (A : ℝ) ≤ D := by exact_mod_cast h1
    have h2' : (D : ℝ) ≤ B := by exact_mod_cast h2.le
    rw [div_mul_eq_mul_div, le_div_iff₀ hB0]
    nlinarith
  have hN : ∀ D, A ≤ D → D < B → |Nn D| ≤ ν * D := by
    intro D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
      intro h1 h2
      have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
      have hm := hM D h1 h2 fun n hn1 hn2 => ih n hn2 hn1 (by omega)
      have hnm := hNM D h1 h2
      have hd := hδ D h1 h2
      -- `|N|(1 − 1/L) ≤ C0 + I + νδD/L² + X D ≤ ν (1 − 1/L) D`
      have hDA : (C0 + I) ≤ (C0 + I) / A * D := by
        have hCI : 0 ≤ C0 + I := by
          have := abs_nonneg (Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1))
          have : 0 ≤ ∑ n ∈ Ioo X0 A, |Nn n| * wN n :=
            sum_nonneg fun n hn => mul_nonneg (abs_nonneg _) (wN_nonneg (by simp at hn; omega))
          linarith
        rw [div_mul_eq_mul_div, le_div_iff₀ hA0]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1) hCI
      have key : |Nn D| * (1 - 1 / L) ≤ ν * (1 - 1 / L) * D := by
        have hνδ : ν * ((D : ℝ) - A) / L ^ 2 ≤ ν * (((B : ℝ) - A) / B) / L ^ 2 * D := by
          rw [div_mul_eq_mul_div, mul_assoc]
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hd hν
        have hc := mul_le_mul_of_nonneg_right hcond hD0.le
        have e1 : |Nn D| * (1 - 1 / L) = |Nn D| - |Nn D| / L := by ring
        rw [e1]
        nlinarith
      have hpos : 0 < 1 - 1 / L := by
        have : 1 / L < 1 := by rw [div_lt_one hL0]; exact hL
        linarith
      have := le_of_mul_le_mul_right (by linarith [key] : |Nn D| * (1 - 1 / L) ≤ ν * D * (1 - 1 / L)) hpos
      exact this
  refine ⟨hN, fun D h1 h2 => ?_, ?_⟩
  · have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have hm := hM D h1 h2 fun n hn1 hn2 => hN n hn1 (by omega)
    have hn := hN D h1 h2
    have hd := hδ D h1 h2
    have hDA : (C0 + I) ≤ (C0 + I) / A * D := by
      have hCI : 0 ≤ C0 + I := by
        have := abs_nonneg (Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1))
        have : 0 ≤ ∑ n ∈ Ioo X0 A, |Nn n| * wN n :=
          sum_nonneg fun n hn => mul_nonneg (abs_nonneg _) (wN_nonneg (by simp at hn; omega))
        linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hA0]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1) hCI
    have h1' : |Nn D| / L ≤ ν * D / L := div_le_div_of_nonneg_right hn hL0.le
    have hνδ : ν * ((D : ℝ) - A) / L ^ 2 ≤ ν * (((B : ℝ) - A) / B) / L ^ 2 * D := by
      rw [div_mul_eq_mul_div, mul_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hd hν
    have e : (ν / L + (C0 + I) / A + ν * (((B : ℝ) - A) / B) / L ^ 2) * D =
        ν * D / L + (C0 + I) / A * D + ν * (((B : ℝ) - A) / B) / L ^ 2 * D := by ring
    rw [e]; linarith
  · rw [show Ioo X0 B = Ioo X0 A ∪ Ico A B by ext; simp; omega, sum_union
      (disjoint_left.2 fun n h1 h2 => by simp at h1 h2; omega)]
    have : ∑ n ∈ Ico A B, |Nn n| * wN n ≤ ν * ((B : ℝ) - A) / L ^ 2 := by
      have hterm : ∀ n ∈ Ico A B, |Nn n| * wN n ≤ ν / L ^ 2 := by
        intro n hn
        obtain ⟨h1, h2⟩ := mem_Ico.1 hn
        have hn2 : 2 ≤ n := by omega
        have hLn : L ≤ Real.log n := hLA.trans (Real.log_le_log hA0 (by exact_mod_cast h1))
        calc |Nn n| * wN n ≤ ν * n * wN n := mul_le_mul_of_nonneg_right (hN n h1 h2) (wN_nonneg hn2)
          _ = ν * (n * wN n) := by ring
          _ ≤ ν * (1 / L ^ 2) := mul_le_mul_of_nonneg_left (n_wN_le hn2 hL0 hLn) hν
          _ = ν / L ^ 2 := by ring
      refine (sum_le_sum hterm).trans ?_
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hAB.le]
      apply le_of_eq; ring
    linarith

end TernaryGoldbach.Prelim.Sch
