import Mathlib

/-!
# Sums versus antiderivatives

Discrete versions of `∑ f ≤ ∫ f` for monotone `f`, via the mean value theorem, so that sums of
`log(x/t)`, `t log(x/t)`, `log(x/t)/t` over arithmetic progressions can be bounded by explicit
antiderivatives without computing integrals.
-/

open Finset Real

namespace TernaryGoldbach.MinorArcs

/-- If `F' = f` on `[s, s+h]` and `f` is antitone there, `h f(s+h) ≤ F(s+h) - F(s)`. -/
theorem step_le_of_antitone {F f : ℝ → ℝ} {s h : ℝ} (hh : 0 < h)
    (hF : ∀ t ∈ Set.Icc s (s + h), HasDerivAt F (f t) t)
    (hf : AntitoneOn f (Set.Icc s (s + h))) : h * f (s + h) ≤ F (s + h) - F s := by
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope F f (by linarith : s < s + h)
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => hF t (Set.Ioo_subset_Icc_self ht))
  have : f (s + h) ≤ f c := hf (Set.Ioo_subset_Icc_self hc) ⟨by linarith, le_rfl⟩ hc.2.le
  rw [add_sub_cancel_left, eq_div_iff hh.ne'] at hcs
  nlinarith

/-- If `F' = f` on `[s, s+h]` and `f` is monotone there, `h f(s) ≤ F(s+h) - F(s)`. -/
theorem step_le_of_monotone {F f : ℝ → ℝ} {s h : ℝ} (hh : 0 < h)
    (hF : ∀ t ∈ Set.Icc s (s + h), HasDerivAt F (f t) t)
    (hf : MonotoneOn f (Set.Icc s (s + h))) : h * f s ≤ F (s + h) - F s := by
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope F f (by linarith : s < s + h)
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => hF t (Set.Ioo_subset_Icc_self ht))
  have : f s ≤ f c := hf ⟨le_rfl, by linarith⟩ (Set.Ioo_subset_Icc_self hc) hc.1.le
  rw [add_sub_cancel_left, eq_div_iff hh.ne'] at hcs
  nlinarith

/-- `h ∑_{i<n} f(a + (i+1)h) ≤ F(a + nh) - F(a)` for antitone `f = F'` on `[a, a + nh]`. -/
theorem sum_le_of_antitone {F f : ℝ → ℝ} {a h : ℝ} (hh : 0 < h) (n : ℕ)
    (hF : ∀ t ∈ Set.Icc a (a + n * h), HasDerivAt F (f t) t)
    (hf : AntitoneOn f (Set.Icc a (a + n * h))) :
    h * ∑ i ∈ range n, f (a + (i + 1) * h) ≤ F (a + n * h) - F a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : Set.Icc a (a + n * h) ⊆ Set.Icc a (a + (n + 1 : ℕ) * h) :=
      Set.Icc_subset_Icc le_rfl (by push_cast; nlinarith)
    have h1 := ih (fun t ht => hF t (hsub ht)) (hf.mono hsub)
    have hsub2 : Set.Icc (a + n * h) (a + n * h + h) ⊆ Set.Icc a (a + (n + 1 : ℕ) * h) :=
      Set.Icc_subset_Icc (by nlinarith [show (0:ℝ) ≤ n by positivity]) (by push_cast; nlinarith)
    have h2 := step_le_of_antitone (s := a + n * h) hh (fun t ht => hF t (hsub2 ht)) (hf.mono hsub2)
    rw [sum_range_succ, mul_add]
    have e : a + (n + 1 : ℕ) * h = a + n * h + h := by push_cast; ring
    have e2 : a + ((n : ℝ) + 1) * h = a + n * h + h := by ring
    rw [e2]; rw [e]
    linarith

/-- `h ∑_{i<n} f(a + ih) ≤ F(a + nh) - F(a)` for monotone `f = F'` on `[a, a + nh]`. -/
theorem sum_le_of_monotone {F f : ℝ → ℝ} {a h : ℝ} (hh : 0 < h) (n : ℕ)
    (hF : ∀ t ∈ Set.Icc a (a + n * h), HasDerivAt F (f t) t)
    (hf : MonotoneOn f (Set.Icc a (a + n * h))) :
    h * ∑ i ∈ range n, f (a + i * h) ≤ F (a + n * h) - F a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : Set.Icc a (a + n * h) ⊆ Set.Icc a (a + (n + 1 : ℕ) * h) :=
      Set.Icc_subset_Icc le_rfl (by push_cast; nlinarith)
    have h1 := ih (fun t ht => hF t (hsub ht)) (hf.mono hsub)
    have hsub2 : Set.Icc (a + n * h) (a + n * h + h) ⊆ Set.Icc a (a + (n + 1 : ℕ) * h) :=
      Set.Icc_subset_Icc (by nlinarith [show (0:ℝ) ≤ n by positivity]) (by push_cast; nlinarith)
    have h2 := step_le_of_monotone (s := a + n * h) hh (fun t ht => hF t (hsub2 ht)) (hf.mono hsub2)
    rw [sum_range_succ, mul_add]
    have e : a + (n + 1 : ℕ) * h = a + n * h + h := by push_cast; ring
    rw [e]
    linarith


/-! ## Three antiderivatives -/

section
variable (x : ℝ)

/-- `d/dt [t log(ex/t)] = log(x/t)` (written with `log x - log t`). -/
theorem hasDerivAt_F₁ {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t * (1 + Real.log x - Real.log t)) (Real.log x - Real.log t) t := by
  have h := ((hasDerivAt_id' t).mul ((hasDerivAt_const t (1 + Real.log x)).sub
    (Real.hasDerivAt_log ht.ne')))
  convert h using 1 <;> first | (funext s; simp; done) | (simp; field_simp; ring) | (simp only [Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]; field_simp; ring) | rfl

/-- `d/dt [(t²/2)(1/2 + log(x/t))] = t log(x/t)`. -/
theorem hasDerivAt_F₂ {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t ^ 2 / 2 * (1 / 2 + Real.log x - Real.log t))
      (t * (Real.log x - Real.log t)) t := by
  have h := ((hasDerivAt_pow 2 t).div_const 2).mul ((hasDerivAt_const t (1 / 2 + Real.log x)).sub
    (Real.hasDerivAt_log ht.ne'))
  convert h using 1 <;> first | (funext s; simp; done) | (simp; field_simp; ring) | (simp only [Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]; field_simp; ring) | rfl

/-- `d/dt [-(log(x/t))²/2] = log(x/t)/t`. -/
theorem hasDerivAt_F₃ {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -(Real.log x - Real.log t) ^ 2 / 2) ((Real.log x - Real.log t) / t) t := by
  have h := (((hasDerivAt_const t (Real.log x)).sub (Real.hasDerivAt_log ht.ne')).pow 2).neg.div_const 2
  convert h using 1 <;> first | (funext s; simp; done) | (simp; field_simp; ring) | (simp only [Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]; field_simp; ring) | rfl

theorem hasDerivAt_f₂ {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t * (Real.log x - Real.log t)) (Real.log x - Real.log t - 1) t := by
  have h := ((hasDerivAt_id' t).mul ((hasDerivAt_const t (Real.log x)).sub
    (Real.hasDerivAt_log ht.ne')))
  convert h using 1 <;> first | (funext s; simp; done) | (simp; field_simp; ring) | (simp only [Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]; field_simp; ring) | rfl

theorem hasDerivAt_f₃ {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => (Real.log x - Real.log t) / t)
      ((-1 - (Real.log x - Real.log t)) / t ^ 2) t := by
  have h := (((hasDerivAt_const t (Real.log x)).sub (Real.hasDerivAt_log ht.ne')).div
    (hasDerivAt_id' t) ht.ne')
  convert h using 1 <;> first | (funext s; simp; done) | (simp; field_simp; ring) | (simp only [Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]; field_simp; ring) | rfl

theorem antitoneOn_f₁ : AntitoneOn (fun t => Real.log x - Real.log t) (Set.Ioi 0) :=
  fun s hs t _ hst => by simp only; linarith [Real.log_le_log hs hst]

/-- `t log(x/t)` is increasing on `(0, x/e]`. -/
theorem monotoneOn_f₂ (hx : 0 < x) :
    MonotoneOn (fun t => t * (Real.log x - Real.log t)) (Set.Ioc 0 (x / rexp 1)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 (x / rexp 1)) ?_ ?_ ?_
  · exact fun t ht => (hasDerivAt_f₂ x ht.1).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioc] at ht
    exact (hasDerivAt_f₂ x ht.1).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioc] at ht
    rw [(hasDerivAt_f₂ x ht.1).deriv]
    have h1 : Real.log t ≤ Real.log x - 1 := by
      have := Real.log_le_log ht.1 ht.2.le
      rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at this; exact this
    linarith

/-- `log(x/t)/t` is decreasing on `(0, ex]`. -/
theorem antitoneOn_f₃ (hx : 0 < x) :
    AntitoneOn (fun t => (Real.log x - Real.log t) / t) (Set.Ioc 0 (rexp 1 * x)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 (rexp 1 * x)) ?_ ?_ ?_
  · exact fun t ht => (hasDerivAt_f₃ x ht.1).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioc] at ht
    exact (hasDerivAt_f₃ x ht.1).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioc] at ht
    rw [(hasDerivAt_f₃ x ht.1).deriv]
    have h1 : Real.log t ≤ 1 + Real.log x := by
      have := Real.log_le_log ht.1 ht.2.le
      rw [Real.log_mul (Real.exp_pos 1).ne' hx.ne', Real.log_exp] at this; exact this
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

end

end TernaryGoldbach.MinorArcs
