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


/-! ## Monotonicity of the antiderivatives, and the sums used in [H, Lemma 4.2.3] -/

section
variable {x : ℝ} (hx : 0 < x)
include hx

/-- `F₁(t) = t log(ex/t)` is increasing on `(0, x]`. -/
theorem F₁_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htx : t ≤ x) :
    s * (1 + Real.log x - Real.log s) ≤ t * (1 + Real.log x - Real.log t) := by
  have := monotoneOn_of_deriv_nonneg (f := fun t => t * (1 + Real.log x - Real.log t))
    (convex_Ioc 0 x)
    (fun u hu => (hasDerivAt_F₁ x hu.1).continuousAt.continuousWithinAt)
    (fun u hu => by rw [interior_Ioc] at hu; exact (hasDerivAt_F₁ x hu.1).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Ioc] at hu; rw [(hasDerivAt_F₁ x hu.1).deriv]
      linarith [Real.log_le_log hu.1 hu.2.le])
  exact this ⟨hs, hst.trans htx⟩ ⟨hs.trans_le hst, htx⟩ hst

/-- `F₂(t) = (t²/2) log(√e x/t)` is increasing on `(0, x]`. -/
theorem F₂_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htx : t ≤ x) :
    s ^ 2 / 2 * (1 / 2 + Real.log x - Real.log s) ≤ t ^ 2 / 2 * (1 / 2 + Real.log x - Real.log t) := by
  have := monotoneOn_of_deriv_nonneg (f := fun t => t ^ 2 / 2 * (1 / 2 + Real.log x - Real.log t))
    (convex_Ioc 0 x)
    (fun u hu => (hasDerivAt_F₂ x hu.1).continuousAt.continuousWithinAt)
    (fun u hu => by rw [interior_Ioc] at hu; exact (hasDerivAt_F₂ x hu.1).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Ioc] at hu; rw [(hasDerivAt_F₂ x hu.1).deriv]
      have := Real.log_le_log hu.1 hu.2.le
      exact mul_nonneg hu.1.le (by linarith))
  exact this ⟨hs, hst.trans htx⟩ ⟨hs.trans_le hst, htx⟩ hst

/-- `S₂ = ∑_{j<J} (j + 3/2) log(x/((j+½)q)) ≤ log(2x/q) + (2D'/q + D'²/2q²) log(√e x/D')`
when `(J - ½)q < D' ≤ x/e` [H, (4.47)]. -/
theorem S2_le {q D' : ℝ} (hq : 0 < q) {J : ℕ} (hJ : 1 ≤ J) (hJD : (J - 1 / 2) * q ≤ D')
    (hD'x : D' ≤ x / rexp 1) :
    ∑ j ∈ range J, ((j : ℝ) + 3 / 2) * (Real.log x - Real.log ((j + 1 / 2) * q)) ≤
      Real.log x - Real.log (q / 2) +
        (2 * D' / q + D' ^ 2 / (2 * q ^ 2)) * (1 / 2 + Real.log x - Real.log D') := by
  have he : x / rexp 1 ≤ x := div_le_self hx.le (by linarith [Real.add_one_le_exp (1:ℝ)])
  have hq2 : 0 < q / 2 := by positivity
  have hD'0 : 0 < D' := by
    have : (1 / 2 : ℝ) * q ≤ ((J : ℝ) - 1 / 2) * q := by
      have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      nlinarith
    linarith
  obtain ⟨K, rfl⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  push_cast at hJD
  set u : ℕ → ℝ := fun j => ((j : ℝ) + 1 / 2) * q
  have hu : ∀ j, u j = q / 2 + j * q := fun j => by simp only [u]; ring
  have huK : u K ≤ D' := by simp only [u]; linarith
  -- Split each term as `log(x/u) + u log(x/u)/q`.
  have hsplit : ∀ j : ℕ, ((j : ℝ) + 3 / 2) * (Real.log x - Real.log ((j + 1 / 2) * q)) =
      (Real.log x - Real.log (u j)) + (u j * (Real.log x - Real.log (u j))) / q := by
    intro j; simp only [u]; field_simp; ring
  simp_rw [hsplit]
  rw [sum_add_distrib, ← sum_div]
  -- The `log(x/u)` part.
  have h1 : ∑ j ∈ range (K + 1), (Real.log x - Real.log (u j)) ≤
      Real.log x - Real.log (q / 2) + D' * (1 + Real.log x - Real.log D') / q := by
    rw [sum_range_succ']
    have hA := sum_le_of_antitone (F := fun t => t * (1 + Real.log x - Real.log t))
      (f := fun t => Real.log x - Real.log t) (a := q / 2) hq K
      (fun t ht => hasDerivAt_F₁ x (lt_of_lt_of_le hq2 ht.1))
      ((antitoneOn_f₁ x).mono fun t ht => lt_of_lt_of_le hq2 ht.1)
    have e : ∀ i : ℕ, q / 2 + ((i : ℝ) + 1) * q = u (i + 1) := fun i => by rw [hu]; push_cast; ring
    simp_rw [e] at hA
    have hF := F₁_mono hx (s := q / 2 + K * q) (t := D') (by positivity) (by rw [← hu]; exact huK)
      (hD'x.trans he)
    have hF0 : 0 ≤ q / 2 * (1 + Real.log x - Real.log (q / 2)) := by
      apply mul_nonneg hq2.le
      have : q / 2 ≤ x := by
        have : u 0 ≤ D' := by
          have := huK; simp only [u] at this ⊢; nlinarith [show (0:ℝ) ≤ K by positivity]
        simp only [u] at this; linarith
      linarith [Real.log_le_log hq2 this]
    have hu0 : u 0 = q / 2 := by simp only [u]; ring
    rw [hu0]
    have : q * ∑ i ∈ range K, (Real.log x - Real.log (u (i + 1))) ≤
        D' * (1 + Real.log x - Real.log D') := by linarith
    have : ∑ i ∈ range K, (Real.log x - Real.log (u (i + 1))) ≤ D' * (1 + Real.log x - Real.log D') / q := by
      rw [le_div_iff₀ hq]; linarith
    linarith
  -- The `u log(x/u)` part.
  have h2 : ∑ j ∈ range (K + 1), u j * (Real.log x - Real.log (u j)) ≤
      D' ^ 2 / 2 * (1 / 2 + Real.log x - Real.log D') / q + D' * (Real.log x - Real.log D') := by
    rw [sum_range_succ]
    have hsub : Set.Icc (q / 2) (q / 2 + K * q) ⊆ Set.Ioc 0 (x / rexp 1) := fun t ht =>
      ⟨lt_of_lt_of_le hq2 ht.1, ht.2.trans (by rw [← hu]; exact huK.trans hD'x)⟩
    have hM := sum_le_of_monotone (F := fun t => t ^ 2 / 2 * (1 / 2 + Real.log x - Real.log t))
      (f := fun t => t * (Real.log x - Real.log t)) (a := q / 2) hq K
      (fun t ht => hasDerivAt_F₂ x (lt_of_lt_of_le hq2 ht.1)) ((monotoneOn_f₂ x hx).mono hsub)
    have key : ∀ i : ℕ, q / 2 + (i : ℝ) * q = u i := fun i => (hu i).symm
    simp only [key] at hM
    have hF := F₂_mono hx (s := u K) (t := D') (by simp only [u]; positivity) huK (hD'x.trans he)
    have hF0 : 0 ≤ (q / 2) ^ 2 / 2 * (1 / 2 + Real.log x - Real.log (q / 2)) := by
      apply mul_nonneg (by positivity)
      have : q / 2 ≤ x := by
        have : u 0 ≤ u K := by simp only [u]; nlinarith [show (0:ℝ) ≤ K by positivity]
        simp only [u] at this; linarith [huK.trans (hD'x.trans he)]
      linarith [Real.log_le_log hq2 this]
    have hlast : u K * (Real.log x - Real.log (u K)) ≤ D' * (Real.log x - Real.log D') :=
      monotoneOn_f₂ x hx ⟨by simp only [u]; positivity, huK.trans hD'x⟩ ⟨hD'0, hD'x⟩ huK
    have : ∑ x_1 ∈ range K, u x_1 * (Real.log x - Real.log (u x_1)) ≤
        D' ^ 2 / 2 * (1 / 2 + Real.log x - Real.log D') / q := by
      rw [le_div_iff₀ hq]
      linarith
    linarith
  have e : Real.log x - Real.log (q / 2) + D' * (1 + Real.log x - Real.log D') / q +
      (D' ^ 2 / 2 * (1 / 2 + Real.log x - Real.log D') / q + D' * (Real.log x - Real.log D')) / q =
      Real.log x - Real.log (q / 2) +
        (2 * D' / q + D' ^ 2 / (2 * q ^ 2)) * (1 / 2 + Real.log x - Real.log D') := by
    field_simp; ring
  calc _ ≤ Real.log x - Real.log (q / 2) + D' * (1 + Real.log x - Real.log D') / q +
        (D' ^ 2 / 2 * (1 / 2 + Real.log x - Real.log D') / q + D' * (Real.log x - Real.log D')) / q := by
        gcongr
    _ = _ := e

end


/-- Odd `n ∈ [1, N]` are `2r + 1`, `r < (N + 1)/2` (real-valued version). -/
theorem sum_Icc_odd_eq' (N : ℕ) (G : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (if Odd n then G n else 0) = ∑ r ∈ range ((N + 1) / 2), G (2 * r + 1) := by
  rw [← sum_filter]
  refine sum_nbij' (fun n => (n - 1) / 2) (fun r => 2 * r + 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [mem_filter, mem_Icc] at hn; obtain ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩ := hn
    simp only [mem_range]; omega
  · intro r hr; simp only [mem_range] at hr; simp only [mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨r, rfl⟩⟩
  · intro n hn; simp only [mem_filter, mem_Icc] at hn; obtain ⟨_, ⟨j, rfl⟩⟩ := hn; omega
  · intro r _; omega
  · intro n hn; simp only [mem_filter, mem_Icc] at hn; obtain ⟨_, ⟨j, rfl⟩⟩ := hn
    congr 1; omega

/-- The error sum of the main term of [H, Lemma 4.2.3] (p. 67):
`∑_{m' ≤ N odd} qm' log(x/qm') ≤ M log(x/M) + (M²/4q) log(√e x/M)` for `qN ≤ M ≤ x/e`. -/
theorem sum_odd_mul_log_le {x : ℝ} (hx : 0 < x) {q : ℕ} (hq : 1 ≤ q) {N : ℕ} {M : ℝ}
    (hM0 : 0 < M) (hNM : (q : ℝ) * N ≤ M) (hMx : M ≤ x / rexp 1) :
    ∑ m' ∈ Icc 1 N, (if Odd m' then ((q : ℝ) * m') * (Real.log x - Real.log (q * m')) else 0) ≤
      M * (Real.log x - Real.log M) + M ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log M) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have he : x / rexp 1 ≤ x := div_le_self hx.le (by linarith [Real.add_one_le_exp (1:ℝ)])
  have hRHS1 : 0 ≤ M * (Real.log x - Real.log M) :=
    mul_nonneg hM0.le (by linarith [Real.log_le_log hM0 (hMx.trans he)])
  have hRHS2 : 0 ≤ M ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log M) :=
    mul_nonneg (by positivity) (by linarith [Real.log_le_log hM0 (hMx.trans he)])
  -- Rewrite as a sum over `i < I`, `m' = 2i + 1`.
  have hodd := sum_Icc_odd_eq' N (fun m' : ℕ => ((q : ℝ) * m') * (Real.log x - Real.log (q * m')))
  rw [hodd]
  set I := (N + 1) / 2
  rcases Nat.eq_zero_or_pos I with hI | hI
  · rw [hI, sum_range_zero]; linarith
  obtain ⟨K, hK⟩ : ∃ K, I = K + 1 := ⟨I - 1, by omega⟩
  rw [hK, sum_range_succ]
  set t : ℕ → ℝ := fun i => (q : ℝ) * ((2 * i + 1 : ℕ) : ℝ)
  have ht : ∀ i : ℕ, t i = q + i * (2 * q) := fun i => by simp only [t]; push_cast; ring
  have htK : t K ≤ M := by
    have : 2 * K + 1 ≤ N := by omega
    have : ((2 * K + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    simp only [t]; nlinarith
  have htKx : t K ≤ x / rexp 1 := htK.trans hMx
  have hsub : Set.Icc (q : ℝ) (q + K * (2 * q)) ⊆ Set.Ioc 0 (x / rexp 1) := fun s hs =>
    ⟨lt_of_lt_of_le hq0 hs.1, hs.2.trans (by rw [← ht]; exact htKx)⟩
  have hMono := sum_le_of_monotone (F := fun s => s ^ 2 / 2 * (1 / 2 + Real.log x - Real.log s))
    (f := fun s => s * (Real.log x - Real.log s)) (a := q) (by positivity : (0 : ℝ) < 2 * q) K
    (fun s hs => hasDerivAt_F₂ x (lt_of_lt_of_le hq0 hs.1)) ((monotoneOn_f₂ x hx).mono hsub)
  have key : ∀ i : ℕ, (q : ℝ) + i * (2 * q) = t i := fun i => (ht i).symm
  simp only [key] at hMono
  have hF := F₂_mono hx (s := t K) (t := M) (by simp only [t]; positivity) htK (hMx.trans he)
  have hF0 : 0 ≤ (q : ℝ) ^ 2 / 2 * (1 / 2 + Real.log x - Real.log q) := by
    apply mul_nonneg (by positivity)
    have : (q : ℝ) ≤ x := by
      have h1 : t 0 ≤ t K := by simp only [t]; push_cast; nlinarith [show (0:ℝ) ≤ K by positivity]
      have h2 : t 0 = q := by simp [t]
      linarith [htKx.trans he]
    linarith [Real.log_le_log hq0 this]
  have hlast : t K * (Real.log x - Real.log (t K)) ≤ M * (Real.log x - Real.log M) :=
    monotoneOn_f₂ x hx ⟨by simp only [t]; positivity, htKx⟩ ⟨hM0, hMx⟩ htK
  have hsum : ∑ i ∈ range K, t i * (Real.log x - Real.log (t i)) ≤
      M ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log M) := by
    have h2q : (0 : ℝ) < 2 * q := by positivity
    have : 2 * q * ∑ i ∈ range K, t i * (Real.log x - Real.log (t i)) ≤
        M ^ 2 / 2 * (1 / 2 + Real.log x - Real.log M) := by linarith
    rw [show M ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log M) =
      (M ^ 2 / 2 * (1 / 2 + Real.log x - Real.log M)) / (2 * q) by field_simp; ring, le_div_iff₀ h2q]
    linarith
  have e : ∀ i : ℕ, (q : ℝ) * ((2 * i + 1 : ℕ) : ℝ) * (Real.log x - Real.log (q * ((2 * i + 1 : ℕ) : ℝ))) =
      t i * (Real.log x - Real.log (t i)) := fun i => rfl
  simp only [e]
  linarith

end TernaryGoldbach.MinorArcs
