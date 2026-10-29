import Mathlib

/-!
# Trigonometric sums [B, §4.1]

Proof of [B, Lemma 4.1.1]: for `α = a/q + β/qQ`, `(a, q) = 1`, `|β| ≤ 1`, `q ≤ Q`,

`∑_{y < n ≤ y + q} min(A, C/sin²(παn)) ≤ min(2A + (6q²/π²) C, 3A + (4q/π) √(AC))`.

The argument follows [B] for the first bound: reduce to residues `R = 0, …, q-1` with shifts
in a window `[s - 1/2, s + 1/2]`, pair `R = k` with `R = q - 1 - k`, and use convexity of
`1/sin²` (pairing and the midpoint inequality), `∫ 1/sin² = -cot`, and
`t²/sin²t + t cot 2t ≤ 3/2` on `(0, π/6]`.  For the second bound we replace [B]'s count of
terms (which uses `arcsin`) by a cleaner estimate: `min(A, C/sin²)` is decreasing, so each run
of unit-spaced terms is at most `(q/π) ∫₀^{π/2} min(A, C/sin² v) dv ≤ (q/π)(Aw + C/w) = (2q/π)√(AC)`
with `w = √(C/A)`.

Proved, with no `sorry`.
-/
open Real Set MeasureTheory

namespace TernaryGoldbach.MinorArcs

/-- `x ↦ 1/sin² x` is convex on `(0, π)`. -/
theorem convexOn_inv_sin_sq : ConvexOn ℝ (Ioo 0 π) fun x => 1 / Real.sin x ^ 2 := by
  have hsin : ConcaveOn ℝ (Ioo 0 π) Real.sin :=
    strictConcaveOn_sin_Icc.concaveOn.subset Ioo_subset_Icc_self (convex_Ioo 0 π)
  have himg : Real.sin '' Ioo 0 π ⊆ Ioi 0 := by
    rintro _ ⟨x, hx, rfl⟩; exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hconv : Convex ℝ (Real.sin '' Ioo 0 π) :=
    ((isPreconnected_Ioo.image _ Real.continuous_sin.continuousOn).ordConnected).convex
  have hg : ConvexOn ℝ (Real.sin '' Ioo 0 π) fun y : ℝ => y ^ (-2 : ℤ) :=
    (convexOn_zpow (-2)).subset himg hconv
  have hanti : AntitoneOn (fun y : ℝ => y ^ (-2 : ℤ)) (Real.sin '' Ioo 0 π) := by
    intro y hy z hz hyz
    have hy0 : 0 < y := himg hy
    simp only [zpow_neg, zpow_ofNat]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hy0.le hyz 2)
  have := hg.comp_concaveOn hsin hanti
  refine this.congr fun x _ => ?_
  simp only [Function.comp_apply, zpow_neg, one_div]
  norm_cast

/-- Pairing ("majorization"): for convex `f` and `a ≤ b ≤ c ≤ d` with `b + c = a + d`,
`f b + f c ≤ f a + f d`. -/
theorem _root_.ConvexOn.add_le_add_of_majorize {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {a b c d : ℝ} (ha : a ∈ s) (hd : d ∈ s) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hsum : b + c = a + d) : f b + f c ≤ f a + f d := by
  rcases eq_or_lt_of_le (hab.trans (hbc.trans hcd)) with had | had
  · have : a = b := le_antisymm hab (by linarith)
    have : c = d := le_antisymm hcd (by linarith)
    subst_vars; rfl
  have hda : d - a ≠ 0 := (sub_pos.2 had).ne'
  have hc' : c = a + d - b := by linarith
  set l := (d - b) / (d - a)
  have hl0 : 0 ≤ l := div_nonneg (by linarith) (by linarith)
  have hl1 : l ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hb : l • a + (1 - l) • d = b := by
    simp only [smul_eq_mul, l]; field_simp; ring
  have hc : (1 - l) • a + l • d = c := by
    simp only [smul_eq_mul, l]; rw [hc']; field_simp; ring
  have h1 : f (l • a + (1 - l) • d) ≤ l • f a + (1 - l) • f d :=
    hf.2 ha hd hl0 (by linarith) (by ring)
  have h2 : f ((1 - l) • a + l • d) ≤ (1 - l) • f a + l • f d :=
    hf.2 ha hd (by linarith) hl0 (by ring)
  rw [hb] at h1; rw [hc] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- Midpoint inequality (half of Hermite–Hadamard): for `f` convex and continuous on
`[m - 1/2, m + 1/2]`, `f m ≤ ∫_{m-1/2}^{m+1/2} f`. -/
theorem _root_.ConvexOn.le_integral_of_midpoint {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f) {m : ℝ}
    (hs : Icc (m - 1 / 2) (m + 1 / 2) ⊆ s) (hc : ContinuousOn f (Icc (m - 1 / 2) (m + 1 / 2))) :
    f m ≤ ∫ x in (m - 1 / 2)..(m + 1 / 2), f x := by
  have hint : IntervalIntegrable f MeasureTheory.volume (m - 1 / 2) (m + 1 / 2) :=
    hc.intervalIntegrable_of_Icc (by linarith)
  -- Reflection `x ↦ 2m - x` preserves the interval.
  have hrefl : ∫ x in (m - 1 / 2)..(m + 1 / 2), f (2 * m - x) = ∫ x in (m - 1 / 2)..(m + 1 / 2), f x := by
    rw [intervalIntegral.integral_comp_sub_left]; ring_nf
  have hint' : IntervalIntegrable (fun x => f (2 * m - x)) MeasureTheory.volume
      (m - 1 / 2) (m + 1 / 2) := by
    refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
    refine hc.comp (continuous_const.sub continuous_id).continuousOn fun x hx => ?_
    simp only [mem_Icc, id] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have hpt : ∀ x ∈ Icc (m - 1 / 2) (m + 1 / 2), 2 * f m ≤ f x + f (2 * m - x) := by
    intro x hx
    have hx' : 2 * m - x ∈ s := hs ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have := hf.2 (hs hx) hx' (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at this
    rw [show 1 / 2 * x + 1 / 2 * (2 * m - x) = m by ring] at this
    linarith
  have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    (hint.add hint') hpt
  rw [intervalIntegral.integral_add hint hint', hrefl, intervalIntegral.integral_const] at this
  simp only [smul_eq_mul] at this
  linarith

/-- `∫_a^b 1/sin² x dx = cot a - cot b` for `0 < a ≤ b < π`. -/
theorem integral_inv_sin_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < π) :
    ∫ x in a..b, 1 / Real.sin x ^ 2 = Real.cos a / Real.sin a - Real.cos b / Real.sin b := by
  have hsin : ∀ x ∈ uIcc a b, Real.sin x ≠ 0 := fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])).ne'
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun x => -(Real.cos x / Real.sin x)) (1 / Real.sin x ^ 2) x := by
    intro x hx
    have h := ((Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) (hsin x hx)).neg
    convert h using 1
    field_simp
    rw [← Real.sin_sq_add_cos_sq x]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · ring
  · refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.div (Real.continuous_sin.continuousOn.pow 2)
      fun x hx => pow_ne_zero 2 (hsin x hx)


theorem trig_core (t S C : ℝ) (ht : 0 < t) (ht1 : t ≤ 5236 / 10000) (hS1 : t - t ^ 3 / 4 < S)
    (hS2 : S ≤ t) (hC1 : 1 - t ^ 2 / 2 ≤ C) :
    t * S * (1 - 2 * S ^ 2) ≤ C * (3 * S ^ 2 - 2 * t ^ 2) := by
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : ℝ, S₀ = t - t ^ 3 / 4 := ⟨_, rfl⟩
  rw [← hS₀] at hS1
  have ht2 : t ^ 2 ≤ 2742 / 10000 := by nlinarith
  have hS₀pos : 93 / 100 * t ≤ S₀ := by rw [hS₀]; nlinarith
  have hSpos : 0 < S := by linarith
  have h3 : 0 < 3 * S ^ 2 - 2 * t ^ 2 := by
    have : S₀ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by linarith) hS1.le 2
    nlinarith
  have step1 : (1 - t ^ 2 / 2) * (3 * S ^ 2 - 2 * t ^ 2) ≤ C * (3 * S ^ 2 - 2 * t ^ 2) :=
    mul_le_mul_of_nonneg_right hC1 h3.le
  let F := fun s : ℝ => (1 - t ^ 2 / 2) * (3 * s ^ 2 - 2 * t ^ 2) - t * s * (1 - 2 * s ^ 2)
  have hB : 0 ≤ 3 * (1 - t ^ 2 / 2) * (S + S₀) - t + 2 * t * (S ^ 2 + S * S₀ + S₀ ^ 2) := by
    have hq : 0 ≤ S ^ 2 + S * S₀ + S₀ ^ 2 := by
      nlinarith [sq_nonneg (S + S₀), sq_nonneg S, sq_nonneg S₀]
    have : 0 ≤ 2 * t * (S ^ 2 + S * S₀ + S₀ ^ 2) := mul_nonneg (by positivity) hq
    nlinarith
  have step2 : F S₀ ≤ F S := by
    have hdiff : F S - F S₀ =
        (S - S₀) * (3 * (1 - t ^ 2 / 2) * (S + S₀) - t + 2 * t * (S ^ 2 + S * S₀ + S₀ ^ 2)) := by
      simp only [F]; ring
    have hprod := mul_nonneg (sub_nonneg.2 hS1.le) hB
    rw [← hdiff] at hprod
    linarith
  have step3 : 0 ≤ F S₀ := by
    have hP : F S₀ = t ^ 4 * (1 / 4 - 9 * t ^ 2 / 16 + 9 * t ^ 4 / 32 - t ^ 6 / 32) := by
      simp only [F]; rw [hS₀]; ring
    rw [hP]
    have : 0 ≤ 1 / 4 - 9 * t ^ 2 / 16 + 9 * t ^ 4 / 32 - t ^ 6 / 32 := by
      have h6 : t ^ 6 ≤ 3 / 100 := by
        have : t ^ 6 = (t ^ 2) ^ 3 := by ring
        rw [this]; nlinarith [pow_le_pow_left₀ (by positivity) ht2 3]
      nlinarith [sq_nonneg (t ^ 2)]
    positivity
  simp only [F] at step2 step3
  linarith

/-- `t²/sin²t + t cot 2t ≤ 3/2` for `0 < t ≤ π/6`. -/
theorem sq_div_sin_sq_add_mul_cot_two_mul_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ π / 6) :
    t ^ 2 / Real.sin t ^ 2 + t * (Real.cos (2 * t) / Real.sin (2 * t)) ≤ 3 / 2 := by
  have hpi : t ≤ 5236 / 10000 := ht1.trans (by linarith [Real.pi_lt_d4])
  have hS1 := Real.sin_gt_sub_cube ht (by linarith)
  have hS2 := Real.sin_le ht.le
  have hC1 := Real.one_sub_sq_div_two_le_cos (x := t)
  have hSpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_gt_three])
  have hCpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [Real.pi_gt_three]⟩
  have hcore := trig_core t (Real.sin t) (Real.cos t) ht hpi hS1 hS2 hC1
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have h : t ^ 2 / Real.sin t ^ 2 + t * ((2 * Real.cos t ^ 2 - 1) / (2 * Real.sin t * Real.cos t)) =
      (2 * t ^ 2 * Real.cos t + t * Real.sin t * (2 * Real.cos t ^ 2 - 1)) /
        (2 * Real.sin t ^ 2 * Real.cos t) := by
    field_simp; ring
  rw [h, div_le_iff₀ (by positivity)]
  have hsc := Real.sin_sq_add_cos_sq t
  have : 2 * Real.cos t ^ 2 - 1 = 1 - 2 * Real.sin t ^ 2 := by linarith
  rw [this]
  nlinarith [hcore]


/-- `f_q(u) = 1/sin²(πu/q)`. -/
noncomputable def fq (q : ℝ) (u : ℝ) : ℝ := 1 / Real.sin (π * u / q) ^ 2

theorem fq_nonneg (q u : ℝ) : 0 ≤ fq q u := by unfold fq; positivity

theorem sin_pos_of_mem {q u : ℝ} (hq : 0 < q) (hu : 0 < u) (huq : u < q) :
    0 < Real.sin (π * u / q) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by rw [div_lt_iff₀ hq]; nlinarith [Real.pi_pos])

theorem convexOn_fq {q : ℝ} (hq : 0 < q) : ConvexOn ℝ (Ioo 0 q) (fq q) := by
  have h := convexOn_inv_sin_sq.comp_linearMap ((π / q) • LinearMap.id)
  refine (h.subset ?_ (convex_Ioo 0 q)).congr fun u _ => ?_
  · intro u hu
    simp only [mem_preimage, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mem_Ioo]
    constructor
    · exact mul_pos (div_pos Real.pi_pos hq) hu.1
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hq]; nlinarith [Real.pi_pos, hu.2]
  · simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, fq]
    ring_nf

theorem continuousOn_fq {q a b : ℝ} (hq : 0 < q) (ha : 0 < a) (hb : b < q) :
    ContinuousOn (fq q) (Icc a b) := by
  unfold fq
  refine continuousOn_const.div ((Real.continuous_sin.comp_continuousOn
    ((continuousOn_const.mul continuousOn_id).div_const q)).pow 2) fun u hu => ?_
  exact pow_ne_zero 2 (sin_pos_of_mem hq (by linarith [hu.1]) (by linarith [hu.2])).ne'

/-- `∫_a^b f_q = (q/π)(cot(πa/q) - cot(πb/q))`. -/
theorem integral_fq {q a b : ℝ} (hq : 0 < q) (ha : 0 < a) (hab : a ≤ b) (hb : b < q) :
    ∫ u in a..b, fq q u =
      q / π * (Real.cos (π * a / q) / Real.sin (π * a / q) -
        Real.cos (π * b / q) / Real.sin (π * b / q)) := by
  have hpq : π / q ≠ 0 := (div_pos Real.pi_pos hq).ne'
  have : (fun u => fq q u) = fun u => (fun x => 1 / Real.sin x ^ 2) ((π / q) * u) := by
    funext u; simp only [fq]; ring_nf
  rw [this, intervalIntegral.integral_comp_mul_left (fun x => 1 / Real.sin x ^ 2) hpq,
    integral_inv_sin_sq]
  · simp only [smul_eq_mul, inv_div]; ring_nf
  · positivity
  · exact mul_le_mul_of_nonneg_left hab (by positivity)
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hq]; nlinarith [Real.pi_pos]

/-- **I1.** `∑_{j=2}^{K} f_q(j - 1/2) ≤ (q/π) cot(π/q)` for `2 ≤ 2K ≤ q`. -/
theorem sum_fq_le {q : ℝ} {K : ℕ} (hq : 2 < q) (hK : (K : ℝ) ≤ q / 2) :
    ∑ j ∈ Finset.Icc 2 K, fq q (j - 1 / 2) ≤
      q / π * (Real.cos (π / q) / Real.sin (π / q)) := by
  have hq0 : 0 < q := by linarith
  -- Midpoint inequality on each `[j - 1, j]`.
  have hHH : ∀ j ∈ Finset.Icc 2 K, fq q (j - 1 / 2) ≤ ∫ u in ((j : ℝ) - 1)..j, fq q u := by
    intro j hj
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
    have hjK : (j : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    have h := (convexOn_fq hq0).le_integral_of_midpoint (m := j - 1 / 2)
      (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (continuousOn_fq hq0 (by linarith) (by linarith))
    convert h using 2 <;> ring
  have hcot0 : 0 ≤ Real.cos (π / q) / Real.sin (π / q) := by
    have h1 : π / q < π / 2 := by
      rw [div_lt_div_iff₀ hq0 (by norm_num)]; nlinarith [Real.pi_pos]
    have h0 : 0 < π / q := by positivity
    exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h1.le⟩)
      (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)).le
  rcases Nat.lt_or_ge K 2 with hK2 | hK2
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    exact mul_nonneg (by positivity) hcot0
  -- Sum of adjacent integrals.
  have hsum : ∑ j ∈ Finset.Icc 2 K, ∫ u in ((j : ℝ) - 1)..j, fq q u = ∫ u in (1 : ℝ)..K, fq q u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fq q) (a := fun k : ℕ => (k : ℝ) + 1) (n := K - 1) fun k hk => by
        have hk2 : k + 2 ≤ K := by omega
        have : (k : ℝ) + 2 ≤ K := by exact_mod_cast hk2
        have hc := continuousOn_fq hq0 (a := (k : ℝ) + 1) (b := (k : ℝ) + 1 + 1)
          (by positivity) (by linarith)
        show IntervalIntegrable (fq q) volume ((k : ℝ) + 1) (((k + 1 : ℕ) : ℝ) + 1)
        push_cast
        exact hc.intervalIntegrable_of_Icc (by linarith)
    simp only [Nat.cast_zero, zero_add] at h
    rw [show ((K - 1 : ℕ) : ℝ) + 1 = K by rw [Nat.cast_sub (by omega)]; ring] at h
    rw [← h]
    refine Finset.sum_bij (fun k _ => k - 2) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; simp only at hab; omega
    · intro k hk; simp only [Finset.mem_range] at hk
      exact ⟨k + 2, by simp only [Finset.mem_Icc]; omega, by simp⟩
    · intro j hj; simp only [Finset.mem_Icc] at hj
      push_cast [Nat.cast_sub hj.1]; ring_nf
  have hKq : ∫ u in (1 : ℝ)..K, fq q u ≤ ∫ u in (1 : ℝ)..(q / 2), fq q u := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (K : ℝ))
      ((continuousOn_fq hq0 one_pos (by linarith)).intervalIntegrable_of_Icc hK1)
      ((continuousOn_fq hq0 (by linarith) (by linarith)).intervalIntegrable_of_Icc hK)]
    have := intervalIntegral.integral_nonneg (μ := volume) hK fun u _ => fq_nonneg q u
    linarith
  calc ∑ j ∈ Finset.Icc 2 K, fq q (j - 1 / 2)
      ≤ ∑ j ∈ Finset.Icc 2 K, ∫ u in ((j : ℝ) - 1)..j, fq q u := Finset.sum_le_sum hHH
    _ ≤ ∫ u in (1 : ℝ)..(q / 2), fq q u := hsum ▸ hKq
    _ = q / π * (Real.cos (π / q) / Real.sin (π / q)) := by
        rw [integral_fq hq0 one_pos (by linarith) (by linarith)]
        rw [show π * (q / 2) / q = π / 2 by field_simp; ring, Real.cos_pi_div_two, mul_one]
        simp


theorem measurable_minInvSin (A C : ℝ) :
    Measurable fun v : ℝ => min A (C * (1 / Real.sin v ^ 2)) :=
  measurable_const.min (measurable_const.mul
    (measurable_const.div (Real.measurable_sin.pow_const 2)))

theorem intervalIntegrable_minInvSin {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => min A (C * (1 / Real.sin v ^ 2))) volume a b := by
  refine (intervalIntegrable_const (c := A)).mono_fun' (measurable_minInvSin A C).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have h0 : 0 ≤ min A (C * (1 / Real.sin v ^ 2)) := le_min hA (by positivity)
  show ‖min A (C * (1 / Real.sin v ^ 2))‖ ≤ A
  rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact min_le_left _ _

/-- `∫₀^{π/2} min(A, C/sin² v) dv ≤ 2√(AC)`. -/
theorem integral_minInvSin_le {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∫ v in (0:ℝ)..(π / 2), min A (C * (1 / Real.sin v ^ 2)) ≤ 2 * √(A * C) := by
  have hpi := Real.pi_pos
  have hII := intervalIntegrable_minInvSin hA hC
  rcases hA.eq_or_lt with rfl | hA'
  · have : ∫ v in (0:ℝ)..(π / 2), min 0 (C * (1 / Real.sin v ^ 2)) ≤ ∫ v in (0:ℝ)..(π / 2), (0:ℝ) :=
      intervalIntegral.integral_mono_on (by positivity) (hII _ _) intervalIntegrable_const
        fun v _ => min_le_left _ _
    simpa using this
  rcases hC.eq_or_lt with rfl | hC'
  · simp [min_eq_right hA]
  set w := √(C / A)
  have hw : 0 < w := Real.sqrt_pos.2 (div_pos hC' hA')
  have hsA := Real.sqrt_pos.2 hA'
  have hsC := Real.sqrt_pos.2 hC'
  have hw' : w = √C / √A := Real.sqrt_div' C hA
  have hAw : A * w = √(A * C) := by
    rw [hw', Real.sqrt_mul hA]; field_simp; nlinarith [Real.mul_self_sqrt hA]
  have hCw : C / w = √(A * C) := by
    rw [hw', Real.sqrt_mul hA]; field_simp; nlinarith [Real.mul_self_sqrt hC]
  have hsAC : 0 ≤ √(A * C) := Real.sqrt_nonneg _
  rcases le_or_lt (π / 2) w with hwpi | hwpi
  · -- `w ≥ π/2`: bound the integrand by `A`.
    have : ∫ v in (0:ℝ)..(π / 2), min A (C * (1 / Real.sin v ^ 2)) ≤ ∫ v in (0:ℝ)..(π / 2), A :=
      intervalIntegral.integral_mono_on (by positivity) (hII _ _) intervalIntegrable_const
        fun v _ => min_le_left _ _
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    nlinarith
  · -- Split at `w`.
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := w) (hII _ _) (hII _ _)]
    have h1 : ∫ v in (0:ℝ)..w, min A (C * (1 / Real.sin v ^ 2)) ≤ A * w := by
      have := intervalIntegral.integral_mono_on hw.le (hII 0 w) intervalIntegrable_const
        fun v _ => min_le_left A (C * (1 / Real.sin v ^ 2))
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      linarith
    have hsinpos : ∀ v ∈ Icc w (π / 2), 0 < Real.sin v := fun v hv =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hv.1]) (by linarith [hv.2])
    have h2 : ∫ v in w..(π / 2), min A (C * (1 / Real.sin v ^ 2)) ≤
        C * (Real.cos w / Real.sin w) := by
      have hcont : ContinuousOn (fun v => C * (1 / Real.sin v ^ 2)) (Icc w (π / 2)) :=
        continuousOn_const.mul (continuousOn_const.div (Real.continuous_sin.continuousOn.pow 2)
          fun v hv => pow_ne_zero 2 (hsinpos v hv).ne')
      have := intervalIntegral.integral_mono_on hwpi.le (hII w (π / 2))
        (hcont.intervalIntegrable_of_Icc hwpi.le) fun v _ => min_le_right A (C * (1 / Real.sin v ^ 2))
      rw [intervalIntegral.integral_const_mul, integral_inv_sin_sq hw hwpi.le (by linarith),
        Real.cos_pi_div_two, zero_div, sub_zero] at this
      exact this
    have hcot : Real.cos w / Real.sin w ≤ 1 / w := by
      have ht := Real.lt_tan hw hwpi
      rw [Real.tan_eq_sin_div_cos] at ht
      have hs := hsinpos w ⟨le_rfl, hwpi.le⟩
      have hc : 0 < Real.cos w := Real.cos_pos_of_mem_Ioo ⟨by linarith, hwpi⟩
      rw [div_le_div_iff₀ hs hw]
      rw [lt_div_iff₀ hc] at ht
      linarith
    have h3 : C * (Real.cos w / Real.sin w) ≤ C / w := by
      calc C * (Real.cos w / Real.sin w) ≤ C * (1 / w) := mul_le_mul_of_nonneg_left hcot hC
        _ = C / w := by ring
    linarith


/-- `f_q` is antitone on `(0, q/2]`. -/
theorem fq_anti {q u v : ℝ} (hq : 0 < q) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ q / 2) :
    fq q v ≤ fq q u := by
  unfold fq
  have hpq : 0 < π / q := div_pos Real.pi_pos hq
  have h1 : π * u / q ≤ π * v / q := by
    rw [div_le_div_iff_of_pos_right hq]; exact mul_le_mul_of_nonneg_left huv Real.pi_pos.le
  have h2 : π * v / q ≤ π / 2 := by
    rw [div_le_iff₀ hq]; nlinarith [Real.pi_pos]
  have hsu : 0 < Real.sin (π * u / q) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have h0 : 0 < π * u / q := by positivity
  have hle := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h2 h1
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hsu.le hle 2)

theorem intervalIntegrable_G {q A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (a b : ℝ) :
    IntervalIntegrable (fun u => min A (C * fq q u)) volume a b := by
  have hm : Measurable fun u => min A (C * fq q u) := by
    unfold fq
    exact measurable_const.min (measurable_const.mul (measurable_const.div
      ((Real.measurable_sin.comp ((measurable_const.mul measurable_id).div_const q)).pow_const 2)))
  refine (intervalIntegrable_const (c := A)).mono_fun' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have h0 : 0 ≤ min A (C * fq q v) := le_min hA (mul_nonneg hC (fq_nonneg q v))
  show ‖min A (C * fq q v)‖ ≤ A
  rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact min_le_left _ _

/-- **I2.** For unit-spaced points `u₁, u₁ + 1, …, u₁ + m - 1` in `[1, q/2]`,
`∑ min(A, C f_q(u)) ≤ (2q/π) √(AC)`. -/
theorem sum_G_le {q A C : ℝ} (hq : 0 < q) (hA : 0 ≤ A) (hC : 0 ≤ C) {u₁ : ℝ} {m : ℕ}
    (hu₁ : 1 ≤ u₁) (hlast : u₁ + m - 1 ≤ q / 2) :
    ∑ i ∈ Finset.range m, min A (C * fq q (u₁ + i)) ≤ 2 * (q / π) * √(A * C) := by
  set G := fun u => min A (C * fq q u)
  have hG0 : ∀ u, 0 ≤ G u := fun u => le_min hA (mul_nonneg hC (fq_nonneg q u))
  have hII : ∀ a b, IntervalIntegrable G volume a b := intervalIntegrable_G hA hC
  -- Each term is at most the integral over the unit interval to its left.
  have hterm : ∀ i ∈ Finset.range m,
      G (u₁ + i) ≤ ∫ u in (u₁ - 1 + i)..(u₁ - 1 + (i + 1 : ℕ)), G u := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.1 hi
    rw [intervalIntegral.integral_of_le (by push_cast; linarith)]
    have hvol : (volume (Ioc (u₁ - 1 + i) (u₁ - 1 + (i + 1 : ℕ)))).toReal = 1 := by
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by push_cast; linarith)]; push_cast; ring
    calc G (u₁ + i) = ∫ _ in Ioc (u₁ - 1 + i) (u₁ - 1 + (i + 1 : ℕ)), G (u₁ + i) := by
          rw [setIntegral_const, hvol, one_smul]
      _ ≤ _ := by
          refine setIntegral_mono_on continuous_const.integrableOn_Ioc ((hII _ _).1) measurableSet_Ioc
            fun v hv => ?_
          simp only [mem_Ioc] at hv; push_cast at hv
          exact min_le_min le_rfl (mul_le_mul_of_nonneg_left
            (fq_anti hq (by linarith) (by linarith) (by linarith)) hC)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := G)
    (a := fun i : ℕ => u₁ - 1 + i) (n := m) fun i _ => hII _ _
  simp only [Nat.cast_zero, add_zero] at hsum
  -- Compare with `∫₀^{q/2} G`.
  have hsub : ∫ u in (u₁ - 1)..(u₁ - 1 + m), G u ≤ ∫ u in (0:ℝ)..(q / 2), G u := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := u₁ - 1)
      (c := q / 2) (hII 0 (u₁ - 1)) (hII (u₁ - 1) (q / 2))
    have e2 := intervalIntegral.integral_add_adjacent_intervals (a := u₁ - 1) (b := u₁ - 1 + m)
      (c := q / 2) (hII (u₁ - 1) (u₁ - 1 + m)) (hII (u₁ - 1 + m) (q / 2))
    have h1 := intervalIntegral.integral_nonneg (μ := volume) (a := 0) (b := u₁ - 1)
      (by linarith) fun u _ => hG0 u
    have h2 := intervalIntegral.integral_nonneg (μ := volume) (a := u₁ - 1 + m) (b := q / 2)
      (by linarith) fun u _ => hG0 u
    linarith
  -- Change of variables `v = πu/q`.
  have hcv : ∫ u in (0:ℝ)..(q / 2), G u =
      q / π * ∫ v in (0:ℝ)..(π / 2), min A (C * (1 / Real.sin v ^ 2)) := by
    have hpq : π / q ≠ 0 := (div_pos Real.pi_pos hq).ne'
    have : G = fun u => (fun v => min A (C * (1 / Real.sin v ^ 2))) ((π / q) * u) := by
      funext u; simp only [G, fq]; ring_nf
    rw [this, intervalIntegral.integral_comp_mul_left _ hpq, smul_eq_mul, inv_div]
    congr 2 <;> field_simp
  calc ∑ i ∈ Finset.range m, G (u₁ + i)
      ≤ ∑ i ∈ Finset.range m, ∫ u in (u₁ - 1 + i)..(u₁ - 1 + (i + 1 : ℕ)), G u :=
        Finset.sum_le_sum hterm
    _ = ∫ u in (u₁ - 1)..(u₁ - 1 + m), G u := hsum
    _ ≤ ∫ u in (0:ℝ)..(q / 2), G u := hsub
    _ ≤ q / π * (2 * √(A * C)) := by
        rw [hcv]; exact mul_le_mul_of_nonneg_left (integral_minInvSin_le hA hC) (by positivity)
    _ = 2 * (q / π) * √(A * C) := by ring


/-- Pair up `R` and `q - 1 - R`. -/
theorem sum_range_pair (F : ℕ → ℝ) (q : ℕ) :
    ∑ R ∈ Finset.range q, F R =
      ∑ k ∈ Finset.range (q / 2), (F k + F (q - 1 - k)) + if q % 2 = 1 then F (q / 2) else 0 := by
  rw [Finset.sum_add_distrib]
  rcases Nat.even_or_odd' q with ⟨K, rfl | rfl⟩
  · have h1 : 2 * K / 2 = K := by omega
    have h2 : ¬ (2 * K % 2 = 1) := by omega
    rw [h1, if_neg h2, add_zero, two_mul, Finset.sum_range_add]
    congr 1
    rw [← Finset.sum_range_reflect (fun x => F (K + x))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj; congr 1; omega
  · have h1 : (2 * K + 1) / 2 = K := by omega
    have h2 : (2 * K + 1) % 2 = 1 := by omega
    rw [h1, if_pos h2, show 2 * K + 1 = K + (K + 1) by ring, Finset.sum_range_add,
      Finset.sum_range_succ', add_zero, add_assoc]
    congr 1
    congr 1
    rw [← Finset.sum_range_reflect (fun x => F (K + (x + 1)))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj; congr 1; omega

/-- `f_q` is symmetric under `u ↦ q - u` and decreasing towards `q/2`. -/
theorem fq_le_of_between {q u v : ℝ} (hq : 0 < q) (hu : 0 < u) (huv : u ≤ v) (hvq : v ≤ q - u) :
    fq q v ≤ fq q u := by
  rcases le_or_lt v (q / 2) with hv | hv
  · exact fq_anti hq hu huv hv
  · have hsym : fq q v = fq q (q - v) := by
      unfold fq
      rw [show π * (q - v) / q = π - π * v / q by field_simp; ring, Real.sin_pi_sub]
    rw [hsym]; exact fq_anti hq hu (by linarith) (by linarith)

/-- **P1** (low residues). -/
theorem fq_low {q s τ : ℝ} {R : ℕ} (hq : 0 < q) (hs : 0 ≤ s) (hR : 1 ≤ R)
    (hRs : (R : ℝ) + s ≤ q / 2) (hτ : τ ∈ Icc (s - 1 / 2) (s + 1 / 2)) :
    fq q (R + τ) ≤ fq q (R - 1 / 2 + s) := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  exact fq_le_of_between hq (by linarith) (by linarith [hτ.1]) (by linarith [hτ.2])

/-- **P2** (high residues `q - k`). -/
theorem fq_high {q s τ : ℝ} {k : ℕ} (hq : 0 < q) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hkq : (k : ℝ) ≤ q / 2) (hs : 0 ≤ s) (hτ : τ ∈ Icc (s - 1 / 2) (s + 1 / 2)) :
    fq q (q - k + τ) ≤ fq q (k - 1 / 2 - s) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsym : fq q (q - k + τ) = fq q (k - τ) := by
    unfold fq
    rw [show π * (q - k + τ) / q = π - π * (k - τ) / q by field_simp; ring, Real.sin_pi_sub]
  rw [hsym]
  exact fq_le_of_between hq (by linarith) (by linarith [hτ.2]) (by linarith [hτ.1])

/-- Telescoping: `∑_{k=1}^{K-1} (g k + g (k+1)) + g K = g 1 + 2 ∑_{j=2}^{K} g j`. -/
theorem pair_telescope (g : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Finset.Ico 1 K, (g k + g (k + 1)) + g K = g 1 + 2 * ∑ j ∈ Finset.Icc 2 K, g j := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Ico_succ_top hK, Finset.sum_Icc_succ_top (by omega)]
    linarith



/-- The final numerical step of the first bound of Lemma 4.1.1:
`f_q(1/2) + 2(q/π) cot(π/q) ≤ 6q²/π²` for `q ≥ 3`. -/
theorem fq_half_add_le {q : ℝ} (hq : 3 ≤ q) :
    fq q (1 / 2) + 2 * (q / π * (Real.cos (π / q) / Real.sin (π / q))) ≤ 6 * q ^ 2 / π ^ 2 := by
  have hq0 : 0 < q := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = π / (2 * q) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ π / 6 := by
    rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
  have key := sq_div_sin_sq_add_mul_cot_two_mul_le ht0 ht1
  have e1 : fq q (1 / 2) = 1 / Real.sin t ^ 2 := by
    simp only [fq, ht]; ring_nf
  have e2 : π / q = 2 * t := by rw [ht]; field_simp; ring
  have e3 : q / π = 1 / (2 * t) := by rw [ht]; field_simp; ring
  rw [e1, e2, e3]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
  have e4 : 6 * q ^ 2 / π ^ 2 = 3 / 2 / t ^ 2 := by rw [ht]; field_simp; ring
  rw [e4, le_div_iff₀ (by positivity)]
  calc (1 / Real.sin t ^ 2 + 2 * (1 / (2 * t) * (Real.cos (2 * t) / Real.sin (2 * t)))) * t ^ 2
      = t ^ 2 / Real.sin t ^ 2 + t * (Real.cos (2 * t) / Real.sin (2 * t)) := by
        have h2t : t ^ 2 * (2 * (1 / (2 * t))) = t := by field_simp; ring
        calc (1 / Real.sin t ^ 2 + 2 * (1 / (2 * t) * (Real.cos (2 * t) / Real.sin (2 * t)))) * t ^ 2
            = t ^ 2 / Real.sin t ^ 2 +
                (t ^ 2 * (2 * (1 / (2 * t)))) * (Real.cos (2 * t) / Real.sin (2 * t)) := by ring
          _ = _ := by rw [h2t]
    _ ≤ 3 / 2 := key

/-- **Core of the first bound of Lemma 4.1.1.**  Residues `R = 0, …, q-1`, each shifted by
`τ_R ∈ [s - 1/2, s + 1/2]`, `0 ≤ s ≤ 1/2`. -/
theorem core_bound₁ {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (τ : ℕ → ℝ) (hτ : ∀ R, τ R ∈ Icc (s - 1 / 2) (s + 1 / 2)) :
    ∑ R ∈ Finset.range q, min A (C * fq q (R + τ R)) ≤ 2 * A + 6 * q ^ 2 / π ^ 2 * C := by
  set F := fun R : ℕ => min A (C * fq q (R + τ R))
  have hFA : ∀ R, F R ≤ A := fun R => min_le_left _ _
  have hF0 : ∀ R, 0 ≤ F R := fun R => le_min hA (mul_nonneg hC (fq_nonneg _ _))
  have hextra : 0 ≤ 6 * q ^ 2 / π ^ 2 * C := by positivity
  show ∑ R ∈ Finset.range q, F R ≤ _
  rw [sum_range_pair]
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · interval_cases q
    · simp; linarith [hFA 0]
    · simp; linarith [hFA 0, hFA 1]
  set K := q / 2 with hK
  have hK1 : 1 ≤ K := by omega
  have hqr : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hKq : (K : ℝ) ≤ q / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : K * 2 ≤ q)
  set g := fun j : ℕ => fq q (j - 1 / 2)
  -- Pairs with `k ≥ 1`.
  have hpair : ∀ k ∈ Finset.Ico 1 K, F k + F (q - 1 - k) ≤ C * (g k + g (k + 1)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk.2
    have h1 : F k ≤ C * fq q (k - 1 / 2 + s) :=
      (min_le_right _ _).trans (mul_le_mul_of_nonneg_left
        (fq_low hq0 hs0 hk.1 (by linarith) (hτ k)) hC)
    have hcast : ((q - 1 - k : ℕ) : ℝ) = q - ((k + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have h2 : F (q - 1 - k) ≤ C * fq q (k + 1 / 2 - s) := by
      refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left ?_ hC)
      have := fq_high (k := k + 1) hq0 hs1 (by omega) (by push_cast; linarith) hs0
        (hτ (q - 1 - k))
      rw [hcast]; convert this using 2; push_cast; ring
    have hmaj := (convexOn_fq hq0).add_le_add_of_majorize (a := k - 1 / 2) (b := k - 1 / 2 + s)
      (c := k + 1 / 2 - s) (d := k + 1 / 2) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith) (by linarith) (by linarith) (by ring)
    have hg : g k + g (k + 1) = fq q (k - 1 / 2) + fq q (k + 1 / 2) := by
      simp only [g]; push_cast; ring_nf
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_left hmaj hC]
  -- The odd leftover.
  have hodd : (if q % 2 = 1 then F K else 0) ≤ C * g K := by
    have hgK : 0 ≤ C * g K := mul_nonneg hC (fq_nonneg _ _)
    split_ifs with ho
    · have hK' : (K : ℝ) + s ≤ q / 2 := by
        have : (2 * K + 1 : ℝ) = q := by exact_mod_cast (by omega : 2 * K + 1 = q)
        linarith
      calc F K ≤ C * fq q (K - 1 / 2 + s) :=
            (min_le_right _ _).trans (mul_le_mul_of_nonneg_left
              (fq_low hq0 hs0 hK1 hK' (hτ K)) hC)
        _ ≤ C * g K := by
            have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
            exact mul_le_mul_of_nonneg_left
              (fq_anti hq0 (by linarith) (by linarith) (by linarith)) hC
    · exact hgK
  -- Assemble.
  have hpeel : ∑ k ∈ Finset.range K, (F k + F (q - 1 - k)) =
      (F 0 + F (q - 1)) + ∑ k ∈ Finset.Ico 1 K, (F k + F (q - 1 - k)) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]; simp
  have htel := pair_telescope g K hK1
  have hI1 := sum_fq_le (by linarith : (2 : ℝ) < q) hKq
  have hfin := fq_half_add_le hqr
  have hg1 : g 1 = fq q (1 / 2) := by simp only [g]; norm_num
  have hsumg : ∑ j ∈ Finset.Icc 2 K, g j = ∑ j ∈ Finset.Icc 2 K, fq q (j - 1 / 2) := rfl
  calc ∑ k ∈ Finset.range K, (F k + F (q - 1 - k)) + (if q % 2 = 1 then F K else 0)
      ≤ 2 * A + C * (∑ k ∈ Finset.Ico 1 K, (g k + g (k + 1)) + g K) := by
        rw [hpeel]
        have := Finset.sum_le_sum hpair
        rw [← Finset.mul_sum] at this
        nlinarith [hFA 0, hFA (q - 1)]
    _ = 2 * A + C * (fq q (1 / 2) + 2 * ∑ j ∈ Finset.Icc 2 K, fq q (j - 1 / 2)) := by
        rw [htel, hg1]
    _ ≤ 2 * A + C * (6 * q ^ 2 / π ^ 2) := by
        gcongr
        linarith
    _ = 2 * A + 6 * q ^ 2 / π ^ 2 * C := by ring


/-- **Core of the second bound of Lemma 4.1.1.** -/
theorem core_bound₂ {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (τ : ℕ → ℝ) (hτ : ∀ R, τ R ∈ Icc (s - 1 / 2) (s + 1 / 2)) :
    ∑ R ∈ Finset.range q, min A (C * fq q (R + τ R)) ≤ 3 * A + 4 * q / π * √(A * C) := by
  set F := fun R : ℕ => min A (C * fq q (R + τ R))
  set G := fun u : ℝ => min A (C * fq q u)
  have hFA : ∀ R, F R ≤ A := fun R => min_le_left _ _
  have hF0 : ∀ R, 0 ≤ F R := fun R => le_min hA (mul_nonneg hC (fq_nonneg _ _))
  have hextra : 0 ≤ 4 * q / π * √(A * C) := by positivity
  show ∑ R ∈ Finset.range q, F R ≤ _
  rw [sum_range_pair]
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · interval_cases q
    · simp; linarith [hFA 0]
    · simp; linarith [hFA 0, hFA 1]
  set K := q / 2 with hK
  have hK1 : 1 ≤ K := by omega
  have hqr : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hKq : (K : ℝ) ≤ q / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : K * 2 ≤ q)
  have hI2 : ∀ {u₁ : ℝ} {m : ℕ}, 1 ≤ u₁ → u₁ + m - 1 ≤ q / 2 →
      ∑ i ∈ Finset.range m, G (u₁ + i) ≤ 2 * (q / π) * √(A * C) :=
    fun h1 h2 => sum_G_le hq0 hA hC h1 h2
  have hpeel : ∑ k ∈ Finset.range K, (F k + F (q - 1 - k)) =
      (F 0 + F (q - 1)) + (∑ k ∈ Finset.Ico 1 K, F k + ∑ k ∈ Finset.Ico 1 K, F (q - 1 - k)) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_add_distrib]
    simp
  -- High residues `q - 1 - k`, `1 ≤ k < K`.
  have hhigh : ∑ k ∈ Finset.Ico 1 K, F (q - 1 - k) ≤ 2 * (q / π) * √(A * C) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine le_trans (Finset.sum_le_sum fun i hi => ?_) (hI2 (u₁ := 3 / 2 - s) (m := K - 1)
      (by linarith) ?_)
    · rw [Finset.mem_range] at hi
      have hcast : ((q - 1 - (1 + i) : ℕ) : ℝ) = q - ((i + 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      refine min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ hC)
      have := fq_high (k := i + 2) hq0 hs1 (by omega)
        (by have : ((i + 2 : ℕ) : ℝ) ≤ K := by exact_mod_cast (by omega : i + 2 ≤ K)
            linarith) hs0 (hτ (q - 1 - (1 + i)))
      rw [hcast]; convert this using 2; push_cast; ring
    · rw [Nat.cast_sub (by omega)]; push_cast; linarith
  -- Low residues `1 ≤ k < K`, and the odd leftover `K`.
  have hlow : ∑ k ∈ Finset.Ico 1 K, F k + (if q % 2 = 1 then F K else 0) ≤
      A + 2 * (q / π) * √(A * C) := by
    have hI2nn : 0 ≤ 2 * (q / π) * √(A * C) := by positivity
    rcases Nat.lt_or_ge K 2 with hK2 | hK2
    · have hK1' : K = 1 := by omega
      rw [hK1', Finset.Ico_self, Finset.sum_empty, zero_add]
      split_ifs <;> linarith [hFA 1]
    have hsplit : ∑ k ∈ Finset.Ico 1 K, F k = F 1 + ∑ i ∈ Finset.range (K - 2), F (2 + i) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i, 2 + i ≤ K → ((2 + i : ℕ) : ℝ) + s ≤ q / 2 →
        F (2 + i) ≤ G (3 / 2 + s + i) := by
      intro i hiK hRs
      refine min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ hC)
      have := fq_low hq0 hs0 (by omega : 1 ≤ 2 + i) hRs (hτ (2 + i))
      convert this using 2; push_cast; ring
    rw [hsplit]
    split_ifs with ho
    · -- `q` odd: the family runs up to `K`.
      have hq' : (2 * K + 1 : ℝ) = q := by exact_mod_cast (by omega : 2 * K + 1 = q)
      have hfam : ∑ i ∈ Finset.range (K - 2), F (2 + i) + F K ≤
          ∑ i ∈ Finset.range (K - 2 + 1), G (3 / 2 + s + i) := by
        rw [Finset.sum_range_succ]
        refine add_le_add (Finset.sum_le_sum fun i hi => ?_) ?_
        · rw [Finset.mem_range] at hi
          refine hterm i (by omega) ?_
          have : ((2 + i : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast (by omega : 2 + i + 1 ≤ K)
          linarith
        · have h := hterm (K - 2) (by omega) (by
            rw [show 2 + (K - 2) = K by omega]; linarith)
          rw [show 2 + (K - 2) = K by omega] at h
          exact h
      have := hI2 (u₁ := 3 / 2 + s) (m := K - 2 + 1) (by linarith)
        (by rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; linarith)
      linarith [hFA 1]
    · -- `q` even.
      have hq' : (2 * K : ℝ) = q := by exact_mod_cast (by omega : 2 * K = q)
      have hfam : ∑ i ∈ Finset.range (K - 2), F (2 + i) ≤
          ∑ i ∈ Finset.range (K - 2), G (3 / 2 + s + i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_range] at hi
        refine hterm i (by omega) ?_
        have : ((2 + i : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast (by omega : 2 + i + 1 ≤ K)
        linarith
      have := hI2 (u₁ := 3 / 2 + s) (m := K - 2) (by linarith)
        (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
      linarith [hFA 1]
  rw [hpeel]
  have h4 : 4 * (q : ℝ) / π * √(A * C) = 2 * (2 * (q / π) * √(A * C)) := by ring
  rw [h4]
  linarith [hFA 0, hFA (q - 1)]


/-- `α = a/q + β/qQ`, `(a, q) = 1`, `|β| ≤ 1`, `q ≤ Q` [B, Lemmas 4.1.1–4.1.3]. -/
def Approx (α : ℝ) (a : ℤ) (q : ℕ) (Q : ℝ) : Prop :=
  1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ ∃ β : ℝ, |β| ≤ 1 ∧ α = a / q + β / (q * Q) ∧ (q : ℝ) ≤ Q

theorem sin_sq_add_int_mul_pi (x : ℝ) (k : ℤ) : Real.sin (x + k * π) ^ 2 = Real.sin x ^ 2 := by
  rw [Real.sin_add_int_mul_pi, mul_pow, ← zpow_natCast, ← zpow_mul, show ((2 : ℕ) : ℤ) = 2 by rfl,
    mul_comm k 2, zpow_mul]
  norm_num

/-- **Reduction to residues.**  For `n ∈ (y, y + q]`, the terms `min(A, C/sin²(παn))` are, up to
reordering, `min(A, C f_q(R + τ_R))` for `R = 0, …, q-1`, with all `τ_R` in a window
`[s - 1/2, s + 1/2]`, `0 ≤ s ≤ 1/2`. -/
theorem residue_form {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) (y A C : ℝ) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 / 2 ∧ ∃ τ : ℕ → ℝ, (∀ R, τ R ∈ Icc (s - 1 / 2) (s + 1 / 2)) ∧
      ∑ n ∈ Finset.Ioc ⌊y⌋ ⌊y + q⌋, min A (C / Real.sin (π * α * n) ^ 2) =
        ∑ R ∈ Finset.range q, min A (C * fq q (R + τ R)) := by
  obtain ⟨hq1, hcop, β, hβ, hα, hqQ⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hQ0 : 0 < Q := by linarith
  set N := ⌊y⌋
  have hfl : ⌊y + q⌋ = N + q := by
    have := Int.floor_add_int y (q : ℤ); push_cast at this; exact this
  rw [hfl]
  set S := Finset.Ioc N (N + q)
  set c : ℝ := N + (q + 1) / 2
  have hdist : ∀ n ∈ S, |(n : ℝ) - c| ≤ q / 2 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have h1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : N + 1 ≤ n)
    have h2 : (n : ℝ) ≤ N + q := by exact_mod_cast hn.2
    rw [abs_le]; constructor <;> simp only [c] <;> linarith
  set w := β * c / Q
  set c₀ := round w
  set s₀ := w - c₀
  have hs₀ : |s₀| ≤ 1 / 2 := abs_sub_round w
  set τn := fun n : ℤ => s₀ + β * (n - c) / Q
  have hsmall : ∀ n ∈ S, |β * (n - c) / Q| ≤ 1 / 2 := by
    intro n hn
    rw [abs_div, abs_mul, abs_of_pos hQ0, div_le_iff₀ hQ0]
    calc |β| * |(n : ℝ) - c| ≤ 1 * (q / 2) :=
          mul_le_mul hβ (hdist n hn) (abs_nonneg _) zero_le_one
      _ ≤ 1 / 2 * Q := by linarith
  have hkey : ∀ n : ℤ, π * α * n = π * ((a * n + c₀ : ℤ) + τn n) / q := by
    intro n
    simp only [τn, s₀, w, hα]
    push_cast
    field_simp
    ring
  -- Choose the orientation `σ = ±1` so that `s = σ s₀ ≥ 0`.
  obtain ⟨σ, hσ, hσs⟩ : ∃ σ : ℤ, σ * σ = 1 ∧ 0 ≤ (σ : ℝ) * s₀ := by
    rcases le_or_lt 0 s₀ with h0 | h0
    · exact ⟨1, by norm_num, by simpa using h0⟩
    · exact ⟨-1, by norm_num, by push_cast; linarith⟩
  have hσr : (σ : ℝ) * σ = 1 := by exact_mod_cast hσ
  have hσabs : |(σ : ℝ)| = 1 := by
    have : |(σ : ℝ)| * |(σ : ℝ)| = 1 := by rw [← abs_mul, hσr, abs_one]
    nlinarith [abs_nonneg (σ : ℝ)]
  set s := (σ : ℝ) * s₀
  have hs1 : s ≤ 1 / 2 := by
    calc s ≤ |s| := le_abs_self _
      _ = |s₀| := by simp only [s, abs_mul, hσabs, one_mul]
      _ ≤ 1 / 2 := hs₀
  set τ' := fun n : ℤ => (σ : ℝ) * τn n
  have hτ' : ∀ n ∈ S, τ' n ∈ Icc (s - 1 / 2) (s + 1 / 2) := by
    intro n hn
    have hb := hsmall n hn
    have : |(σ : ℝ) * (β * (n - c) / Q)| ≤ 1 / 2 := by rw [abs_mul, hσabs, one_mul]; exact hb
    rw [abs_le] at this
    simp only [τ', τn, s, mul_add, mem_Icc]
    constructor <;> linarith [this.1, this.2]
  set m := fun n : ℤ => σ * (a * n + c₀)
  set R := fun n : ℤ => (m n % (q : ℤ)).toNat
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq1
  have hRlt : ∀ n, R n < q := by
    intro n; simp only [R]
    have h1 := Int.emod_nonneg (m n) hqz.ne'
    have h2 := Int.emod_lt_of_pos (m n) hqz
    omega
  have hRcast : ∀ n, ((R n : ℕ) : ℤ) = m n % q := fun n =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hqz.ne')
  -- Each term only depends on the residue.
  have hterm : ∀ n : ℤ, min A (C / Real.sin (π * α * n) ^ 2) = min A (C * fq q (R n + τ' n)) := by
    intro n
    congr 1
    rw [hkey, fq, mul_one_div]
    congr 1
    have hm : (a * n + c₀ : ℤ) = σ * (q * (m n / q) + (R n : ℤ)) := by
      rw [hRcast, Int.ediv_add_emod]; simp only [m]; rw [← mul_assoc, hσ, one_mul]
    have harg : π * (((a * n + c₀ : ℤ) : ℝ) + τn n) / q =
        (σ : ℝ) * (π * ((R n : ℝ) + τ' n) / q + ((m n / q : ℤ) : ℝ) * π) := by
      rw [hm]; push_cast; simp only [τ']; field_simp; ring_nf
      rw [show (σ : ℝ) ^ 2 = 1 by rw [sq, hσr]]; ring
    rw [harg]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hσ with hs | hs <;>
    · subst hs; push_cast
      simp only [one_mul, neg_one_mul, Real.sin_neg, neg_sq]
      rw [sin_sq_add_int_mul_pi]
  -- Reindex by residues.
  set τR := fun r : ℕ => if hr : ∃ n ∈ S, R n = r then τ' hr.choose else s
  have hinj : Set.InjOn R S := by
    intro n hn n' hn' hR
    have hmod : m n % q = m n' % q := by rw [← hRcast, ← hRcast]; exact congrArg _ hR
    have hdvd : (q : ℤ) ∣ a * (n - n') := by
      have h1 : (q : ℤ) ∣ m n - m n' := Int.ModEq.dvd hmod.symm
      have : m n - m n' = σ * (a * (n - n')) := by simp only [m]; ring
      rw [this] at h1
      have h2 : (q : ℤ) ∣ σ * (σ * (a * (n - n'))) := dvd_mul_of_dvd_right h1 σ
      rwa [← mul_assoc, hσ, one_mul] at h2
    have hd : (q : ℤ) ∣ n - n' := hcop.symm.dvd_of_dvd_mul_left hdvd
    simp only [S, Finset.coe_Ioc, Set.mem_Ioc] at hn hn'
    obtain ⟨t, ht⟩ := hd
    have : t = 0 := by
      by_contra ht0
      rcases lt_or_gt_of_ne ht0 with h | h
      · have : (q : ℤ) * t ≤ -q := by nlinarith
        omega
      · have : (q : ℤ) ≤ q * t := by nlinarith
        omega
    subst this; omega
  have hτR : ∀ n ∈ S, τR (R n) = τ' n := by
    intro n hn
    have hex : ∃ n' ∈ S, R n' = R n := ⟨n, hn, rfl⟩
    simp only [τR, dif_pos hex]
    have := hex.choose_spec
    rw [hinj this.1 hn this.2]
  refine ⟨s, hσs, hs1, τR, fun r => ?_, ?_⟩
  · simp only [τR]
    split_ifs with hr
    · exact hτ' _ hr.choose_spec.1
    · exact ⟨by linarith, by linarith⟩
  · rw [Finset.sum_congr rfl fun n _ => hterm n]
    refine Finset.sum_nbij R (fun n _ => Finset.mem_range.2 (hRlt n)) hinj ?_ ?_
    · have hcard : (Finset.range q).card ≤ S.card := by
        simp only [S, Int.card_Ioc, Finset.card_range]; omega
      intro r hr
      obtain ⟨n, hn, hrn⟩ := Finset.surj_on_of_inj_on_of_card_le (fun n _ => R n)
        (fun n _ => Finset.mem_range.2 (hRlt n)) (fun n n' hn hn' h => hinj hn hn' h) hcard r hr
      exact ⟨n, hn, hrn.symm⟩
    · intro n hn; rw [hτR n hn]


/-- **[B, Lemma 4.1.1]** -/
theorem lemma_4_1_1 {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) (y : ℝ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∑ n ∈ Finset.Ioc ⌊y⌋ ⌊y + q⌋, min A (C / Real.sin (π * α * n) ^ 2) ≤
      min (2 * A + 6 * q ^ 2 / π ^ 2 * C) (3 * A + 4 * q / π * √(A * C)) := by
  obtain ⟨s, hs0, hs1, τ, hτ, heq⟩ := residue_form h y A C
  rw [heq]
  exact le_min (core_bound₁ h.1 hs0 hs1 hA hC τ hτ) (core_bound₂ h.1 hs0 hs1 hA hC τ hτ)

end TernaryGoldbach.MinorArcs
