import Mathlib

/-!
# Trigonometric sums [B, §4.1]

Proofs of [B, Lemmas 4.1.1, 4.1.2]: for `α = a/q + β/qQ`, `(a, q) = 1`, `|β| ≤ 1`, `q ≤ Q`,

* (4.1.1) `∑_{y < n ≤ y + q} min(A, C/sin²(παn)) ≤ min(2A + (6q²/π²) C, 3A + (4q/π) √(AC))`;
* (4.1.2) if `0 ≤ y₁ < y₂ ≤ Q/2`, `y₂ - y₁ ≤ q`:
  `∑_{y₁ < n ≤ y₂, q ∤ n} min(A, C/sin²(παn)) ≤ min((20/3π²) C q², 2A + (4q/π) √(AC))`.

* (4.1.3) under the same hypotheses,
  `∑_{y₁ < n ≤ y₂, q ∤ n} min(B/|sin(παn)|, C/sin²(παn)) ≤ (2Bq/π) max(2, log(Ce³q/(Bπ)))`
  and `≤ (2Bq/π) log(2e²q/π)`.

For 4.1.2 the final step needs `t²/sin²t + (t/2) cot 2t ≤ 5/4` (tight to fourth order) and
`t²/sin²t + t cot(3t/2) ≤ 5/3`; we prove them from `x cot x ≤ 1 - x²/3 (- x⁴/45)` and
`t²/sin²t ≤ 1 + t²/3 + …`, using alternating Taylor bounds for `sin`, `cos` up to degree 8.

For 4.1.3 we do **not** follow [B]'s proof, which bounds the sum by
`2 ∑_{r ≤ q/2} min(B/sin(π(r-1/2)/q), C/sin²(π(r-1/2)/q))`: that intermediate quantity can exceed
the stated `(2Bq/π) max(2, …)` (numerically by ≈7% at `q = 140`, `C ≈ Bπ/2q`), and [B]'s
treatment of small `C` ("relax the input to `C = B sin π/q`") yields `max(≈2.55, …)`, not
`max(2, …)`.  The statement itself is true.  We use the sharper fact that the residues lie at
distance `≥ r` (low) and `≥ k - 1/2` (high), i.e. at most one point per half-integer, so the sum
is `≤ h(1/2) + (2q/π) ∫_{π/2q}^{π/2} min(B/sin v, C/sin² v) dv`, and then treat the three ranges
`C ≥ B`, `B sin(π/2q) ≤ C < B`, `C < B sin(π/2q)` separately.

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
  have hS1 : t - t ^ 3 / 4 < Real.sin t := by
    have := Real.sin_gt_sub_cube ht; nlinarith [pow_pos ht 3]
  have hS2 := Real.sin_le ht.le
  have hC1 := Real.one_sub_sq_div_two_le_cos (x := t)
  have hSpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_gt_three])
  have hCpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [Real.pi_gt_three]⟩
  have hcore := trig_core t (Real.sin t) (Real.cos t) ht hpi hS1 hS2 hC1
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have h : t ^ 2 / Real.sin t ^ 2 + t * ((2 * Real.cos t ^ 2 - 1) / (2 * Real.sin t * Real.cos t)) =
      (2 * t ^ 2 * Real.cos t + t * Real.sin t * (2 * Real.cos t ^ 2 - 1)) /
        (2 * Real.sin t ^ 2 * Real.cos t) := by
    field_simp
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
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
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
        rw [show π * (q / 2) / q = π / 2 by field_simp, Real.cos_pi_div_two, mul_one]
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
  rcases le_or_gt (π / 2) w with hwpi | hwpi
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
    have hvol : volume.real (Ioc (u₁ - 1 + i) (u₁ - 1 + (i + 1 : ℕ))) = 1 := by
      rw [Real.volume_real_Ioc_of_le (by push_cast; linarith)]; push_cast; ring
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
    congr 2 <;> field_simp <;> simp
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
    rw [h1, ite_eq_right h2, add_zero, two_mul, Finset.sum_range_add]
    congr 1
    rw [← Finset.sum_range_reflect (fun x => F (K + x))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj; congr 1; omega
  · have h1 : (2 * K + 1) / 2 = K := by omega
    have h2 : (2 * K + 1) % 2 = 1 := by omega
    rw [h1, ite_eq_left h2, show 2 * K + 1 = K + (K + 1) by ring, Finset.sum_range_add,
      Finset.sum_range_succ', add_zero, add_assoc]
    congr 1
    congr 1
    rw [← Finset.sum_range_reflect (fun x => F (K + (x + 1)))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj; congr 1; omega

/-- `f_q` is symmetric under `u ↦ q - u` and decreasing towards `q/2`. -/
theorem fq_le_of_between {q u v : ℝ} (hq : 0 < q) (hu : 0 < u) (huv : u ≤ v) (hvq : v ≤ q - u) :
    fq q v ≤ fq q u := by
  rcases le_or_gt v (q / 2) with hv | hv
  · exact fq_anti hq hu huv hv
  · have hsym : fq q v = fq q (q - v) := by
      unfold fq
      rw [show π * (q - v) / q = π - π * v / q by field_simp, Real.sin_pi_sub]
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
  have e2 : π / q = 2 * t := by rw [ht]; field_simp
  have e3 : q / π = 1 / (2 * t) := by rw [ht]; field_simp
  rw [e1, e2, e3]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
  have e4 : 6 * q ^ 2 / π ^ 2 = 3 / 2 / t ^ 2 := by rw [ht]; field_simp; ring
  rw [e4, le_div_iff₀ (by positivity)]
  calc (1 / Real.sin t ^ 2 + 2 * (1 / (2 * t) * (Real.cos (2 * t) / Real.sin (2 * t)))) * t ^ 2
      = t ^ 2 / Real.sin t ^ 2 + t * (Real.cos (2 * t) / Real.sin (2 * t)) := by
        have h2t : t ^ 2 * (2 * (1 / (2 * t))) = t := by field_simp
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
    have := Int.floor_add_intCast y (q : ℤ); push_cast at this; exact this
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
    rcases le_or_gt 0 s₀ with h0 | h0
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
      rw [hRcast, Int.mul_ediv_add_emod]; simp only [m]; rw [← mul_assoc, hσ, one_mul]
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
    simp only [τR, dite_eq_left hex]
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


/-! ## Taylor bounds and the inequalities for Lemma 4.1.2 -/

/-- Comparison of functions with the same value at `0` via their derivatives on `[0, ∞)`. -/
theorem le_of_hasDerivAt_le {f g f' g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (h0 : f 0 ≤ g 0) (h : ∀ x, 0 ≤ x → f' x ≤ g' x)
    {x : ℝ} (hx : 0 ≤ x) : f x ≤ g x := by
  have hmono : MonotoneOn (fun x => g x - f x) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y _ => ((hg y).sub (hf y)).continuousAt.continuousWithinAt)
      (fun y _ => ((hg y).sub (hf y)).hasDerivWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    linarith [h y (le_of_lt hy)]
  have := hmono Set.self_mem_Ici hx hx
  simp only at this
  linarith

theorem sin_ge_deg3 {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  refine le_of_hasDerivAt_le (f := fun x => x - x ^ 3 / 6) (g := Real.sin)
    (f' := fun x => 1 - x ^ 2 / 2) (g' := Real.cos)
    (fun x => ?_) Real.hasDerivAt_sin (by simp) (fun x _ => one_sub_sq_div_two_le_cos) hx
  convert (hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6) using 1 <;> first | ring1 | (funext y; simp only [Pi.sub_apply, Pi.add_apply, id_eq]; done) | (simp; ring1) | (norm_num; ring1)

theorem cos_le_deg4 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  refine le_of_hasDerivAt_le (f := Real.cos) (g := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24)
    (f' := fun x => -Real.sin x) (g' := fun x => -x + x ^ 3 / 6)
    Real.hasDerivAt_cos (fun x => ?_) (by simp) (fun x hx => by linarith [sin_ge_deg3 hx]) hx
  convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
    ((hasDerivAt_pow 4 x).div_const 24) using 1 <;> first | ring1 | (funext y; simp only [Pi.sub_apply, Pi.add_apply, id_eq]; done) | (simp; ring1) | (norm_num; ring1)

theorem sin_le_deg5 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  refine le_of_hasDerivAt_le (f := Real.sin) (g := fun x => x - x ^ 3 / 6 + x ^ 5 / 120)
    (f' := Real.cos) (g' := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24)
    Real.hasDerivAt_sin (fun x => ?_) (by simp) (fun x hx => cos_le_deg4 hx) hx
  convert ((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
    ((hasDerivAt_pow 5 x).div_const 120) using 1 <;> first | ring1 | (funext y; simp only [Pi.sub_apply, Pi.add_apply, id_eq]; done) | (simp; ring1) | (norm_num; ring1)

theorem cos_ge_deg6 {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  refine le_of_hasDerivAt_le (f := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)
    (g := Real.cos) (f' := fun x => -x + x ^ 3 / 6 - x ^ 5 / 120)
    (g' := fun x => -Real.sin x) (fun x => ?_) Real.hasDerivAt_cos (by simp)
    (fun x hx => by linarith [sin_le_deg5 hx]) hx
  convert (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
    ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_pow 6 x).div_const 720) using 1 <;> first | ring1 | (funext y; simp only [Pi.sub_apply, Pi.add_apply, id_eq]; done) | (simp; ring1) | (norm_num; ring1)

theorem sin_ge_deg7 {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  refine le_of_hasDerivAt_le (f := fun x => x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)
    (g := Real.sin) (f' := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)
    (g' := Real.cos) (fun x => ?_) Real.hasDerivAt_sin (by simp) (fun x hx => cos_ge_deg6 hx) hx
  convert (((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
    ((hasDerivAt_pow 5 x).div_const 120)).sub ((hasDerivAt_pow 7 x).div_const 5040) using 1 <;> first | ring1 | (funext y; simp only [Pi.sub_apply, Pi.add_apply, id_eq]; done) | (simp; ring1) | (norm_num; ring1)


theorem cos_le_deg8 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  refine le_of_hasDerivAt_le (f := Real.cos)
    (g := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320)
    (f' := fun x => -Real.sin x) (g' := fun x => -x + x ^ 3 / 6 - x ^ 5 / 120 + x ^ 7 / 5040)
    Real.hasDerivAt_cos (fun x => ?_) (by simp) (fun x hx => by linarith [sin_ge_deg7 hx]) hx
  convert ((((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
    ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_pow 6 x).div_const 720)).add
    ((hasDerivAt_pow 8 x).div_const 40320) using 1 <;> first | ring1 | (funext y; simp only [Pi.sub_apply, Pi.add_apply, id_eq]; done) | (simp; ring1) | (norm_num; ring1)

/-- `x cot x ≤ 1 - x²/3` for `0 < x ≤ π/2`, in the form `x cos x ≤ (1 - x²/3) sin x`. -/
theorem mul_cos_le₁ {x : ℝ} (hx : 0 < x) (hx1 : x ≤ π / 2) :
    x * Real.cos x ≤ (1 - x ^ 2 / 3) * Real.sin x := by
  have hx2 : x ≤ 1571 / 1000 := hx1.trans (by linarith [Real.pi_lt_d4])
  have hc := cos_le_deg4 hx.le
  have hs := sin_ge_deg7 hx.le
  have hk : 0 ≤ 1 - x ^ 2 / 3 := by nlinarith
  have hpoly : x * (1 - x ^ 2 / 2 + x ^ 4 / 24) ≤
      (1 - x ^ 2 / 3) * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) := by
    have h : (1 - x ^ 2 / 3) * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) -
        x * (1 - x ^ 2 / 2 + x ^ 4 / 24) = x ^ 5 * (1 / 45 - x ^ 2 / 336 + x ^ 4 / 15120) := by ring
    have : 0 ≤ 1 / 45 - x ^ 2 / 336 + x ^ 4 / 15120 := by nlinarith [sq_nonneg (x ^ 2)]
    nlinarith [pow_pos hx 5]
  calc x * Real.cos x ≤ x * (1 - x ^ 2 / 2 + x ^ 4 / 24) := mul_le_mul_of_nonneg_left hc hx.le
    _ ≤ _ := hpoly
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hk

/-- `x cot x ≤ 1 - x²/3 - x⁴/45` for `0 < x ≤ π/3`. -/
theorem mul_cos_le₂ {x : ℝ} (hx : 0 < x) (hx1 : x ≤ π / 3) :
    x * Real.cos x ≤ (1 - x ^ 2 / 3 - x ^ 4 / 45) * Real.sin x := by
  have hx2 : x ≤ 1048 / 1000 := hx1.trans (by linarith [Real.pi_lt_d4])
  have hc := cos_le_deg8 hx.le
  have hs := sin_ge_deg7 hx.le
  have hu : x ^ 2 ≤ 11 / 10 := by nlinarith
  have hu2 : x ^ 4 ≤ 121 / 100 := by nlinarith [pow_le_pow_left₀ (sq_nonneg x) hu 2]
  have hk : 0 ≤ 1 - x ^ 2 / 3 - x ^ 4 / 45 := by linarith
  have hpoly : x * (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) ≤
      (1 - x ^ 2 / 3 - x ^ 4 / 45) * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) := by
    have h : (1 - x ^ 2 / 3 - x ^ 4 / 45) * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) -
        x * (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) =
        x ^ 7 * (2 / 945 - 29 * x ^ 2 / 201600 + x ^ 4 / 226800) := by ring
    have : 0 ≤ 2 / 945 - 29 * x ^ 2 / 201600 + x ^ 4 / 226800 := by nlinarith [sq_nonneg (x ^ 2)]
    nlinarith [pow_pos hx 7]
  calc x * Real.cos x ≤ x * (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) :=
        mul_le_mul_of_nonneg_left hc hx.le
    _ ≤ _ := hpoly
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hk

/-- `t² ≤ (1 + t²/3 + t⁴/10) sin² t` for `0 < t ≤ π/3`. -/
theorem sq_le_sin_sq₁ {t : ℝ} (ht : 0 < t) (ht1 : t ≤ π / 3) :
    t ^ 2 ≤ (1 + t ^ 2 / 3 + t ^ 4 / 10) * Real.sin t ^ 2 := by
  have ht2 : t ≤ 1048 / 1000 := ht1.trans (by linarith [Real.pi_lt_d4])
  have hs := sin_ge_deg7 ht.le
  set L := t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040
  have hL0 : 0 ≤ L := by
    have : t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 =
        t * (1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040) := by ring
    simp only [L]; rw [this]
    have : 0 ≤ 1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040 := by
      have hu : t ^ 2 ≤ 11 / 10 := by nlinarith
      have hu3 : t ^ 6 ≤ 2 := by
        have := pow_le_pow_left₀ (sq_nonneg t) hu 3
        rw [← pow_mul] at this; norm_num at this; linarith
      have : 0 ≤ t ^ 4 := by positivity
      linarith
    positivity
  have hpoly : t ^ 2 ≤ (1 + t ^ 2 / 3 + t ^ 4 / 10) * L ^ 2 := by
    have h : (1 + t ^ 2 / 3 + t ^ 4 / 10) * L ^ 2 - t ^ 2 = t ^ 6 * (t ^ 12 / 254016000 -
        121 * t ^ 10 / 381024000 + 529 * t ^ 8 / 42336000 - 5 * t ^ 6 / 18144 +
        71 * t ^ 4 / 20160 - 41 * t ^ 2 / 1890 + 1 / 30) := by simp only [L]; ring
    have hu : t ^ 2 ≤ 1099 / 1000 := by nlinarith
    have : 0 ≤ t ^ 12 / 254016000 - 121 * t ^ 10 / 381024000 + 529 * t ^ 8 / 42336000 -
        5 * t ^ 6 / 18144 + 71 * t ^ 4 / 20160 - 41 * t ^ 2 / 1890 + 1 / 30 := by
      have h6 : t ^ 6 ≤ 2 := by nlinarith [pow_le_pow_left₀ (by positivity) hu 3]
      have h10 : t ^ 10 ≤ 2 := by nlinarith [pow_le_pow_left₀ (by positivity) hu 5]
      nlinarith [pow_pos ht 12, pow_pos ht 8, pow_pos ht 4]
    nlinarith [pow_pos ht 6]
  calc t ^ 2 ≤ (1 + t ^ 2 / 3 + t ^ 4 / 10) * L ^ 2 := hpoly
    _ ≤ (1 + t ^ 2 / 3 + t ^ 4 / 10) * Real.sin t ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hs 2) (by positivity)

/-- `t² ≤ (1 + t²/3 + t⁴/15 + t⁶/20) sin² t` for `0 < t ≤ π/6`. -/
theorem sq_le_sin_sq₂ {t : ℝ} (ht : 0 < t) (ht1 : t ≤ π / 6) :
    t ^ 2 ≤ (1 + t ^ 2 / 3 + t ^ 4 / 15 + t ^ 6 / 20) * Real.sin t ^ 2 := by
  have ht2 : t ≤ 524 / 1000 := ht1.trans (by linarith [Real.pi_lt_d4])
  have hs := sin_ge_deg7 ht.le
  set L := t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040
  have hL0 : 0 ≤ L := by
    have : t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 =
        t * (1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040) := by ring
    simp only [L]; rw [this]
    have : 0 ≤ 1 - t ^ 2 / 6 + t ^ 4 / 120 - t ^ 6 / 5040 := by
      have hu : t ^ 2 ≤ 11 / 10 := by nlinarith
      have hu3 : t ^ 6 ≤ 2 := by
        have := pow_le_pow_left₀ (sq_nonneg t) hu 3
        rw [← pow_mul] at this; norm_num at this; linarith
      have : 0 ≤ t ^ 4 := by positivity
      linarith
    positivity
  have hpoly : t ^ 2 ≤ (1 + t ^ 2 / 3 + t ^ 4 / 15 + t ^ 6 / 20) * L ^ 2 := by
    have h : (1 + t ^ 2 / 3 + t ^ 4 / 15 + t ^ 6 / 20) * L ^ 2 - t ^ 2 = t ^ 8 * (t ^ 12 / 508032000 -
        31 * t ^ 10 / 190512000 + 313 * t ^ 8 / 47628000 - 19147 * t ^ 6 / 127008000 +
        133 * t ^ 4 / 64800 - 4423 * t ^ 2 / 302400 + 149 / 3780) := by simp only [L]; ring
    have hu : t ^ 2 ≤ 275 / 1000 := by nlinarith
    have : 0 ≤ t ^ 12 / 508032000 - 31 * t ^ 10 / 190512000 + 313 * t ^ 8 / 47628000 -
        19147 * t ^ 6 / 127008000 + 133 * t ^ 4 / 64800 - 4423 * t ^ 2 / 302400 + 149 / 3780 := by
      have h6 : t ^ 6 ≤ 1 := by nlinarith [pow_le_pow_left₀ (by positivity) hu 3]
      have h10 : t ^ 10 ≤ 1 := by nlinarith [pow_le_pow_left₀ (by positivity) hu 5]
      nlinarith [pow_pos ht 12, pow_pos ht 8, pow_pos ht 4]
    nlinarith [pow_pos ht 8]
  calc t ^ 2 ≤ (1 + t ^ 2 / 3 + t ^ 4 / 15 + t ^ 6 / 20) * L ^ 2 := hpoly
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hs 2) (by positivity)

/-- **T2.** `t²/sin²t + (t/2) cot 2t ≤ 5/4` for `0 < t ≤ π/6`. -/
theorem trig_T2 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ π / 6) :
    t ^ 2 / Real.sin t ^ 2 + t / 2 * (Real.cos (2 * t) / Real.sin (2 * t)) ≤ 5 / 4 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hs2 : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have ha := mul_cos_le₂ (x := 2 * t) (by linarith) (by linarith)
  have hb := sq_le_sin_sq₂ ht ht1
  have ht2 : t ^ 2 ≤ 275 / 1000 := by nlinarith [Real.pi_lt_d4]
  have h1 : t ^ 2 / Real.sin t ^ 2 ≤ 1 + t ^ 2 / 3 + t ^ 4 / 15 + t ^ 6 / 20 := by
    rw [div_le_iff₀ (by positivity)]; exact hb
  have h2 : t / 2 * (Real.cos (2 * t) / Real.sin (2 * t)) ≤
      1 / 4 * (1 - (2 * t) ^ 2 / 3 - (2 * t) ^ 4 / 45) := by
    have := mul_le_mul_of_nonneg_left (div_le_iff₀ hs2 |>.2 ha) (by norm_num : (0:ℝ) ≤ 1 / 4)
    calc t / 2 * (Real.cos (2 * t) / Real.sin (2 * t))
        = 1 / 4 * (2 * t * Real.cos (2 * t) / Real.sin (2 * t)) := by ring
      _ ≤ _ := this
  nlinarith [pow_pos ht 4, pow_pos ht 6]

/-- **T3.** `t²/sin²t + t cot(3t/2) ≤ 5/3` for `0 < t ≤ π/3`. -/
theorem trig_T3 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ π / 3) :
    t ^ 2 / Real.sin t ^ 2 + t * (Real.cos (3 * t / 2) / Real.sin (3 * t / 2)) ≤ 5 / 3 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hs3 : 0 < Real.sin (3 * t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have ha := mul_cos_le₁ (x := 3 * t / 2) (by linarith) (by linarith)
  have hb := sq_le_sin_sq₁ ht ht1
  have ht2 : t ^ 2 ≤ 1099 / 1000 := by nlinarith [Real.pi_lt_d4]
  have h1 : t ^ 2 / Real.sin t ^ 2 ≤ 1 + t ^ 2 / 3 + t ^ 4 / 10 := by
    rw [div_le_iff₀ (by positivity)]; exact hb
  have h2 : t * (Real.cos (3 * t / 2) / Real.sin (3 * t / 2)) ≤
      2 / 3 * (1 - (3 * t / 2) ^ 2 / 3) := by
    have := mul_le_mul_of_nonneg_left (div_le_iff₀ hs3 |>.2 ha) (by norm_num : (0:ℝ) ≤ 2 / 3)
    calc t * (Real.cos (3 * t / 2) / Real.sin (3 * t / 2))
        = 2 / 3 * (3 * t / 2 * Real.cos (3 * t / 2) / Real.sin (3 * t / 2)) := by ring
      _ ≤ _ := this
  nlinarith [pow_pos ht 4]


/-! ## Lemma 4.1.2 -/

/-- Midpoint sums at integer points: `∑_{r=2}^{L} f_q(r) ≤ (q/π) cot(3π/2q)` for `2L + 1 ≤ q`. -/
theorem sum_fq_int_le {q : ℝ} {L : ℕ} (hq : 3 ≤ q) (hL : 2 * (L : ℝ) + 1 ≤ q) :
    ∑ r ∈ Finset.Icc 2 L, fq q r ≤
      q / π * (Real.cos (3 * π / (2 * q)) / Real.sin (3 * π / (2 * q))) := by
  have hq0 : 0 < q := by linarith
  have hcot0 : 0 ≤ Real.cos (3 * π / (2 * q)) / Real.sin (3 * π / (2 * q)) := by
    have h1 : 3 * π / (2 * q) ≤ π / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
    have h0 : 0 < 3 * π / (2 * q) := by positivity
    exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h1⟩)
      (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])).le
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    exact mul_nonneg (by positivity) hcot0
  have hHH : ∀ r ∈ Finset.Icc 2 L, fq q r ≤ ∫ u in ((r : ℝ) - 1 / 2)..(r + 1 / 2), fq q u := by
    intro r hr
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.1 hr).1
    have hrL : (r : ℝ) ≤ L := by exact_mod_cast (Finset.mem_Icc.1 hr).2
    exact (convexOn_fq hq0).le_integral_of_midpoint (m := r)
      (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (continuousOn_fq hq0 (by linarith) (by linarith))
  have hsum : ∑ r ∈ Finset.Icc 2 L, ∫ u in ((r : ℝ) - 1 / 2)..(r + 1 / 2), fq q u =
      ∫ u in (3 / 2 : ℝ)..(L + 1 / 2), fq q u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (f := fq q) (a := fun k : ℕ => (k : ℝ) + 3 / 2) (n := L - 1) fun k hk => by
        have hk2 : k + 2 ≤ L := by omega
        have : (k : ℝ) + 2 ≤ L := by exact_mod_cast hk2
        have hc := continuousOn_fq hq0 (a := (k : ℝ) + 3 / 2) (b := (k : ℝ) + 3 / 2 + 1)
          (by positivity) (by linarith)
        show IntervalIntegrable (fq q) MeasureTheory.volume ((k : ℝ) + 3 / 2)
          (((k + 1 : ℕ) : ℝ) + 3 / 2)
        push_cast; ring_nf at hc ⊢
        exact hc.intervalIntegrable_of_Icc (by linarith)
    simp only [Nat.cast_zero, zero_add] at h
    rw [show ((L - 1 : ℕ) : ℝ) + 3 / 2 = L + 1 / 2 by rw [Nat.cast_sub (by omega)]; ring] at h
    rw [← h]
    refine Finset.sum_bij (fun r _ => r - 2) ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_Icc] at hr; simp only [Finset.mem_range]; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
    · intro k hk; simp only [Finset.mem_range] at hk
      exact ⟨k + 2, by simp only [Finset.mem_Icc]; omega, by simp⟩
    · intro r hr; simp only [Finset.mem_Icc] at hr
      push_cast [Nat.cast_sub hr.1]; ring_nf
  have hLq : ∫ u in (3 / 2 : ℝ)..(L + 1 / 2), fq q u ≤ ∫ u in (3 / 2 : ℝ)..(q / 2), fq q u := by
    have hL1 : (3 / 2 : ℝ) ≤ L + 1 / 2 := by
      have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
      linarith
    have e := intervalIntegral.integral_add_adjacent_intervals (a := (3 / 2 : ℝ))
      (b := (L : ℝ) + 1 / 2) (c := q / 2) (μ := MeasureTheory.volume)
      ((continuousOn_fq hq0 (by norm_num) (by linarith)).intervalIntegrable_of_Icc hL1)
      ((continuousOn_fq hq0 (by linarith) (by linarith)).intervalIntegrable_of_Icc
        (by linarith))
    have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume)
      (show (L : ℝ) + 1 / 2 ≤ q / 2 by linarith) fun u _ => fq_nonneg q u
    linarith
  calc ∑ r ∈ Finset.Icc 2 L, fq q r
      ≤ ∑ r ∈ Finset.Icc 2 L, ∫ u in ((r : ℝ) - 1 / 2)..(r + 1 / 2), fq q u :=
        Finset.sum_le_sum hHH
    _ ≤ ∫ u in (3 / 2 : ℝ)..(q / 2), fq q u := hsum ▸ hLq
    _ = _ := by
        rw [integral_fq hq0 (by norm_num) (by linarith) (by linarith)]
        rw [show π * (q / 2) / q = π / 2 by field_simp, Real.cos_pi_div_two,
          show π * (3 / 2) / q = 3 * π / (2 * q) by ring]
        simp


/-- Split residues `1, …, q-1` into low `r ≤ (q-1)/2` and high `q - k`, `k ≤ q/2`. -/
theorem sum_Icc_low_high (F : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) :
    ∑ R ∈ Finset.Icc 1 (q - 1), F R =
      ∑ r ∈ Finset.Icc 1 ((q - 1) / 2), F r + ∑ k ∈ Finset.Icc 1 (q / 2), F (q - k) := by
  have hIcc : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, hIcc, hIcc, ← Finset.sum_Ioc_consecutive F (Nat.zero_le ((q - 1) / 2))
    (by omega : (q - 1) / 2 ≤ q - 1)]
  congr 1
  refine Finset.sum_bij (fun R _ => q - R) ?_ ?_ ?_ ?_
  · intro R hR; simp only [Finset.mem_Ioc] at hR ⊢; omega
  · intro a ha b hb hab; simp only [Finset.mem_Ioc] at ha hb; omega
  · intro k hk; simp only [Finset.mem_Ioc] at hk
    exact ⟨q - k, by simp only [Finset.mem_Ioc]; omega, by omega⟩
  · intro R hR; simp only [Finset.mem_Ioc] at hR; show F R = F (q - (q - R)); congr 1; omega

set_option maxHeartbeats 800000 in
/-- **Core of Lemma 4.1.2.**  Residues `1, …, q-1` with shifts `τ_R ∈ [0, 1/2]`. -/
theorem core_4_1_2 {q : ℕ} (hq : 1 ≤ q) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (τ : ℕ → ℝ)
    (hτ : ∀ R, τ R ∈ Icc (0 : ℝ) (1 / 2)) :
    ∑ R ∈ Finset.Icc 1 (q - 1), min A (C * fq q (R + τ R)) ≤
      min (20 / (3 * π ^ 2) * C * q ^ 2) (2 * A + 4 * q / π * √(A * C)) := by
  have hb1 : 0 ≤ 20 / (3 * π ^ 2) * C * q ^ 2 := by positivity
  have hb2 : 0 ≤ 4 * q / π * √(A * C) := by positivity
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · interval_cases q
    · simp only [Nat.sub_self, Finset.Icc_eq_empty (by norm_num : ¬ (1 ≤ 0)), Finset.sum_empty]
      exact le_min hb1 (by linarith)
    · simp only [show (2 : ℕ) - 1 = 1 by rfl, Finset.Icc_self, Finset.sum_singleton]
      have hval : fq ((2 : ℕ) : ℝ) (1 / 2) = 2 := by
        unfold fq
        rw [show π * (1 / 2) / ((2 : ℕ) : ℝ) = π / 4 by push_cast; ring, Real.sin_pi_div_four]
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      have hle : fq ((2 : ℕ) : ℝ) (((1 : ℕ) : ℝ) + τ 1) ≤ 2 := by
        rw [← hval]
        exact fq_le_of_between (by norm_num) (by norm_num) (by push_cast; linarith [(hτ 1).1])
          (by push_cast; linarith [(hτ 1).2])
      have hpi : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have h80 : 2 * C ≤ 20 / (3 * π ^ 2) * C * ((2 : ℕ) : ℝ) ^ 2 := by
        rw [show 20 / (3 * π ^ 2) * C * ((2 : ℕ) : ℝ) ^ 2 = 80 / (3 * π ^ 2) * C by push_cast; ring]
        have : 2 ≤ 80 / (3 * π ^ 2) := by rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith
      refine le_min ?_ ?_
      · exact (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left hle hC).trans (by linarith))
      · exact (min_le_left _ _).trans (by linarith)
  set F := fun R : ℕ => min A (C * fq q (R + τ R))
  set G := fun u : ℝ => min A (C * fq q u)
  show ∑ R ∈ Finset.Icc 1 (q - 1), F R ≤ _
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set L := (q - 1) / 2
  set K := q / 2
  have hLq : 2 * (L : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : 2 * L + 1 ≤ q)
  have hKq : 2 * (K : ℝ) ≤ q := by exact_mod_cast (by omega : 2 * K ≤ q)
  -- Pointwise bounds.
  have hlow : ∀ r ∈ Finset.Icc 1 L, F r ≤ G r := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.1 hr).1
    have hrL : (r : ℝ) ≤ L := by exact_mod_cast (Finset.mem_Icc.1 hr).2
    refine min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ hC)
    exact fq_le_of_between hq0 (by linarith) (by linarith [(hτ r).1]) (by linarith [(hτ r).2])
  have hhigh : ∀ k ∈ Finset.Icc 1 K, F (q - k) ≤ G (k - 1 / 2) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.1 hk).2
    have hkq : k ≤ q := by have := (Finset.mem_Icc.1 hk).2; omega
    refine min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ hC)
    have hsym : fq q (((q - k : ℕ) : ℝ) + τ (q - k)) = fq q (k - τ (q - k)) := by
      unfold fq
      rw [Nat.cast_sub hkq, show π * ((q : ℝ) - k + τ (q - k)) / q =
        π - π * (k - τ (q - k)) / q by field_simp; ring, Real.sin_pi_sub]
    show fq q (((q - k : ℕ) : ℝ) + τ (q - k)) ≤ fq q (k - 1 / 2)
    rw [hsym]
    exact fq_le_of_between hq0 (by linarith) (by linarith [(hτ (q - k)).2])
      (by linarith [(hτ (q - k)).1])
  rw [sum_Icc_low_high F q hq]
  have hS1 := Finset.sum_le_sum hlow
  have hS2 := Finset.sum_le_sum hhigh
  refine le_min ?_ ?_
  · -- First bound.
    have hqr : (3 : ℝ) ≤ q := by exact_mod_cast hq3
    have hL1 : 1 ≤ L := by omega
    have hK1 : 1 ≤ K := by omega
    have hlowC : ∑ r ∈ Finset.Icc 1 L, G r ≤ C * (fq q 1 + ∑ r ∈ Finset.Icc 2 L, fq q r) := by
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (by simp; omega : 1 ∈ Finset.Icc 1 L)]
      rw [show Finset.Icc 1 L \ {1} = Finset.Icc 2 L by ext x; simp; omega, mul_add,
        Finset.mul_sum]
      refine add_le_add ?_ (Finset.sum_le_sum fun r _ => min_le_right _ _)
      show G ((1 : ℕ) : ℝ) ≤ C * fq q 1
      rw [Nat.cast_one]; exact min_le_right _ _
    have hhighC : ∑ k ∈ Finset.Icc 1 K, G (k - 1 / 2) ≤
        C * (fq q (1 / 2) + ∑ k ∈ Finset.Icc 2 K, fq q (k - 1 / 2)) := by
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (by simp; omega : 1 ∈ Finset.Icc 1 K)]
      rw [show Finset.Icc 1 K \ {1} = Finset.Icc 2 K by ext x; simp; omega, mul_add,
        Finset.mul_sum]
      refine add_le_add ?_ (Finset.sum_le_sum fun k _ => min_le_right _ _)
      show G (((1 : ℕ) : ℝ) - 1 / 2) ≤ C * fq q (1 / 2)
      rw [Nat.cast_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]; exact min_le_right _ _
    have hI1 := sum_fq_le (by linarith : (2 : ℝ) < q) (by linarith : (K : ℝ) ≤ q / 2)
    have hI1' := sum_fq_int_le hqr hLq
    -- T2 and T3.
    have hT2 : fq q (1 / 2) + q / π * (Real.cos (π / q) / Real.sin (π / q)) ≤ 5 * q ^ 2 / π ^ 2 := by
      obtain ⟨t, ht⟩ : ∃ t, t = π / (2 * q) := ⟨_, rfl⟩
      have ht0 : 0 < t := by rw [ht]; positivity
      have ht1 : t ≤ π / 6 := by
        rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
      have key := trig_T2 ht0 ht1
      have e1 : fq q (1 / 2) = 1 / Real.sin t ^ 2 := by simp only [fq, ht]; ring_nf
      have e2 : π / q = 2 * t := by rw [ht]; field_simp
      have e3 : (q : ℝ) / π = 1 / (2 * t) := by rw [ht]; field_simp
      have e4 : 5 * (q : ℝ) ^ 2 / π ^ 2 = 5 / 4 / t ^ 2 := by rw [ht]; field_simp; ring
      rw [e1, e2, e3, e4, le_div_iff₀ (by positivity)]
      have h2t : t ^ 2 * (1 / (2 * t)) = t / 2 := by field_simp
      calc (1 / Real.sin t ^ 2 + 1 / (2 * t) * (Real.cos (2 * t) / Real.sin (2 * t))) * t ^ 2
          = t ^ 2 / Real.sin t ^ 2 + (t ^ 2 * (1 / (2 * t))) *
              (Real.cos (2 * t) / Real.sin (2 * t)) := by ring
        _ = _ := by rw [h2t]
        _ ≤ 5 / 4 := key
    have hT3 : fq q 1 + q / π * (Real.cos (3 * π / (2 * q)) / Real.sin (3 * π / (2 * q))) ≤
        5 * q ^ 2 / (3 * π ^ 2) := by
      obtain ⟨t, ht⟩ : ∃ t, t = π / q := ⟨_, rfl⟩
      have ht0 : 0 < t := by rw [ht]; positivity
      have ht1 : t ≤ π / 3 := by
        rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
      have key := trig_T3 ht0 ht1
      have e1 : fq q 1 = 1 / Real.sin t ^ 2 := by simp only [fq, ht]; ring_nf
      have e2 : 3 * π / (2 * q) = 3 * t / 2 := by rw [ht]; field_simp
      have e3 : (q : ℝ) / π = 1 / t := by rw [ht]; field_simp
      have e4 : 5 * (q : ℝ) ^ 2 / (3 * π ^ 2) = 5 / 3 / t ^ 2 := by rw [ht]; field_simp; try ring
      rw [e1, e2, e3, e4, le_div_iff₀ (by positivity)]
      have h2t : t ^ 2 * (1 / t) = t := by field_simp
      calc (1 / Real.sin t ^ 2 + 1 / t * (Real.cos (3 * t / 2) / Real.sin (3 * t / 2))) * t ^ 2
          = t ^ 2 / Real.sin t ^ 2 + (t ^ 2 * (1 / t)) *
              (Real.cos (3 * t / 2) / Real.sin (3 * t / 2)) := by ring
        _ = _ := by rw [h2t]
        _ ≤ 5 / 3 := key
    have htot : 5 * (q : ℝ) ^ 2 / π ^ 2 + 5 * q ^ 2 / (3 * π ^ 2) = 20 / (3 * π ^ 2) * q ^ 2 := by
      field_simp; ring
    calc ∑ r ∈ Finset.Icc 1 L, F r + ∑ k ∈ Finset.Icc 1 K, F (q - k)
        ≤ C * (fq q 1 + ∑ r ∈ Finset.Icc 2 L, fq q r) +
            C * (fq q (1 / 2) + ∑ k ∈ Finset.Icc 2 K, fq q (k - 1 / 2)) :=
          add_le_add (hS1.trans hlowC) (hS2.trans hhighC)
      _ ≤ C * (5 * q ^ 2 / (3 * π ^ 2)) + C * (5 * q ^ 2 / π ^ 2) := by
          have e1 := mul_le_mul_of_nonneg_left
            (show fq q 1 + ∑ r ∈ Finset.Icc 2 L, fq q r ≤ 5 * q ^ 2 / (3 * π ^ 2) by linarith) hC
          have e2 := mul_le_mul_of_nonneg_left
            (show fq q (1 / 2) + ∑ k ∈ Finset.Icc 2 K, fq q (k - 1 / 2) ≤ 5 * q ^ 2 / π ^ 2 by
              linarith) hC
          linarith
      _ = C * (5 * q ^ 2 / π ^ 2 + 5 * q ^ 2 / (3 * π ^ 2)) := by ring
      _ = 20 / (3 * π ^ 2) * C * q ^ 2 := by rw [htot]; ring
  · -- Second bound.
    have hGA : ∀ u, G u ≤ A := fun u => min_le_left _ _
    have hG0 : ∀ u, 0 ≤ G u := fun u => le_min hA (mul_nonneg hC (fq_nonneg _ _))
    have hfam1 : ∑ r ∈ Finset.Icc 1 L, G r ≤ 2 * (q / π) * √(A * C) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      have := sum_G_le (u₁ := 1) (m := L) hq0 hA hC le_rfl (by linarith)
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [G]; push_cast; ring_nf
    have hfam2 : ∑ k ∈ Finset.Icc 1 K, G (k - 1 / 2) ≤ A + 2 * (q / π) * √(A * C) := by
      rcases Nat.lt_or_ge K 1 with hK | hK
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (by simp; omega : 1 ∈ Finset.Icc 1 K)]
      rw [show Finset.Icc 1 K \ {1} = Finset.Ico 2 (K + 1) by ext x; simp; omega,
        Finset.sum_Ico_eq_sum_range, show K + 1 - 2 = K - 1 by omega]
      refine add_le_add (hGA _) ?_
      have := sum_G_le (u₁ := 3 / 2) (m := K - 1) hq0 hA hC (by norm_num)
        (by rw [Nat.cast_sub hK]; push_cast; linarith)
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [G]; push_cast; ring_nf
    have h4 : 4 * (q : ℝ) / π * √(A * C) = 2 * (2 * (q / π) * √(A * C)) := by ring
    rw [h4]
    linarith


open Classical in
/-- **Reduction for Lemma 4.1.2.**  For `0 ≤ y₁ < n ≤ y₂ ≤ Q/2`, `q ∤ n`, `y₂ - y₁ ≤ q`, the terms
are bounded by `min(A, C f_q(R + τ_R))` over distinct residues `R ∈ [1, q-1]`, `τ_R ∈ [0, 1/2]`. -/
theorem residue_form₂ {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) {y₁ y₂ : ℝ}
    (hy : 0 ≤ y₁) (hlen : y₂ - y₁ ≤ q) (hy₂ : y₂ ≤ Q / 2) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ τ : ℕ → ℝ, (∀ R, τ R ∈ Icc (0 : ℝ) (1 / 2)) ∧
      ∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋,
          (if (q : ℤ) ∣ n then 0 else min A (C / Real.sin (π * α * n) ^ 2)) ≤
        ∑ R ∈ Finset.Icc 1 (q - 1), min A (C * fq q (R + τ R)) := by
  obtain ⟨hq1, hcop, β, hβ, hα, hqQ⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hQ0 : 0 < Q := by linarith
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq1
  set S := Finset.Ioc ⌊y₁⌋ ⌊y₂⌋
  set S' := S.filter fun n => ¬ (q : ℤ) ∣ n
  have hS : ∀ n ∈ S, 1 ≤ n ∧ (n : ℝ) ≤ y₂ := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have h0 : 0 ≤ ⌊y₁⌋ := Int.floor_nonneg.2 hy
    exact ⟨by omega, (Int.cast_le.2 hn.2).trans (Int.floor_le y₂)⟩
  have hgap : ∀ n ∈ S, ∀ n' ∈ S, n - n' < q := by
    intro n hn n' hn'
    rw [Finset.mem_Ioc] at hn hn'
    have h1 : ((n - n' : ℤ) : ℝ) < q := by
      have a1 : (n : ℝ) ≤ y₂ := (Int.cast_le.2 hn.2).trans (Int.floor_le y₂)
      have a2 : y₁ < n' := by
        have := Int.lt_floor_add_one y₁
        have : ((⌊y₁⌋ : ℤ) : ℝ) + 1 ≤ n' := by exact_mod_cast hn'.1
        linarith
      push_cast; linarith
    exact_mod_cast h1
  -- Orientation.
  obtain ⟨σ, hσ, hσβ⟩ : ∃ σ : ℤ, σ * σ = 1 ∧ 0 ≤ (σ : ℝ) * β := by
    rcases le_or_gt 0 β with h0 | h0
    · exact ⟨1, by norm_num, by simpa using h0⟩
    · exact ⟨-1, by norm_num, by push_cast; linarith⟩
  have hσr : (σ : ℝ) * σ = 1 := by exact_mod_cast hσ
  have hσabs : |(σ : ℝ)| = 1 := by
    have : |(σ : ℝ)| * |(σ : ℝ)| = 1 := by rw [← abs_mul, hσr, abs_one]
    nlinarith [abs_nonneg (σ : ℝ)]
  set τ' := fun n : ℤ => (σ : ℝ) * β * n / Q
  have hτ' : ∀ n ∈ S, τ' n ∈ Icc (0 : ℝ) (1 / 2) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hS n hn
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : (0 : ℤ) ≤ n)
    have hσβ1 : (σ : ℝ) * β ≤ 1 := by
      calc (σ : ℝ) * β ≤ |(σ : ℝ) * β| := le_abs_self _
        _ = |β| := by rw [abs_mul, hσabs, one_mul]
        _ ≤ 1 := hβ
    simp only [τ', mem_Icc]
    constructor
    · positivity
    · rw [div_le_iff₀ hQ0]; nlinarith
  set m := fun n : ℤ => σ * (a * n)
  set R := fun n : ℤ => (m n % (q : ℤ)).toNat
  have hRcast : ∀ n, ((R n : ℕ) : ℤ) = m n % q := fun n =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hqz.ne')
  have hRlt : ∀ n, R n < q := by
    intro n; simp only [R]
    have h1 := Int.emod_nonneg (m n) hqz.ne'
    have h2 := Int.emod_lt_of_pos (m n) hqz
    omega
  have hRpos : ∀ n ∈ S', 1 ≤ R n := by
    intro n hn
    rw [Finset.mem_filter] at hn
    by_contra h0
    have h00 : m n % q = 0 := by have := hRcast n; omega
    apply hn.2
    have h1 : (q : ℤ) ∣ σ * (a * n) := Int.dvd_of_emod_eq_zero h00
    have h2 : (q : ℤ) ∣ σ * (σ * (a * n)) := dvd_mul_of_dvd_right h1 σ
    rw [← mul_assoc, hσ, one_mul] at h2
    exact hcop.symm.dvd_of_dvd_mul_left h2
  have hterm : ∀ n : ℤ, min A (C / Real.sin (π * α * n) ^ 2) = min A (C * fq q (R n + τ' n)) := by
    intro n
    congr 1
    rw [fq, mul_one_div]
    congr 1
    have hm : a * n = σ * (q * (m n / q) + (R n : ℤ)) := by
      rw [hRcast, Int.mul_ediv_add_emod]; simp only [m]; rw [← mul_assoc, hσ, one_mul]
    have harg : π * α * n = (σ : ℝ) * (π * ((R n : ℝ) + τ' n) / q + ((m n / q : ℤ) : ℝ) * π) := by
      have e : π * α * n = π * (((a * n : ℤ) : ℝ) + β * n / Q) / q := by
        rw [hα]; push_cast; field_simp
      rw [e, hm]; push_cast; simp only [τ']; field_simp; ring_nf
      rw [show (σ : ℝ) ^ 2 = 1 by rw [sq, hσr]]; ring
    rw [harg]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hσ with hs | hs <;>
    · subst hs; push_cast
      simp only [one_mul, neg_one_mul, Real.sin_neg, neg_sq]
      rw [sin_sq_add_int_mul_pi]
  have hinj : Set.InjOn R S' := by
    intro n hn n' hn' hR
    have hn1 := (Finset.mem_filter.1 hn).1
    have hn1' := (Finset.mem_filter.1 hn').1
    have hmod : m n % q = m n' % q := by rw [← hRcast, ← hRcast]; exact congrArg _ hR
    have hdvd : (q : ℤ) ∣ a * (n - n') := by
      have h1 : (q : ℤ) ∣ m n - m n' := Int.ModEq.dvd hmod.symm
      have : m n - m n' = σ * (a * (n - n')) := by simp only [m]; ring
      rw [this] at h1
      have h2 : (q : ℤ) ∣ σ * (σ * (a * (n - n'))) := dvd_mul_of_dvd_right h1 σ
      rwa [← mul_assoc, hσ, one_mul] at h2
    have hd : (q : ℤ) ∣ n - n' := hcop.symm.dvd_of_dvd_mul_left hdvd
    have g1 := hgap n hn1 n' hn1'
    have g2 := hgap n' hn1' n hn1
    obtain ⟨t, ht⟩ := hd
    have : t = 0 := by
      by_contra ht0
      rcases lt_or_gt_of_ne ht0 with h | h
      · have : (q : ℤ) * t ≤ -q := by nlinarith
        omega
      · have : (q : ℤ) ≤ q * t := by nlinarith
        omega
    subst this; omega
  set τR := fun r : ℕ => if hr : ∃ n ∈ S', R n = r then τ' hr.choose else 0
  have hτR : ∀ n ∈ S', τR (R n) = τ' n := by
    intro n hn
    have hex : ∃ n' ∈ S', R n' = R n := ⟨n, hn, rfl⟩
    simp only [τR, dite_eq_left hex]
    have := hex.choose_spec
    rw [hinj this.1 hn this.2]
  refine ⟨τR, fun r => ?_, ?_⟩
  · simp only [τR]
    split_ifs with hr
    · exact hτ' _ (Finset.mem_filter.1 hr.choose_spec.1).1
    · exact ⟨le_rfl, by norm_num⟩
  · set g := fun r : ℕ => min A (C * fq q (r + τR r))
    have hg0 : ∀ r, 0 ≤ g r := fun r => le_min hA (mul_nonneg hC (fq_nonneg _ _))
    rw [← Finset.sum_filter_not_add_sum_filter S (fun n => (q : ℤ) ∣ n)]
    have hzero : ∑ n ∈ S.filter (fun n => (q : ℤ) ∣ n),
        (if (q : ℤ) ∣ n then 0 else min A (C / Real.sin (π * α * n) ^ 2)) = 0 :=
      Finset.sum_eq_zero fun n hn => by rw [ite_eq_left (Finset.mem_filter.1 hn).2]
    rw [hzero, add_zero]
    have hS'eq : ∑ n ∈ S', (if (q : ℤ) ∣ n then 0 else min A (C / Real.sin (π * α * n) ^ 2)) =
        ∑ n ∈ S', g (R n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [ite_eq_right (Finset.mem_filter.1 hn).2, hterm n]
      simp only [g, hτR n hn]
    rw [hS'eq, ← Finset.sum_image (fun n hn n' hn' h => hinj hn hn' h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => hg0 r
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hr
    simp only [Finset.mem_Icc]
    exact ⟨hRpos n hn, by have := hRlt n; omega⟩

/-- **[B, Lemma 4.1.2]** -/
theorem lemma_4_1_2 {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) {y₁ y₂ : ℝ}
    (hy : 0 ≤ y₁) (_hy₁₂ : y₁ < y₂) (hlen : y₂ - y₁ ≤ q) (hy₂ : y₂ ≤ Q / 2) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋,
        (if (q : ℤ) ∣ n then 0 else min A (C / Real.sin (π * α * n) ^ 2)) ≤
      min (20 / (3 * π ^ 2) * C * q ^ 2) (2 * A + 4 * q / π * √(A * C)) := by
  obtain ⟨τ, hτ, hle⟩ := residue_form₂ h hy hlen hy₂ hA hC
  exact hle.trans (core_4_1_2 h.1 hA hC τ hτ)


/-! ## Lemma 4.1.3 -/

open Classical in
/-- **Reduction for Lemmas 4.1.2–4.1.3**, for any nonnegative summand `Φ(sin²(παn))`.  For `0 ≤ y₁ < n ≤ y₂ ≤ Q/2`, `q ∤ n`, `y₂ - y₁ ≤ q`, the terms
are bounded by `Φ(sin²(π(R + τ_R)/q))` over distinct residues `R ∈ [1, q-1]`, `τ_R ∈ [0, 1/2]`. -/
theorem residue_form_gen {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) {y₁ y₂ : ℝ}
    (hy : 0 ≤ y₁) (hlen : y₂ - y₁ ≤ q) (hy₂ : y₂ ≤ Q / 2) (Φ : ℝ → ℝ) (hΦ : ∀ x, 0 ≤ Φ x) :
    ∃ τ : ℕ → ℝ, (∀ R, τ R ∈ Icc (0 : ℝ) (1 / 2)) ∧
      ∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋,
          (if (q : ℤ) ∣ n then 0 else Φ (Real.sin (π * α * n) ^ 2)) ≤
        ∑ R ∈ Finset.Icc 1 (q - 1), Φ (Real.sin (π * (R + τ R) / q) ^ 2) := by
  obtain ⟨hq1, hcop, β, hβ, hα, hqQ⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hQ0 : 0 < Q := by linarith
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq1
  set S := Finset.Ioc ⌊y₁⌋ ⌊y₂⌋
  set S' := S.filter fun n => ¬ (q : ℤ) ∣ n
  have hS : ∀ n ∈ S, 1 ≤ n ∧ (n : ℝ) ≤ y₂ := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have h0 : 0 ≤ ⌊y₁⌋ := Int.floor_nonneg.2 hy
    exact ⟨by omega, (Int.cast_le.2 hn.2).trans (Int.floor_le y₂)⟩
  have hgap : ∀ n ∈ S, ∀ n' ∈ S, n - n' < q := by
    intro n hn n' hn'
    rw [Finset.mem_Ioc] at hn hn'
    have h1 : ((n - n' : ℤ) : ℝ) < q := by
      have a1 : (n : ℝ) ≤ y₂ := (Int.cast_le.2 hn.2).trans (Int.floor_le y₂)
      have a2 : y₁ < n' := by
        have := Int.lt_floor_add_one y₁
        have : ((⌊y₁⌋ : ℤ) : ℝ) + 1 ≤ n' := by exact_mod_cast hn'.1
        linarith
      push_cast; linarith
    exact_mod_cast h1
  -- Orientation.
  obtain ⟨σ, hσ, hσβ⟩ : ∃ σ : ℤ, σ * σ = 1 ∧ 0 ≤ (σ : ℝ) * β := by
    rcases le_or_gt 0 β with h0 | h0
    · exact ⟨1, by norm_num, by simpa using h0⟩
    · exact ⟨-1, by norm_num, by push_cast; linarith⟩
  have hσr : (σ : ℝ) * σ = 1 := by exact_mod_cast hσ
  have hσabs : |(σ : ℝ)| = 1 := by
    have : |(σ : ℝ)| * |(σ : ℝ)| = 1 := by rw [← abs_mul, hσr, abs_one]
    nlinarith [abs_nonneg (σ : ℝ)]
  set τ' := fun n : ℤ => (σ : ℝ) * β * n / Q
  have hτ' : ∀ n ∈ S, τ' n ∈ Icc (0 : ℝ) (1 / 2) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hS n hn
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : (0 : ℤ) ≤ n)
    have hσβ1 : (σ : ℝ) * β ≤ 1 := by
      calc (σ : ℝ) * β ≤ |(σ : ℝ) * β| := le_abs_self _
        _ = |β| := by rw [abs_mul, hσabs, one_mul]
        _ ≤ 1 := hβ
    simp only [τ', mem_Icc]
    constructor
    · positivity
    · rw [div_le_iff₀ hQ0]; nlinarith
  set m := fun n : ℤ => σ * (a * n)
  set R := fun n : ℤ => (m n % (q : ℤ)).toNat
  have hRcast : ∀ n, ((R n : ℕ) : ℤ) = m n % q := fun n =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hqz.ne')
  have hRlt : ∀ n, R n < q := by
    intro n; simp only [R]
    have h1 := Int.emod_nonneg (m n) hqz.ne'
    have h2 := Int.emod_lt_of_pos (m n) hqz
    omega
  have hRpos : ∀ n ∈ S', 1 ≤ R n := by
    intro n hn
    rw [Finset.mem_filter] at hn
    by_contra h0
    have h00 : m n % q = 0 := by have := hRcast n; omega
    apply hn.2
    have h1 : (q : ℤ) ∣ σ * (a * n) := Int.dvd_of_emod_eq_zero h00
    have h2 : (q : ℤ) ∣ σ * (σ * (a * n)) := dvd_mul_of_dvd_right h1 σ
    rw [← mul_assoc, hσ, one_mul] at h2
    exact hcop.symm.dvd_of_dvd_mul_left h2
  have hterm : ∀ n : ℤ, Φ (Real.sin (π * α * n) ^ 2) = Φ (Real.sin (π * (R n + τ' n) / q) ^ 2) := by
    intro n
    congr 1
    have hm : a * n = σ * (q * (m n / q) + (R n : ℤ)) := by
      rw [hRcast, Int.mul_ediv_add_emod]; simp only [m]; rw [← mul_assoc, hσ, one_mul]
    have harg : π * α * n = (σ : ℝ) * (π * ((R n : ℝ) + τ' n) / q + ((m n / q : ℤ) : ℝ) * π) := by
      have e : π * α * n = π * (((a * n : ℤ) : ℝ) + β * n / Q) / q := by
        rw [hα]; push_cast; field_simp
      rw [e, hm]; push_cast; simp only [τ']; field_simp; ring_nf
      rw [show (σ : ℝ) ^ 2 = 1 by rw [sq, hσr]]; ring
    rw [harg]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hσ with hs | hs <;>
    · subst hs; push_cast
      simp only [one_mul, neg_one_mul, Real.sin_neg, neg_sq]
      rw [sin_sq_add_int_mul_pi]
  have hinj : Set.InjOn R S' := by
    intro n hn n' hn' hR
    have hn1 := (Finset.mem_filter.1 hn).1
    have hn1' := (Finset.mem_filter.1 hn').1
    have hmod : m n % q = m n' % q := by rw [← hRcast, ← hRcast]; exact congrArg _ hR
    have hdvd : (q : ℤ) ∣ a * (n - n') := by
      have h1 : (q : ℤ) ∣ m n - m n' := Int.ModEq.dvd hmod.symm
      have : m n - m n' = σ * (a * (n - n')) := by simp only [m]; ring
      rw [this] at h1
      have h2 : (q : ℤ) ∣ σ * (σ * (a * (n - n'))) := dvd_mul_of_dvd_right h1 σ
      rwa [← mul_assoc, hσ, one_mul] at h2
    have hd : (q : ℤ) ∣ n - n' := hcop.symm.dvd_of_dvd_mul_left hdvd
    have g1 := hgap n hn1 n' hn1'
    have g2 := hgap n' hn1' n hn1
    obtain ⟨t, ht⟩ := hd
    have : t = 0 := by
      by_contra ht0
      rcases lt_or_gt_of_ne ht0 with h | h
      · have : (q : ℤ) * t ≤ -q := by nlinarith
        omega
      · have : (q : ℤ) ≤ q * t := by nlinarith
        omega
    subst this; omega
  set τR := fun r : ℕ => if hr : ∃ n ∈ S', R n = r then τ' hr.choose else 0
  have hτR : ∀ n ∈ S', τR (R n) = τ' n := by
    intro n hn
    have hex : ∃ n' ∈ S', R n' = R n := ⟨n, hn, rfl⟩
    simp only [τR, dite_eq_left hex]
    have := hex.choose_spec
    rw [hinj this.1 hn this.2]
  refine ⟨τR, fun r => ?_, ?_⟩
  · simp only [τR]
    split_ifs with hr
    · exact hτ' _ (Finset.mem_filter.1 hr.choose_spec.1).1
    · exact ⟨le_rfl, by norm_num⟩
  · set g := fun r : ℕ => Φ (Real.sin (π * (r + τR r) / q) ^ 2)
    have hg0 : ∀ r, 0 ≤ g r := fun r => hΦ _
    rw [← Finset.sum_filter_not_add_sum_filter S (fun n => (q : ℤ) ∣ n)]
    have hzero : ∑ n ∈ S.filter (fun n => (q : ℤ) ∣ n),
        (if (q : ℤ) ∣ n then 0 else Φ (Real.sin (π * α * n) ^ 2)) = 0 :=
      Finset.sum_eq_zero fun n hn => by rw [ite_eq_left (Finset.mem_filter.1 hn).2]
    rw [hzero, add_zero]
    have hS'eq : ∑ n ∈ S', (if (q : ℤ) ∣ n then 0 else Φ (Real.sin (π * α * n) ^ 2)) =
        ∑ n ∈ S', g (R n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [ite_eq_right (Finset.mem_filter.1 hn).2, hterm n]
      simp only [g, hτR n hn]
    rw [hS'eq, ← Finset.sum_image (fun n hn n' hn' h => hinj hn hn' h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => hg0 r
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hr
    simp only [Finset.mem_Icc]
    exact ⟨hRpos n hn, by have := hRlt n; omega⟩

/-- An antiderivative of `1/sin`: `F(v) = log sin v - log(1 + cos v)` (`= log tan(v/2)`). -/

noncomputable def logTanHalf (v : ℝ) : ℝ := Real.log (Real.sin v) - Real.log (1 + Real.cos v)

theorem integral_inv_sin {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < π) :
    ∫ x in a..b, 1 / Real.sin x = logTanHalf b - logTanHalf a := by
  have hsin : ∀ x ∈ uIcc a b, 0 < Real.sin x := fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  have hcos : ∀ x ∈ uIcc a b, 0 < 1 + Real.cos x := fun x hx => by
    have := hsin x hx
    have h1 := Real.neg_one_le_cos x
    rcases h1.lt_or_eq with h | h
    · linarith
    · exfalso
      have h0 : Real.sin x ^ 2 = 0 := by nlinarith [Real.sin_sq_add_cos_sq x]
      have : Real.sin x = 0 := pow_eq_zero_iff two_ne_zero |>.1 h0
      linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := logTanHalf)]
  · intro x hx
    have h1 := (Real.hasDerivAt_sin x).log (hsin x hx).ne'
    have h2 := ((hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_cos x)).log (hcos x hx).ne'
    convert h1.sub h2 using 1
    · rfl
    have hs := (hsin x hx).ne'
    have hc := (hcos x hx).ne'
    simp only [Pi.add_apply] at hc ⊢
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  · exact ContinuousOn.intervalIntegrable (continuousOn_const.div
      Real.continuous_sin.continuousOn fun x hx => (hsin x hx).ne')

theorem logTanHalf_pi_div_two : logTanHalf (π / 2) = 0 := by
  simp [logTanHalf]

/-- `cot(a/2) = (1 + cos a)/sin a ≤ 2/a` for `0 < a ≤ 1`. -/
theorem neg_logTanHalf_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    -logTanHalf a ≤ Real.log (2 / a) := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_gt_three])
  have hc : 0 < 1 + Real.cos a := by
    have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
      (x := a); linarith
  have key : (1 + Real.cos a) / Real.sin a ≤ 2 / a := by
    rw [div_le_div_iff₀ hs ha]
    have h1 := sin_ge_deg3 ha.le
    have h3 := cos_le_deg4 ha.le
    have h4 := mul_le_mul_of_nonneg_left h3 ha.le
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    nlinarith [pow_pos ha 3, pow_pos ha 5]
  unfold logTanHalf
  rw [neg_sub, ← Real.log_div hc.ne' hs.ne']
  exact Real.log_le_log (by positivity) key

/-- `a / sin a ≤ 2 - log 2` (indeed `≤ 1.12`) for `0 < a ≤ π/4`. -/
theorem div_sin_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ π / 4) : a / Real.sin a ≤ 112 / 100 := by
  have ha1' : a ≤ 786 / 1000 := ha1.trans (by linarith [Real.pi_lt_d4])
  have hs := sin_ge_deg3 ha.le
  have ha2 : a ^ 2 ≤ 618 / 1000 := by nlinarith
  have hs1 : a * (1 - a ^ 2 / 6) ≤ Real.sin a := by nlinarith
  have hk : 897 / 1000 ≤ 1 - a ^ 2 / 6 := by linarith
  have hs0 : 0 < Real.sin a := by nlinarith
  rw [div_le_iff₀ hs0]
  nlinarith

theorem log_two_bounds : 0.693 < Real.log 2 ∧ Real.log 2 < 0.694 :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩


/-- `sin` is larger in the middle: `0 < u ≤ v ≤ q - u ⇒ sin(πu/q) ≤ sin(πv/q)`. -/
theorem sin_le_of_between {q u v : ℝ} (hq : 0 < q) (hu : 0 < u) (huv : u ≤ v) (hvq : v ≤ q - u) :
    Real.sin (π * u / q) ≤ Real.sin (π * v / q) := by
  have hpi := Real.pi_pos
  have key : ∀ w, u ≤ w → w ≤ q / 2 → Real.sin (π * u / q) ≤ Real.sin (π * w / q) := by
    intro w huw hw
    refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_
    · have : 0 < π * u / q := by positivity
      linarith
    · rw [div_le_iff₀ hq]; nlinarith
    · rw [div_le_div_iff_of_pos_right hq]; exact mul_le_mul_of_nonneg_left huw hpi.le
  rcases le_or_gt v (q / 2) with hv | hv
  · exact key v huv hv
  · rw [show π * v / q = π - π * (q - v) / q by field_simp; ring, Real.sin_pi_sub]
    exact key (q - v) (by linarith) (by linarith)

/-- `h(u) = min(B / sin(πu/q), C / sin²(πu/q))`. -/
noncomputable def hBC (B C q u : ℝ) : ℝ :=
  min (B / Real.sin (π * u / q)) (C / Real.sin (π * u / q) ^ 2)

theorem hBC_nonneg {B C q u : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hq : 0 < q) (hu : 0 < u)
    (huq : u < q) : 0 ≤ hBC B C q u := by
  have := sin_pos_of_mem hq hu huq
  exact le_min (by positivity) (by positivity)

/-- `min(B/|s|, C/s²) ≤ h(u)` whenever `|s| ≥ sin(πu/q) > 0`. -/
theorem minBC_le_hBC {B C q u s : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hpos : 0 < Real.sin (π * u / q))
    (hs : Real.sin (π * u / q) ≤ |s|) :
    min (B / √(s ^ 2)) (C / s ^ 2) ≤ hBC B C q u := by
  rw [Real.sqrt_sq_eq_abs]
  have hs2 : Real.sin (π * u / q) ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs s]; exact pow_le_pow_left₀ hpos.le hs 2
  exact min_le_min (div_le_div_of_nonneg_left hB hpos hs)
    (div_le_div_of_nonneg_left hC (by positivity) hs2)

theorem hBC_anti {B C q u v : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hq : 0 < q) (hu : 0 < u)
    (huv : u ≤ v) (hv : v ≤ q / 2) : hBC B C q v ≤ hBC B C q u := by
  have hpos := sin_pos_of_mem hq hu (by linarith)
  have hle := sin_le_of_between hq hu huv (by linarith)
  have := minBC_le_hBC (s := Real.sin (π * v / q)) hB hC hpos (hle.trans (le_abs_self _))
  rwa [Real.sqrt_sq_eq_abs, abs_of_pos (hpos.trans_le hle)] at this

theorem continuousOn_hBC {B C q a b : ℝ} (hq : 0 < q) (ha : 0 < a) (hb : b < q) :
    ContinuousOn (hBC B C q) (Icc a b) := by
  have hs : ∀ u ∈ Icc a b, Real.sin (π * u / q) ≠ 0 := fun u hu =>
    (sin_pos_of_mem hq (by linarith [hu.1]) (by linarith [hu.2])).ne'
  have hc : ContinuousOn (fun u => Real.sin (π * u / q)) (Icc a b) :=
    Real.continuous_sin.comp_continuousOn ((continuousOn_const.mul continuousOn_id).div_const q)
  exact (continuousOn_const.div hc hs).inf (continuousOn_const.div (hc.pow 2)
    fun u hu => pow_ne_zero 2 (hs u hu))

/-- Parity split of `1, …, q-1` into `2r` (`r ≤ (q-1)/2`) and `2k - 1` (`k ≤ q/2`). -/
theorem sum_Icc_parity (g : ℕ → ℝ) (q : ℕ) :
    ∑ j ∈ Finset.Icc 1 (q - 1), g j =
      ∑ r ∈ Finset.Icc 1 ((q - 1) / 2), g (2 * r) + ∑ k ∈ Finset.Icc 1 (q / 2), g (2 * k - 1) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (q - 1)) (fun j => Even j)]
  congr 1
  · refine Finset.sum_bij (fun j _ => j / 2) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩ := hj; simp only [Finset.mem_Icc]; omega
    · intro a ha b hb hab; simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
      obtain ⟨_, ⟨m, rfl⟩⟩ := ha; obtain ⟨_, ⟨m', rfl⟩⟩ := hb; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr
      exact ⟨2 * r, by simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨by omega, ⟨r, by ring⟩⟩,
        by simp⟩
    · intro j hj; simp only [Finset.mem_filter] at hj
      obtain ⟨_, ⟨m, rfl⟩⟩ := hj; show g (m + m) = g (2 * ((m + m) / 2)); congr 1; omega
  · refine Finset.sum_bij (fun j _ => (j + 1) / 2) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_Icc, Nat.not_even_iff_odd] at hj
      obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩ := hj; simp only [Finset.mem_Icc]; omega
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.not_even_iff_odd] at ha hb
      obtain ⟨_, ⟨m, rfl⟩⟩ := ha; obtain ⟨_, ⟨m', rfl⟩⟩ := hb; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk
      exact ⟨2 * k - 1, by
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.not_even_iff_odd]
        exact ⟨by omega, ⟨k - 1, by omega⟩⟩, by omega⟩
    · intro j hj; simp only [Finset.mem_filter, Nat.not_even_iff_odd] at hj
      obtain ⟨_, ⟨m, rfl⟩⟩ := hj
      show g (2 * m + 1) = g (2 * ((2 * m + 1 + 1) / 2) - 1); congr 1; omega


/-- `∑_{j=1}^{q-1} h(j/2) ≤ h(1/2) + 2 ∫_{1/2}^{q/2} h`. -/
theorem sum_hBC_half_le {B C : ℝ} {q : ℕ} (hq : 2 ≤ q) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∑ j ∈ Finset.Icc 1 (q - 1), hBC B C q ((j : ℝ) / 2) ≤
      hBC B C q (1 / 2) + 2 * ∫ u in (1 / 2 : ℝ)..(q / 2), hBC B C q u := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hII : ∀ a b : ℝ, 0 < a → b < q → a ≤ b → IntervalIntegrable (hBC B C q) volume a b :=
    fun a b ha hb hab => (continuousOn_hBC hq0 ha hb).intervalIntegrable_of_Icc hab
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (by simp; omega : 1 ∈ Finset.Icc 1 (q - 1)),
    show Finset.Icc 1 (q - 1) \ {1} = Finset.Icc 2 (q - 1) by ext x; simp; omega]
  simp only [Nat.cast_one]
  refine add_le_add le_rfl ?_
  -- Each `h(j/2)` is at most twice the integral over `[(j-1)/2, j/2]`.
  have hterm : ∀ j ∈ Finset.Icc 2 (q - 1),
      hBC B C q ((j : ℝ) / 2) ≤ 2 * ∫ u in (((j : ℝ) - 1) / 2)..((j : ℝ) / 2), hBC B C q u := by
    intro j hj
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
    have hjq : (j : ℝ) ≤ q - 1 := by
      have := (Finset.mem_Icc.1 hj).2
      have : (j : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
    have h := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hII (((j : ℝ) - 1) / 2) ((j : ℝ) / 2) (by linarith) (by linarith) (by linarith))
      fun u hu => hBC_anti hB hC hq0 (by linarith [hu.1]) hu.2 (by linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hsum : ∑ j ∈ Finset.Icc 2 (q - 1), ∫ u in (((j : ℝ) - 1) / 2)..((j : ℝ) / 2), hBC B C q u =
      ∫ u in (1 / 2 : ℝ)..((q : ℝ) - 1) / 2, hBC B C q u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := hBC B C q)
      (a := fun i : ℕ => ((i : ℝ) + 1) / 2) (n := q - 2) fun i hi => by
        have : (i : ℝ) + 3 ≤ q := by exact_mod_cast (by omega : i + 3 ≤ q)
        show IntervalIntegrable (hBC B C q) volume (((i : ℝ) + 1) / 2) ((((i + 1 : ℕ) : ℝ) + 1) / 2)
        push_cast
        exact hII _ _ (by positivity) (by linarith) (by linarith)
    simp only [Nat.cast_zero, zero_add] at h
    rw [show (((q - 2 : ℕ) : ℝ) + 1) / 2 = ((q : ℝ) - 1) / 2 by
      rw [Nat.cast_sub hq]; push_cast; ring] at h
    rw [← h]
    refine Finset.sum_bij (fun j _ => j - 2) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
    · intro i hi; simp only [Finset.mem_range] at hi
      exact ⟨i + 2, by simp only [Finset.mem_Icc]; omega, by simp⟩
    · intro j hj; simp only [Finset.mem_Icc] at hj
      push_cast [Nat.cast_sub hj.1]; ring_nf
  have htail : ∫ u in (1 / 2 : ℝ)..((q : ℝ) - 1) / 2, hBC B C q u ≤
      ∫ u in (1 / 2 : ℝ)..(q / 2), hBC B C q u := by
    have e := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := (1 / 2 : ℝ))
      (b := ((q : ℝ) - 1) / 2) (c := q / 2) (hII _ _ (by norm_num) (by linarith) (by linarith))
      (hII _ _ (by linarith) (by linarith) (by linarith))
    have := intervalIntegral.integral_nonneg (μ := volume) (show ((q : ℝ) - 1) / 2 ≤ q / 2 by linarith)
      fun u hu => hBC_nonneg (u := u) hB hC hq0 (by linarith [hu.1]) (by linarith [hu.2])
    linarith
  calc ∑ j ∈ Finset.Icc 2 (q - 1), hBC B C q ((j : ℝ) / 2)
      ≤ ∑ j ∈ Finset.Icc 2 (q - 1), 2 * ∫ u in (((j : ℝ) - 1) / 2)..((j : ℝ) / 2), hBC B C q u :=
        Finset.sum_le_sum hterm
    _ = 2 * ∫ u in (1 / 2 : ℝ)..((q : ℝ) - 1) / 2, hBC B C q u := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := by linarith

/-- The function `min(B/sin v, C/sin² v)`. -/
noncomputable def mBC (B C v : ℝ) : ℝ := min (B / Real.sin v) (C / Real.sin v ^ 2)

theorem integral_hBC {B C : ℝ} {q : ℝ} (hq : 0 < q) :
    ∫ u in (1 / 2 : ℝ)..(q / 2), hBC B C q u = q / π * ∫ v in (π / (2 * q))..(π / 2), mBC B C v := by
  have hpq : π / q ≠ 0 := (div_pos Real.pi_pos hq).ne'
  have : hBC B C q = fun u => mBC B C ((π / q) * u) := by
    funext u; simp only [hBC, mBC]; ring_nf
  rw [this, intervalIntegral.integral_comp_mul_left (fun v => mBC B C v) hpq, smul_eq_mul, inv_div]
  congr 2 <;> field_simp <;> ring_nf <;> simp

theorem continuousOn_mBC {B C a b : ℝ} (ha : 0 < a) (hb : b < π) :
    ContinuousOn (mBC B C) (Icc a b) := by
  have hs : ∀ v ∈ Icc a b, Real.sin v ≠ 0 := fun v hv =>
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hv.1]) (by linarith [hv.2])).ne'
  exact (continuousOn_const.div Real.continuous_sin.continuousOn hs).inf
    (continuousOn_const.div (Real.continuous_sin.continuousOn.pow 2) fun v hv => pow_ne_zero 2 (hs v hv))

/-- Splitting `∫_a^{π/2} min(B/sin, C/sin²)` at `w`. -/
theorem integral_mBC_le_split {B C a w : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (ha : 0 < a) (haw : a ≤ w)
    (hw : w ≤ π / 2) :
    ∫ v in a..(π / 2), mBC B C v ≤
      B * (logTanHalf w - logTanHalf a) + C * (Real.cos w / Real.sin w) := by
  have hpi := Real.pi_pos
  have hII : ∀ x y, 0 < x → x ≤ y → y ≤ π / 2 → IntervalIntegrable (mBC B C) volume x y :=
    fun x y hx hxy hy => (continuousOn_mBC hx (by linarith)).intervalIntegrable_of_Icc hxy
  have hsin : ∀ v ∈ Icc a (π / 2), 0 < Real.sin v := fun v hv =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hv.1]) (by linarith [hv.2])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := w) (hII _ _ ha haw hw)
    (hII _ _ (by linarith) hw le_rfl)]
  have h1 : ∫ v in a..w, mBC B C v ≤ B * (logTanHalf w - logTanHalf a) := by
    have hg : IntervalIntegrable (fun v => B * (1 / Real.sin v)) volume a w :=
      (continuousOn_const.mul (continuousOn_const.div Real.continuous_sin.continuousOn
        fun v hv => (hsin v ⟨hv.1, hv.2.trans hw⟩).ne')).intervalIntegrable_of_Icc haw
    have := intervalIntegral.integral_mono_on haw (hII _ _ ha haw hw) hg
      fun v _ => (min_le_left (B / Real.sin v) (C / Real.sin v ^ 2)).trans (le_of_eq (by ring))
    rw [intervalIntegral.integral_const_mul, integral_inv_sin ha haw (by linarith)] at this
    exact this
  have h2 : ∫ v in w..(π / 2), mBC B C v ≤ C * (Real.cos w / Real.sin w) := by
    have hw0 : 0 < w := by linarith
    have hg : IntervalIntegrable (fun v => C * (1 / Real.sin v ^ 2)) volume w (π / 2) :=
      (continuousOn_const.mul (continuousOn_const.div (Real.continuous_sin.continuousOn.pow 2)
        fun v hv => pow_ne_zero 2 (hsin v ⟨by linarith [hv.1], hv.2⟩).ne')).intervalIntegrable_of_Icc hw
    have := intervalIntegral.integral_mono_on hw (hII _ _ hw0 hw le_rfl) hg
      fun v _ => (min_le_right (B / Real.sin v) (C / Real.sin v ^ 2)).trans (le_of_eq (by ring))
    rw [intervalIntegral.integral_const_mul, integral_inv_sin_sq hw0 hw (by linarith),
      Real.cos_pi_div_two, zero_div, sub_zero] at this
    exact this
  linarith


/-- `log(1 + y) ≥ y log 2` for `0 ≤ y ≤ 1` (concavity of `log`). -/
theorem log_one_add_ge {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : y * Real.log 2 ≤ Real.log (1 + y) := by
  have h : (1 - y) • Real.log 1 + y • Real.log 2 ≤ Real.log ((1 - y) • (1 : ℝ) + y • (2 : ℝ)) :=
    strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num : (1 : ℝ) ∈ Ioi 0)
      (by norm_num : (2 : ℝ) ∈ Ioi 0) (by linarith) hy0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at h
  rw [show (1 - y) + y * 2 = 1 + y by ring] at h
  exact h

set_option maxHeartbeats 2000000 in
/-- The analytic bound for Lemma 4.1.3: `h(1/2) + (2q/π) J` against both right-hand sides. -/
theorem final_4_1_3 {B C a : ℝ} (hB : 0 < B) (hC : 0 ≤ C) (ha : 0 < a) (ha1 : a ≤ π / 4) :
    mBC B C a + (∫ v in a..(π / 2), mBC B C v) / a ≤
        B / a * max 2 (Real.log (C * rexp 3 / (B * (2 * a)))) ∧
      mBC B C a + (∫ v in a..(π / 2), mBC B C v) / a ≤ B / a * Real.log (rexp 2 / a) := by
  have hpi := Real.pi_pos
  have ha2 : a ≤ π / 2 := by linarith
  have ha1' : a ≤ 1 := ha1.trans (by linarith [Real.pi_lt_d2])
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hdiv := div_sin_le ha ha1
  have hF := neg_logTanHalf_le ha ha1'
  have hl2 := log_two_bounds
  have hlog2a : Real.log (2 / a) = Real.log 2 - Real.log a := Real.log_div (by norm_num) ha.ne'
  -- `J ≤ -B F(a)` always.
  have hJ1 : ∫ v in a..(π / 2), mBC B C v ≤ B * Real.log (2 / a) := by
    have := integral_mBC_le_split hB.le hC ha ha2 le_rfl
    rw [logTanHalf_pi_div_two, Real.cos_pi_div_two, zero_div, mul_zero, add_zero, zero_sub] at this
    nlinarith
  have hmA : mBC B C a ≤ B / Real.sin a := min_le_left _ _
  have hBsa : B / Real.sin a = B / a * (a / Real.sin a) := by field_simp
  -- The `C ≥ B`-type bound.
  have hbig : mBC B C a + (∫ v in a..(π / 2), mBC B C v) / a ≤
      B / a * (a / Real.sin a + Real.log (2 / a)) := by
    rw [mul_add, ← hBsa]
    have := div_le_div_of_nonneg_right hJ1 ha.le
    rw [show B * Real.log (2 / a) / a = B / a * Real.log (2 / a) by ring] at this
    linarith
  have hBa : 0 < B / a := by positivity
  have hlogea : Real.log (rexp 2 / a) = 2 - Real.log a := by
    rw [Real.log_div (by positivity) ha.ne', Real.log_exp]
  refine ⟨?_, ?_⟩
  · set x := C / B
    have hx0 : 0 ≤ x := div_nonneg hC hB.le
    have hCx : C = x * B := by simp only [x]; field_simp
    rcases le_or_gt 1 x with hx1 | hx1
    · -- `C ≥ B`.
      have hlog : Real.log (C * rexp 3 / (B * (2 * a))) = Real.log x + 3 - Real.log 2 - Real.log a := by
        rw [hCx, show x * B * rexp 3 / (B * (2 * a)) = x * rexp 3 / 2 / a by field_simp; try ring,
          Real.log_div (by positivity) ha.ne', Real.log_div (by positivity) (by norm_num),
          Real.log_mul (by positivity) (by positivity), Real.log_exp]
        try ring
      have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
      refine hbig.trans (mul_le_mul_of_nonneg_left ?_ hBa.le)
      refine le_trans ?_ (le_max_right _ _)
      rw [hlog, hlog2a]; linarith
    rcases le_or_gt (Real.sin a) x with hxa | hxa
    · -- `B sin a ≤ C < B`: split at `w = arcsin x`.
      set w := Real.arcsin x
      have hx1' : x ≤ 1 := hx1.le
      have hxpos : 0 < x := hsa.trans_le hxa
      have hsw : Real.sin w = x := Real.sin_arcsin (by linarith) hx1'
      have hcw : Real.cos w = √(1 - x ^ 2) := Real.cos_arcsin x
      have haw : a ≤ w := by
        rw [← Real.arcsin_sin (x := a) (by linarith) ha2]; exact Real.monotone_arcsin hxa
      have hw2 : w ≤ π / 2 := Real.arcsin_le_pi_div_two x
      set y := √(1 - x ^ 2)
      have hy0 : 0 ≤ y := Real.sqrt_nonneg _
      have hy1 : y ≤ 1 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by nlinarith)
      have hJ := integral_mBC_le_split hB.le hC ha haw hw2
      have hFw : logTanHalf w = Real.log x - Real.log (1 + y) := by
        simp only [logTanHalf, hsw, hcw]
      have hCcot : C * (Real.cos w / Real.sin w) = B * y := by
        rw [hsw, hcw, hCx]; field_simp
      rw [hFw, hCcot] at hJ
      have hlog : Real.log (C * rexp 3 / (B * (2 * a))) = Real.log x + 3 - Real.log 2 - Real.log a := by
        rw [hCx, show x * B * rexp 3 / (B * (2 * a)) = x * rexp 3 / 2 / a by field_simp; try ring,
          Real.log_div (by positivity) ha.ne', Real.log_div (by positivity) (by norm_num),
          Real.log_mul (by positivity) (by positivity), Real.log_exp]
        try ring
      have hconc := log_one_add_ge hy0 hy1
      have hJ' : (∫ v in a..(π / 2), mBC B C v) / a ≤
          B / a * (Real.log x - Real.log (1 + y) + Real.log (2 / a) + y) := by
        rw [div_le_iff₀ ha]
        have : B / a * (Real.log x - Real.log (1 + y) + Real.log (2 / a) + y) * a =
            B * (Real.log x - Real.log (1 + y) + Real.log (2 / a) + y) := by field_simp
        rw [this]
        have h2 := mul_le_mul_of_nonneg_left hF hB.le
        linarith only [hJ, h2]
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_right _ _) hBa.le)
      rw [hlog]
      have hm' : mBC B C a ≤ B / a * (a / Real.sin a) := hmA.trans (le_of_eq hBsa)
      have hy2 : y * (1 - Real.log 2) ≤ 1 - Real.log 2 := by
        have : 0 ≤ 1 - Real.log 2 := by linarith [hl2.2]
        nlinarith
      have key : a / Real.sin a + (Real.log x - Real.log (1 + y) + Real.log (2 / a) + y) ≤
          Real.log x + 3 - Real.log 2 - Real.log a := by
        rw [hlog2a]; linarith only [hl2.1, hl2.2, hdiv, hconc, hy2]
      have h3 := mul_le_mul_of_nonneg_left key hBa.le
      rw [mul_add] at h3
      linarith only [h3, hm', hJ']
    · -- `C < B sin a`: only the `C/sin²` branch matters.
      have hJ := integral_mBC_le_split hB.le hC ha le_rfl ha2
      rw [sub_self, mul_zero, zero_add] at hJ
      have hmC : mBC B C a ≤ C / Real.sin a ^ 2 := min_le_right _ _
      -- `a/sin a + cos a ≤ 2`.
      have hk : a / Real.sin a + Real.cos a ≤ 2 := by
        have h1 := sin_ge_deg3 ha.le
        have h3 := cos_le_deg4 ha.le
        rw [div_add' _ _ _ hsa.ne', div_le_iff₀ hsa]
        have hsc : a ≤ Real.sin a * (2 - Real.cos a) := by
          have e1 : (1 : ℝ) + a ^ 2 / 2 - a ^ 4 / 24 ≤ 2 - Real.cos a := by linarith
          have ha2' : a ^ 2 ≤ 1 := by nlinarith
          have e0 : 0 ≤ a - a ^ 3 / 6 := by nlinarith
          have e3 : 0 ≤ 1 + a ^ 2 / 2 - a ^ 4 / 24 := by nlinarith [sq_nonneg (a ^ 2)]
          have hmul : (a - a ^ 3 / 6) * (1 + a ^ 2 / 2 - a ^ 4 / 24) ≤ Real.sin a * (2 - Real.cos a) :=
            mul_le_mul h1 e1 e3 hsa.le
          have hexp : (a - a ^ 3 / 6) * (1 + a ^ 2 / 2 - a ^ 4 / 24) - a =
              a ^ 3 * (1 / 3 - a ^ 2 / 8 + a ^ 4 / 144) := by ring
          have hpos : 0 ≤ a ^ 3 * (1 / 3 - a ^ 2 / 8 + a ^ 4 / 144) :=
            mul_nonneg (pow_pos ha 3).le (by nlinarith [sq_nonneg (a ^ 2)])
          linarith
        linarith
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_left _ _) hBa.le)
      have hC' : C ≤ B * Real.sin a := by
        simp only [x] at hxa; have := (div_lt_iff₀ hB).1 hxa; linarith
      calc mBC B C a + (∫ v in a..(π / 2), mBC B C v) / a
          ≤ C / Real.sin a ^ 2 + C * (Real.cos a / Real.sin a) / a := by
            gcongr
        _ = C / a * (a / Real.sin a ^ 2 + Real.cos a / Real.sin a) := by field_simp
        _ ≤ B * Real.sin a / a * (a / Real.sin a ^ 2 + Real.cos a / Real.sin a) := by
            gcongr
        _ = B / a * (a / Real.sin a + Real.cos a) := by field_simp
        _ ≤ B / a * 2 := mul_le_mul_of_nonneg_left hk hBa.le
  · refine hbig.trans (mul_le_mul_of_nonneg_left ?_ hBa.le)
    rw [hlogea, hlog2a]; linarith


open Classical in
/-- **[B, Lemma 4.1.3]** -/
theorem lemma_4_1_3 {α Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx α a q Q) {y₁ y₂ : ℝ}
    (hy : 0 ≤ y₁) (_hy₁₂ : y₁ < y₂) (hlen : y₂ - y₁ ≤ q) (hy₂ : y₂ ≤ Q / 2) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋, (if (q : ℤ) ∣ n then 0 else
        min (B / |Real.sin (π * α * n)|) (C / Real.sin (π * α * n) ^ 2))) ≤
      2 * B * q / π * max 2 (Real.log (C * rexp 3 * q / (B * π))) ∧
    (∑ n ∈ Finset.Ioc ⌊y₁⌋ ⌊y₂⌋, (if (q : ℤ) ∣ n then 0 else
        min (B / |Real.sin (π * α * n)|) (C / Real.sin (π * α * n) ^ 2))) ≤
      2 * B * q / π * Real.log (2 * rexp 2 * q / π) := by
  have habs : ∀ s : ℝ, |s ^ 2| = s ^ 2 := fun s => abs_of_nonneg (sq_nonneg s)
  set Φ := fun x : ℝ => min (B / √x) (C / |x|)
  have hΦ : ∀ x, 0 ≤ Φ x := fun x =>
    le_min (div_nonneg hB (Real.sqrt_nonneg _)) (div_nonneg hC (abs_nonneg _))
  have hsum_eq : ∀ n : ℤ, min (B / |Real.sin (π * α * n)|) (C / Real.sin (π * α * n) ^ 2) =
      Φ (Real.sin (π * α * n) ^ 2) := fun n => by
    simp only [Φ, Real.sqrt_sq_eq_abs, habs]
  simp_rw [hsum_eq]
  obtain ⟨τ, hτ, hle⟩ := residue_form_gen h hy hlen hy₂ Φ hΦ
  have hq1 := h.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  -- Nonnegativity of the right-hand sides.
  have hR1 : 0 ≤ 2 * B * q / π * max 2 (Real.log (C * rexp 3 * q / (B * π))) :=
    mul_nonneg (by positivity) (le_trans (by norm_num) (le_max_left _ _))
  have hR2 : 0 ≤ 2 * B * q / π * Real.log (2 * rexp 2 * q / π) := by
    refine mul_nonneg (by positivity) (Real.log_nonneg ?_)
    rw [le_div_iff₀ Real.pi_pos]
    have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have he : 3 ≤ rexp 2 := by linarith [Real.add_one_le_exp 2]
    have : 3 ≤ rexp 2 * q := by nlinarith
    linarith [Real.pi_lt_d2]
  -- Edge cases.
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · have : q = 1 := by omega
    subst this
    simp only [Nat.sub_self, Finset.Icc_eq_empty (by norm_num : ¬ (1 ≤ 0)), Finset.sum_empty] at hle
    exact ⟨hle.trans hR1, hle.trans hR2⟩
  rcases hB.eq_or_lt with hB0 | hBpos
  · have hzero : ∑ R ∈ Finset.Icc 1 (q - 1), Φ (Real.sin (π * (R + τ R) / q) ^ 2) ≤ 0 :=
      Finset.sum_nonpos fun R _ => by
        simp only [Φ, ← hB0, zero_div]; exact min_le_left _ _
    exact ⟨(hle.trans hzero).trans hR1, (hle.trans hzero).trans hR2⟩
  -- Main case.
  set A := π / (2 * q)
  have hA0 : 0 < A := by positivity
  have hA1 : A ≤ π / 4 := by
    have hq2r : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
  set L := (q - 1) / 2
  set K := q / 2
  have hLq : 2 * (L : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : 2 * L + 1 ≤ q)
  have hKq : 2 * (K : ℝ) ≤ q := by exact_mod_cast (by omega : 2 * K ≤ q)
  set F := fun R : ℕ => Φ (Real.sin (π * (R + τ R) / q) ^ 2)
  have hlow : ∀ r ∈ Finset.Icc 1 L, F r ≤ hBC B C q r := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.1 hr).1
    have hrL : (r : ℝ) ≤ L := by exact_mod_cast (Finset.mem_Icc.1 hr).2
    have hpos := sin_pos_of_mem hq0 (by linarith : (0 : ℝ) < r) (by linarith)
    have hbet := sin_le_of_between hq0 (by linarith : (0 : ℝ) < r)
      (by linarith [(hτ r).1] : (r : ℝ) ≤ r + τ r) (by linarith [(hτ r).2])
    show Φ (Real.sin (π * (r + τ r) / q) ^ 2) ≤ _
    simp only [Φ, habs]
    exact minBC_le_hBC hB hC hpos (hbet.trans (le_abs_self _))
  have hhigh : ∀ k ∈ Finset.Icc 1 K, F (q - k) ≤ hBC B C q (k - 1 / 2) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.1 hk).2
    have hkq : k ≤ q := by have := (Finset.mem_Icc.1 hk).2; omega
    have hsym : Real.sin (π * (((q - k : ℕ) : ℝ) + τ (q - k)) / q) =
        Real.sin (π * (k - τ (q - k)) / q) := by
      rw [Nat.cast_sub hkq, show π * ((q : ℝ) - k + τ (q - k)) / q =
        π - π * (k - τ (q - k)) / q by field_simp; ring, Real.sin_pi_sub]
    have hpos := sin_pos_of_mem hq0 (by linarith : (0 : ℝ) < k - 1 / 2) (by linarith)
    have hbet := sin_le_of_between hq0 (by linarith : (0 : ℝ) < k - 1 / 2)
      (by linarith [(hτ (q - k)).2] : (k : ℝ) - 1 / 2 ≤ k - τ (q - k))
      (by linarith [(hτ (q - k)).1])
    show Φ (Real.sin (π * (((q - k : ℕ) : ℝ) + τ (q - k)) / q) ^ 2) ≤ _
    rw [hsym]
    simp only [Φ, habs]
    exact minBC_le_hBC hB hC hpos (hbet.trans (le_abs_self _))
  have hmerge : ∑ R ∈ Finset.Icc 1 (q - 1), F R ≤ ∑ j ∈ Finset.Icc 1 (q - 1), hBC B C q ((j : ℝ) / 2) := by
    rw [sum_Icc_low_high F q hq1, sum_Icc_parity (fun j : ℕ => hBC B C q ((j : ℝ) / 2)) q]
    refine add_le_add ((Finset.sum_le_sum hlow).trans (le_of_eq ?_))
      ((Finset.sum_le_sum hhigh).trans (le_of_eq ?_))
    · refine Finset.sum_congr rfl fun r _ => ?_; push_cast; ring_nf
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 := (Finset.mem_Icc.1 hk).1
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; ring_nf
  have hhalf := sum_hBC_half_le hq2 hB hC
  rw [integral_hBC hq0] at hhalf
  have hval : hBC B C q (1 / 2) = mBC B C A := by simp only [hBC, mBC, A]; ring_nf
  have hT : ∑ R ∈ Finset.Icc 1 (q - 1), F R ≤ mBC B C A + (∫ v in A..(π / 2), mBC B C v) / A := by
    refine hmerge.trans (hhalf.trans (le_of_eq ?_))
    rw [hval]; simp only [A]; field_simp
  obtain ⟨f1, f2⟩ := final_4_1_3 hBpos hC hA0 hA1
  have e1 : B / A = 2 * B * q / π := by simp only [A]; field_simp
  have e2 : C * rexp 3 / (B * (2 * A)) = C * rexp 3 * q / (B * π) := by simp only [A]; field_simp
  have e3 : rexp 2 / A = 2 * rexp 2 * q / π := by simp only [A]; field_simp
  rw [e1, e2] at f1
  rw [e1, e3] at f2
  exact ⟨hle.trans (hT.trans f1), hle.trans (hT.trans f2)⟩

end TernaryGoldbach.MinorArcs
