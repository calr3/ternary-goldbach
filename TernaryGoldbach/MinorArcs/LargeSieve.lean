import TernaryGoldbach.CircleMethod

/-!
# The large sieve (Gallagher's form)

For points `α_r` whose `δ`-neighbourhoods `(α_r - δ/2, α_r + δ/2]` are disjoint and lie in a
window of length 1 (i.e. the points are `δ`-spaced modulo 1),

`∑_r |S(α_r)|² ≤ (δ⁻¹ + 4πX) ∑_{n ≤ X} |a(n)|²`, where `S(α) = ∑_{n ≤ X} a(n) e(nα)`.

The proof is Gallagher's: apply `|F(c)| ≤ δ⁻¹ ∫_I |F| + ∫_I |F'|` to `F = S²`, sum over the
disjoint intervals, and finish with Parseval and Cauchy–Schwarz (`CircleMethod.lean`).
The corollary `large_sieve_farey` takes the points to be the Farey fractions `a/q`, `q ≤ Q`:

`∑_{q ≤ Q} ∑_{a ≤ q, (a,q)=1} |S(a/q)|² ≤ (Q² + 4πX) ∑ |a(n)|²`.

(The optimal constant, `X + Q² - 1`, is due to Montgomery–Vaughan and Selberg; we don't need it.)

Proved, with no `sorry`.
-/

open Complex MeasureTheory Finset

namespace TernaryGoldbach

/-! ## Derivative and periodicity of `S` -/

theorem hasDerivAt_e_mul (n : ℕ) (α : ℝ) :
    HasDerivAt (fun α : ℝ => e (n * α)) (2 * Real.pi * I * n * e (n * α)) α := by
  have h : HasDerivAt (fun α : ℝ => (2 * Real.pi * I * n : ℂ) * (α : ℂ))
      (2 * Real.pi * I * n) α := by
    simpa using ((hasDerivAt_id (α : ℝ)).ofReal_comp).const_mul (2 * Real.pi * I * n : ℂ)
  have := h.cexp
  convert this using 1
  · funext α; simp only [e]; push_cast; ring_nf
  · simp only [e]; push_cast; ring_nf

/-- The derivative of `S_a` is `S_{2πi n a}`. -/
theorem hasDerivAt_expSum (X : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    HasDerivAt (expSum X a) (expSum X (fun n => 2 * Real.pi * I * n * a n) α) α := by
  unfold expSum
  have := HasDerivAt.sum (u := range (X + 1)) (A := fun n α => a n * e (n * α))
    (A' := fun n => a n * (2 * Real.pi * I * n * e (n * α))) (x := α)
    fun n _ => (hasDerivAt_e_mul n α).const_mul (a n)
  convert this using 1
  refine sum_congr rfl fun n _ => ?_
  simp only
  ring

theorem e_nat_mul_add_one (n : ℕ) (α : ℝ) : e (n * (α + 1)) = e (n * α) := by
  rw [mul_add, mul_one, e_add]
  have : e n = 1 := by
    simp only [e]
    rw [show (2 * Real.pi * I * ((n : ℝ) : ℂ)) = (n : ℤ) * (2 * Real.pi * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [this, mul_one]

theorem periodic_expSum (X : ℕ) (a : ℕ → ℂ) : Function.Periodic (expSum X a) 1 := by
  intro α
  simp only [expSum, e_nat_mul_add_one]

/-! ## Gallagher's lemma -/
/-- **Gallagher's lemma.** For `F` with continuous derivative `F'` and `I = (c - δ/2, c + δ/2]`,
`|F(c)| ≤ δ⁻¹ ∫_I |F| + ∫_I |F'|`. -/
theorem gallagher {F F' : ℝ → ℂ} (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖F c‖ ≤ δ⁻¹ * (∫ t in Set.Ioc (c - δ / 2) (c + δ / 2), ‖F t‖) +
      ∫ t in Set.Ioc (c - δ / 2) (c + δ / 2), ‖F' t‖ := by
  set a := c - δ / 2
  set b := c + δ / 2
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  set C := ∫ t in Set.Ioc a b, ‖F' t‖
  have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _
  -- Pointwise: `|F(c)| ≤ |F(t)| + C` for `t ∈ [a, b]`.
  have hpt : ∀ t ∈ Set.Ioc a b, ‖F c‖ ≤ ‖F t‖ + C := by
    intro t ht
    have hdiff : F c - F t = ∫ x in t..c, F' x :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
        (hF'.intervalIntegrable _ _)).symm
    have hsub : Set.uIoc t c ⊆ Set.uIoc a b := by
      rw [Set.uIoc_of_le hab]
      intro x hx
      rcases le_total t c with h | h
      · rw [Set.uIoc_of_le h] at hx
        exact ⟨by linarith [ht.1, hx.1], by simp only [b] at *; linarith [hx.2]⟩
      · rw [Set.uIoc_of_ge h] at hx
        exact ⟨by simp only [a] at *; linarith [hx.1], by linarith [hx.2, ht.2]⟩
    have hbound : ‖∫ x in t..c, F' x‖ ≤ C := by
      refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
      refine (intervalIntegral.abs_integral_mono_interval hsub
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (hF'.norm.intervalIntegrable _ _)).trans (le_of_eq ?_)
      rw [_root_.abs_of_nonneg (intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _),
        intervalIntegral.integral_of_le hab]
    calc ‖F c‖ = ‖F t + (F c - F t)‖ := by ring_nf
      _ ≤ ‖F t‖ + ‖F c - F t‖ := norm_add_le _ _
      _ ≤ ‖F t‖ + C := by rw [hdiff]; linarith
  -- Average over `t ∈ (a, b]`.
  have hint : ∫ t in Set.Ioc a b, ‖F c‖ ≤ ∫ t in Set.Ioc a b, (‖F t‖ + C) :=
    setIntegral_mono_on (continuous_const.integrableOn_Ioc)
      ((hFc.norm.add continuous_const).integrableOn_Ioc) measurableSet_Ioc hpt
  have hvol : (volume (Set.Ioc a b)).toReal = δ := by
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]; simp only [a, b]; ring
  rw [integral_add hFc.norm.integrableOn_Ioc continuous_const.integrableOn_Ioc,
    setIntegral_const, setIntegral_const, hvol, smul_eq_mul, smul_eq_mul] at hint
  have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
  calc ‖F c‖ = δ⁻¹ * (δ * ‖F c‖) := by field_simp
    _ ≤ δ⁻¹ * ((∫ t in Set.Ioc a b, ‖F t‖) + δ * C) := by gcongr
    _ = _ := by field_simp; ring
/-! ## Summing over disjoint intervals -/

/-- For a nonnegative continuous 1-periodic `f` and disjoint intervals `I_r` inside a window of
length 1, `∑_r ∫_{I_r} f ≤ ∫₀¹ f`. -/
theorem sum_setIntegral_le_of_disjoint {ι : Type*} {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (hper : Function.Periodic f 1) (s : Finset ι) (I : ι → Set ℝ)
    (hI : ∀ r ∈ s, MeasurableSet (I r)) (hdisj : (s : Set ι).PairwiseDisjoint I) (β : ℝ)
    (hsub : ∀ r ∈ s, I r ⊆ Set.Ioc β (β + 1)) :
    ∑ r ∈ s, ∫ x in I r, f x ≤ ∫ x in Set.Ioc (0:ℝ) 1, f x := by
  have hint : ∀ r ∈ s, IntegrableOn f (I r) :=
    fun r hr => (hf.integrableOn_Ioc (a := β) (b := β + 1)).mono_set (hsub r hr)
  rw [← integral_finset_biUnion s hI hdisj hint]
  have hwin : ∫ x in Set.Ioc β (β + 1), f x = ∫ x in Set.Ioc (0:ℝ) 1, f x := by
    rw [← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le zero_le_one,
      hper.intervalIntegral_add_eq β 0, zero_add]
  rw [← hwin]
  refine setIntegral_mono_set hf.integrableOn_Ioc (Filter.Eventually.of_forall hf0) ?_
  exact (Set.iUnion₂_subset hsub).eventuallyLE

/-! ## The large sieve -/

/-- **The large sieve inequality** (Gallagher's form). -/
theorem large_sieve {ι : Type*} (s : Finset ι) (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (β : ℝ)
    (hdisj : (s : Set ι).PairwiseDisjoint fun r => Set.Ioc (α r - δ / 2) (α r + δ / 2))
    (hsub : ∀ r ∈ s, Set.Ioc (α r - δ / 2) (α r + δ / 2) ⊆ Set.Ioc β (β + 1))
    (X : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ s, ‖expSum X a (α r)‖ ^ 2 ≤
      (δ⁻¹ + 4 * Real.pi * X) * ∑ n ∈ range (X + 1), ‖a n‖ ^ 2 := by
  set b : ℕ → ℂ := fun n => 2 * Real.pi * I * n * a n
  set S := expSum X a
  set S' := expSum X b
  have hS : Continuous S := continuous_expSum X a
  have hS' : Continuous S' := continuous_expSum X b
  set I : ι → Set ℝ := fun r => Set.Ioc (α r - δ / 2) (α r + δ / 2)
  set g : ℝ → ℝ := fun x => ‖S x‖ ^ 2
  set h : ℝ → ℝ := fun x => 2 * (‖S x‖ * ‖S' x‖)
  have hg : Continuous g := hS.norm.pow 2
  have hh : Continuous h := continuous_const.mul (hS.norm.mul hS'.norm)
  -- Gallagher at each point.
  have hpt : ∀ r ∈ s, ‖S (α r)‖ ^ 2 ≤ δ⁻¹ * (∫ x in I r, g x) + ∫ x in I r, h x := by
    intro r _
    have hF : ∀ t, HasDerivAt (fun x => S x * S x) (S' t * S t + S t * S' t) t :=
      fun t => (hasDerivAt_expSum X a t).mul (hasDerivAt_expSum X a t)
    have hF' : Continuous fun t => S' t * S t + S t * S' t := (hS'.mul hS).add (hS.mul hS')
    have := gallagher hF hF' (α r) hδ
    simp only [← sq, norm_pow] at this
    refine this.trans (add_le_add le_rfl ?_)
    · refine setIntegral_mono_on hF'.norm.integrableOn_Ioc hh.integrableOn_Ioc measurableSet_Ioc
        fun x _ => ?_
      calc ‖S' x * S x + S x * S' x‖ ≤ ‖S' x * S x‖ + ‖S x * S' x‖ := norm_add_le _ _
        _ = h x := by simp only [h, norm_mul]; ring
  -- Sum over the disjoint intervals.
  have hperS : Function.Periodic S 1 := periodic_expSum X a
  have hperS' : Function.Periodic S' 1 := periodic_expSum X b
  have hsumg := sum_setIntegral_le_of_disjoint hg (fun x => by positivity)
    (fun x => by simp only [g, hperS x]) s I (fun _ _ => measurableSet_Ioc) hdisj β hsub
  have hsumh := sum_setIntegral_le_of_disjoint hh (fun x => by positivity)
    (fun x => by simp only [h, hperS x, hperS' x]) s I (fun _ _ => measurableSet_Ioc) hdisj β hsub
  -- Parseval and Cauchy–Schwarz on `[0, 1]`.
  set A := ∑ n ∈ range (X + 1), ‖a n‖ ^ 2
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => by positivity
  have hgA : ∫ x in Set.Ioc (0:ℝ) 1, g x = A := setIntegral_norm_sq_expSum X a
  have hB : ∑ n ∈ range (X + 1), ‖b n‖ ^ 2 ≤ (2 * Real.pi * X) ^ 2 * A := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hb : ‖b n‖ ^ 2 = (2 * Real.pi * n) ^ 2 * ‖a n‖ ^ 2 := by
      simp only [b, norm_mul, Complex.norm_eq_abs, Complex.abs_two, Complex.abs_ofReal,
        Complex.abs_I, Complex.abs_natCast, abs_of_pos Real.pi_pos]
      ring
    rw [hb]
    have := Real.pi_pos
    gcongr
  have hhA : ∫ x in Set.Ioc (0:ℝ) 1, h x ≤ 4 * Real.pi * X * A := by
    rw [MeasureTheory.integral_mul_left]
    have hcs := setIntegral_norm_mul_norm_expSum_le X a b
    have hsqB : √(∑ n ∈ range (X + 1), ‖b n‖ ^ 2) ≤ 2 * Real.pi * X * √A := by
      calc √(∑ n ∈ range (X + 1), ‖b n‖ ^ 2) ≤ √((2 * Real.pi * X) ^ 2 * A) :=
            Real.sqrt_le_sqrt hB
        _ = 2 * Real.pi * X * √A := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hsA : √A * √A = A := Real.mul_self_sqrt hA0
    calc 2 * ∫ x in Set.Ioc (0:ℝ) 1, ‖S x‖ * ‖S' x‖ ≤ 2 * (√A * (2 * Real.pi * X * √A)) := by
          gcongr
          exact hcs.trans (mul_le_mul_of_nonneg_left hsqB (Real.sqrt_nonneg _))
      _ = 4 * Real.pi * X * A := by linear_combination (4 * Real.pi * X) * hsA
  calc ∑ r ∈ s, ‖S (α r)‖ ^ 2
      ≤ ∑ r ∈ s, (δ⁻¹ * (∫ x in I r, g x) + ∫ x in I r, h x) := sum_le_sum hpt
    _ = δ⁻¹ * ∑ r ∈ s, (∫ x in I r, g x) + ∑ r ∈ s, ∫ x in I r, h x := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ δ⁻¹ * A + 4 * Real.pi * X * A := by
        gcongr
        · exact hsumg.trans hgA.le
        · exact hsumh.trans hhA
    _ = (δ⁻¹ + 4 * Real.pi * X) * A := by ring

/-! ## Farey fractions -/

/-- Distinct reduced fractions with denominators `≤ Q` are `Q⁻²`-apart. -/
theorem farey_sep {Q q q' b b' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqQ : q ≤ Q) (hq'Q : q' ≤ Q)
    (hb : Nat.Coprime b q) (hb' : Nat.Coprime b' q') (hne : (q, b) ≠ (q', b')) :
    ((Q : ℝ) ^ 2)⁻¹ ≤ |(b : ℝ) / q - b' / q'| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'r : (0 : ℝ) < q' := by exact_mod_cast hq'
  set k : ℤ := b * q' - b' * q
  have hk : k ≠ 0 := by
    intro hk0
    have heq : b * q' = b' * q := by
      have : (b : ℤ) * q' = b' * q := by simp only [k] at hk0; linarith
      exact_mod_cast this
    have h1 : q ∣ q' := hb.symm.dvd_of_dvd_mul_left ⟨b', by rw [heq, mul_comm]⟩
    have h2 : q' ∣ q := hb'.symm.dvd_of_dvd_mul_left ⟨b, by rw [← heq, mul_comm]⟩
    have hqq : q = q' := Nat.dvd_antisymm h1 h2
    subst hqq
    have : b = b' := Nat.eq_of_mul_eq_mul_right hq heq
    exact hne (by rw [this])
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hdiff : (b : ℝ) / q - b' / q' = k / (q * q') := by
    simp only [k]; push_cast; field_simp; ring
  rw [hdiff, abs_div, abs_of_pos (mul_pos hqr hq'r)]
  have hQq : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    rw [sq]; exact mul_le_mul (by exact_mod_cast hqQ) (by exact_mod_cast hq'Q) hq'r.le (by positivity)
  calc ((Q : ℝ) ^ 2)⁻¹ ≤ ((q : ℝ) * q')⁻¹ := inv_anti₀ (by positivity) hQq
    _ = 1 / (q * q') := by rw [one_div]
    _ ≤ |(k : ℝ)| / (q * q') := by gcongr

/-- **The large sieve at Farey fractions**:
`∑_{q ≤ Q} ∑_{1 ≤ b ≤ q, (b,q)=1} |S(b/q)|² ≤ (Q² + 4πX) ∑_{n ≤ X} |a(n)|²`. -/
theorem large_sieve_farey (Q X : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) :
    ∑ q ∈ Icc 1 Q, ∑ b ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
        ‖expSum X a ((b : ℝ) / q)‖ ^ 2 ≤
      ((Q : ℝ) ^ 2 + 4 * Real.pi * X) * ∑ n ∈ range (X + 1), ‖a n‖ ^ 2 := by
  set s := (Icc 1 Q).sigma fun q => (Icc 1 q).filter fun b => Nat.Coprime b q
  set α : (Σ _ : ℕ, ℕ) → ℝ := fun p => (p.2 : ℝ) / p.1
  set δ : ℝ := ((Q : ℝ) ^ 2)⁻¹
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hδ : 0 < δ := by positivity
  have hmem : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 ≤ Q ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1 := by
    intro p hp
    simp only [s, mem_sigma, mem_Icc, mem_filter] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2.1.1, hp.2.1.2, hp.2.2⟩
  have hdisj : (s : Set (Σ _ : ℕ, ℕ)).PairwiseDisjoint
      fun p => Set.Ioc (α p - δ / 2) (α p + δ / 2) := by
    intro p hp p' hp' hne
    obtain ⟨h1, h2, -, -, h5⟩ := hmem p hp
    obtain ⟨h1', h2', -, -, h5'⟩ := hmem p' hp'
    have hne' : (p.1, p.2) ≠ (p'.1, p'.2) := by
      intro h; apply hne; cases p; cases p'; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    have hsep := farey_sep h1 h1' h2 h2' h5 h5' hne'
    refine Set.disjoint_left.2 fun z hz hz' => ?_
    simp only [Set.mem_Ioc] at hz hz'
    have : |α p - α p'| < δ := by rw [abs_lt]; constructor <;> linarith
    exact absurd hsep (not_le.2 this)
  have hsub : ∀ p ∈ s, Set.Ioc (α p - δ / 2) (α p + δ / 2) ⊆ Set.Ioc (δ / 2) (δ / 2 + 1) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, -⟩ := hmem p hp
    have hq : (0 : ℝ) < p.1 := by exact_mod_cast h1
    have hlo : δ ≤ α p := by
      have : (1 : ℝ) / p.1 ≤ α p := div_le_div_of_nonneg_right (by exact_mod_cast h3) hq.le
      refine le_trans ?_ this
      rw [one_div]
      refine inv_anti₀ hq ?_
      calc (p.1 : ℝ) ≤ Q := by exact_mod_cast h2
        _ ≤ (Q : ℝ) ^ 2 := by nlinarith
    have hhi : α p ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast h4) hq.le
    intro z hz
    simp only [Set.mem_Ioc] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  have := large_sieve s α hδ (δ / 2) hdisj hsub X a
  rw [sum_sigma] at this
  simpa only [δ, inv_inv] using this

end TernaryGoldbach
