import TernaryGoldbach.MinorArcs.LargeSieveArcs

/-!
# The major arcs as a disjoint union of the arcs `J_{q,b}`

`∫_{(0,1] ∩ 𝔐_{δ₀,R}} g = Σ_{q, b} ∫_{J_{q,b}} g` for `g ≥ 0` continuous `1`-periodic and `δ₀R² ≤ x/2`:
`≤` is `integral_majorArcs_le`; `≥` (`sum_arcs_le_integral_majorArcs`) refines `sum_arcs_le_integral`.
-/

open Real Set MeasureTheory

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs)

theorem mem_majorArcs_of_arc {δ₀ R x α : ℝ} {q b : ℕ} {k : ℤ} (hq : q ∈ Qset R) (hb : b ∈ Bset q)
    (h : α - k ∈ arc δ₀ R x q b) : α ∈ majorArcs δ₀ R x := by
  obtain ⟨hq1, hqR⟩ := Finset.mem_filter.1 hq
  have hq1 := (Finset.mem_Icc.1 hq1).1
  obtain ⟨-, hbc⟩ := Finset.mem_filter.1 hb
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq1
  rw [mem_majorArcs_iff]
  refine ⟨q, hq1, hqR, b + k * q, ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]
    have : Int.gcd ((b : ℤ) + k * q) q = Int.gcd b q := by
      rw [Int.gcd_comm, Int.gcd_comm (b : ℤ)]
      simpa using Int.gcd_add_mul_self (q : ℤ) b k
    rw [this, Int.gcd_natCast_natCast]; exact hbc
  · obtain ⟨h1, h2⟩ := h
    have e : (((b : ℤ) + k * q : ℤ) : ℝ) / q = b / q + k := by push_cast; field_simp
    rw [e, abs_sub_lt_iff]; constructor <;> linarith

/-- **Disjointness, restricted to `𝔐`**: `Σ_{q, b} ∫_{J_{q,b}} g ≤ ∫_{(0,1] ∩ 𝔐} g`. -/
theorem sum_arcs_le_integral_majorArcs {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g 1)
    (hg0 : ∀ α, 0 ≤ g α) {δ₀ Q x : ℝ} (hx : 0 < x) (hδ : 0 < δ₀) (hQ : 0 < Q)
    (hQx : δ₀ * Q ^ 2 ≤ x / 2) (hw : δ₀ * Q ≤ x) :
    ∑ q ∈ Qset Q, ∑ b ∈ Bset q, ∫ y in arc δ₀ Q x q b, g y ≤
      ∫ α in Ioc (0 : ℝ) 1 ∩ majorArcs δ₀ Q x, g α := by
  set K : Finset ℤ := {-1, 0, 1}
  have hδQ : 0 ≤ δ₀ * Q := by positivity
  have hmem : ∀ q ∈ Qset Q, 1 ≤ q := fun q hq => (Finset.mem_Icc.1 (Finset.mem_filter.1 hq).1).1
  have hbmem : ∀ q b, b ∈ Bset q → b < q := fun q b hb => Finset.mem_range.1 (Finset.mem_filter.1 hb).1
  have hP : ∀ q ∈ Qset Q, ∀ b ∈ Bset q, ∫ y in arc δ₀ Q x q b, g y =
      ∑ k ∈ K, ∫ α in Ioc (0 : ℝ) 1, (arc δ₀ Q x q b).indicator 1 (α - k) * g α := fun q hq b hb =>
    setIntegral_eq_sum_periodize hg hper measurableSet_Ioo
      (arc_subset hx hδQ hw (hmem q hq) (hbmem q b hb))
  rw [Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun b hb => hP q hq b hb]
  have hint : ∀ (q b : ℕ) (k : ℤ), IntegrableOn
      (fun α => (arc δ₀ Q x q b).indicator 1 (α - k) * g α) (Ioc (0 : ℝ) 1) := by
    intro q b k
    refine (hg.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self |>.bdd_mul
      (c := 1) ?_ ?_
    · exact ((measurable_const.indicator measurableSet_Ioo).comp
        (measurable_sub_const _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun α => by simp only [indicator]; split_ifs <;> simp
  simp_rw [← integral_finset_sum _ fun _ _ => hint _ _ _]
  have hint2 : ∀ q b, IntegrableOn (fun α => ∑ k ∈ K, (arc δ₀ Q x q b).indicator 1 (α - k) * g α)
      (Ioc (0 : ℝ) 1) := fun q b => integrable_finset_sum _ fun k _ => hint q b k
  have hmerge : ∑ q ∈ Qset Q, ∑ b ∈ Bset q, ∫ α in Ioc (0 : ℝ) 1,
      ∑ k ∈ K, (arc δ₀ Q x q b).indicator 1 (α - k) * g α =
      ∫ α in Ioc (0 : ℝ) 1, ∑ q ∈ Qset Q, ∑ b ∈ Bset q, ∑ k ∈ K,
        (arc δ₀ Q x q b).indicator 1 (α - k) * g α := by
    rw [integral_finset_sum _ fun q _ => integrable_finset_sum _ fun b _ => hint2 q b]
    exact Finset.sum_congr rfl fun q _ => (integral_finset_sum _ fun b _ => hint2 q b).symm
  rw [hmerge, ← setIntegral_indicator (Helfgott.measurableSet_majorArcs δ₀ Q x)]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun α _ => ?_
  · exact integrable_finset_sum _ fun q _ => integrable_finset_sum _ fun b _ => hint2 q b
  · exact ((hg.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self).indicator
      (Helfgott.measurableSet_majorArcs δ₀ Q x)
  · simp_rw [← Finset.sum_mul]
    have h1 := sum_arc_indicator_le_one hx hδ hQ hQx α
    by_cases hM : α ∈ majorArcs δ₀ Q x
    · rw [indicator_of_mem hM]; nlinarith [hg0 α]
    · rw [indicator_of_notMem hM]
      have h0 : ∑ q ∈ Qset Q, ∑ b ∈ Bset q, ∑ k ∈ K, (arc δ₀ Q x q b).indicator (1 : ℝ → ℝ) (α - k) = 0 :=
        Finset.sum_eq_zero fun q hq => Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun k _ =>
          indicator_of_notMem (fun hin => hM (mem_majorArcs_of_arc hq hb hin)) _
      rw [h0, zero_mul]

end TernaryGoldbach.MinorArcs
