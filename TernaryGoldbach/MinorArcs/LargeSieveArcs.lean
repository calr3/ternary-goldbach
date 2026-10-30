import TernaryGoldbach.MinorArcs.Periodize
import TernaryGoldbach.MinorArcs.LargeSieveWeights

/-!
# Major arcs as sums over arcs [B, Props. 12.1.1, 12.1.2]

Uniform description of `𝔐_{δ₀,R}` ((10.5), `majorArcs δ₀ R x`): `q ≥ 1` contributes iff
`q̃ ≤ 2R` (`q̃ = q` for even `q`, `2q` for odd `q`), with radius `w_q = δ₀R/(q̃x)` around `a/q`,
`(a, q) = 1` (`mem_majorArcs_iff`).

* `integral_majorArcs_le` (covering): `∫_{(0,1] ∩ 𝔐} g ≤ Σ_{q, b} ∫_{|β| < w_q} g(b/q + β) dβ`.
* `sum_arcs_le_integral` (disjointness, `δ₀R² ≤ x/2`): `Σ_{q, b} ∫_{|β| < w_q} g(b/q + β) dβ ≤ ∫_0^1 g`.

Here `b` runs over `0 ≤ b < q`, `(b, q) = 1`, and `g` is continuous, `≥ 0`, `1`-periodic.
-/

open MeasureTheory Set Finset

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs)

theorem qt_ge (q : ℕ) : q ≤ qt q := by unfold qt; split_ifs <;> omega

theorem two_le_qt {q : ℕ} (hq : 1 ≤ q) : 2 ≤ qt q := by
  unfold qt; split_ifs with h
  · obtain ⟨k, rfl⟩ := h; omega
  · omega

/-- The radius `w_q = δ₀R/(q̃x)`. -/
noncomputable def wrad (δ₀ R x : ℝ) (q : ℕ) : ℝ := δ₀ * R / (qt q * x)

/-- The moduli of `𝔐_{δ₀,R}`: `q ≥ 1` with `q̃ ≤ 2R`. -/
noncomputable def Qset (R : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊2 * R⌋₊).filter (fun q => (qt q : ℝ) ≤ 2 * R)

/-- The residues `0 ≤ b < q`, `(b, q) = 1`. -/
def Bset (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun b => Nat.Coprime b q)

theorem mem_majorArcs_iff {δ₀ R x α : ℝ} :
    α ∈ majorArcs δ₀ R x ↔ ∃ q : ℕ, 1 ≤ q ∧ (qt q : ℝ) ≤ 2 * R ∧ ∃ a : ℤ, IsCoprime a q ∧
      |α - a / q| < wrad δ₀ R x q := by
  simp only [majorArcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo, exists_prop]
  have hodd : ∀ q : ℕ, ¬ Even q → wrad δ₀ R x q = δ₀ * R / (2 * q * x) := fun q h => by
    unfold wrad qt; rw [if_neg h]; push_cast; ring_nf
  have hev : ∀ q : ℕ, Even q → wrad δ₀ R x q = δ₀ * R / (q * x) := fun q h => by
    unfold wrad qt; rw [if_pos h]
  constructor
  · rintro (⟨q, ⟨hq1, hqR, ho⟩, a, hcop, h1, h2⟩ | ⟨q, ⟨hq1, hqR, he⟩, a, hcop, h1, h2⟩)
    · have hne : ¬ Even q := Nat.not_even_iff_odd.2 ho
      refine ⟨q, hq1, ?_, a, hcop, ?_⟩
      · unfold qt; rw [if_neg hne]; push_cast; linarith
      · rw [hodd q hne, abs_sub_lt_iff]; constructor <;> linarith
    · refine ⟨q, hq1, ?_, a, hcop, ?_⟩
      · unfold qt; rw [if_pos he]; exact hqR
      · rw [hev q he, abs_sub_lt_iff]; constructor <;> linarith
  · rintro ⟨q, hq1, hqR, a, hcop, h⟩
    rw [abs_sub_lt_iff] at h
    by_cases he : Even q
    · right
      refine ⟨q, ⟨hq1, ?_, he⟩, a, hcop, ?_, ?_⟩
      · unfold qt at hqR; rw [if_pos he] at hqR; exact hqR
      · rw [hev q he] at h; linarith
      · rw [hev q he] at h; linarith
    · left
      refine ⟨q, ⟨hq1, ?_, Nat.not_even_iff_odd.1 he⟩, a, hcop, ?_, ?_⟩
      · unfold qt at hqR; rw [if_neg he] at hqR; push_cast at hqR; linarith
      · rw [hodd q he] at h; linarith
      · rw [hodd q he] at h; linarith

/-- The arc `J_{q,b} = (b/q − w_q, b/q + w_q)`. -/
noncomputable def arc (δ₀ R x : ℝ) (q b : ℕ) : Set ℝ :=
  Ioo ((b : ℝ) / q - wrad δ₀ R x q) ((b : ℝ) / q + wrad δ₀ R x q)

theorem wrad_le_half {δ₀ R x : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ₀ * R) (hw : δ₀ * R ≤ x) {q : ℕ}
    (hq : 1 ≤ q) : wrad δ₀ R x q ≤ 1 / 2 := by
  unfold wrad
  have h2 : (2 : ℝ) ≤ qt q := by exact_mod_cast two_le_qt hq
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem arc_subset {δ₀ R x : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ₀ * R) (hw : δ₀ * R ≤ x) {q b : ℕ}
    (hq : 1 ≤ q) (hb : b < q) : arc δ₀ R x q b ⊆ Ioc (-1) 2 := by
  intro y ⟨h1, h2⟩
  have hw' := wrad_le_half hx hδ hw hq
  have hb0 : (0 : ℝ) ≤ b / q := by positivity
  have hb1 : (b : ℝ) / q < 1 := by
    rw [div_lt_one (by exact_mod_cast hq)]; exact_mod_cast hb
  constructor <;> linarith

/-- **Covering**: `∫_{(0,1] ∩ 𝔐_{δ₀,R}} g ≤ Σ_{q, b} ∫_{J_{q,b}} g` for `g ≥ 0` continuous
`1`-periodic. -/
theorem integral_majorArcs_le {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g 1)
    (hg0 : ∀ α, 0 ≤ g α) {δ₀ R x : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ₀ * R) (hw : δ₀ * R ≤ x) :
    ∫ α in Ioc (0 : ℝ) 1 ∩ majorArcs δ₀ R x, g α ≤
      ∑ q ∈ Qset R, ∑ b ∈ Bset q, ∫ y in arc δ₀ R x q b, g y := by
  set K : Finset ℤ := {-1, 0, 1}
  have hmem : ∀ q ∈ Qset R, 1 ≤ q := fun q hq => (Finset.mem_Icc.1 (Finset.mem_filter.1 hq).1).1
  have hbmem : ∀ q b, b ∈ Bset q → b < q := fun q b hb => Finset.mem_range.1 (Finset.mem_filter.1 hb).1
  -- periodize every arc
  have hP : ∀ q ∈ Qset R, ∀ b ∈ Bset q, ∫ y in arc δ₀ R x q b, g y =
      ∑ k ∈ K, ∫ α in Ioc (0 : ℝ) 1, (arc δ₀ R x q b).indicator 1 (α - k) * g α := fun q hq b hb =>
    setIntegral_eq_sum_periodize hg hper measurableSet_Ioo
      (arc_subset hx hδ hw (hmem q hq) (hbmem q b hb))
  rw [Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun b hb => hP q hq b hb]
  have hint : ∀ (q b : ℕ) (k : ℤ), IntegrableOn
      (fun α => (arc δ₀ R x q b).indicator 1 (α - k) * g α) (Ioc (0 : ℝ) 1) := by
    intro q b k
    refine (hg.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self |>.bdd_mul
      (c := 1) ?_ ?_
    · exact ((measurable_const.indicator measurableSet_Ioo).comp
        (measurable_sub_const _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun α => by simp only [indicator]; split_ifs <;> simp
  simp_rw [← integral_finset_sum _ fun _ _ => hint _ _ _]
  have hint2 : ∀ q b, IntegrableOn (fun α => ∑ k ∈ K, (arc δ₀ R x q b).indicator 1 (α - k) * g α)
      (Ioc (0 : ℝ) 1) := fun q b => integrable_finset_sum _ fun k _ => hint q b k
  have hmerge : ∑ q ∈ Qset R, ∑ b ∈ Bset q, ∫ α in Ioc (0 : ℝ) 1,
      ∑ k ∈ K, (arc δ₀ R x q b).indicator 1 (α - k) * g α =
      ∫ α in Ioc (0 : ℝ) 1, ∑ q ∈ Qset R, ∑ b ∈ Bset q, ∑ k ∈ K,
        (arc δ₀ R x q b).indicator 1 (α - k) * g α := by
    rw [integral_finset_sum _ fun q _ => integrable_finset_sum _ fun b _ => hint2 q b]
    exact Finset.sum_congr rfl fun q _ => (integral_finset_sum _ fun b _ => hint2 q b).symm
  rw [hmerge, ← setIntegral_indicator (TernaryGoldbach.Helfgott.measurableSet_majorArcs _ _ _)]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun α hα => ?_
  · exact ((hg.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self).indicator
      (TernaryGoldbach.Helfgott.measurableSet_majorArcs _ _ _)
  · exact integrable_finset_sum _ fun q _ => integrable_finset_sum _ fun b _ => hint2 q b
  -- pointwise
  by_cases hM : α ∈ majorArcs δ₀ R x
  · rw [indicator_of_mem hM]
    obtain ⟨q, hq1, hqR, a, hcop, hαa⟩ := mem_majorArcs_iff.1 hM
    have hq0 : (0 : ℤ) < q := by exact_mod_cast hq1
    set b := (a % q).toNat
    set k := a / (q : ℤ)
    have hbz : (b : ℤ) = a % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hq0.ne')
    have hab : a = b + q * k := by rw [hbz, add_comm]; exact (Int.mul_ediv_add_emod a q).symm
    have hbq : b < q := by
      have := Int.emod_lt_of_pos a hq0
      omega
    have hbcop : Nat.Coprime b q := by
      rw [← Nat.isCoprime_iff_coprime, hbz]
      have : IsCoprime (a + q * (-k)) q := hcop.add_mul_left_left _
      convert this using 1; rw [Int.emod_def]; ring
    have hqmem : q ∈ Qset R := by
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hq1, Nat.le_floor ?_⟩, hqR⟩
      exact le_trans (by exact_mod_cast qt_ge q) hqR
    have hbmem' : b ∈ Bset q := Finset.mem_filter.2 ⟨Finset.mem_range.2 hbq, hbcop⟩
    have hw' := wrad_le_half hx hδ hw hq1
    have hareal : (a : ℝ) / q = b / q + k := by
      rw [hab]; push_cast; field_simp
    have hin : α - k ∈ arc δ₀ R x q b := by
      rw [hareal, abs_sub_lt_iff] at hαa
      constructor <;> linarith
    have hkK : k ∈ K := by
      obtain ⟨h1, h2⟩ := hin
      obtain ⟨hα0, hα1⟩ := hα
      have hb0 : (0 : ℝ) ≤ b / q := by positivity
      have hb1 : (b : ℝ) / q < 1 := by
        rw [div_lt_one (by exact_mod_cast hq1)]; exact_mod_cast hbq
      have hk1 : (k : ℝ) < 2 := by linarith
      have hk2 : (-2 : ℝ) < k := by linarith
      have : -2 < k ∧ k < 2 := ⟨by exact_mod_cast hk2, by exact_mod_cast hk1⟩
      simp only [K, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hone : (1 : ℝ) ≤ ∑ q ∈ Qset R, ∑ b ∈ Bset q, ∑ k ∈ K,
        (arc δ₀ R x q b).indicator 1 (α - k) := by
      refine le_trans ?_ (Finset.single_le_sum (fun q _ => Finset.sum_nonneg fun b _ =>
        Finset.sum_nonneg fun k _ => indicator_nonneg (fun _ _ => zero_le_one) _) hqmem)
      refine le_trans ?_ (Finset.single_le_sum (fun b _ =>
        Finset.sum_nonneg fun k _ => indicator_nonneg (fun _ _ => zero_le_one) _) hbmem')
      refine le_trans ?_ (Finset.single_le_sum (fun k _ =>
        indicator_nonneg (fun _ _ => zero_le_one) _) hkK)
      rw [indicator_of_mem hin]
    simp_rw [← Finset.sum_mul]
    nlinarith [hg0 α]
  · rw [indicator_of_notMem hM]
    simp_rw [← Finset.sum_mul]
    exact mul_nonneg (Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun k _ => indicator_nonneg (fun _ _ => zero_le_one) _) (hg0 α)

end TernaryGoldbach.MinorArcs
