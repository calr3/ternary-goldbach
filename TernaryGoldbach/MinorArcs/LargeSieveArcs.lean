import TernaryGoldbach.MinorArcs.Periodize
import TernaryGoldbach.MinorArcs.LargeSieveWeights

/-!
# Major arcs as sums over arcs [H, Props. 12.1.1, 12.1.2]

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

/-- `w_q + w_{q'} < D/(qq')` with `D = 2` if `q, q'` are both even and `D = 1` otherwise, when
`δ₀Q² ≤ x/2` and `q̃, q̃' ≤ 2Q`. -/
theorem wrad_add_le {δ₀ Q x : ℝ} (hx : 0 < x) (hδ : 0 < δ₀) (hQ : 0 < Q) (hQx : δ₀ * Q ^ 2 ≤ x / 2)
    {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqQ : (qt q : ℝ) ≤ 2 * Q) (hqQ' : (qt q' : ℝ) ≤ 2 * Q) :
    wrad δ₀ Q x q + wrad δ₀ Q x q' ≤ (if Even q ∧ Even q' then 2 else 1) / (q * q') := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  -- `δ₀Q/x ≤ 1/(2Q)`
  have hk : δ₀ * Q / x ≤ 1 / (2 * Q) := by
    rw [div_le_div_iff₀ hx (by positivity)]; nlinarith
  have hw : ∀ p : ℕ, 1 ≤ p → wrad δ₀ Q x p ≤ 1 / (2 * Q * qt p) := by
    intro p hp
    have hp2 : (0 : ℝ) < qt p := by have := two_le_qt hp; exact_mod_cast (by omega : 0 < qt p)
    unfold wrad
    rw [show δ₀ * Q / (qt p * x) = δ₀ * Q / x / qt p by field_simp]
    calc δ₀ * Q / x / qt p ≤ 1 / (2 * Q) / qt p := by gcongr
      _ = 1 / (2 * Q * qt p) := by field_simp
  refine (add_le_add (hw q hq) (hw q' hq')).trans ?_
  unfold qt at hqQ hqQ' ⊢
  by_cases he : Even q <;> by_cases he' : Even q' <;> simp only [he, he', if_true, if_false,
    and_self, and_true, and_false] at hqQ hqQ' ⊢ <;> push_cast at hqQ hqQ' ⊢ <;>
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)] <;>
    nlinarith [mul_pos hqr hqr', mul_pos (mul_pos hqr hqr') hQ]

/-- **The arcs at level `Q` are disjoint** (`δ₀Q² ≤ x/2`): if `α − k ∈ J_{q,b}` and
`α − k' ∈ J_{q',b'}`, then `(q, b, k) = (q', b', k')`. -/
theorem arcs_unique {δ₀ Q x : ℝ} (hx : 0 < x) (hδ : 0 < δ₀) (hQ : 0 < Q) (hQx : δ₀ * Q ^ 2 ≤ x / 2)
    {α : ℝ} {q b q' b' : ℕ} {k k' : ℤ} (hq : q ∈ Qset Q) (hb : b ∈ Bset q) (hq' : q' ∈ Qset Q)
    (hb' : b' ∈ Bset q') (h1 : α - k ∈ arc δ₀ Q x q b) (h2 : α - k' ∈ arc δ₀ Q x q' b') :
    q = q' ∧ b = b' ∧ k = k' := by
  obtain ⟨hq1, hqQ⟩ := Finset.mem_filter.1 hq
  obtain ⟨hq1', hqQ'⟩ := Finset.mem_filter.1 hq'
  have hq1 := (Finset.mem_Icc.1 hq1).1
  have hq1' := (Finset.mem_Icc.1 hq1').1
  obtain ⟨hbq, hbc⟩ := Finset.mem_filter.1 hb
  obtain ⟨hbq', hbc'⟩ := Finset.mem_filter.1 hb'
  have hbq := Finset.mem_range.1 hbq
  have hbq' := Finset.mem_range.1 hbq'
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  set c : ℤ := b + k * q
  set c' : ℤ := b' + k' * q'
  have hc : (c : ℝ) / q = b / q + k := by simp only [c]; push_cast; field_simp
  have hc' : (c' : ℝ) / q' = b' / q' + k' := by simp only [c']; push_cast; field_simp
  have hdist : |(c : ℝ) / q - c' / q'| < wrad δ₀ Q x q + wrad δ₀ Q x q' := by
    obtain ⟨h11, h12⟩ := h1
    obtain ⟨h21, h22⟩ := h2
    rw [hc, hc', abs_sub_lt_iff]; constructor <;> linarith
  have hW := wrad_add_le hx hδ hQ hQx hq1 hq1' hqQ hqQ'
  -- `cq' = c'q`
  have hcross : c * q' = c' * q := by
    by_contra hne
    set N : ℤ := c * q' - c' * q
    have hN : N ≠ 0 := sub_ne_zero.2 hne
    have hexpr : (c : ℝ) / q - c' / q' = N / (q * q') := by
      simp only [N]; push_cast; field_simp
    rw [hexpr, abs_div, abs_of_pos (by positivity : (0:ℝ) < q * q')] at hdist
    have hD : (if Even q ∧ Even q' then (2 : ℝ) else 1) ≤ |(N : ℝ)| := by
      split_ifs with hev
      · have hNe : Even N := by
          have e1 : Even (c * q') := ((Int.even_coe_nat q').2 hev.2).mul_left c
          have e2 : Even (c' * q) := ((Int.even_coe_nat q).2 hev.1).mul_left c'
          exact e1.sub e2
        obtain ⟨m, hm⟩ := hNe
        have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hN hm
        have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
        rw [hm]; push_cast
        rw [show (m : ℝ) + m = 2 * m by ring, abs_mul]
        have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast this
        norm_num; linarith
      · exact_mod_cast Int.one_le_abs hN
    have := lt_of_lt_of_le hdist hW
    rw [div_lt_div_iff_of_pos_right (by positivity)] at this
    linarith
  -- coprimality gives `q = q'`
  have hcop : IsCoprime c q := by
    have : IsCoprime (b : ℤ) q := Nat.isCoprime_iff_coprime.2 hbc
    simpa [c] using this.add_mul_right_left k
  have hcop' : IsCoprime c' q' := by
    have : IsCoprime (b' : ℤ) q' := Nat.isCoprime_iff_coprime.2 hbc'
    simpa [c'] using this.add_mul_right_left k'
  have hd1 : (q : ℤ) ∣ q' := by
    have : (q : ℤ) ∣ c * q' := ⟨c', by rw [hcross]; ring⟩
    exact hcop.symm.dvd_of_dvd_mul_left this
  have hd2 : (q' : ℤ) ∣ q := by
    have : (q' : ℤ) ∣ c' * q := ⟨c, by rw [← hcross]; ring⟩
    exact hcop'.symm.dvd_of_dvd_mul_left this
  have hqq : q = q' := by
    have := Int.dvd_antisymm (by positivity) (by positivity) hd1 hd2
    exact_mod_cast this
  subst hqq
  have hcc : c = c' := by
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    exact mul_right_cancel₀ hq0 hcross
  -- `b + kq = b' + k'q` with `0 ≤ b, b' < q`
  have hkk : k = k' := by
    have h : ((b : ℤ) - b') = (k' - k) * q := by simp only [c, c'] at hcc; linarith
    by_contra hne
    have : (1 : ℤ) ≤ |k' - k| := Int.one_le_abs (sub_ne_zero.2 (Ne.symm hne))
    have hlt : |(b : ℤ) - b'| < q := by rw [abs_lt]; constructor <;> omega
    rw [h, abs_mul, abs_of_pos (by exact_mod_cast hq1 : (0:ℤ) < q)] at hlt
    nlinarith
  subst hkk
  refine ⟨rfl, ?_, rfl⟩
  have : (b : ℤ) = b' := by simp only [c, c'] at hcc; linarith
  exact_mod_cast this

theorem sum_arc_indicator_le_one {δ₀ Q x : ℝ} (hx : 0 < x) (hδ : 0 < δ₀) (hQ : 0 < Q)
    (hQx : δ₀ * Q ^ 2 ≤ x / 2) (α : ℝ) :
    ∑ q ∈ Qset Q, ∑ b ∈ Bset q, ∑ k ∈ ({-1, 0, 1} : Finset ℤ),
      (arc δ₀ Q x q b).indicator (1 : ℝ → ℝ) (α - k) ≤ 1 := by
  set K : Finset ℤ := {-1, 0, 1}
  by_cases h : ∃ q ∈ Qset Q, ∃ b ∈ Bset q, ∃ k ∈ K, α - k ∈ arc δ₀ Q x q b
  · obtain ⟨q₀, hq₀, b₀, hb₀, k₀, hk₀, hin⟩ := h
    have hzero : ∀ q ∈ Qset Q, ∀ b ∈ Bset q, ∀ k ∈ K, (q, b, k) ≠ (q₀, b₀, k₀) →
        (arc δ₀ Q x q b).indicator (1 : ℝ → ℝ) (α - k) = 0 := by
      intro q hq b hb k _ hne
      apply indicator_of_notMem
      intro hin'
      obtain ⟨rfl, rfl, rfl⟩ := arcs_unique hx hδ hQ hQx hq hb hq₀ hb₀ hin' hin
      exact hne rfl
    rw [Finset.sum_eq_single q₀ (fun q hq hne => Finset.sum_eq_zero fun b hb =>
      Finset.sum_eq_zero fun k hk => hzero q hq b hb k hk (by simp [hne])) (fun h => absurd hq₀ h)]
    rw [Finset.sum_eq_single b₀ (fun b hb hne => Finset.sum_eq_zero fun k hk =>
      hzero q₀ hq₀ b hb k hk (by simp [hne])) (fun h => absurd hb₀ h)]
    rw [Finset.sum_eq_single k₀ (fun k hk hne => hzero q₀ hq₀ b₀ hb₀ k hk (by simp [hne]))
      (fun h => absurd hk₀ h)]
    rw [indicator_of_mem hin]; simp
  · push Not at h
    rw [Finset.sum_eq_zero fun q hq => Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun k hk =>
      indicator_of_notMem (h q hq b hb k hk) _]
    norm_num

/-- **Disjointness**: for `δ₀Q² ≤ x/2`, `Σ_{q, b} ∫_{J_{q,b}} g ≤ ∫_0^1 g` (`g ≥ 0` continuous
`1`-periodic). -/
theorem sum_arcs_le_integral {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g 1)
    (hg0 : ∀ α, 0 ≤ g α) {δ₀ Q x : ℝ} (hx : 0 < x) (hδ : 0 < δ₀) (hQ : 0 < Q)
    (hQx : δ₀ * Q ^ 2 ≤ x / 2) (hw : δ₀ * Q ≤ x) :
    ∑ q ∈ Qset Q, ∑ b ∈ Bset q, ∫ y in arc δ₀ Q x q b, g y ≤ ∫ α in Ioc (0 : ℝ) 1, g α := by
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
  rw [hmerge]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun α _ => ?_
  · exact integrable_finset_sum _ fun q _ => integrable_finset_sum _ fun b _ => hint2 q b
  · exact (hg.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  · simp_rw [← Finset.sum_mul]
    have := sum_arc_indicator_le_one hx hδ hQ hQx α
    nlinarith [hg0 α]

end TernaryGoldbach.MinorArcs
