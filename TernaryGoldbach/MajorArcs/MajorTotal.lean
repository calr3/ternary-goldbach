import TernaryGoldbach.MajorArcs.L2Major
import TernaryGoldbach.MajorArcs.ArcCharsStar
import TernaryGoldbach.MajorArcs.Singular
import TernaryGoldbach.MajorArcs.FourierMain

/-!
# [B, (14.27)]: the integral over the major arcs

`Re ∫_{(0,1] ∩ 𝔐_{8,r₀}} S_{η₊}(α,x)² S_{η_*}(α,x) e(−Nα) dα ≥ 1.045 x²/κ` for odd `N ≥ 10²⁷`.

This file, part 1: the major arcs as a disjoint union of arcs for a signed integrand, and
`Σ_b |S(b/q + β) − μ(q)/φ(q) S(β)|² = Σ_b |S(b/q + β)|² − μ²(q)/φ(q) |S(β)|²`.
-/

open Real MeasureTheory FourierTransform Set Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open TernaryGoldbach (e expTsum Schar)
open TernaryGoldbach.MinorArcs (coprimePart Qset Bset qt wrad arc integral_majorArcs_le
  sum_arcs_le_integral_majorArcs expTsum_periodic etaU)
open TernaryGoldbach.Helfgott (etaPlus etaStar S r₀ κ majorArcs)

namespace TernaryGoldbach.MajorArcs

/-! ## The arcs for a signed integrand -/

/-- **`∫_{(0,1] ∩ 𝔐} g = Σ_{q,b} ∫_{J_{q,b}} g`** for continuous `1`-periodic real `g` (`x ≥ 4.9·10²⁶`). -/
theorem integral_majorArcs_eq {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g 1)
    {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, g α =
      ∑ q ∈ Qset r₀, ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, g y := by
  have hx0 : 0 < x := by linarith
  have hr₀ : r₀ = 150000 := rfl
  have h1 : (0 : ℝ) ≤ 8 * r₀ := by rw [hr₀]; norm_num
  have h2 : 8 * r₀ ≤ x := by rw [hr₀]; linarith
  have h3 : (0 : ℝ) < r₀ := by rw [hr₀]; norm_num
  have h4 : 8 * r₀ ^ 2 ≤ x / 2 := by rw [hr₀]; linarith
  set gp : ℝ → ℝ := fun α => max (g α) 0
  set gm : ℝ → ℝ := fun α => max (-g α) 0
  have hgp : Continuous gp := hg.max continuous_const
  have hgm : Continuous gm := hg.neg.max continuous_const
  have hperp : Function.Periodic gp 1 := fun α => by simp only [gp, hper α]
  have hperm : Function.Periodic gm 1 := fun α => by simp only [gm, hper α]
  have hgp0 : ∀ α, 0 ≤ gp α := fun α => le_max_right _ _
  have hgm0 : ∀ α, 0 ≤ gm α := fun α => le_max_right _ _
  have hpm : ∀ α, g α = gp α - gm α := fun α => by
    simp only [gp, gm]; rcases le_total (g α) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have eqp : ∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, gp α =
      ∑ q ∈ Qset r₀, ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, gp y :=
    le_antisymm (integral_majorArcs_le hgp hperp hgp0 hx0 h1 h2)
      (sum_arcs_le_integral_majorArcs hgp hperp hgp0 hx0 (by norm_num) h3 h4 h2)
  have eqm : ∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, gm α =
      ∑ q ∈ Qset r₀, ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, gm y :=
    le_antisymm (integral_majorArcs_le hgm hperm hgm0 hx0 h1 h2)
      (sum_arcs_le_integral_majorArcs hgm hperm hgm0 hx0 (by norm_num) h3 h4 h2)
  have hsub : Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x ⊆ Icc 0 1 := fun α hα => Ioc_subset_Icc_self hα.1
  have iP : IntegrableOn gp (Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x) :=
    (hgp.integrableOn_Icc (a := 0) (b := 1)).mono_set hsub
  have iM : IntegrableOn gm (Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x) :=
    (hgm.integrableOn_Icc (a := 0) (b := 1)).mono_set hsub
  have harc : ∀ q b, arc 8 r₀ x q b ⊆ Icc ((b : ℝ) / q - wrad 8 r₀ x q) ((b : ℝ) / q + wrad 8 r₀ x q) :=
    fun q b => Ioo_subset_Icc_self
  rw [setIntegral_congr_fun ((measurableSet_Ioc).inter (TernaryGoldbach.Helfgott.measurableSet_majorArcs _ _ _))
    (fun α _ => hpm α), integral_sub iP iM, eqp, eqm, ← sum_sub_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← integral_sub ((hgp.integrableOn_Icc).mono_set (harc q b))
    ((hgm.integrableOn_Icc).mono_set (harc q b))]
  exact setIntegral_congr_fun measurableSet_Ioo fun α _ => (hpm α).symm

/-! ## Removing the principal character in `ℓ²` -/

theorem gaussSum_one_eq {q : ℕ} [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar = (μ q : ℂ) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← TernaryGoldbach.ramanujan_coprime q 1 hq1 (Nat.coprime_one_left q), gaussSum,
    TernaryGoldbach.sum_zmod_eq_sum_range, sum_filter]
  refine sum_congr rfl fun c hc => ?_
  have hcq := mem_range.1 hc
  by_cases h : q.Coprime c
  · have hu : IsUnit (c : ZMod q) := (ZMod.isUnit_iff_coprime c q).2 (Nat.Coprime.symm h)
    rw [if_pos h, MulChar.one_apply hu, one_mul, TernaryGoldbach.stdAddChar_natCast_eq_e]
    congr 1; push_cast; ring
  · have hu : ¬IsUnit (c : ZMod q) := fun hu =>
      h (Nat.Coprime.symm ((ZMod.isUnit_iff_coprime c q).1 hu))
    rw [if_neg h, MulChar.map_nonunit _ hu, zero_mul]

theorem sum_units_expTsum {q : ℕ} [NeZero q] {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q) (β : ℝ) :
    ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit, expTsum a ((b.val : ℝ) / q + β) =
      (μ q : ℂ) * expTsum a β := by
  have h := TernaryGoldbach.sum_char_mul_S (1 : DirichletCharacter ℂ q) ha hcop β
  rw [inv_one, Schar_one_eq_expTsum hcop, gaussSum_one_eq] at h
  rw [← h, sum_filter]
  refine sum_congr rfl fun b _ => ?_
  by_cases hb : IsUnit b
  · rw [if_pos hb, MulChar.one_apply hb, one_mul]
  · rw [if_neg hb, MulChar.map_nonunit _ hb, zero_mul]

theorem moebius_sq_real (q : ℕ) : ((μ q : ℂ)) * (starRingEnd ℂ) (μ q : ℂ) =
    ((if Squarefree q then (1 : ℝ) else 0 : ℝ) : ℂ) := by
  rw [map_intCast, ← sq, show ((μ q : ℤ) : ℂ) ^ 2 = (((μ q : ℤ) : ℝ) ^ 2 : ℝ) by push_cast; rfl,
    moebius_sq_eq]

/-- **`Σ_b |S(b/q+β) − μ(q)/φ(q) S(β)|² = Σ_b |S(b/q+β)|² − μ²(q)/φ(q) |S(β)|²`**. -/
theorem sum_units_sq_sub_principal {q : ℕ} [NeZero q] {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q) (β : ℝ) :
    ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit,
        ‖expTsum a ((b.val : ℝ) / q + β) - (μ q : ℂ) / q.totient * expTsum a β‖ ^ 2 =
      ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖expTsum a ((b.val : ℝ) / q + β)‖ ^ 2 -
        (if Squarefree q then (1 : ℝ) else 0) / q.totient * ‖expTsum a β‖ ^ 2 := by
  set U := (univ : Finset (ZMod q)).filter IsUnit
  set c : ℂ := (μ q : ℂ) / q.totient * expTsum a β with hc
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcard : (U.card : ℝ) = q.totient := by
    have h := TernaryGoldbach.MinorArcs.sum_Bset_eq_units (q := q) (fun _ => (1 : ℝ)) 0
    simp only [sum_const, nsmul_eq_mul, mul_one] at h
    have hB : (Bset q).card = q.totient := by
      unfold TernaryGoldbach.MinorArcs.Bset
      rw [Nat.totient]; congr 1; exact filter_congr fun b _ => Nat.coprime_comm
    rw [show U = (univ : Finset (ZMod q)).filter IsUnit from rfl, ← h, hB]
  have hS := sum_units_expTsum ha hcop β
  have hpt : ∀ b ∈ U, ‖expTsum a ((b.val : ℝ) / q + β) - c‖ ^ 2 =
      ‖expTsum a ((b.val : ℝ) / q + β)‖ ^ 2 + ‖c‖ ^ 2 -
        2 * (expTsum a ((b.val : ℝ) / q + β) * (starRingEnd ℂ) c).re := fun b _ => by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  rw [sum_congr rfl hpt, sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, hcard,
    ← mul_sum, ← Complex.re_sum, ← sum_mul, hS]
  -- `‖c‖² φ − 2 Re(μ S · conj c) = −μ²/φ |S|²`
  have hm := moebius_sq_real q
  set S0 := expTsum a β
  have e1 : (q.totient : ℝ) * ‖c‖ ^ 2 = (if Squarefree q then (1 : ℝ) else 0) / q.totient * ‖S0‖ ^ 2 := by
    rw [hc, norm_mul, norm_div, mul_pow, div_pow, Complex.norm_natCast, Complex.norm_intCast]
    have : |((μ q : ℤ) : ℝ)| ^ 2 = if Squarefree q then (1 : ℝ) else 0 := by
      rw [sq_abs, moebius_sq_eq]
    rw [this]; field_simp
  have e2 : ((μ q : ℂ) * S0 * (starRingEnd ℂ) c).re =
      (if Squarefree q then (1 : ℝ) else 0) / q.totient * ‖S0‖ ^ 2 := by
    rw [hc, map_mul, map_div₀, Complex.conj_natCast]
    have : (μ q : ℂ) * S0 * ((starRingEnd ℂ) (μ q : ℂ) / q.totient * (starRingEnd ℂ) S0) =
        ((μ q : ℂ) * (starRingEnd ℂ) (μ q : ℂ)) * (S0 * (starRingEnd ℂ) S0) / q.totient := by ring
    rw [this, hm, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_div,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    ring
  rw [e1, e2]; ring

/-! ## The residuals after the principal character -/

theorem norm_sq_add3_le (u v w : ℂ) : ‖u + v + w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have h := norm_add₃_le (a := u) (b := v) (c := w)
  have h0 := norm_nonneg (u + v + w)
  nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖v‖ - ‖w‖), sq_nonneg (‖u‖ - ‖w‖),
    norm_nonneg u, norm_nonneg v, norm_nonneg w]

theorem card_Bset_eq (q : ℕ) : ((Bset q).card : ℝ) = q.totient := by
  unfold TernaryGoldbach.MinorArcs.Bset
  rw [Nat.totient]; congr 2; exact filter_congr fun b _ => Nat.coprime_comm

theorem norm_moebius_div_sq_le (q : ℕ) :
    ‖(μ q : ℂ) / q.totient‖ ^ 2 = (if Squarefree q then (1 : ℝ) else 0) / (q.totient : ℝ) ^ 2 := by
  rw [norm_div, div_pow, Complex.norm_natCast, Complex.norm_intCast, sq_abs, moebius_sq_eq]

/-- A generic residual bound: `Σ_b ‖S(α_b) − m A‖² ≤ 3(φ D² + E² + φ|m|² F²)` from the three pieces. -/
theorem sum_residual_le {q : ℕ} {T S' : ℝ → ℂ} {m A : ℂ} {β D E F : ℝ}
    (hD : ∀ α, ‖T α - S' α‖ ≤ D) (hD0 : 0 ≤ D)
    (hE : ∑ b ∈ Bset q, ‖S' ((b : ℝ) / q + β) - m * S' β‖ ^ 2 ≤ E ^ 2)
    (hF : ‖S' β - A‖ ≤ F) :
    ∑ b ∈ Bset q, ‖T ((b : ℝ) / q + β) - m * A‖ ^ 2 ≤
      3 * (q.totient * D ^ 2 + E ^ 2 + q.totient * ‖m‖ ^ 2 * F ^ 2) := by
  have hpt : ∀ b ∈ Bset q, ‖T ((b : ℝ) / q + β) - m * A‖ ^ 2 ≤
      3 * (D ^ 2 + ‖S' ((b : ℝ) / q + β) - m * S' β‖ ^ 2 + ‖m‖ ^ 2 * F ^ 2) := by
    intro b _
    have e : T ((b : ℝ) / q + β) - m * A = (T ((b : ℝ) / q + β) - S' ((b : ℝ) / q + β)) +
        (S' ((b : ℝ) / q + β) - m * S' β) + m * (S' β - A) := by ring
    rw [e]
    refine (norm_sq_add3_le _ _ _).trans ?_
    have h1 : ‖T ((b : ℝ) / q + β) - S' ((b : ℝ) / q + β)‖ ^ 2 ≤ D ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hD _) 2
    have h3 : ‖m * (S' β - A)‖ ^ 2 ≤ ‖m‖ ^ 2 * F ^ 2 := by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hF 2) (by positivity)
    linarith
  calc ∑ b ∈ Bset q, ‖T ((b : ℝ) / q + β) - m * A‖ ^ 2
      ≤ ∑ b ∈ Bset q, 3 * (D ^ 2 + ‖S' ((b : ℝ) / q + β) - m * S' β‖ ^ 2 + ‖m‖ ^ 2 * F ^ 2) :=
        sum_le_sum hpt
    _ = 3 * ((Bset q).card * D ^ 2 + ∑ b ∈ Bset q, ‖S' ((b : ℝ) / q + β) - m * S' β‖ ^ 2 +
          (Bset q).card * (‖m‖ ^ 2 * F ^ 2)) := by
        rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_const, sum_const, nsmul_eq_mul,
          nsmul_eq_mul]
    _ ≤ 3 * (q.totient * D ^ 2 + E ^ 2 + q.totient * ‖m‖ ^ 2 * F ^ 2) := by
        rw [card_Bset_eq]; nlinarith

/-- The principal-character residual for coprime-supported coefficients, over `Bset q`. -/
theorem sum_Bset_sq_sub_principal {q : ℕ} [NeZero q] {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q) (β : ℝ) :
    ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β) - (μ q : ℂ) / q.totient * expTsum a β‖ ^ 2 =
      ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 -
        (if Squarefree q then (1 : ℝ) else 0) / q.totient * ‖expTsum a β‖ ^ 2 := by
  rw [TernaryGoldbach.MinorArcs.sum_Bset_eq_units
      (fun t => ‖expTsum a t - (μ q : ℂ) / q.totient * expTsum a β‖ ^ 2) β,
    TernaryGoldbach.MinorArcs.sum_Bset_eq_units (fun t => ‖expTsum a t‖ ^ 2) β]
  exact sum_units_sq_sub_principal ha hcop β

theorem mem_Qset_bounds {q : ℕ} (hq : q ∈ Qset r₀) : 1 ≤ q ∧ (qt q : ℝ) ≤ 300000 ∧ q ≤ 300000 := by
  have hr₀ : r₀ = 150000 := rfl
  obtain ⟨hqI, hqt⟩ := Finset.mem_filter.1 hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hqI).1
  have hqt' : (qt q : ℝ) ≤ 300000 := by rw [hr₀] at hqt; linarith
  have hqq : q ≤ qt q := by unfold qt; split_ifs <;> omega
  have hq3 : q ≤ 300000 := by
    have : (q : ℝ) ≤ 300000 := le_trans (by exact_mod_cast hqq) hqt'
    exact_mod_cast this
  exact ⟨hq1, hqt', hq3⟩

theorem totient_bounds {q : ℕ} (hq1 : 1 ≤ q) (hq3 : q ≤ 300000) :
    (1 : ℝ) ≤ q.totient ∧ (q.totient : ℝ) ≤ 300000 := by
  have h1 : 1 ≤ q.totient := Nat.totient_pos.2 (by omega)
  have h2 : q.totient ≤ q := Nat.totient_le q
  constructor <;> [exact_mod_cast h1; exact_mod_cast h2.trans hq3]

theorem totient_mul_norm_sq_le {q : ℕ} (hq1 : 1 ≤ q) :
    (q.totient : ℝ) * ‖(μ q : ℂ) / q.totient‖ ^ 2 ≤ 1 := by
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [norm_moebius_div_sq_le]
  split_ifs
  · rw [mul_one_div, div_le_one (by positivity)]; nlinarith
  · simp

/-- **`η₊`**: `Σ_b |S_{η₊}(b/q + β) − μ(q)/φ(q) η̂₊(−βx) x|² ≤ 2.14·10⁻¹⁵ x²`. -/
theorem resid_plus {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq : q ∈ Qset r₀) {β : ℝ}
    (hβ : |β * x| ≤ 1200000 / qt q) :
    ∑ b ∈ Bset q, ‖S etaPlus x ((b : ℝ) / q + β) - (μ q : ℂ) / q.totient * (𝓕 etaPC (-(β * x)) * x)‖ ^ 2 ≤
      2.14e-15 * x ^ 2 := by
  obtain ⟨hq1, hqt', hq3⟩ := mem_Qset_bounds hq
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
  set a := coprimePart q (cP x)
  have ha : Summable fun n => ‖a n‖ :=
    (summable_cP hx0).of_nonneg_of_le (fun n => norm_nonneg _) (TernaryGoldbach.MinorArcs.norm_coprimePart_le q _)
  have hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q := fun n hn => by
    by_contra h; exact hn (by simp [a, TernaryGoldbach.MinorArcs.coprimePart, h])
  obtain ⟨⟨-, hup⟩, hpr⟩ := arc_chars hx hq1 hqt' hβ
  have hE : ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β) - (μ q : ℂ) / q.totient * expTsum a β‖ ^ 2 ≤
      (2.41e-8 * x) ^ 2 := by
    rw [sum_Bset_sq_sub_principal ha hcop]; linarith
  have h := sum_residual_le (T := S etaPlus x) (S' := expTsum a) (m := (μ q : ℂ) / q.totient)
    (A := 𝓕 etaPC (-(β * x)) * x) (q := q) (β := β) (D := 1e-15 * x)
    (fun α => norm_S_sub_coprime_le hx hq1 hq3 α) (by positivity) hE hpr
  have hφ := totient_bounds hq1 hq3
  have hm := totient_mul_norm_sq_le hq1
  refine h.trans ?_
  have h1 : (q.totient : ℝ) * (1e-15 * x) ^ 2 ≤ 300000 * (1e-15 * x) ^ 2 :=
    mul_le_mul_of_nonneg_right hφ.2 (by positivity)
  have h2 : (q.totient : ℝ) * ‖(μ q : ℂ) / q.totient‖ ^ 2 * (1.141e-8 * x) ^ 2 ≤ (1.141e-8 * x) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ (1.141e-8 * x) ^ 2)
    linarith
  nlinarith

/-- **`η_*`**: `|S_{η_*}(b/q + β) − μ(q)/φ(q) η̂(−βy) y|² ≤ 9.9·10⁻¹⁴ y²` (`y = x/κ`) for each `b`. -/
theorem resid_star {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq : q ∈ Qset r₀) {β : ℝ}
    (hβ : |β * x| ≤ 1200000 / qt q) {b : ℕ} (hb : b ∈ Bset q) :
    ‖S etaStar x ((b : ℝ) / q + β) - (μ q : ℂ) / q.totient *
        (𝓕 (fun u => (etaU u : ℂ)) (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ))‖ ^ 2 ≤ 9.9e-14 * (x / κ) ^ 2 := by
  obtain ⟨hq1, hqt', hq3⟩ := mem_Qset_bounds hq
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
  set y := x / κ with hy
  have hy0 : 0 < y := by rw [hy]; exact div_pos hx0 kappa_pos
  set a := coprimePart q (cU y)
  have ha : Summable fun n => ‖a n‖ :=
    (summable_cU hy0).of_nonneg_of_le (fun n => norm_nonneg _) (TernaryGoldbach.MinorArcs.norm_coprimePart_le q _)
  have hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q := fun n hn => by
    by_contra h; exact hn (by simp [a, TernaryGoldbach.MinorArcs.coprimePart, h])
  obtain ⟨⟨-, hup⟩, hpr⟩ := arc_chars_star hx hq1 hqt' hβ
  have hE : ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β) - (μ q : ℂ) / q.totient * expTsum a β‖ ^ 2 ≤
      (1.35e-7 * y) ^ 2 := by
    rw [sum_Bset_sq_sub_principal ha hcop]; linarith
  have h := sum_residual_le (T := S etaStar x) (S' := expTsum a) (m := (μ q : ℂ) / q.totient)
    (A := 𝓕 (fun u => (etaU u : ℂ)) (-(β * y)) * ((y : ℝ) : ℂ)) (q := q) (β := β) (D := 1e-12 * y)
    (fun α => norm_S_star_sub_coprime_le hx hq1 hq3 α) (by positivity) hE hpr
  have hφ := totient_bounds hq1 hq3
  have hm := totient_mul_norm_sq_le hq1
  have hsingle := Finset.single_le_sum
    (f := fun b : ℕ => ‖S etaStar x ((b : ℝ) / q + β) - (μ q : ℂ) / q.totient *
      (𝓕 (fun u => (etaU u : ℂ)) (-(β * y)) * ((y : ℝ) : ℂ))‖ ^ 2) (fun _ _ => by positivity) hb
  refine hsingle.trans (h.trans ?_)
  have h1 : (q.totient : ℝ) * (1e-12 * y) ^ 2 ≤ 300000 * (1e-12 * y) ^ 2 :=
    mul_le_mul_of_nonneg_right hφ.2 (by positivity)
  have h2 : (q.totient : ℝ) * ‖(μ q : ℂ) / q.totient‖ ^ 2 * (1.21e-7 * y) ^ 2 ≤ (1.21e-7 * y) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ (1.21e-7 * y) ^ 2)
    linarith
  nlinarith

/-! ## The per-point error of `Σ_b S₊² S_* e` -/

/-- With `S₊ = M₊ + R₊` (`Σ_b |R₊|² ≤ ρ²`) and `S_* = M_* + R_*` (`|R_*| ≤ U`):
`|Σ_b (S₊²S_* − M₊²M_*) e_b| ≤ U Σ_b |S₊|² + (ρ/2)(9|M_*|² + (2Σ_b |S₊|² + 2 #b |M₊|²)/9)`. -/
theorem sum_cubic_error {s : Finset ℕ} (Sp Ss eb : ℕ → ℂ) (Mp Ms : ℂ) {U ρ : ℝ} (hρ : 0 < ρ)
    (heb : ∀ b ∈ s, ‖eb b‖ = 1) (hU : ∀ b ∈ s, ‖Ss b - Ms‖ ≤ U)
    (hR : ∑ b ∈ s, ‖Sp b - Mp‖ ^ 2 ≤ ρ ^ 2) :
    ‖∑ b ∈ s, Sp b ^ 2 * Ss b * eb b - Mp ^ 2 * Ms * ∑ b ∈ s, eb b‖ ≤
      U * ∑ b ∈ s, ‖Sp b‖ ^ 2 +
        ρ / 2 * (9 * ‖Ms‖ ^ 2 + (2 * ∑ b ∈ s, ‖Sp b‖ ^ 2 + 2 * s.card * ‖Mp‖ ^ 2) / 9) := by
  have hpt : ∀ b ∈ s, ‖(Sp b ^ 2 * Ss b - Mp ^ 2 * Ms) * eb b‖ ≤
      U * ‖Sp b‖ ^ 2 + (9 / (2 * ρ) * ‖Ms‖ ^ 2 * ‖Sp b - Mp‖ ^ 2 + ρ / 18 * ‖Sp b + Mp‖ ^ 2) := by
    intro b hb
    rw [norm_mul, heb b hb, mul_one]
    have e : Sp b ^ 2 * Ss b - Mp ^ 2 * Ms = Sp b ^ 2 * (Ss b - Ms) + Ms * ((Sp b - Mp) * (Sp b + Mp)) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_pow]
    have h1 : ‖Sp b‖ ^ 2 * ‖Ss b - Ms‖ ≤ U * ‖Sp b‖ ^ 2 := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hU b hb) (by positivity)
    have h2 : ‖Ms‖ * (‖Sp b - Mp‖ * ‖Sp b + Mp‖) ≤
        9 / (2 * ρ) * ‖Ms‖ ^ 2 * ‖Sp b - Mp‖ ^ 2 + ρ / 18 * ‖Sp b + Mp‖ ^ 2 := by
      have hamgm : 0 ≤ (9 / ρ * (‖Ms‖ * ‖Sp b - Mp‖) - ‖Sp b + Mp‖) ^ 2 * (ρ / 18) := by positivity
      have e2 : (9 / ρ * (‖Ms‖ * ‖Sp b - Mp‖) - ‖Sp b + Mp‖) ^ 2 * (ρ / 18) =
          9 / (2 * ρ) * ‖Ms‖ ^ 2 * ‖Sp b - Mp‖ ^ 2 + ρ / 18 * ‖Sp b + Mp‖ ^ 2 -
            ‖Ms‖ * (‖Sp b - Mp‖ * ‖Sp b + Mp‖) := by
        field_simp; ring
      linarith
    linarith
  have hsum : ‖∑ b ∈ s, Sp b ^ 2 * Ss b * eb b - Mp ^ 2 * Ms * ∑ b ∈ s, eb b‖ ≤
      ∑ b ∈ s, (U * ‖Sp b‖ ^ 2 + (9 / (2 * ρ) * ‖Ms‖ ^ 2 * ‖Sp b - Mp‖ ^ 2 +
        ρ / 18 * ‖Sp b + Mp‖ ^ 2)) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum fun b hb => ?_)
    have := hpt b hb
    calc ‖Sp b ^ 2 * Ss b * eb b - Mp ^ 2 * Ms * eb b‖ = ‖(Sp b ^ 2 * Ss b - Mp ^ 2 * Ms) * eb b‖ := by
          congr 1; ring
      _ ≤ _ := this
  refine hsum.trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  have hsq : ∑ b ∈ s, ‖Sp b + Mp‖ ^ 2 ≤ 2 * ∑ b ∈ s, ‖Sp b‖ ^ 2 + 2 * s.card * ‖Mp‖ ^ 2 := by
    calc ∑ b ∈ s, ‖Sp b + Mp‖ ^ 2 ≤ ∑ b ∈ s, (2 * ‖Sp b‖ ^ 2 + 2 * ‖Mp‖ ^ 2) := by
          refine sum_le_sum fun b _ => ?_
          have := norm_add_le (Sp b) Mp
          nlinarith [norm_nonneg (Sp b + Mp), norm_nonneg (Sp b), norm_nonneg Mp,
            sq_nonneg (‖Sp b‖ - ‖Mp‖)]
      _ = 2 * ∑ b ∈ s, ‖Sp b‖ ^ 2 + 2 * s.card * ‖Mp‖ ^ 2 := by
          rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]; ring
  have hA : 9 / (2 * ρ) * ‖Ms‖ ^ 2 * ∑ b ∈ s, ‖Sp b - Mp‖ ^ 2 ≤ 9 / (2 * ρ) * ‖Ms‖ ^ 2 * ρ ^ 2 :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have hB : ρ / 18 * ∑ b ∈ s, ‖Sp b + Mp‖ ^ 2 ≤ ρ / 18 * (2 * ∑ b ∈ s, ‖Sp b‖ ^ 2 + 2 * s.card * ‖Mp‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have e3 : 9 / (2 * ρ) * ‖Ms‖ ^ 2 * ρ ^ 2 = ρ / 2 * (9 * ‖Ms‖ ^ 2) := by field_simp
  rw [e3] at hA
  nlinarith

end TernaryGoldbach.MajorArcs
