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

/-- **`η₊`**: `Σ_b |S_{η₊}(b/q + β) − μ(q)/φ(q) η̂₊(−βx) x|² ≤ 7.83·10⁻¹³ x²`. -/
theorem resid_plus {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq : q ∈ Qset r₀) {β : ℝ}
    (hβ : |β * x| ≤ 1200000 / qt q) :
    ∑ b ∈ Bset q, ‖S etaPlus x ((b : ℝ) / q + β) - (μ q : ℂ) / q.totient * (𝓕 etaPC (-(β * x)) * x)‖ ^ 2 ≤
      7.83e-13 * x ^ 2 := by
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
      (4.25e-7 * x) ^ 2 := by
    rw [sum_Bset_sq_sub_principal ha hcop]; linarith
  have h := sum_residual_le (T := S etaPlus x) (S' := expTsum a) (m := (μ q : ℂ) / q.totient)
    (A := 𝓕 etaPC (-(β * x)) * x) (q := q) (β := β) (D := 1e-15 * x)
    (fun α => norm_S_sub_coprime_le hx hq1 hq3 α) (by positivity) hE hpr
  have hφ := totient_bounds hq1 hq3
  have hm := totient_mul_norm_sq_le hq1
  refine h.trans ?_
  have h1 : (q.totient : ℝ) * (1e-15 * x) ^ 2 ≤ 300000 * (1e-15 * x) ^ 2 :=
    mul_le_mul_of_nonneg_right hφ.2 (by positivity)
  have h2 : (q.totient : ℝ) * ‖(μ q : ℂ) / q.totient‖ ^ 2 * (2.83e-7 * x) ^ 2 ≤ (2.83e-7 * x) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ (2.83e-7 * x) ^ 2)
    linarith
  nlinarith

/-- **`η_*`**: `|S_{η_*}(b/q + β) − μ(q)/φ(q) η̂(−βy) y|² ≤ 1.34·10⁻¹¹ y²` (`y = x/κ`) for each `b`. -/
theorem resid_star {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq : q ∈ Qset r₀) {β : ℝ}
    (hβ : |β * x| ≤ 1200000 / qt q) {b : ℕ} (hb : b ∈ Bset q) :
    ‖S etaStar x ((b : ℝ) / q + β) - (μ q : ℂ) / q.totient *
        (𝓕 (fun u => (etaU u : ℂ)) (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ))‖ ^ 2 ≤ 1.34e-11 * (x / κ) ^ 2 := by
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
      (1.49e-6 * y) ^ 2 := by
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
  have h2 : (q.totient : ℝ) * ‖(μ q : ℂ) / q.totient‖ ^ 2 * (1.49e-6 * y) ^ 2 ≤ (1.49e-6 * y) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ (1.49e-6 * y) ^ 2)
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

/-! ## The main term -/

/-- `η = η₂ *_M φ` (`etaU`) as a complex function. -/
noncomputable def etaUC (u : ℝ) : ℂ := (etaU u : ℂ)

theorem fourier_etaSC (ξ : ℝ) : 𝓕 etaSC ξ = (κ⁻¹ : ℂ) * 𝓕 etaUC (ξ / κ) := by
  have h := TernaryGoldbach.fourier_comp_affine etaUC kappa_pos 0 ξ
  simp only [add_zero, zero_mul, zero_div, TernaryGoldbach.e_zero, one_mul] at h
  push_cast at h
  rw [← h]; rfl

/-- `η̂(−βy) y = η̂_*(−βx) x` (`y = x/κ`). -/
theorem As_eq {x : ℝ} (β : ℝ) :
    𝓕 (fun u => (etaU u : ℂ)) (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ) = 𝓕 etaSC (-(β * x)) * x := by
  rw [fourier_etaSC]
  have hκ : (κ : ℂ) ≠ 0 := by exact_mod_cast kappa_pos.ne'
  have e1 : -(β * x) / κ = -(β * (x / κ)) := by ring
  rw [e1]; push_cast; field_simp; rw [mul_comm]; rfl

theorem e_eq_cexp (N β x : ℝ) (hx : x ≠ 0) :
    e (-(N * β)) = Complex.exp (↑(2 * π * (-(β * x)) * (N / x)) * Complex.I) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  unfold TernaryGoldbach.e; congr 1; push_cast; field_simp

/-- **The completed main term**: `∫_ℝ (η̂◦(−βx)x)² η̂_*(−βx)x e(−Nβ) dβ = x² C_{η◦,η_*}(N/x)`. -/
theorem integral_full_main {x : ℝ} (hx : 0 < x) (N : ℝ) :
    ∫ β, (𝓕 etaOC (-(β * x)) * x) ^ 2 * (𝓕 etaSC (-(β * x)) * x) * e (-(N * β)) =
      (x : ℂ) ^ 2 * (Cmain (N / x) : ℂ) := by
  set g : ℝ → ℂ := fun ξ => Complex.exp (↑(2 * π * ξ * (N / x)) * Complex.I) *
    (𝓕 etaOC ξ * 𝓕 etaOC ξ * 𝓕 etaSC ξ) with hg
  have hid := fourier_identity (N / x)
  have hpt : ∀ β : ℝ, (𝓕 etaOC (-(β * x)) * x) ^ 2 * (𝓕 etaSC (-(β * x)) * x) * e (-(N * β)) =
      (x : ℂ) ^ 3 * g ((-x) * β) := by
    intro β
    simp only [hg]
    rw [e_eq_cexp N β x hx.ne', show (-x) * β = -(β * x) by ring]
    ring
  simp_rw [hpt]
  have hid' : ∫ ξ, g ξ = (Cmain (N / x) : ℂ) := hid
  rw [integral_const_mul, Measure.integral_comp_mul_left g (-x), hid']
  rw [abs_inv, abs_neg, abs_of_pos hx, Complex.real_smul]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast; field_simp

/-! ## `‖η◦‖₂` and `‖η₊ − η◦‖₂` -/

theorem integral_sq_etaO_bounds :
    0.63965 ≤ ∫ t, etaO t ^ 2 ∧ ∫ t, etaO t ^ 2 ≤ 0.6408 := by
  have hP := integral_sq_etaPlus_bounds
  have hD := integral_sq_etaPlus_sub_etaO_le'
  have iP : Integrable fun t => etaPlus t ^ 2 :=
    ((memLp_two_iff_integrable_sq_norm measurable_etaPlus.aestronglyMeasurable).1 memLp_etaPlus).congr
      (Filter.Eventually.of_forall fun t => by simp [Real.norm_eq_abs, sq_abs])
  have iD : Integrable fun t => (etaPlus t - etaO t) ^ 2 := by
    have h := memLp_etaPlus.sub memLp_etaO
    exact ((memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h).congr
      (Filter.Eventually.of_forall fun t => by simp [Real.norm_eq_abs, sq_abs])
  constructor
  · -- `η◦² ≥ (1 − t) η₊² − (1/t)(η₊ − η◦)²`, `t = 5·10⁻⁴`
    have hpt : ∀ t, (1 - 5e-4) * etaPlus t ^ 2 - 2000 * (etaPlus t - etaO t) ^ 2 ≤ etaO t ^ 2 := by
      intro t; nlinarith [sq_nonneg (5e-4 * etaPlus t - (etaPlus t - etaO t)), sq_nonneg (etaPlus t)]
    have iL : Integrable fun t => (1 - 5e-4) * etaPlus t ^ 2 - 2000 * (etaPlus t - etaO t) ^ 2 :=
      (iP.const_mul _).sub (iD.const_mul _)
    have := integral_mono iL integrable_etaO_sq hpt
    rw [integral_sub (iP.const_mul _) (iD.const_mul _), integral_const_mul, integral_const_mul] at this
    linarith [hP.1]
  · have hpt : ∀ t, etaO t ^ 2 ≤ (1 + 5e-4) * etaPlus t ^ 2 + 2001 * (etaPlus t - etaO t) ^ 2 := by
      intro t; nlinarith [sq_nonneg (5e-4 * etaPlus t + (etaPlus t - etaO t)), sq_nonneg (etaPlus t)]
    have iU : Integrable fun t => (1 + 5e-4) * etaPlus t ^ 2 + 2001 * (etaPlus t - etaO t) ^ 2 :=
      (iP.const_mul _).add (iD.const_mul _)
    have := integral_mono integrable_etaO_sq iU hpt
    rw [integral_add (iP.const_mul _) (iD.const_mul _), integral_const_mul, integral_const_mul] at this
    norm_num at hD
    linarith [hP.2]

/-! ## `L²` facts for the main term -/

theorem etaU_le_six (u : ℝ) : etaU u ≤ 6.2 := by
  rcases le_or_gt u 0 with h | h
  · rw [etaU_of_nonpos h]; norm_num
  · exact (le_abs_self _).trans (TernaryGoldbach.MinorArcs.abs_etaU_le_const h)

theorem measurable_etaU : Measurable etaU := by
  have : etaU = fun u => ∫ w in Ioi (0:ℝ), TernaryGoldbach.Helfgott.eta2 (u / w) *
      TernaryGoldbach.Helfgott.phi w / w := rfl
  rw [this]
  have h : Measurable (Function.uncurry fun u w : ℝ => TernaryGoldbach.Helfgott.eta2 (u / w) *
      TernaryGoldbach.Helfgott.phi w / w) :=
    ((TernaryGoldbach.Helfgott.continuous_eta2.measurable.comp (measurable_fst.div measurable_snd)).mul
      (continuous_phi.measurable.comp measurable_snd)).div measurable_snd
  exact (h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioi 0))).measurable

theorem integrable_etaU_sq : Integrable fun u => etaU u ^ 2 := by
  refine Integrable.mono' (integrable_etaU.const_mul 6.2) (measurable_etaU.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right (etaU_le_six u) (etaU_nonneg u)

theorem integral_etaU_sq_le : ∫ u, etaU u ^ 2 ≤ 7.78 := by
  have h1 : ∫ u, etaU u ^ 2 ≤ ∫ u, 6.2 * etaU u :=
    integral_mono integrable_etaU_sq (integrable_etaU.const_mul 6.2) fun u => by
      rw [sq]; exact mul_le_mul_of_nonneg_right (etaU_le_six u) (etaU_nonneg u)
  rw [integral_const_mul, integral_etaU] at h1
  have : √(π / 2) ≤ 1.2534 := by
    rw [Real.sqrt_le_left (by norm_num)]; have := Real.pi_lt_d4; linarith
  linarith

theorem integrable_etaUC : Integrable etaUC := integrable_etaU.ofReal

theorem memLp_etaUC : MemLp etaUC 2 := by
  refine (memLp_two_iff_integrable_sq_norm integrable_etaUC.aestronglyMeasurable).2 ?_
  refine integrable_etaU_sq.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [etaUC, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem integral_norm_sq_fourier_etaUC_le : ∫ ξ, ‖𝓕 etaUC ξ‖ ^ 2 ≤ 7.78 := by
  rw [TernaryGoldbach.integral_norm_sq_fourier integrable_etaUC memLp_etaUC]
  have : (fun u => ‖etaUC u‖ ^ 2) = fun u => etaU u ^ 2 := by
    ext u; simp [etaUC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [this]; exact integral_etaU_sq_le

theorem norm_fourier_etaUC_le (ξ : ℝ) : ‖𝓕 etaUC ξ‖ ≤ 1.2534 := by
  refine (Real.norm_fourier_le_integral_norm etaUC ξ).trans ?_
  have : (fun u => ‖etaUC u‖) = etaU := by
    ext u; simp [etaUC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (etaU_nonneg u)]
  rw [this, integral_etaU, Real.sqrt_le_left (by norm_num)]
  have := Real.pi_lt_d4; linarith

/-- `∫_ℝ |f((−c)β)|² dβ = (1/c) ∫ |f|²` for `c > 0`. -/
theorem integral_norm_sq_comp_mul {f : ℝ → ℂ} {c : ℝ} (hc : 0 < c) :
    ∫ β, ‖f (-(β * c))‖ ^ 2 = c⁻¹ * ∫ ξ, ‖f ξ‖ ^ 2 := by
  have h := Measure.integral_comp_mul_left (fun ξ => ‖f ξ‖ ^ 2) (-c)
  rw [show (fun β => ‖f (-(β * c))‖ ^ 2) = fun β => ‖f (-c * β)‖ ^ 2 by ext β; ring_nf, h,
    abs_inv, abs_neg, abs_of_pos hc, smul_eq_mul]

theorem integral_sq_fourier_sub_le :
    ∫ ξ, ‖𝓕 etaPC ξ - 𝓕 etaOC ξ‖ ^ 2 ≤ 1.15e-7 := by
  set D : ℝ → ℂ := fun t => etaPC t - etaOC t
  have hD1 : Integrable D := integrable_etaPC.sub integrable_etaOC
  have hD2 : MemLp D 2 := memLp_etaPC.sub memLp_etaOC
  have e : (fun ξ => ‖𝓕 etaPC ξ - 𝓕 etaOC ξ‖ ^ 2) = fun ξ => ‖𝓕 D ξ‖ ^ 2 := by
    ext ξ; rw [fourier_sub_of_integrable integrable_etaPC integrable_etaOC]
  rw [e, TernaryGoldbach.integral_norm_sq_fourier hD1 hD2]
  have : (fun t => ‖D t‖ ^ 2) = fun t => (etaPlus t - etaO t) ^ 2 := by
    ext t; simp only [D, etaPC, etaOC]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [this]
  have := integral_sq_etaPlus_sub_etaO_le'
  norm_num at this ⊢; linarith

theorem integral_sq_fourier_add_le :
    ∫ ξ, ‖𝓕 etaPC ξ + 𝓕 etaOC ξ‖ ^ 2 ≤ 2.5621 := by
  have iP := integrable_norm_sq_fourier integrable_etaPC memLp_etaPC
  have iO := integrable_norm_sq_fourier integrable_etaOC memLp_etaOC
  have hpt : ∀ ξ, ‖𝓕 etaPC ξ + 𝓕 etaOC ξ‖ ^ 2 ≤ 2 * ‖𝓕 etaPC ξ‖ ^ 2 + 2 * ‖𝓕 etaOC ξ‖ ^ 2 := by
    intro ξ
    have := norm_add_le (𝓕 etaPC ξ) (𝓕 etaOC ξ)
    nlinarith [norm_nonneg (𝓕 etaPC ξ + 𝓕 etaOC ξ), norm_nonneg (𝓕 etaPC ξ), norm_nonneg (𝓕 etaOC ξ),
      sq_nonneg (‖𝓕 etaPC ξ‖ - ‖𝓕 etaOC ξ‖)]
  have i2 : Integrable fun ξ => 2 * ‖𝓕 etaPC ξ‖ ^ 2 + 2 * ‖𝓕 etaOC ξ‖ ^ 2 :=
    (iP.const_mul 2).add (iO.const_mul 2)
  have hint : Integrable fun ξ => ‖𝓕 etaPC ξ + 𝓕 etaOC ξ‖ ^ 2 :=
    i2.mono' (((continuous_fourier_etaPC.add (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) integrable_etaOC)).norm.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt ξ)
  have h := integral_mono hint i2 hpt
  rw [integral_add (iP.const_mul 2) (iO.const_mul 2), integral_const_mul, integral_const_mul,
    integral_norm_sq_fourier_etaPC, TernaryGoldbach.integral_norm_sq_fourier integrable_etaOC memLp_etaOC] at h
  have e : (fun t => ‖etaOC t‖ ^ 2) = fun t => etaO t ^ 2 := by
    ext t; simp [etaOC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e] at h
  linarith [integral_sq_etaPlus_bounds.2, integral_sq_etaO_bounds.2]

/-! ## The main term of one modulus -/

theorem norm_fourier_etaSC_le' (ξ : ℝ) : ‖𝓕 etaSC ξ‖ ≤ 0.02558 := by
  rw [fourier_etaSC, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos kappa_pos]
  have h := norm_fourier_etaUC_le (ξ / κ)
  rw [TernaryGoldbach.Helfgott.κ]
  calc (49 : ℝ)⁻¹ * ‖𝓕 etaUC (ξ / κ)‖ ≤ 49⁻¹ * 1.2534 := by gcongr
    _ ≤ 0.02558 := by norm_num

theorem continuous_fourier_etaOC' : Continuous (𝓕 etaOC) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) integrable_etaOC

theorem continuous_fourier_etaSC' : Continuous (𝓕 etaSC) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) integrable_etaSC

theorem integral_indicator_comp_mul {f : ℝ → ℝ} {c w : ℝ} (hc : 0 < c) :
    ∫ β, {β : ℝ | w ≤ |β|}.indicator (fun β => f (-(β * c))) β =
      c⁻¹ * ∫ ξ in {ξ : ℝ | w * c ≤ |ξ|}, f ξ := by
  rw [← integral_indicator ((isClosed_le continuous_const continuous_abs).measurableSet)]
  have h := Measure.integral_comp_mul_left ({ξ : ℝ | w * c ≤ |ξ|}.indicator f) (-c)
  rw [abs_inv, abs_neg, abs_of_pos hc, smul_eq_mul] at h
  rw [← h]
  congr 1; ext β
  simp only [indicator, mem_setOf_eq]
  have e : |-c * β| = |β| * c := by rw [abs_mul, abs_neg, abs_of_pos hc, mul_comm]
  rw [e, show -(β * c) = -c * β by ring]
  by_cases h1 : w ≤ |β|
  · rw [if_pos h1, if_pos (by nlinarith)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (by nlinarith [abs_nonneg β]))]

set_option maxHeartbeats 2000000 in
/-- **The main term of one modulus**: `‖∫_{−w}^{w} (η̂₊(−βx)x)² η̂_*(−βx)x e(−Nβ) dβ − x² C(N/x)‖ ≤
2.03·10⁻⁵ x²` for `wx ≥ 4`. -/
theorem main_comparison {x : ℝ} (hx : 0 < x) {w : ℝ} (hw : 0 ≤ w) (hwx : 4 ≤ w * x) (N : ℝ) :
    ‖(∫ β in -w..w, (𝓕 etaPC (-(β * x)) * x) ^ 2 * (𝓕 etaSC (-(β * x)) * x) * e (-(N * β))) -
        (x : ℂ) ^ 2 * (Cmain (N / x) : ℂ)‖ ≤ 2.03e-5 * x ^ 2 := by
  set P : ℝ → ℂ := fun β => 𝓕 etaPC (-(β * x)) * x with hP
  set O : ℝ → ℂ := fun β => 𝓕 etaOC (-(β * x)) * x with hO
  set Sx : ℝ → ℂ := fun β => 𝓕 etaSC (-(β * x)) * x with hSx
  set E : ℝ → ℂ := fun β => e (-(N * β)) with hE
  have hPc : Continuous P := (continuous_fourier_etaPC.comp (by fun_prop)).mul continuous_const
  have hOc : Continuous O := (continuous_fourier_etaOC'.comp (by fun_prop)).mul continuous_const
  have hSc : Continuous Sx := (continuous_fourier_etaSC'.comp (by fun_prop)).mul continuous_const
  have hEc : Continuous E := TernaryGoldbach.continuous_e.comp (by fun_prop)
  have hEn : ∀ β, ‖E β‖ = 1 := fun β => TernaryGoldbach.norm_e _
  have hSn : ∀ β, ‖Sx β‖ ≤ 0.02558 * x := fun β => by
    simp only [hSx]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    exact mul_le_mul_of_nonneg_right (norm_fourier_etaSC_le' _) hx.le
  -- `L²` integrals after the substitution `ξ = −βx`
  have iO2 : Integrable fun β => ‖O β‖ ^ 2 := by
    have h := (integrable_norm_sq_fourier integrable_etaOC memLp_etaOC).comp_mul_left' (neg_ne_zero.2 hx.ne')
    refine (h.const_mul (x ^ 2)).congr (Filter.Eventually.of_forall fun β => ?_)
    simp only [Function.comp, hO, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    ring_nf
  have iPm : Integrable fun β => ‖P β - O β‖ ^ 2 := by
    have hc : Continuous fun ξ => ‖𝓕 etaPC ξ - 𝓕 etaOC ξ‖ ^ 2 :=
      ((continuous_fourier_etaPC.sub continuous_fourier_etaOC').norm.pow 2)
    have hi : Integrable fun ξ => ‖𝓕 etaPC ξ - 𝓕 etaOC ξ‖ ^ 2 := by
      have iP := integrable_norm_sq_fourier integrable_etaPC memLp_etaPC
      have iO := integrable_norm_sq_fourier integrable_etaOC memLp_etaOC
      have i2 : Integrable fun ξ => 2 * ‖𝓕 etaPC ξ‖ ^ 2 + 2 * ‖𝓕 etaOC ξ‖ ^ 2 :=
        (iP.const_mul 2).add (iO.const_mul 2)
      refine i2.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := norm_sub_le (𝓕 etaPC ξ) (𝓕 etaOC ξ)
      nlinarith [norm_nonneg (𝓕 etaPC ξ - 𝓕 etaOC ξ), norm_nonneg (𝓕 etaPC ξ),
        norm_nonneg (𝓕 etaOC ξ), sq_nonneg (‖𝓕 etaPC ξ‖ - ‖𝓕 etaOC ξ‖)]
    have h := hi.comp_mul_left' (neg_ne_zero.2 hx.ne')
    refine (h.const_mul (x ^ 2)).congr (Filter.Eventually.of_forall fun β => ?_)
    simp only [Function.comp, hO, hP, ← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx]
    ring_nf
  have iPp : Integrable fun β => ‖P β + O β‖ ^ 2 := by
    have iP2 : Integrable fun β => ‖P β‖ ^ 2 := by
      have h := (integrable_norm_sq_fourier integrable_etaPC memLp_etaPC).comp_mul_left'
        (neg_ne_zero.2 hx.ne')
      refine (h.const_mul (x ^ 2)).congr (Filter.Eventually.of_forall fun β => ?_)
      simp only [Function.comp, hP, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      ring_nf
    have i2 : Integrable fun β => 2 * ‖P β‖ ^ 2 + 2 * ‖O β‖ ^ 2 := (iP2.const_mul 2).add (iO2.const_mul 2)
    refine i2.mono' ((hPc.add hOc).norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := norm_add_le (P β) (O β)
    nlinarith [norm_nonneg (P β + O β), norm_nonneg (P β), norm_nonneg (O β), sq_nonneg (‖P β‖ - ‖O β‖)]
  have hIPm : ∫ β, ‖P β - O β‖ ^ 2 ≤ x * 1.15e-7 := by
    have e : (fun β => ‖P β - O β‖ ^ 2) =
        fun β => x ^ 2 * ‖𝓕 etaPC (-(β * x)) - 𝓕 etaOC (-(β * x))‖ ^ 2 := by
      ext β; simp only [hP, hO, ← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx]; ring
    rw [e, integral_const_mul, integral_norm_sq_comp_mul (f := fun ξ => 𝓕 etaPC ξ - 𝓕 etaOC ξ) hx]
    have := integral_sq_fourier_sub_le
    have hxx : x ^ 2 * x⁻¹ = x := by field_simp
    calc x ^ 2 * (x⁻¹ * ∫ ξ, ‖𝓕 etaPC ξ - 𝓕 etaOC ξ‖ ^ 2) = x * ∫ ξ, ‖𝓕 etaPC ξ - 𝓕 etaOC ξ‖ ^ 2 := by
          rw [← mul_assoc, hxx]
      _ ≤ x * 1.15e-7 := mul_le_mul_of_nonneg_left this hx.le
  have hIPp : ∫ β, ‖P β + O β‖ ^ 2 ≤ x * 2.5621 := by
    have e : (fun β => ‖P β + O β‖ ^ 2) =
        fun β => x ^ 2 * ‖𝓕 etaPC (-(β * x)) + 𝓕 etaOC (-(β * x))‖ ^ 2 := by
      ext β; simp only [hP, hO, ← add_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx]; ring
    rw [e, integral_const_mul, integral_norm_sq_comp_mul (f := fun ξ => 𝓕 etaPC ξ + 𝓕 etaOC ξ) hx]
    have := integral_sq_fourier_add_le
    have hxx : x ^ 2 * x⁻¹ = x := by field_simp
    calc x ^ 2 * (x⁻¹ * ∫ ξ, ‖𝓕 etaPC ξ + 𝓕 etaOC ξ‖ ^ 2) = x * ∫ ξ, ‖𝓕 etaPC ξ + 𝓕 etaOC ξ‖ ^ 2 := by
          rw [← mul_assoc, hxx]
      _ ≤ x * 2.5621 := mul_le_mul_of_nonneg_left this hx.le
  have hItail' : ∫ β in {β : ℝ | w ≤ |β|}, ‖O β‖ ^ 2 ≤ x * 2.47e-4 := by
    have h := integral_indicator_comp_mul (f := fun ξ => ‖𝓕 etaOC ξ‖ ^ 2) (w := w) hx
    rw [integral_indicator ((isClosed_le continuous_const continuous_abs).measurableSet)] at h
    have e : (fun β => ‖O β‖ ^ 2) = fun β => x ^ 2 * ‖𝓕 etaOC (-(β * x))‖ ^ 2 := by
      ext β; simp only [hO, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; ring
    rw [e, integral_const_mul, h]
    have ht := tail_etaO_le (T := w * x) (by linarith)
    have hπ := Real.pi_gt_d2
    have hT : 98 / (2 * π * (w * x)) ^ 4 ≤ 2.47e-4 := by
      have h1 : (25.12 : ℝ) ≤ 2 * π * (w * x) := by nlinarith
      have h2 : (25.12 : ℝ) ^ 4 ≤ (2 * π * (w * x)) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
      calc 98 / (2 * π * (w * x)) ^ 4 ≤ 98 / 25.12 ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
        _ ≤ 2.47e-4 := by norm_num
    have hxx : x ^ 2 * x⁻¹ = x := by field_simp
    calc x ^ 2 * (x⁻¹ * ∫ ξ in {ξ : ℝ | w * x ≤ |ξ|}, ‖𝓕 etaOC ξ‖ ^ 2) =
          x * ∫ ξ in {ξ : ℝ | w * x ≤ |ξ|}, ‖𝓕 etaOC ξ‖ ^ 2 := by rw [← mul_assoc, hxx]
      _ ≤ x * 2.47e-4 := mul_le_mul_of_nonneg_left (ht.trans hT) hx.le
  -- the decomposition
  set F : ℝ → ℂ := fun β => O β ^ 2 * Sx β * E β with hF
  set G : ℝ → ℂ := fun β => P β ^ 2 * Sx β * E β with hG
  have hFc : Continuous F := ((hOc.pow 2).mul hSc).mul hEc
  have hGc : Continuous G := ((hPc.pow 2).mul hSc).mul hEc
  have hFn : ∀ β, ‖F β‖ ≤ 0.02558 * x * ‖O β‖ ^ 2 := fun β => by
    simp only [hF, norm_mul, norm_pow, hEn, mul_one]
    rw [mul_comm (0.02558 * x)]; exact mul_le_mul_of_nonneg_left (hSn β) (by positivity)
  have hFi : Integrable F := (iO2.const_mul (0.02558 * x)).mono' hFc.aestronglyMeasurable
    (Filter.Eventually.of_forall hFn)
  have hfull : ∫ β, F β = (x : ℂ) ^ 2 * (Cmain (N / x) : ℂ) := integral_full_main hx N
  have hw' : -w ≤ w := by linarith
  have hGi : IntegrableOn G (Ioc (-w) w) := (hGc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hFi' : IntegrableOn F (Ioc (-w) w) := hFi.integrableOn
  show ‖(∫ β in -w..w, G β) - (x : ℂ) ^ 2 * (Cmain (N / x) : ℂ)‖ ≤ 2.03e-5 * x ^ 2
  rw [← hfull, intervalIntegral.integral_of_le hw', ← integral_add_compl measurableSet_Ioc hFi]
  have e : (∫ β in Ioc (-w) w, G β) - ((∫ β in Ioc (-w) w, F β) + ∫ β in (Ioc (-w) w)ᶜ, F β) =
      (∫ β in Ioc (-w) w, (G β - F β)) - ∫ β in (Ioc (-w) w)ᶜ, F β := by
    rw [integral_sub hGi hFi']; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  -- the change of weight
  have hAM : ∀ β, ‖G β - F β‖ ≤
      0.02558 * x * (2360 * ‖P β - O β‖ ^ 2 + 1 / 9440 * ‖P β + O β‖ ^ 2) := by
    intro β
    have e1 : G β - F β = (P β - O β) * (P β + O β) * Sx β * E β := by simp only [hG, hF]; ring
    rw [e1, norm_mul, norm_mul, norm_mul, hEn, mul_one]
    have h1 : ‖P β - O β‖ * ‖P β + O β‖ ≤ 2360 * ‖P β - O β‖ ^ 2 + 1 / 9440 * ‖P β + O β‖ ^ 2 := by
      nlinarith [sq_nonneg (4720 * ‖P β - O β‖ - ‖P β + O β‖)]
    calc ‖P β - O β‖ * ‖P β + O β‖ * ‖Sx β‖ ≤
          (2360 * ‖P β - O β‖ ^ 2 + 1 / 9440 * ‖P β + O β‖ ^ 2) * (0.02558 * x) :=
          mul_le_mul h1 (hSn β) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hgi : Integrable fun β => 0.02558 * x * (2360 * ‖P β - O β‖ ^ 2 + 1 / 9440 * ‖P β + O β‖ ^ 2) :=
    ((iPm.const_mul 2360).add (iPp.const_mul (1 / 9440))).const_mul _
  have hI1 : ‖∫ β in Ioc (-w) w, (G β - F β)‖ ≤ 1.3886e-5 * x ^ 2 := by
    refine (norm_integral_le_of_norm_le hgi.integrableOn (Filter.Eventually.of_forall hAM)).trans ?_
    refine (setIntegral_le_integral hgi (Filter.Eventually.of_forall fun β => by
      simp only [Pi.zero_apply]; positivity)).trans ?_
    rw [integral_const_mul, integral_add (iPm.const_mul 2360) (iPp.const_mul (1 / 9440)),
      integral_const_mul, integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hIPm hx.le, mul_le_mul_of_nonneg_left hIPp hx.le]
  -- the tail
  have hsub : (Ioc (-w) w)ᶜ ⊆ {β : ℝ | w ≤ |β|} := fun β hβ => by
    rw [mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hβ
    show w ≤ |β|
    rcases hβ with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hI2 : ‖∫ β in (Ioc (-w) w)ᶜ, F β‖ ≤ 6.3183e-6 * x ^ 2 := by
    have hOi : Integrable fun β => 0.02558 * x * ‖O β‖ ^ 2 := iO2.const_mul _
    refine (norm_integral_le_of_norm_le hOi.integrableOn (Filter.Eventually.of_forall hFn)).trans ?_
    refine (setIntegral_mono_set (t := {β : ℝ | w ≤ |β|}) hOi.integrableOn
      (Filter.Eventually.of_forall fun β => by simp only [Pi.zero_apply]; positivity)
      (Filter.Eventually.of_forall hsub)).trans ?_
    rw [integral_const_mul]
    have h := mul_le_mul_of_nonneg_left hItail' (by positivity : (0:ℝ) ≤ 0.02558 * x)
    calc 0.02558 * x * ∫ β in {β : ℝ | w ≤ |β|}, ‖O β‖ ^ 2 ≤ 0.02558 * x * (x * 2.47e-4) := h
      _ ≤ 6.3183e-6 * x ^ 2 := by nlinarith
  calc _ ≤ 1.3886e-5 * x ^ 2 + 6.3183e-6 * x ^ 2 := add_le_add hI1 hI2
    _ ≤ 2.03e-5 * x ^ 2 := by nlinarith

/-! ## The arcs of one modulus -/

theorem abs_coefN_le (N : ℕ) {q : ℕ} (hq : 1 ≤ q) : |coefN N q| ≤ mPhi2 q := by
  have h := coef_eq (N := N) hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hμ : ‖(μ q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hsum : ‖∑ b ∈ Bset q, e (-(N * ((b : ℝ) / q)))‖ ≤ q.totient := by
    refine (norm_sum_le _ _).trans ?_
    simp only [TernaryGoldbach.norm_e, sum_const, nsmul_eq_mul, mul_one]
    rw [card_Bset_eq]
  have hm : ‖(μ q : ℂ) / q.totient‖ = ‖(μ q : ℂ)‖ / q.totient := by
    rw [norm_div, Complex.norm_natCast]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← h]
  calc ‖((μ q : ℂ) / q.totient) ^ 3 * ∑ b ∈ Bset q, e (-(N * ((b : ℝ) / q)))‖
      ≤ ‖(μ q : ℂ) / q.totient‖ ^ 3 * q.totient := by
        rw [norm_mul, norm_pow]; exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖(μ q : ℂ) / q.totient‖ ^ 2 * (‖(μ q : ℂ)‖ / q.totient * q.totient) := by rw [hm]; ring
    _ = ‖(μ q : ℂ) / q.totient‖ ^ 2 * ‖(μ q : ℂ)‖ := by rw [div_mul_cancel₀ _ hφ.ne']
    _ ≤ ‖(μ q : ℂ) / q.totient‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hμ (by positivity)
    _ = mPhi2 q := by rw [mul_one, norm_moebius_div_sq_le]; rfl

theorem setIntegral_arc_eq_C {g : ℝ → ℂ} {δ₀ R x : ℝ} {q b : ℕ} (hw : 0 ≤ wrad δ₀ R x q) :
    ∫ y in arc δ₀ R x q b, g y =
      ∫ β in -wrad δ₀ R x q..wrad δ₀ R x q, g ((b : ℝ) / q + β) := by
  set w := wrad δ₀ R x q
  rw [intervalIntegral.integral_comp_add_left, arc, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), sub_eq_add_neg]

theorem continuous_S_etaPlus {x : ℝ} (hx : 0 < x) : Continuous (S etaPlus x) := by
  have : S etaPlus x = expTsum (cP x) := funext fun α => S_etaPlus_eq_expTsum x α
  rw [this]; exact TernaryGoldbach.continuous_expTsum (summable_cP hx)

theorem continuous_S_etaStar {x : ℝ} (hx : 0 < x) : Continuous (S etaStar x) := by
  have : S etaStar x = expTsum (cU (x / κ)) := funext fun α => S_etaStar_eq_cU hx α
  rw [this]; exact TernaryGoldbach.continuous_expTsum (summable_cU (div_pos hx kappa_pos))

/-- The integrand `S_{η₊}(α)² S_{η_*}(α) e(−Nα)` at a general `x`. -/
noncomputable def fI (N : ℕ) (x α : ℝ) : ℂ := S etaPlus x α ^ 2 * S etaStar x α * e (-(N * α))

theorem continuous_fI (N : ℕ) {x : ℝ} (hx : 0 < x) : Continuous (fI N x) :=
  (((continuous_S_etaPlus hx).pow 2).mul (continuous_S_etaStar hx)).mul
    (TernaryGoldbach.continuous_e.comp (by fun_prop))

/-- **The pointwise estimate** at `α = b/q + β`, summed over `b`. -/
theorem pointwise_bound (N : ℕ) {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq : q ∈ Qset r₀) {β : ℝ}
    (hβ : |β * x| ≤ 1200000 / qt q) :
    ‖∑ b ∈ Bset q, fI N x ((b : ℝ) / q + β) -
        (coefN N q : ℂ) * ((𝓕 etaPC (-(β * x)) * x) ^ 2 * (𝓕 etaSC (-(β * x)) * x) * e (-(N * β)))‖ ≤
      (3.67e-6 * (x / κ) + 8.85e-7 * x / 9) * ∑ b ∈ Bset q, ‖S etaPlus x ((b : ℝ) / q + β)‖ ^ 2 +
        9 * 8.85e-7 * x / 2 * mPhi2 q * ‖𝓕 etaUC (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ)‖ ^ 2 +
        8.85e-7 * x / 9 * mPhi q * ‖𝓕 etaPC (-(β * x)) * x‖ ^ 2 := by
  obtain ⟨hq1, hqt', hq3⟩ := mem_Qset_bounds hq
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < x / κ := div_pos hx0 kappa_pos
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (by omega)).ne'
  set m : ℂ := (μ q : ℂ) / q.totient with hm
  set Ap : ℂ := 𝓕 etaPC (-(β * x)) * x with hAp
  set Au : ℂ := 𝓕 etaUC (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ) with hAu
  have hAs : Au = 𝓕 etaSC (-(β * x)) * x := As_eq β
  have hρ : ∑ b ∈ Bset q, ‖S etaPlus x ((b : ℝ) / q + β) - m * Ap‖ ^ 2 ≤ (8.85e-7 * x) ^ 2 := by
    refine (resid_plus hx hq hβ).trans ?_; nlinarith
  have hU : ∀ b ∈ Bset q, ‖S etaStar x ((b : ℝ) / q + β) - m * Au‖ ≤ 3.67e-6 * (x / κ) := by
    intro b hb
    have h := resid_star hx hq hβ hb
    have h2 : ‖S etaStar x ((b : ℝ) / q + β) - m * Au‖ ^ 2 ≤ (3.67e-6 * (x / κ)) ^ 2 := by
      refine h.trans ?_; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have heb : ∀ b ∈ Bset q, ‖e (-(N * ((b : ℝ) / q + β)))‖ = 1 := fun b _ => TernaryGoldbach.norm_e _
  have hmain := sum_cubic_error (s := Bset q) (fun b => S etaPlus x ((b : ℝ) / q + β))
    (fun b => S etaStar x ((b : ℝ) / q + β)) (fun b => e (-(N * ((b : ℝ) / q + β)))) (m * Ap) (m * Au)
    (by positivity : (0:ℝ) < 8.85e-7 * x) heb hU hρ
  have hid : (m * Ap) ^ 2 * (m * Au) * ∑ b ∈ Bset q, e (-(N * ((b : ℝ) / q + β))) =
      (coefN N q : ℂ) * (Ap ^ 2 * (𝓕 etaSC (-(β * x)) * x) * e (-(N * β))) := by
    rw [← coef_eq hq1, ← hAs, hm]
    have : ∀ b ∈ Bset q, e (-(N * ((b : ℝ) / q + β))) = e (-(N * ((b : ℝ) / q))) * e (-(N * β)) := by
      intro b _; rw [← TernaryGoldbach.e_add]; congr 1; ring
    rw [sum_congr rfl this, ← sum_mul]; ring
  have h1 : ‖m * Au‖ ^ 2 = mPhi2 q * ‖Au‖ ^ 2 := by
    rw [norm_mul, mul_pow, hm, norm_moebius_div_sq_le]; rfl
  have h2 : 2 * ((Bset q).card : ℝ) * ‖m * Ap‖ ^ 2 = 2 * (mPhi q * ‖Ap‖ ^ 2) := by
    rw [card_Bset_eq, norm_mul, mul_pow, hm, norm_moebius_div_sq_le]
    unfold mPhi; field_simp
  rw [hid, h1, h2] at hmain
  have e1 : ∑ b ∈ Bset q, fI N x ((b : ℝ) / q + β) = ∑ b ∈ Bset q, S etaPlus x ((b : ℝ) / q + β) ^ 2 *
      S etaStar x ((b : ℝ) / q + β) * e (-(N * ((b : ℝ) / q + β))) := rfl
  rw [e1]
  refine hmain.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **One modulus**: `Σ_b ∫_{J_{q,b}} S₊²S_* e(−N·)` is `c_q x² C_{η◦,η_*}(N/x)` up to a small error. -/
theorem per_modulus (N : ℕ) {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq : q ∈ Qset r₀) :
    ‖(∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, fI N x y) -
        (coefN N q : ℂ) * ((x : ℂ) ^ 2 * (Cmain (N / x) : ℂ))‖ ≤
      (3.67e-6 * (x / κ) + 8.85e-7 * x / 9) * (∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, ‖S etaPlus x y‖ ^ 2) +
        9 * 8.85e-7 * x / 2 * mPhi2 q * (7.78 * (x / κ)) +
        8.85e-7 * x / 9 * mPhi q * (0.640208 * x) + mPhi2 q * (2.03e-5 * x ^ 2) := by
  obtain ⟨hq1, hqt', hq3⟩ := mem_Qset_bounds hq
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < x / κ := div_pos hx0 kappa_pos
  have hr₀ : r₀ = 150000 := rfl
  have hqt0 : (0 : ℝ) < qt q := by
    have : 1 ≤ qt q := by unfold qt; split_ifs <;> omega
    exact_mod_cast this
  set w := wrad 8 r₀ x q with hw
  have hwx : w * x = 1200000 / qt q := by
    rw [hw, TernaryGoldbach.MinorArcs.wrad, hr₀]; field_simp; norm_num
  have hw0 : 0 ≤ w := by rw [hw, TernaryGoldbach.MinorArcs.wrad, hr₀]; positivity
  have hwx4 : 4 ≤ w * x := by rw [hwx, le_div_iff₀ hqt0]; linarith
  have hβ : ∀ β ∈ Ioc (-w) w, |β * x| ≤ 1200000 / qt q := fun β hβ => by
    rw [← hwx, abs_mul, abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_right (abs_le.2 ⟨hβ.1.le, hβ.2⟩) hx0.le
  have hfc := continuous_fI N hx0
  have hsw : ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, fI N x y =
      ∫ β in -w..w, ∑ b ∈ Bset q, fI N x ((b : ℝ) / q + β) := by
    rw [intervalIntegral.integral_finset_sum (f := fun (b : ℕ) (β : ℝ) => fI N x ((b : ℝ) / q + β))
      (fun b _ => (hfc.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)]
    exact sum_congr rfl fun b _ => setIntegral_arc_eq_C (g := fI N x) hw0
  set Mn : ℝ → ℂ := fun β => (𝓕 etaPC (-(β * x)) * x) ^ 2 * (𝓕 etaSC (-(β * x)) * x) * e (-(N * β))
    with hMn
  have kM : Continuous Mn :=
    ((((continuous_fourier_etaPC.comp (by fun_prop)).mul continuous_const).pow 2).mul
      ((continuous_fourier_etaSC'.comp (by fun_prop)).mul continuous_const)).mul
      (TernaryGoldbach.continuous_e.comp (by fun_prop))
  have kF : Continuous fun β => ∑ b ∈ Bset q, fI N x ((b : ℝ) / q + β) :=
    continuous_finsetSum _ fun b _ => hfc.comp (continuous_const.add continuous_id)
  have hmc : ‖(∫ β in -w..w, Mn β) - (x : ℂ) ^ 2 * (Cmain (N / x) : ℂ)‖ ≤ 2.03e-5 * x ^ 2 :=
    main_comparison hx0 hw0 hwx4 (N : ℝ)
  have hdec : (∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, fI N x y) -
        (coefN N q : ℂ) * ((x : ℂ) ^ 2 * (Cmain (N / x) : ℂ)) =
      (∫ β in -w..w, (∑ b ∈ Bset q, fI N x ((b : ℝ) / q + β) - (coefN N q : ℂ) * Mn β)) +
        (coefN N q : ℂ) * ((∫ β in -w..w, Mn β) - (x : ℂ) ^ 2 * (Cmain (N / x) : ℂ)) := by
    have iM : IntervalIntegrable (fun β => (coefN N q : ℂ) * Mn β) volume (-w) w :=
      (continuous_const.mul kM).intervalIntegrable _ _
    rw [hsw, intervalIntegral.integral_sub (kF.intervalIntegrable _ _) iM,
      intervalIntegral.integral_const_mul]
    ring
  -- the pointwise bound, integrated
  have kS : Continuous fun β => ∑ b ∈ Bset q, ‖S etaPlus x ((b : ℝ) / q + β)‖ ^ 2 :=
    continuous_finsetSum _ fun b _ => (continuous_norm_sq_S hx0).comp (continuous_const.add continuous_id)
  have kU : Continuous fun β => ‖𝓕 etaUC (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ)‖ ^ 2 :=
    (((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      integrable_etaUC).comp (by fun_prop)).mul continuous_const).norm.pow 2
  have kP : Continuous fun β => ‖𝓕 etaPC (-(β * x)) * x‖ ^ 2 :=
    ((continuous_fourier_etaPC.comp (by fun_prop)).mul continuous_const).norm.pow 2
  set k1 : ℝ := 3.67e-6 * (x / κ) + 8.85e-7 * x / 9
  set k2 : ℝ := 9 * 8.85e-7 * x / 2 * mPhi2 q
  set k3 : ℝ := 8.85e-7 * x / 9 * mPhi q
  have hInt : ‖∫ β in -w..w, (∑ b ∈ Bset q, fI N x ((b : ℝ) / q + β) - (coefN N q : ℂ) * Mn β)‖ ≤
      ∫ β in -w..w, (k1 * ∑ b ∈ Bset q, ‖S etaPlus x ((b : ℝ) / q + β)‖ ^ 2 +
        k2 * ‖𝓕 etaUC (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ)‖ ^ 2 + k3 * ‖𝓕 etaPC (-(β * x)) * x‖ ^ 2) :=
    intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall fun β hβ' => pointwise_bound N hx hq (hβ β hβ'))
      ((((continuous_const.mul kS).add (continuous_const.mul kU)).add
        (continuous_const.mul kP)).intervalIntegrable _ _)
  have iS : IntervalIntegrable (fun β => k1 * ∑ b ∈ Bset q, ‖S etaPlus x ((b : ℝ) / q + β)‖ ^ 2)
      volume (-w) w := (continuous_const.mul kS).intervalIntegrable _ _
  have iU : IntervalIntegrable (fun β => k2 * ‖𝓕 etaUC (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ)‖ ^ 2)
      volume (-w) w := (continuous_const.mul kU).intervalIntegrable _ _
  have iP : IntervalIntegrable (fun β => k3 * ‖𝓕 etaPC (-(β * x)) * x‖ ^ 2)
      volume (-w) w := (continuous_const.mul kP).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (iS.add iU) iP, intervalIntegral.integral_add iS iU,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hInt
  have hB1 : ∫ β in -w..w, ∑ b ∈ Bset q, ‖S etaPlus x ((b : ℝ) / q + β)‖ ^ 2 =
      ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, ‖S etaPlus x y‖ ^ 2 := by
    rw [intervalIntegral.integral_finset_sum
      (f := fun (b : ℕ) (β : ℝ) => ‖S etaPlus x ((b : ℝ) / q + β)‖ ^ 2) (fun b _ =>
      ((continuous_norm_sq_S hx0).comp (continuous_const.add continuous_id)).intervalIntegrable _ _)]
    exact sum_congr rfl fun b _ => (setIntegral_arc_eq (g := fun y => ‖S etaPlus x y‖ ^ 2) hw0).symm
  have hB2 : ∫ β in -w..w, ‖𝓕 etaUC (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ)‖ ^ 2 ≤ 7.78 * (x / κ) := by
    set y := x / κ
    have e : (fun β => ‖𝓕 etaUC (-(β * y)) * ((y : ℝ) : ℂ)‖ ^ 2) =
        fun β => y ^ 2 * ‖𝓕 etaUC (-(β * y))‖ ^ 2 := by
      ext β; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]; ring
    have hi : Integrable fun β => y ^ 2 * ‖𝓕 etaUC (-(β * y))‖ ^ 2 := by
      have h := (integrable_norm_sq_fourier integrable_etaUC memLp_etaUC).comp_mul_left'
        (neg_ne_zero.2 hy0.ne')
      refine (h.const_mul (y ^ 2)).congr (Filter.Eventually.of_forall fun β => ?_)
      ring_nf
    rw [e, intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_le_integral hi (Filter.Eventually.of_forall fun β => by
      simp only [Pi.zero_apply]; positivity)).trans ?_
    rw [integral_const_mul, integral_norm_sq_comp_mul (f := 𝓕 etaUC) hy0]
    have := integral_norm_sq_fourier_etaUC_le
    have hyy : y ^ 2 * y⁻¹ = y := by field_simp
    calc y ^ 2 * (y⁻¹ * ∫ ξ, ‖𝓕 etaUC ξ‖ ^ 2) = y * ∫ ξ, ‖𝓕 etaUC ξ‖ ^ 2 := by rw [← mul_assoc, hyy]
      _ ≤ 7.78 * y := by nlinarith
  have hB3 : ∫ β in -w..w, ‖𝓕 etaPC (-(β * x)) * x‖ ^ 2 ≤ 0.640208 * x := by
    rw [integral_main_term hx0 hw0]
    have hi := integrable_norm_sq_fourier integrable_etaPC memLp_etaPC
    have h1 : ∫ δ in Ioo (-(w * x)) (w * x), ‖𝓕 etaPC δ‖ ^ 2 ≤ ∫ δ, ‖𝓕 etaPC δ‖ ^ 2 :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall fun δ => by
        simp only [Pi.zero_apply]; positivity)
    rw [integral_norm_sq_fourier_etaPC] at h1
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans integral_sq_etaPlus_bounds.2) hx0.le]
  have hm2 : 0 ≤ mPhi2 q := div_nonneg (by split_ifs <;> norm_num) (by positivity)
  have hm1 : 0 ≤ mPhi q := mPhi_nonneg q
  have hk2 : 0 ≤ k2 := by positivity
  have hk3 : 0 ≤ k3 := by positivity
  have hc : ‖(coefN N q : ℂ)‖ ≤ mPhi2 q := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_coefN_le N hq1
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hT2 := mul_le_mul hc hmc (norm_nonneg _) hm2
  rw [hB1] at hInt
  have hT1 := hInt.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hB2 hk2))
    (mul_le_mul_of_nonneg_left hB3 hk3))
  calc _ ≤ _ := add_le_add hT1 hT2
    _ = _ := by ring

/-! ## Assembly: [B, (14.27)] -/

theorem fI_periodic (N : ℕ) {x : ℝ} (hx : 0 < x) : Function.Periodic (fI N x) 1 := by
  intro α
  have h1 : S etaPlus x (α + 1) = S etaPlus x α := by
    rw [S_etaPlus_eq_expTsum, S_etaPlus_eq_expTsum, expTsum_periodic]
  have h2 : S etaStar x (α + 1) = S etaStar x α := by
    rw [S_etaStar_eq_cU hx, S_etaStar_eq_cU hx, expTsum_periodic]
  have h3 : e (-(N * (α + 1))) = e (-(N * α)) := by
    rw [show -((N : ℝ) * (α + 1)) = -(N * α) + ((-(N : ℤ) : ℤ) : ℝ) by push_cast; ring,
      TernaryGoldbach.e_add, TernaryGoldbach.e_intCast, mul_one]
  simp only [fI, h1, h2, h3]

theorem Cmain_ge_num {x : ℝ} (N : ℝ) (hNx : N / x = 2 + 9 / (8 * √(π / 2)) / κ) :
    0.800689 / κ ≤ Cmain (N / x) := by
  have hs1 : (1.25331 : ℝ) ≤ √(π / 2) := Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_d6])
  have hs2 : √(π / 2) ≤ 1.25332 := by
    rw [Real.sqrt_le_left (by norm_num)]; have := Real.pi_lt_d6; linarith
  set s := √(π / 2)
  set c := 9 / (8 * s) with hc
  have hs0 : 0 < s := by linarith
  have hcs : c * s = 9 / 8 := by rw [hc]; field_simp
  have hc1 : 0.8976 ≤ c := by
    rw [hc, le_div_iff₀ (by positivity)]; nlinarith
  have hQ : 49 / 48 * s - 9 / 4 * c + c ^ 2 * s ≤ 0.2696413 := by
    have : c ^ 2 * s = 9 / 8 * c := by rw [sq, mul_assoc, hcs]; ring
    rw [this]; nlinarith
  have hO := integral_sq_etaO_bounds.1
  rw [hNx]
  refine le_trans ?_ (Cmain_ge c)
  rw [TernaryGoldbach.Helfgott.κ]
  have h1 : 0.63965 * 1.25331 ≤ (∫ t, etaO t ^ 2) * s := by
    have := mul_le_mul hO hs1 (by norm_num) (by linarith)
    linarith
  have h2 : 8.82 * ((49 / 48 * s - 9 / 4 * c + c ^ 2 * s) / 49 ^ 3) ≤ 8.82 * (0.2696413 / 49 ^ 3) := by
    gcongr
  have e1 : (∫ t, etaO t ^ 2) * (s / 49) = (∫ t, etaO t ^ 2) * s / 49 := by ring
  rw [e1]
  norm_num at h1 h2
  linarith

set_option maxHeartbeats 2000000 in
/-- **[B, (14.27)]** (with `1.049` in place of [B]'s `1.058259`):
`Re ∫_{(0,1] ∩ 𝔐_{8,r₀}} S_{η₊}(α)² S_{η_*}(α) e(−Nα) dα ≥ 1.049 x²/κ`. -/
theorem major_total {N : ℕ} (hN : Odd N) {x : ℝ} (hx : 4.9e26 ≤ x)
    (hNx : (N : ℝ) / x = 2 + 9 / (8 * √(π / 2)) / κ) :
    1.049 * x ^ 2 / κ ≤ (∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, fI N x α).re := by
  have hx0 : 0 < x := by linarith
  have hfc := continuous_fI N hx0
  have hsub : Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x ⊆ Icc 0 1 := fun α hα => Ioc_subset_Icc_self hα.1
  have hint : IntegrableOn (fI N x) (Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x) :=
    (hfc.integrableOn_Icc).mono_set hsub
  have hre : (∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, fI N x α).re =
      ∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, (fI N x α).re := (integral_re hint).symm
  rw [hre, integral_majorArcs_eq (g := fun α => (fI N x α).re) (Complex.continuous_re.comp hfc)
    (fun α => by show (fI N x (α + 1)).re = (fI N x α).re; rw [fI_periodic N hx0 α]) hx]
  have harc : ∀ q b, ∫ y in arc 8 r₀ x q b, (fI N x y).re = (∫ y in arc 8 r₀ x q b, fI N x y).re :=
    fun q b => integral_re ((hfc.integrableOn_Icc
      (a := (b : ℝ) / q - wrad 8 r₀ x q) (b := (b : ℝ) / q + wrad 8 r₀ x q)).mono_set Ioo_subset_Icc_self)
  simp_rw [harc, ← Complex.re_sum]
  rw [Complex.re_sum]
  -- each modulus
  have hlow : ∀ q ∈ Qset r₀, coefN N q * (x ^ 2 * Cmain (N / x)) -
      ((3.67e-6 * (x / κ) + 8.85e-7 * x / 9) *
          (∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, ‖S etaPlus x y‖ ^ 2) +
        9 * 8.85e-7 * x / 2 * mPhi2 q * (7.78 * (x / κ)) +
        8.85e-7 * x / 9 * mPhi q * (0.640208 * x) + mPhi2 q * (2.03e-5 * x ^ 2)) ≤
      (∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, fI N x y).re := by
    intro q hq
    have h := per_modulus N hx hq
    have hw : (coefN N q : ℂ) * ((x : ℂ) ^ 2 * (Cmain (N / x) : ℂ)) =
        ((coefN N q * (x ^ 2 * Cmain (N / x)) : ℝ) : ℂ) := by push_cast; ring
    rw [hw] at h
    have h1 := (Complex.abs_re_le_norm _).trans h
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    linarith [(abs_le.1 h1).1]
  refine le_trans ?_ (sum_le_sum hlow)
  rw [sum_sub_distrib, ← sum_mul]
  -- the error terms, summed
  set k1 : ℝ := 3.67e-6 * (x / κ) + 8.85e-7 * x / 9
  set K2 : ℝ := 9 * 8.85e-7 * x / 2 * (7.78 * (x / κ)) + 2.03e-5 * x ^ 2
  set K3 : ℝ := 8.85e-7 * x / 9 * (0.640208 * x)
  have hEsum : ∑ q ∈ Qset r₀, (k1 * (∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, ‖S etaPlus x y‖ ^ 2) +
        9 * 8.85e-7 * x / 2 * mPhi2 q * (7.78 * (x / κ)) +
        8.85e-7 * x / 9 * mPhi q * (0.640208 * x) + mPhi2 q * (2.03e-5 * x ^ 2)) =
      k1 * (∑ q ∈ Qset r₀, ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, ‖S etaPlus x y‖ ^ 2) +
        K2 * (∑ q ∈ Qset r₀, mPhi2 q) + K3 * (∑ q ∈ Qset r₀, mPhi q) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun q _ => by ring
  rw [hEsum]
  have hJ : ∑ q ∈ Qset r₀, ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, ‖S etaPlus x y‖ ^ 2 ≤ 8.79 * x := by
    rw [← integral_majorArcs_eq (continuous_norm_sq_S hx0)
      (fun α => by simp only [S_etaPlus_eq_expTsum]; rw [expTsum_periodic]) hx]
    exact (l2_major_bounds hx).2
  have hm2 := sum_Qset_mPhi2_le
  have hm1 := sum_Qset_mPhi_bounds.2
  have hcN := sum_Qset_coefN_ge hN
  have hC := Cmain_ge_num (x := x) N hNx
  have hκ : κ = 49 := rfl
  have hy : 0 ≤ x / κ := by rw [hκ]; positivity
  have hk1 : 0 ≤ k1 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  have hK3 : 0 ≤ K3 := by positivity
  have hxC : 0 ≤ x ^ 2 * Cmain (N / x) := by
    have : 0 ≤ Cmain (N / x) := le_trans (by rw [hκ]; norm_num) hC
    positivity
  have hP1 := mul_le_mul_of_nonneg_left hJ hk1
  have hP2 := mul_le_mul_of_nonneg_left hm2 hK2
  have hP3 := mul_le_mul_of_nonneg_left hm1 hK3
  have hP4 := mul_le_mul_of_nonneg_right hcN hxC
  have hP5 := mul_le_mul_of_nonneg_left hC (sq_nonneg x)
  have hr₀ : r₀ = 150000 := rfl
  rw [hr₀] at hP1 ⊢
  simp only [k1, K2, K3, hκ] at hP1 hP2 hP3 hP4 hP5 ⊢
  nlinarith [sq_nonneg x]

end TernaryGoldbach.MajorArcs
