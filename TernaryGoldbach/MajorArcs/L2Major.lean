import TernaryGoldbach.MajorArcs.ArcChars
import TernaryGoldbach.MajorArcs.SumMuPhi

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# [H, (14.7)]: `∫_{𝔐_{8,r₀}} |S_{η₊}(α, x)|² dα = (8.7052 + O*(0.0756)) x` for `x ≥ 4.9·10²⁶`

[H, Lemma 10.3.1] for `η₊`, with the Cauchy–Schwarz-free variant of its error terms (each
pointwise square is split as `|u + v|² = (1 ± t)|u|² + O((1 + 1/t)|v|²)` with `t = 10⁻⁴`). Per modulus
`q` (`ArcChars.lean`): coprime split, Bombieri's identity, [H, Thm 7.1.4]; the main term
`μ²(q)/φ(q) · x ∫_{|δ| < T_q} |η̂₊(δ)|² dδ` with `T_q = 1.2·10⁶/q̃ ≥ 4` (`EtaPlusL2.lean`); then
`Σ_q μ²(q)/φ(q) = 2 · 6.798779…` (`SumMuPhi.lean`). Result: `8.675 x ≤ ∫ ≤ 8.786 x`.
-/

open Real MeasureTheory FourierTransform Set Finset
open TernaryGoldbach (e expTsum)
open TernaryGoldbach.MinorArcs (coprimePart Qset Bset qt wrad arc integral_majorArcs_le
  sum_arcs_le_integral_majorArcs expTsum_periodic)
open TernaryGoldbach.Helfgott (etaPlus S r₀ majorArcs)

namespace TernaryGoldbach.MajorArcs

theorem norm_sq_add_ge (a b : ℂ) {t : ℝ} (ht : 0 < t) :
    (1 - t) * ‖a‖ ^ 2 - (1 / t) * ‖b‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by
  have h1 : |‖a‖ - ‖b‖| ≤ ‖a + b‖ := by
    have := abs_norm_sub_norm_le a (-b)
    rwa [norm_neg, sub_neg_eq_add] at this
  have h2 : (‖a‖ - ‖b‖) ^ 2 ≤ ‖a + b‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : 2 * ‖a‖ * ‖b‖ ≤ t * ‖a‖ ^ 2 + (1 / t) * ‖b‖ ^ 2 := by
    have : 0 ≤ (t * ‖a‖ - ‖b‖) ^ 2 / t := by positivity
    have e : (t * ‖a‖ - ‖b‖) ^ 2 / t = t * ‖a‖ ^ 2 + (1 / t) * ‖b‖ ^ 2 - 2 * ‖a‖ * ‖b‖ := by
      field_simp; ring
    linarith
  nlinarith [sq_nonneg ‖b‖]

theorem norm_sq_add_le (a b : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖a + b‖ ^ 2 ≤ (1 + t) * ‖a‖ ^ 2 + (1 + 1 / t) * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖a‖ * ‖b‖ ≤ t * ‖a‖ ^ 2 + (1 / t) * ‖b‖ ^ 2 := by
    have : 0 ≤ (t * ‖a‖ - ‖b‖) ^ 2 / t := by positivity
    have e : (t * ‖a‖ - ‖b‖) ^ 2 / t = t * ‖a‖ ^ 2 + (1 / t) * ‖b‖ ^ 2 - 2 * ‖a‖ * ‖b‖ := by
      field_simp; ring
    linarith
  nlinarith

theorem continuous_fourier_etaPC : Continuous (𝓕 etaPC) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) integrable_etaPC

/-- An arc as an interval integral in `β = α − b/q`. -/
theorem setIntegral_arc_eq {g : ℝ → ℝ} {δ₀ R x : ℝ} {q b : ℕ} (hw : 0 ≤ wrad δ₀ R x q) :
    ∫ y in arc δ₀ R x q b, g y =
      ∫ β in -wrad δ₀ R x q..wrad δ₀ R x q, g ((b : ℝ) / q + β) := by
  set w := wrad δ₀ R x q
  rw [intervalIntegral.integral_comp_add_left, arc, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), sub_eq_add_neg]

/-- `∫_{−w}^{w} |η̂₊(−βx) x|² dβ = x ∫_{|δ|<wx} |η̂₊(δ)|² dδ`. -/
theorem integral_main_term {x w : ℝ} (hx : 0 < x) (hw : 0 ≤ w) :
    ∫ β in -w..w, ‖𝓕 etaPC (-(β * x)) * x‖ ^ 2 =
      x * ∫ δ in Ioo (-(w * x)) (w * x), ‖𝓕 etaPC δ‖ ^ 2 := by
  have e1 : (fun β : ℝ => ‖𝓕 etaPC (-(β * x)) * x‖ ^ 2) =
      fun β => x ^ 2 * (fun δ => ‖𝓕 etaPC δ‖ ^ 2) ((-x) * β) := by
    ext β
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_comm]
    congr 3; ring
  rw [e1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun δ => ‖𝓕 etaPC δ‖ ^ 2) (neg_ne_zero.2 hx.ne'),
    intervalIntegral.integral_symm, smul_eq_mul,
    intervalIntegral.integral_of_le (by nlinarith), integral_Ioc_eq_integral_Ioo]
  have e2 : -x * w = -(w * x) := by ring
  have e3 : -x * -w = w * x := by ring
  rw [e2, e3]
  field_simp

theorem mPhi_nonneg (q : ℕ) : 0 ≤ mPhi q := by
  unfold mPhi; split_ifs <;> positivity

theorem mPhi_le_one (q : ℕ) : mPhi q ≤ 1 := by
  unfold mPhi
  rcases Nat.eq_zero_or_pos q.totient with h | h
  · rw [h]; simp
  · have h' : (1 : ℝ) ≤ q.totient := by exact_mod_cast h
    split_ifs
    · rw [div_le_one (by linarith)]; exact h'
    · simp

theorem card_Bset_le (q : ℕ) : ((Bset q).card : ℝ) ≤ q := by
  have : (Bset q).card ≤ q := (Finset.card_filter_le _ _).trans (Finset.card_range q).le
  exact_mod_cast this

theorem continuous_norm_sq_S {x : ℝ} (hx : 0 < x) : Continuous fun y => ‖S etaPlus x y‖ ^ 2 :=
  (TernaryGoldbach.continuous_expTsum (summable_cP hx)).norm.pow 2

set_option maxHeartbeats 4000000 in
/-- **The arcs of modulus `q`** (`q ∈ Qset r₀`, `x ≥ 4.9·10²⁶`):
`Σ_b ∫_{J_{q,b}} |S_{η₊}|² = μ²(q)/φ(q) · (0.6392…0.64034) x + O(9.62·10⁻⁴ μ²(q)/φ(q) x + 2.17·10⁻⁷ x)`. -/
theorem Jq_bounds {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq : q ∈ Qset r₀) :
    0.63907 * mPhi q * x - 9.62e-4 * mPhi q * x - 3.6e-9 * x ≤
        ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, ‖S etaPlus x y‖ ^ 2 ∧
      ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, ‖S etaPlus x y‖ ^ 2 ≤
        0.64034 * mPhi q * x + 9.62e-4 * mPhi q * x + 2.17e-7 * x := by
  have hx0 : 0 < x := by linarith
  have hr₀ : r₀ = 150000 := rfl
  obtain ⟨hqI, hqt⟩ := Finset.mem_filter.1 hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hqI).1
  have hqt' : (qt q : ℝ) ≤ 300000 := by rw [hr₀] at hqt; linarith
  have hqq : q ≤ qt q := by unfold qt; split_ifs <;> omega
  have hq3 : q ≤ 300000 := by
    have : (q : ℝ) ≤ 300000 := le_trans (by exact_mod_cast hqq) hqt'
    exact_mod_cast this
  have hq3r : (q : ℝ) ≤ 300000 := by exact_mod_cast hq3
  have hqt2 : (2 : ℝ) ≤ qt q := by
    have : 2 ≤ qt q := by
      unfold qt; split_ifs with h
      · obtain ⟨k, hk⟩ := h; omega
      · omega
    exact_mod_cast this
  have hqt0 : (0 : ℝ) < qt q := by linarith
  set w := wrad 8 r₀ x q with hw_def
  have hwx : w * x = 1200000 / qt q := by
    rw [hw_def, TernaryGoldbach.MinorArcs.wrad, hr₀]; field_simp; ring
  have hw0 : 0 ≤ w := by rw [hw_def, TernaryGoldbach.MinorArcs.wrad]; positivity
  have h2w : 2 * w ≤ 1200000 / x := by
    have h1 : 2 * w * x ≤ 1200000 := by
      rw [mul_assoc, hwx, mul_div_assoc', div_le_iff₀ hqt0]; nlinarith
    rw [le_div_iff₀ hx0]; exact h1
  have hT : 4 ≤ w * x := by rw [hwx, le_div_iff₀ hqt0]; linarith
  set M := ∫ δ in Ioo (-(w * x)) (w * x), ‖𝓕 etaPC δ‖ ^ 2 with hM
  obtain ⟨hMlo, hMhi⟩ := integral_fourier_etaPlus_Ioo_bounds hT
  set a := coprimePart q (cP x) with ha
  set G : ℝ → ℝ := fun y => ‖S etaPlus x y‖ ^ 2 with hG
  have hGc : Continuous G := continuous_norm_sq_S hx0
  set f : ℝ → ℝ := fun β => ‖𝓕 etaPC (-(β * x)) * x‖ ^ 2 with hf
  have hfc : Continuous f := by
    simp only [hf]
    exact ((continuous_fourier_etaPC.comp (by fun_prop)).mul continuous_const).norm.pow 2
  set m := mPhi q
  have hm0 : 0 ≤ m := mPhi_nonneg q
  have hm1 : m ≤ 1 := mPhi_le_one q
  set t : ℝ := 1e-4 with ht
  have ht0 : (0 : ℝ) < t := by norm_num
  set Cb := (1e-15 * x) ^ 2
  set Cp := (2.83e-7 * x) ^ 2
  set Cn := (4.25e-7 * x) ^ 2
  have hCb : 0 ≤ Cb := sq_nonneg _
  have hCp : 0 ≤ Cp := sq_nonneg _
  have hCn : 0 ≤ Cn := sq_nonneg _
  have hcard := card_Bset_le q
  -- Step A: the arcs as one integral in `β`
  have hA : ∑ b ∈ Bset q, ∫ y in arc 8 r₀ x q b, G y = ∫ β in -w..w, ∑ b ∈ Bset q, G ((b : ℝ) / q + β) := by
    have hint : ∀ b ∈ Bset q, IntervalIntegrable (fun β => G ((b : ℝ) / q + β)) volume (-w) w :=
      fun b _ => (hGc.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finset_sum hint]
    exact Finset.sum_congr rfl fun b _ => setIntegral_arc_eq hw0
  -- Step B: pointwise bounds
  set A1lo := (1 - t) ^ 2 * m
  set A0lo := -((1 - t) * m * (1 / t) * Cp + (1 / t) * q * Cb)
  set A1hi := (1 + t) ^ 2 * m
  set A0hi := (1 + t) * m * (1 + 1 / t) * Cp + (1 + t) * Cn + (1 + 1 / t) * q * Cb
  have hpt : ∀ β ∈ Icc (-w) w, A1lo * f β + A0lo ≤ ∑ b ∈ Bset q, G ((b : ℝ) / q + β) ∧
      ∑ b ∈ Bset q, G ((b : ℝ) / q + β) ≤ A1hi * f β + A0hi := by
    intro β hβ
    have hβx : |β * x| ≤ 1200000 / qt q := by
      rw [abs_mul, abs_of_pos hx0, ← hwx]
      exact mul_le_mul_of_nonneg_right (abs_le.2 ⟨hβ.1, hβ.2⟩) hx0.le
    obtain ⟨⟨hlo, hhi⟩, hpr⟩ := arc_chars hx hq1 hqt' hβx
    have hb : ∀ y, (1 - t) * ‖expTsum a y‖ ^ 2 - (1 / t) * Cb ≤ G y ∧
        G y ≤ (1 + t) * ‖expTsum a y‖ ^ 2 + (1 + 1 / t) * Cb := by
      intro y
      have hd := norm_S_sub_coprime_le hx hq1 hq3 y
      have hd2 : ‖S etaPlus x y - expTsum a y‖ ^ 2 ≤ Cb := pow_le_pow_left₀ (norm_nonneg _) hd 2
      have e : S etaPlus x y = expTsum a y + (S etaPlus x y - expTsum a y) := by ring
      have l1 := norm_sq_add_ge (expTsum a y) (S etaPlus x y - expTsum a y) ht0
      have l2 := norm_sq_add_le (expTsum a y) (S etaPlus x y - expTsum a y) ht0
      rw [← e] at l1 l2
      have h1t : 0 ≤ 1 / t := by positivity
      have h1t' : 0 ≤ 1 + 1 / t := by positivity
      constructor
      · simp only [hG]; nlinarith [mul_le_mul_of_nonneg_left hd2 h1t]
      · simp only [hG]; nlinarith [mul_le_mul_of_nonneg_left hd2 h1t']
    have sB_lo : (1 - t) * ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 - (1 / t) * q * Cb ≤
        ∑ b ∈ Bset q, G ((b : ℝ) / q + β) := by
      have := Finset.sum_le_sum fun b (_ : b ∈ Bset q) => (hb ((b : ℝ) / q + β)).1
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at this
      have : ((Bset q).card : ℝ) * ((1 / t) * Cb) ≤ q * ((1 / t) * Cb) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      nlinarith
    have sB_hi : ∑ b ∈ Bset q, G ((b : ℝ) / q + β) ≤
        (1 + t) * ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 + (1 + 1 / t) * q * Cb := by
      have := Finset.sum_le_sum fun b (_ : b ∈ Bset q) => (hb ((b : ℝ) / q + β)).2
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at this
      have : ((Bset q).card : ℝ) * ((1 + 1 / t) * Cb) ≤ q * ((1 + 1 / t) * Cb) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      nlinarith
    -- the principal character
    have hp2 : ‖expTsum a β - 𝓕 etaPC (-(β * x)) * x‖ ^ 2 ≤ Cp := pow_le_pow_left₀ (norm_nonneg _) hpr 2
    have ep : expTsum a β = 𝓕 etaPC (-(β * x)) * x + (expTsum a β - 𝓕 etaPC (-(β * x)) * x) := by ring
    have p1 := norm_sq_add_ge (𝓕 etaPC (-(β * x)) * x) (expTsum a β - 𝓕 etaPC (-(β * x)) * x) ht0
    have p2 := norm_sq_add_le (𝓕 etaPC (-(β * x)) * x) (expTsum a β - 𝓕 etaPC (-(β * x)) * x) ht0
    rw [← ep] at p1 p2
    have hP_lo : (1 - t) * f β - (1 / t) * Cp ≤ ‖expTsum a β‖ ^ 2 := by
      simp only [hf]; nlinarith [mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 1 / t by positivity)]
    have hP_hi : ‖expTsum a β‖ ^ 2 ≤ (1 + t) * f β + (1 + 1 / t) * Cp := by
      simp only [hf]; nlinarith [mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 1 + 1 / t by positivity)]
    have hlo' : m * ‖expTsum a β‖ ^ 2 ≤ ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 := hlo
    have hhi' : ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 ≤ m * ‖expTsum a β‖ ^ 2 + Cn := hhi
    have ht1 : 0 ≤ 1 - t := by norm_num [ht]
    constructor
    · have k1 : m * ((1 - t) * f β - (1 / t) * Cp) ≤ m * ‖expTsum a β‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hP_lo hm0
      have k2 : (1 - t) * (m * ((1 - t) * f β - (1 / t) * Cp)) ≤
          (1 - t) * ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (k1.trans hlo') ht1
      have : A1lo * f β + A0lo = (1 - t) * (m * ((1 - t) * f β - (1 / t) * Cp)) - (1 / t) * q * Cb := by
        simp only [A1lo, A0lo]; ring
      rw [this]; linarith
    · have k1 : m * ‖expTsum a β‖ ^ 2 ≤ m * ((1 + t) * f β + (1 + 1 / t) * Cp) :=
        mul_le_mul_of_nonneg_left hP_hi hm0
      have k2 : (1 + t) * ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 ≤
          (1 + t) * (m * ((1 + t) * f β + (1 + 1 / t) * Cp) + Cn) :=
        mul_le_mul_of_nonneg_left (hhi'.trans (by linarith)) (by norm_num [ht])
      have : A1hi * f β + A0hi = (1 + t) * (m * ((1 + t) * f β + (1 + 1 / t) * Cp) + Cn) +
          (1 + 1 / t) * q * Cb := by
        simp only [A1hi, A0hi]; ring
      rw [this]; linarith
  -- Step C: integrate
  have hLc : Continuous fun β => ∑ b ∈ Bset q, G ((b : ℝ) / q + β) :=
    continuous_finsetSum _ fun b _ => hGc.comp (continuous_const.add continuous_id)
  have hint_f : ∫ β in -w..w, f β = x * M := integral_main_term hx0 hw0
  have hI : ∀ A1 A0 : ℝ, ∫ β in -w..w, (A1 * f β + A0) = A1 * (x * M) + A0 * (2 * w) := by
    intro A1 A0
    have h1 : IntervalIntegrable (fun β => A1 * f β) volume (-w) w :=
      (continuous_const.mul hfc).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h1 intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hint_f, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hlo_int : A1lo * (x * M) + A0lo * (2 * w) ≤ ∫ β in -w..w, ∑ b ∈ Bset q, G ((b : ℝ) / q + β) := by
    rw [← hI]
    exact intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous fun β => A1lo * f β + A0lo).intervalIntegrable _ _)
      (hLc.intervalIntegrable _ _) fun β hβ => (hpt β hβ).1
  have hhi_int : ∫ β in -w..w, ∑ b ∈ Bset q, G ((b : ℝ) / q + β) ≤ A1hi * (x * M) + A0hi * (2 * w) := by
    rw [← hI]
    exact intervalIntegral.integral_mono_on (by linarith) (hLc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun β => A1hi * f β + A0hi).intervalIntegrable _ _)
      fun β hβ => (hpt β hβ).2
  rw [hA]
  -- Step D: numerics
  have hmx : 0 ≤ m * x := by positivity
  have hxM : 0.6392 * x ≤ x * M := by nlinarith
  have hxM' : x * M ≤ 0.640208 * x := by nlinarith
  have hCpx : (1200000 / x) * Cp = 9.61068e-8 * x := by
    simp only [Cp]; field_simp; ring
  have hCnx : (1200000 / x) * Cn = 2.1675e-7 * x := by
    simp only [Cn]; field_simp; ring
  have hCbx : (1200000 / x) * Cb = 1.2e-24 * x := by
    simp only [Cb]; field_simp; ring
  constructor
  · -- lower
    have e1 : A1lo * (x * M) ≥ 0.99980001 * m * (0.6392 * x) := by
      simp only [A1lo, ht]; nlinarith
    have e2 : -A0lo * (2 * w) ≤ (1e4 * m * Cp + 1e4 * q * Cb) * (1200000 / x) := by
      have hA0 : -A0lo ≤ 1e4 * m * Cp + 1e4 * q * Cb := by
        simp only [A0lo, ht]; nlinarith
      calc -A0lo * (2 * w) ≤ (1e4 * m * Cp + 1e4 * q * Cb) * (2 * w) :=
            mul_le_mul_of_nonneg_right hA0 (by positivity)
        _ ≤ (1e4 * m * Cp + 1e4 * q * Cb) * (1200000 / x) :=
            mul_le_mul_of_nonneg_left h2w (by positivity)
    have e3 : (1e4 * m * Cp + 1e4 * q * Cb) * (1200000 / x) =
        1e4 * m * ((1200000 / x) * Cp) + 1e4 * q * ((1200000 / x) * Cb) := by ring
    rw [e3, hCpx, hCbx] at e2
    have hqx : (q : ℝ) * (1.2e-24 * x) ≤ 300000 * (1.2e-24 * x) :=
      mul_le_mul_of_nonneg_right hq3r (by positivity)
    nlinarith
  · -- upper
    have e1 : A1hi * (x * M) ≤ 1.00020001 * m * (0.640208 * x) := by
      simp only [A1hi, ht]; nlinarith
    have hA0 : A0hi ≤ 1.0001 * 10001 * m * Cp + 1.0001 * Cn + 10001 * q * Cb := by
      simp only [A0hi, ht]; nlinarith
    have hA0' : 0 ≤ A0hi := by simp only [A0hi, ht]; positivity
    have e2 : A0hi * (2 * w) ≤ (1.0001 * 10001 * m * Cp + 1.0001 * Cn + 10001 * q * Cb) * (1200000 / x) :=
      (mul_le_mul_of_nonneg_right hA0 (by positivity)).trans
        (mul_le_mul_of_nonneg_left h2w (by positivity))
    have e3 : (1.0001 * 10001 * m * Cp + 1.0001 * Cn + 10001 * q * Cb) * (1200000 / x) =
        1.0001 * 10001 * m * ((1200000 / x) * Cp) + 1.0001 * ((1200000 / x) * Cn) +
          10001 * q * ((1200000 / x) * Cb) := by ring
    rw [e3, hCpx, hCnx, hCbx] at e2
    have hqx : (q : ℝ) * (1.2e-24 * x) ≤ 300000 * (1.2e-24 * x) :=
      mul_le_mul_of_nonneg_right hq3r (by positivity)
    nlinarith

theorem card_Qset_le : ((Qset r₀).card : ℝ) ≤ 300000 := by
  have hfl : ⌊2 * r₀⌋₊ = 300000 := by
    rw [show (2 * r₀ : ℝ) = ((300000 : ℕ) : ℝ) by norm_num [r₀]]; exact Nat.floor_natCast _
  have h : Qset r₀ ⊆ Finset.Icc 1 300000 := by
    intro q hq
    have := (Finset.mem_filter.1 hq).1
    rwa [hfl] at this
  have h2 := Finset.card_le_card h
  rw [Nat.card_Icc] at h2
  exact_mod_cast (by omega : (Qset r₀).card ≤ 300000)

/-- **[H, (14.7)], proved**: for `x ≥ 4.9·10²⁶`,
`8.6296 x ≤ ∫_{(0,1] ∩ 𝔐_{8,r₀}} |S_{η₊}(α, x)|² dα ≤ 8.79 x` (in fact `8.675 x … 8.786 x`). -/
theorem l2_major_bounds {x : ℝ} (hx : 4.9e26 ≤ x) :
    8.6296 * x ≤ ∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, ‖S etaPlus x α‖ ^ 2 ∧
      ∫ α in Ioc (0:ℝ) 1 ∩ majorArcs 8 r₀ x, ‖S etaPlus x α‖ ^ 2 ≤ 8.79 * x := by
  have hx0 : 0 < x := by linarith
  have hr₀ : r₀ = 150000 := rfl
  set g : ℝ → ℝ := fun α => ‖S etaPlus x α‖ ^ 2 with hg
  have hgc : Continuous g := continuous_norm_sq_S hx0
  have hper : Function.Periodic g 1 := fun α => by
    simp only [hg, S_etaPlus_eq_expTsum]; rw [expTsum_periodic]
  have hg0 : ∀ α, 0 ≤ g α := fun α => by positivity
  have hle := integral_majorArcs_le hgc hper hg0 hx0 (δ₀ := 8) (R := r₀)
    (by rw [hr₀]; norm_num) (by rw [hr₀]; linarith)
  have hge := sum_arcs_le_integral_majorArcs hgc hper hg0 hx0 (δ₀ := 8) (Q := r₀) (by norm_num)
    (by rw [hr₀]; norm_num) (by rw [hr₀]; linarith) (by rw [hr₀]; linarith)
  have hlo := Finset.sum_le_sum fun q (hq : q ∈ Qset r₀) => (Jq_bounds hx hq).1
  have hhi := Finset.sum_le_sum fun q (hq : q ∈ Qset r₀) => (Jq_bounds hx hq).2
  have e1 : ∑ q ∈ Qset r₀, (0.63907 * mPhi q * x - 9.62e-4 * mPhi q * x - 3.6e-9 * x) =
      (0.63907 - 9.62e-4) * x * (∑ q ∈ Qset r₀, mPhi q) - 3.6e-9 * x * (Qset r₀).card := by
    have : ∀ q, 0.63907 * mPhi q * x - 9.62e-4 * mPhi q * x - 3.6e-9 * x =
        ((0.63907 - 9.62e-4) * x) * mPhi q - 3.6e-9 * x := fun q => by ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring
  have e2 : ∑ q ∈ Qset r₀, (0.64034 * mPhi q * x + 9.62e-4 * mPhi q * x + 2.17e-7 * x) =
      (0.64034 + 9.62e-4) * x * (∑ q ∈ Qset r₀, mPhi q) + 2.17e-7 * x * (Qset r₀).card := by
    have : ∀ q, 0.64034 * mPhi q * x + 9.62e-4 * mPhi q * x + 2.17e-7 * x =
        ((0.64034 + 9.62e-4) * x) * mPhi q + 2.17e-7 * x := fun q => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring
  rw [e1] at hlo
  rw [e2] at hhi
  obtain ⟨hm1, hm2⟩ := sum_Qset_mPhi_bounds
  have hm1' : 13.597558 ≤ ∑ q ∈ Qset r₀, mPhi q := hm1
  have hm2' : ∑ q ∈ Qset r₀, mPhi q ≤ 13.59756 := hm2
  have hc := card_Qset_le
  have hc0 : (0 : ℝ) ≤ (Qset r₀).card := Nat.cast_nonneg _
  constructor
  · refine le_trans ?_ (hlo.trans hge)
    nlinarith
  · refine (hle.trans hhi).trans ?_
    nlinarith

end TernaryGoldbach.MajorArcs
