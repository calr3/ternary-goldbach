import TernaryGoldbach.Prelim.MertensProduct
import TernaryGoldbach.MinorArcs.PartIICited
import TernaryGoldbach.MinorArcs.BaseGap
import TernaryGoldbach.MinorArcs.LinftyLevels
import TernaryGoldbach.Helfgott.SupNorms

/-!
# The base gap: `|S_{η_*}(α, x)| ≤ 0.0121 y` on `𝔐_{8,r₀}(y) \ 𝔐_{8,r₀}(x)`

* `sum_noncoprime_le`: `Σ_{(n,q) > 1} Λ(n) |η(n/y)| ≤ 6.2 K log q + 1` if `y² ≤ 2^K`
  (prime powers `n ≤ y²` with `(n, q) > 1` divide `q^K`, and `Σ_{d ∣ m} Λ(d) = log m`; the tail
  `n > y²` is negligible by the Gaussian decay of `η`).
-/

open Real Set MeasureTheory Filter FourierTransform
open scoped ArithmeticFunction.vonMangoldt
open TernaryGoldbach (e expTsum)

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 phi mellinConv)

theorem etaU_eq_mellinConv {u : ℝ} (hu : 0 < u) : etaU u = mellinConv eta2 phi u := by
  unfold etaU; rw [mellinConv_eq_swap _ _ hu]

theorem abs_etaU_le_const {u : ℝ} (hu : 0 < u) : |etaU u| ≤ 6.2 := by
  rw [etaU_eq_mellinConv hu]; exact Helfgott.abs_mellinConv_eta2_phi_le_const u

theorem abs_etaU_le_gauss {u : ℝ} (hu : 0 < u) : |etaU u| ≤ 144 * u ^ 2 * rexp (-u ^ 2 / 2) := by
  rw [etaU_eq_mellinConv hu]; exact Helfgott.abs_mellinConv_eta2_phi_le hu.le

/-- `n³ e^{-n/2} ≤ 384 e^{-n/4}`. -/
theorem cube_mul_exp_le (t : ℝ) (ht : 0 ≤ t) : t ^ 3 * rexp (-t / 2) ≤ 384 * rexp (-t / 4) := by
  have h := Real.pow_div_factorial_le_exp (x := t / 4) (by positivity) 3
  norm_num [Nat.factorial] at h
  have e1 : rexp (-t / 4) = rexp (t / 4) * rexp (-t / 2) := by rw [← Real.exp_add]; ring_nf
  rw [e1]
  have := Real.exp_pos (-t / 2)
  nlinarith

theorem sum_noncoprime_le {y : ℝ} (hy : 1e25 ≤ y) {q K : ℕ} (hq : 1 ≤ q) (hK : y ^ 2 ≤ 2 ^ K) :
    ∑' n, ‖((Λ n * etaU (n / y) : ℝ) : ℂ) - coprimePart q (fun n => ((Λ n * etaU (n / y) : ℝ) : ℂ)) n‖
      ≤ 6.2 * K * Real.log q + 1 := by
  have hy0 : 0 < y := by linarith
  set c : ℕ → ℂ := fun n => ((Λ n * etaU (n / y) : ℝ) : ℂ)
  set g : ℕ → ℝ := fun n => ‖c n - coprimePart q c n‖ with hg
  set g₁ : ℕ → ℝ := fun n => if n ∈ (q ^ K).divisors then 6.2 * Λ n else 0
  set g₂ : ℕ → ℝ := fun n => 55296 / y ^ 2 * rexp (-(n : ℝ) / 4)
  have hgeom : Summable fun n : ℕ => rexp (-(n : ℝ) / 4) := by
    have := Real.summable_exp_neg_nat.comp_injective (show Function.Injective (fun n : ℕ => n) from
      fun a b h => h)
    have h := (Real.summable_pow_mul_exp_neg_nat_mul 0 (show (0:ℝ) < 1 / 4 by norm_num))
    refine h.congr fun n => ?_
    simp only [pow_zero, one_mul]; ring_nf
  have hs₁ : Summable g₁ := summable_of_ne_finset_zero (s := (q ^ K).divisors)
    (fun n hn => by simp only [g₁, hn, ite_false])
  have hs₂ : Summable g₂ := hgeom.mul_left _
  have hpt : ∀ n, g n ≤ g₁ n + g₂ n := by
    intro n
    have hg2 : 0 ≤ g₂ n := by positivity
    have hg1 : 0 ≤ g₁ n := by
      simp only [g₁]; split_ifs
      · exact mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl
    by_cases hc : Nat.Coprime n q
    · have : g n = 0 := by
        simp only [hg, coprimePart]; rw [ite_eq_left (c := Nat.Coprime n q) hc, sub_self, norm_zero]
      rw [this]; linarith
    have hgn : g n = Λ n * |etaU (n / y)| := by
      simp only [hg, coprimePart, hc, ite_false, sub_zero, c, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [hgn]
    by_cases hΛ : Λ n = 0
    · rw [hΛ, zero_mul]; linarith
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hΛ
      · exact h
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    by_cases hny : (n : ℝ) ≤ y ^ 2
    · -- `n ∣ q^K`
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
      have hpq : p ∣ q := by
        by_contra h
        exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
      have hkK : k ≤ K := by
        have h1 : (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := pow_le_pow_left₀ (by norm_num)
          (by exact_mod_cast hp.two_le) k
        have h2 : (2 : ℝ) ^ k ≤ 2 ^ K := by push_cast at hny; linarith
        exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).1 h2
      have hdvd : p ^ k ∣ q ^ K := (pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK)
      have hmem : p ^ k ∈ (q ^ K).divisors :=
        Nat.mem_divisors.2 ⟨hdvd, pow_ne_zero _ (by omega)⟩
      have : g₁ (p ^ k) = 6.2 * Λ (p ^ k) := by simp only [g₁, hmem, ite_true]
      rw [this]
      have := abs_etaU_le_const (u := ((p ^ k : ℕ) : ℝ) / y) (by positivity)
      nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := p ^ k)]
    · -- the Gaussian tail
      push Not at hny
      have hu : 0 < (n : ℝ) / y := by positivity
      have h1 := abs_etaU_le_gauss hu
      have hsq : (n : ℝ) ≤ ((n : ℝ) / y) ^ 2 := by
        rw [div_pow, le_div_iff₀ (by positivity)]; nlinarith
      have h2 : rexp (-((n : ℝ) / y) ^ 2 / 2) ≤ rexp (-(n : ℝ) / 2) := Real.exp_le_exp.2 (by linarith)
      have hΛn : Λ n ≤ n := ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn0.le)
      have h3 := cube_mul_exp_le n hn0.le
      calc Λ n * |etaU (n / y)| ≤ n * (144 * ((n : ℝ) / y) ^ 2 * rexp (-(n : ℝ) / 2)) := by
            refine mul_le_mul hΛn (h1.trans ?_) (abs_nonneg _) hn0.le
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 144 / y ^ 2 * ((n : ℝ) ^ 3 * rexp (-(n : ℝ) / 2)) := by field_simp
        _ ≤ 144 / y ^ 2 * (384 * rexp (-(n : ℝ) / 4)) := by gcongr
        _ = g₂ n := by simp only [g₂]; ring
        _ ≤ g₁ n + g₂ n := by linarith
  have hs : Summable g := (hs₁.add hs₂).of_nonneg_of_le (fun n => norm_nonneg _) hpt
  calc ∑' n, g n ≤ ∑' n, (g₁ n + g₂ n) := Summable.tsum_le_tsum hpt hs (hs₁.add hs₂)
    _ = ∑' n, g₁ n + ∑' n, g₂ n := hs₁.tsum_add hs₂
    _ ≤ 6.2 * K * Real.log q + 1 := by
        have e1 : ∑' n, g₁ n = 6.2 * (K * Real.log q) := by
          rw [tsum_eq_sum (s := (q ^ K).divisors) (fun n hn => by simp only [g₁, hn, ite_false])]
          rw [Finset.sum_congr rfl (g := fun n => 6.2 * Λ n) (fun n hn => by simp only [g₁, hn, ite_true]),
            ← Finset.mul_sum,
            ArithmeticFunction.vonMangoldt_sum]
          push_cast; rw [Real.log_pow]
        have e2 : ∑' n, g₂ n ≤ 1 := by
          simp only [g₂]
          rw [tsum_mul_left]
          have hsum : ∑' n : ℕ, rexp (-(n : ℝ) / 4) ≤ 5 := by
            have h := tsum_geometric_of_lt_one (r := rexp (-1 / 4)) (Real.exp_pos _).le
              (Real.exp_lt_one_iff.2 (by norm_num))
            have e : ∀ n : ℕ, rexp (-(n : ℝ) / 4) = rexp (-1 / 4) ^ n := fun n => by
              rw [← Real.exp_nat_mul]; ring_nf
            simp_rw [e, h]
            have : rexp (-1 / 4) ≤ 0.8 := by
              have := Real.add_one_le_exp (1 / 4)
              have h2 : rexp (-1 / 4) = (rexp (1 / 4))⁻¹ := by rw [← Real.exp_neg]; ring_nf
              rw [h2]
              rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
            rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
          have hy2 : (1e50 : ℝ) ≤ y ^ 2 := by nlinarith
          have : 55296 / y ^ 2 ≤ 55296 / 1e50 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hy2
          have h0 : 0 ≤ ∑' n : ℕ, rexp (-(n : ℝ) / 4) := tsum_nonneg fun n => (Real.exp_pos _).le
          nlinarith
        linarith

/-! ## Numerical constants -/

theorem Fr_300000_le : Fr 300000 ≤ 5.53 := by
  have h1 : Real.log 300000 ≤ 12.6116 := by
    refine (log_le_num 12 0.6116 (by norm_num) (by norm_num) ?_).trans (by norm_num)
    unfold taylor6; norm_num
  have h2 : 12.6114 ≤ Real.log 300000 := by
    have := le_log_num (z := 300000) 12 0.6114 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num at this ⊢; linarith
  have h3 : Real.log (Real.log 300000) ≤ 2.5347 :=
    (Real.log_le_log (by linarith) h1).trans
      ((log_le_num 2 0.5347 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)).trans (by norm_num))
  have h4 : 2.5345 ≤ Real.log (Real.log 300000) := by
    have := le_log_num (z := 12.6114) 2 0.5345 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    have h5 := Real.log_le_log (by norm_num) h2
    norm_num at this ⊢; linarith
  unfold Fr
  have hg := exp_gamma_le_sharp
  have hl0 : 0 < Real.log (Real.log 300000) := by linarith
  have : 2.50637 / Real.log (Real.log 300000) ≤ 2.50637 / 2.5345 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
  have : rexp eulerMascheroniConstant * Real.log (Real.log 300000) ≤ 1.7882 * 2.5347 :=
    mul_le_mul hg h3 hl0.le (by norm_num)
  norm_num at *; linarith

theorem fourier_const_le : c₀ * (√(π / (1 / 2)) / 2) / (2 * π) ^ 2 ≤ 1.016 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hs : √(π / (1 / 2)) ≤ 2.50664 := by
    rw [Real.sqrt_le_left (by norm_num), div_div_eq_mul_div]; nlinarith
  unfold c₀
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ## The gap -/

open TernaryGoldbach.Helfgott (majorArcs S etaStar κ r₀)

/-- A point of `𝔐_{8,r₀}(y) \ 𝔐_{8,r₀}(x)` (`x = κy`) is `a/q + δ/y` with `1 ≤ q ≤ 2r₀`,
`(a, q) = 1` and `4r₀/(κq) ≤ |δ| < 8r₀/q`. -/
theorem gap_point {x α : ℝ} (hx : 0 < x) (h1 : α ∈ majorArcs 8 r₀ (x / κ))
    (h2 : α ∉ majorArcs 8 r₀ x) :
    ∃ (q : ℕ) (a : ℤ), 1 ≤ q ∧ (q : ℝ) ≤ 2 * r₀ ∧ IsCoprime a (q : ℤ) ∧
      4 * r₀ / (κ * q) ≤ |(α - a / q) * (x / κ)| ∧ |(α - a / q) * (x / κ)| < 8 * r₀ / q := by
  have hκ : (κ : ℝ) = 49 := rfl
  have hy : 0 < x / κ := by rw [hκ]; positivity
  have hr₀ : (r₀ : ℝ) = 150000 := rfl
  simp only [majorArcs, mem_union, mem_iUnion] at h1 h2
  push Not at h2
  rcases h1 with ⟨q, ⟨hq1, hqr, hqo⟩, a, ha, hI⟩ | ⟨q, ⟨hq1, hqr, hqe⟩, a, ha, hI⟩
  · have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
    have hout := h2.1 q ⟨hq1, hqr, hqo⟩ a ha
    refine ⟨q, a, hq1, by linarith, ha, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos hy]
      have : 8 * r₀ / (2 * q * x) ≤ |α - a / q| := by
        by_contra h; push Not at h
        exact hout ⟨by linarith [neg_abs_le (α - a / q)], by linarith [le_abs_self (α - a / q)]⟩
      calc 4 * r₀ / (κ * q) = 8 * r₀ / (2 * q * x) * (x / κ) := by field_simp; ring
        _ ≤ |α - a / q| * (x / κ) := mul_le_mul_of_nonneg_right this hy.le
    · rw [abs_mul, abs_of_pos hy]
      have : |α - a / q| < 8 * r₀ / (2 * q * (x / κ)) := by
        rw [abs_lt]; constructor <;> linarith [hI.1, hI.2]
      calc |α - a / q| * (x / κ) < 8 * r₀ / (2 * q * (x / κ)) * (x / κ) :=
            mul_lt_mul_of_pos_right this hy
        _ = 4 * r₀ / q := by field_simp; ring
        _ ≤ 8 * r₀ / q := by gcongr; norm_num
  · have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
    have hout := h2.2 q ⟨hq1, hqr, hqe⟩ a ha
    refine ⟨q, a, hq1, hqr, ha, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos hy]
      have : 8 * r₀ / (q * x) ≤ |α - a / q| := by
        by_contra h; push Not at h
        exact hout ⟨by linarith [neg_abs_le (α - a / q)], by linarith [le_abs_self (α - a / q)]⟩
      calc 4 * r₀ / (κ * q) ≤ 8 * r₀ / (q * x) * (x / κ) := by
            rw [show 8 * r₀ / (q * x) * (x / κ) = 8 * r₀ / (κ * q) by field_simp]
            gcongr; norm_num
        _ ≤ |α - a / q| * (x / κ) := mul_le_mul_of_nonneg_right this hy.le
    · rw [abs_mul, abs_of_pos hy]
      have : |α - a / q| < 8 * r₀ / (q * (x / κ)) := by
        rw [abs_lt]; constructor <;> linarith [hI.1, hI.2]
      calc |α - a / q| * (x / κ) < 8 * r₀ / (q * (x / κ)) * (x / κ) :=
            mul_lt_mul_of_pos_right this hy
        _ = 8 * r₀ / q := by field_simp

theorem S_etaStar_eq_expTsum {x : ℝ} (hx : 0 < x) (α : ℝ) :
    S etaStar x α = expTsum (fun n => ((Λ n * etaU (n / (x / κ)) : ℝ) : ℂ)) α := by
  have hκ : (0:ℝ) < κ := by rw [Helfgott.κ]; norm_num
  unfold S expTsum
  congr 1; ext n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [etaStar_eq_etaU (by positivity)]
    congr 3; field_simp

set_option maxHeartbeats 1000000 in
variable [Fact TernaryGoldbach.PlattGRH] in
/-- **The base gap**: on `𝔐_{8,r₀}(y) \ 𝔐_{8,r₀}(x)`, `|S_{η_*}(α, x)| ≤ 0.0121 y`
(from [H, Cor 7.1.3]). -/
theorem norm_S_etaStar_le_gap {x α : ℝ} (hx : 4.9e26 ≤ x) (h1 : α ∈ majorArcs 8 r₀ (x / κ))
    (h2 : α ∉ majorArcs 8 r₀ x) : ‖S etaStar x α‖ ≤ 0.0121 * (x / κ) := by
  have hκ : (κ : ℝ) = 49 := rfl
  have hr₀ : (r₀ : ℝ) = 150000 := rfl
  have hx0 : 0 < x := by linarith
  set y := x / κ with hy_def
  have hy : 1e25 ≤ y := by rw [hy_def, hκ, le_div_iff₀ (by norm_num)]; linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨q, a, hq1, hq2, ha, hδ1, hδ2⟩ := gap_point hx0 h1 h2
  have : NeZero q := ⟨by omega⟩
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
  have hq3 : (q : ℝ) ≤ 300000 := by rw [hr₀] at hq2; linarith
  have hq3n : q ≤ 300000 := by exact_mod_cast hq3
  set δ := (α - a / q) * y with hδ_def
  set c : ℕ → ℂ := fun n => ((Λ n * etaU (n / y) : ℝ) : ℂ) with hc_def
  have hcs : Summable fun n => ‖c n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (Helfgott.summable_etaStar hx0)
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [c]
    · rw [etaStar_eq_etaU (by positivity)]
      simp only [c, Complex.norm_real]
      apply le_of_eq; congr 3; rw [hy_def]; field_simp
  -- move to `b.val / q + δ/y`
  set b : ZMod q := (a : ZMod q)
  have hb : IsUnit b := (ZMod.coe_int_isUnit_iff_isCoprime a q).mpr ha.symm
  have hval : ((b.val : ℤ) : ℝ) = (a % q : ℤ) := by rw [ZMod.val_intCast]
  have hα : α = (b.val : ℝ) / q + δ / y + (a / q : ℤ) := by
    have e1 : (a : ℝ) = (a % q : ℤ) + q * (a / q : ℤ) := by
      have := Int.mul_ediv_add_emod a q
      have h' : ((q * (a / q) + a % q : ℤ) : ℝ) = (a : ℝ) := by exact_mod_cast this
      push_cast at h' ⊢; linarith
    have e2 : ((b.val : ℕ) : ℝ) = ((a % q : ℤ) : ℝ) := by exact_mod_cast hval
    rw [hδ_def, e2]; field_simp; rw [e1]; ring
  have hper := (expTsum_periodic c).int_mul (a / q) ((b.val : ℝ) / q + δ / y)
  rw [mul_one] at hper
  rw [S_etaStar_eq_expTsum hx0, ← hy_def, ← hc_def, hα, hper]
  -- the character bound
  set E₁ : ℝ := 1e-17 + 4.7e6 / √y
  set K : ℕ := ⌈2 * Real.log y / Real.log 2⌉₊ + 1
  have hl2 : 0.693 < Real.log 2 := Real.log_two_gt_d9.trans' (by norm_num)
  have hK : y ^ 2 ≤ 2 ^ K := by
    have h1 : 2 * Real.log y / Real.log 2 ≤ K := by
      have := Nat.le_ceil (2 * Real.log y / Real.log 2); push_cast [K]; linarith
    have : Real.log (y ^ 2) ≤ Real.log ((2:ℝ) ^ K) := by
      rw [Real.log_pow, Real.log_pow]
      rw [div_le_iff₀ (by linarith)] at h1; push_cast; linarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).1 this
  have hD := sum_noncoprime_le hy hq1 hK
  have hchar : ∀ ψ : DirichletCharacter ℂ q,
      ‖Schar ψ⁻¹.primitiveCharacter c (δ / y) -
        (if ψ = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * y else 0)‖ ≤ E₁ * y := by
    intro ψ
    set d := ψ⁻¹.conductor
    have : NeZero d := ⟨DirichletCharacter.conductor_ne_zero _⟩
    have hdq : d ∣ q := DirichletCharacter.conductor_dvd_level _
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hdq' : (d : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hdq
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
    have hδd : |δ| ≤ 4 * 300000 / d := by
      have : 8 * r₀ / q ≤ 4 * 300000 / (d : ℝ) := by
        rw [hr₀, div_le_div_iff₀ hq0 hd0]; nlinarith
      linarith
    have key := cor_7_1_3 (y := y) (by linarith) (by exact_mod_cast hdq'.trans hq3) _
      (DirichletCharacter.primitiveCharacter_isPrimitive ψ⁻¹) hδd
    have hiff : (ψ = 1) ↔ (d = 1) := by
      rw [← inv_eq_one, DirichletCharacter.eq_one_iff_conductor_eq_one]
    have hif : (if ψ = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * y else 0) =
        (if d = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * y else 0) := by
      by_cases h : ψ = 1
      · rw [ite_eq_left h, ite_eq_left (hiff.1 h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.2 h'))]
    rw [hif]
    refine key.trans (mul_le_mul_of_nonneg_right ?_ hy0.le)
    have hsd : 1 ≤ √(d : ℝ) := by rw [Real.le_sqrt (by norm_num) hd0.le]; exact_mod_cast hd1
    have : 4.7e6 / √(d : ℝ) ≤ 4.7e6 := div_le_self (by norm_num) hsd
    have hsy : 0 < √y := Real.sqrt_pos.2 hy0
    simp only [E₁]
    have : 4.7e6 / √(d : ℝ) / √y ≤ 4.7e6 / √y := div_le_div_of_nonneg_right this hsy.le
    linarith
  refine (norm_expTsum_le_of_chars hcs (δ / y) hb hD hchar).trans ?_
  -- numerics
  have hδ0 : 600000 / (49 * q) ≤ |δ| := by
    have : 4 * r₀ / (κ * q) = 600000 / (49 * q) := by rw [hr₀, hκ]; ring
    linarith
  have hδpos : 0 < |δ| := lt_of_lt_of_le (by positivity) hδ0
  have hδne : -δ ≠ 0 := by
    intro h; rw [neg_eq_zero] at h; rw [h, abs_zero] at hδpos; exact lt_irrefl 0 hδpos
  have hM : ‖𝓕 (fun u => (etaU u : ℂ)) (-δ) * (y : ℂ)‖ ≤ 1.016 / δ ^ 2 * y := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    refine mul_le_mul_of_nonneg_right ?_ hy0.le
    refine (norm_fourier_etaU_le hδne).trans ?_
    have hc := fourier_const_le
    have e : c₀ * (√(π / (1 / 2)) / 2) / (2 * π * -δ) ^ 2 =
        c₀ * (√(π / (1 / 2)) / 2) / (2 * π) ^ 2 / δ ^ 2 := by
      have : (0:ℝ) < π := Real.pi_pos
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hc (by positivity)
  have hφ : (q : ℝ) / q.totient < 5.53 := by
    have := Prelim.div_totient_lt hq1 (r := 300000) (by norm_num) hq3
    have h := Fr_300000_le
    unfold Fr at h
    linarith
  have htot : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hMφ : ‖𝓕 (fun u => (etaU u : ℂ)) (-δ) * (y : ℂ)‖ / q.totient ≤ 0.01125 * y := by
    have hδsq : (600000 / (49 * q)) ^ 2 ≤ δ ^ 2 := by
      rw [← sq_abs δ]; exact pow_le_pow_left₀ (by positivity) hδ0 2
    have h1 : 1.016 / δ ^ 2 ≤ 1.016 / (600000 / (49 * q)) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hδsq
    have h2 : ‖𝓕 (fun u => (etaU u : ℂ)) (-δ) * (y : ℂ)‖ / q.totient ≤
        1.016 / (600000 / (49 * q)) ^ 2 * y / q.totient :=
      div_le_div_of_nonneg_right (hM.trans (mul_le_mul_of_nonneg_right h1 hy0.le)) htot.le
    refine h2.trans ?_
    have e : 1.016 / (600000 / (49 * q)) ^ 2 * y / q.totient =
        1.016 * 2401 / 3.6e11 * y * q * (q / q.totient) := by field_simp; ring
    rw [e]
    have : (q : ℝ) * (q / q.totient) ≤ 300000 * 5.53 :=
      mul_le_mul hq3 hφ.le (by positivity) (by norm_num)
    nlinarith
  have hsq : √(q : ℝ) ≤ 548 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hsy : 3.16e12 ≤ √y := by rw [Real.le_sqrt (by norm_num) hy0.le]; linarith
  have hE₁ : E₁ ≤ 1.4874e-6 := by
    simp only [E₁]
    have : 4.7e6 / √y ≤ 4.7e6 / 3.16e12 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsy
    norm_num at this ⊢; linarith
  -- `D = 6.2 K log q + 1` is negligible
  have hlogy : Real.log y ≤ 2 * √y := by
    have := Real.log_le_rpow_div hy0.le (show (0:ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this; linarith
  have hsyy : √y ≤ y / 3.16e12 := by
    rw [le_div_iff₀ (by norm_num)]
    have := Real.mul_self_sqrt hy0.le
    nlinarith
  have hKb : (K : ℝ) ≤ 2.9 * Real.log y + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log y / Real.log 2 by
      have := Real.log_nonneg (show (1:ℝ) ≤ y by linarith); positivity)
    have : 2 * Real.log y / Real.log 2 ≤ 2.9 * Real.log y := by
      rw [div_le_iff₀ (by linarith)]
      have hl0 := Real.log_nonneg (show (1:ℝ) ≤ y by linarith)
      have h2 : (2:ℝ) ≤ 2.9 * Real.log 2 := by linarith
      calc 2 * Real.log y ≤ (2.9 * Real.log 2) * Real.log y := mul_le_mul_of_nonneg_right h2 hl0
        _ = 2.9 * Real.log y * Real.log 2 := by ring
    push_cast [K]; linarith
  have hlq : Real.log q ≤ 12.62 := by
    refine (Real.log_le_log hq0 hq3).trans ?_
    refine (log_le_num 12 0.62 (by norm_num) (by norm_num) ?_).trans (by norm_num)
    unfold taylor6; norm_num
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  have hDb : 6.2 * K * Real.log q + 1 ≤ 2e-9 * y := by
    have hly0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have : 6.2 * K * Real.log q ≤ 6.2 * (2.9 * Real.log y + 2) * 12.62 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hKb (by norm_num)) hlq hlq0 (by positivity)
    linarith [hlogy, hsyy, hy]
  have hE0 : 0 ≤ E₁ := by simp only [E₁]; positivity
  have hD0 : 0 ≤ 6.2 * K * Real.log q + 1 := by positivity
  have h3 : √(q : ℝ) * (E₁ * y + (6.2 * K * Real.log q + 1)) ≤ 548 * (1.4874e-6 * y + 2e-9 * y) :=
    mul_le_mul hsq (by linarith [mul_le_mul_of_nonneg_right hE₁ hy0.le]) (by positivity) (by norm_num)
  linarith

end TernaryGoldbach.MinorArcs
