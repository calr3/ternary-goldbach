import TernaryGoldbach.MinorArcs.G2TailNum
import TernaryGoldbach.MinorArcs.T2Small
import TernaryGoldbach.MinorArcs.G2Euler
import TernaryGoldbach.Prelim.MoebiusProfile
import Mathlib.NumberTheory.ZetaValues

/-!
# `∫_{10⁴}^S |g₂(y)|/y dy ≤ 0.0082`

For `y ≥ 1`, `N = ⌊y⌋`: `|g₂(y)| ≤ ∑_d f(d)² S_d(N/d)²` (`abs_g2_le_sum`) and
`S_d(M) = ∑_{a ≤ M} H_d(a) m(M/a)` (`Sd_eq`), `m(K) = ∑_{n ≤ K} μ(n)/n`. By Cauchy–Schwarz with
weights `H_d(a) λ(da)` (`λ > 0` arbitrary),
`S_d(M)² ≤ (∑_a H_d(a) λ(da)) (∑_a H_d(a) m(M/a)²/λ(da))`,
and `∫_X^S m(⌊y/u⌋)²/y dy ≤ ∫_{X/u}^∞ m(⌊t⌋)²/t dt =: V(X/u)` (Minkowski in the form of a weighted
Cauchy–Schwarz). With `λ(u) ≈ √V(X/u)` this gives
`∫_X^S |g₂|/y ≤ ∑_d f(d)² (∑_a H_d(a) λ(da)) (∑_a H_d(a) V(X/(da))/λ(da))`.
`V(k)` for `k ≤ X = 10⁴` is computed by the kernel from `m(j)`, `j < 11815`, plus
`|m(x)| log x ≤ mprof(x)` beyond (`MoebiusProfile.lean`; `∑_{j ≥ 11815} m(j)² log(1 + 1/j) ≤ 5.0423·10⁻⁴`,
`sum_tail_le`); the sum over `d ≤ X`, `a ≤ X/d` is evaluated by the kernel
(`G2TailNum.lean`), the rest by `∑_a H_d(a) ≤ 2 (π²/8) σ(d)/d` (an Euler product and `ζ(2) = π²/6`).
-/

open Real Finset MeasureTheory
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs.G2Tail

open TernaryGoldbach.MinorArcs TernaryGoldbach.MinorArcs.T2K TernaryGoldbach.MinorArcs.G2TailNum

/-! ### `∏_{p odd} p²/(p² − 1) ≤ π²/8` -/

/-- `f(n) = 1/n²` for odd `n`, `0` otherwise. -/
noncomputable def fodd (n : ℕ) : ℝ := if Odd n then 1 / (n : ℝ) ^ 2 else 0

theorem fodd_nonneg (n : ℕ) : 0 ≤ fodd n := by unfold fodd; split_ifs <;> positivity

theorem hasSum_fodd : HasSum fodd (π ^ 2 / 8) := by
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hg : HasSum g (π ^ 2 / 6) := hasSum_zeta_two
  set e : ℕ → ℝ := fun n => if Even n then g n else 0
  have hge : ∀ n, 0 ≤ e n := fun n => by simp only [e, g]; split_ifs <;> positivity
  have hse : Summable e := Summable.of_nonneg_of_le hge
    (fun n => by simp only [e, g]; split_ifs <;> [exact le_rfl; positivity]) hg.summable
  have hte : ∑' n, e n = π ^ 2 / 24 := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
    have hsupp : Function.support e ⊆ Set.range (fun k : ℕ => 2 * k) := by
      intro n hn
      simp only [Function.mem_support, e] at hn
      split_ifs at hn with h
      · obtain ⟨k, hk⟩ := h; exact ⟨k, by simp only; omega⟩
      · exact absurd rfl hn
    rw [← hinj.tsum_eq hsupp]
    have : ∀ k : ℕ, e (2 * k) = 1 / 4 * g k := by
      intro k
      simp only [e, g, even_two_mul, if_true]
      push_cast
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · field_simp; ring
    simp_rw [this]
    rw [tsum_mul_left, hg.tsum_eq]
    ring
  have hfo : fodd = fun n => g n - e n := by
    funext n
    simp only [fodd, e, g]
    rcases Nat.even_or_odd n with h | h
    · rw [if_neg (Nat.not_odd_iff_even.2 h), if_pos h, sub_self]
    · rw [if_pos h, if_neg (Nat.not_even_iff_odd.2 h), sub_zero]
  rw [hfo]
  have := hg.sub (hte ▸ hse.hasSum)
  convert this using 1
  ring

theorem tsum_fodd_le : ∑' n, fodd n ≤ 1.2338 := by
  rw [hasSum_fodd.tsum_eq]
  have h1 := Real.pi_lt_d4
  have h0 := Real.pi_pos
  nlinarith

theorem fodd_mul {m n : ℕ} : fodd (m * n) = fodd m * fodd n := by
  unfold fodd
  by_cases hm : Odd m <;> by_cases hn : Odd n
  · rw [if_pos (hm.mul hn), if_pos hm, if_pos hn]; push_cast; ring
  · rw [if_neg (fun h => hn (Nat.odd_mul.1 h).2), if_neg hn]; simp
  · rw [if_neg (fun h => hm (Nat.odd_mul.1 h).1), if_neg hm]; simp
  · rw [if_neg (fun h => hm (Nat.odd_mul.1 h).1), if_neg hm]; simp

theorem tsum_fodd_pow {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, fodd (p ^ e) = if p = 2 then 1 else ell 0 p := by
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl, tsum_eq_single 0]
    · simp [fodd]
    · intro e he
      have : ¬ Odd (2 ^ e) := by
        rw [Nat.not_odd_iff_even]; exact (Nat.even_pow.2 ⟨even_two, he⟩)
      simp [fodd, this]
  · rw [if_neg h2]
    have hodd : Odd p := hp.odd_of_ne_two h2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have e1 : ∀ e : ℕ, fodd (p ^ e) = (((p : ℝ) ^ 2)⁻¹) ^ e := by
      intro e
      simp only [fodd, if_pos (hodd.pow), Nat.cast_pow]
      rw [one_div, inv_pow]; congr 1; ring
    simp_rw [e1]
    have hr : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    rw [tsum_geometric_of_lt_one (by positivity) hr]
    unfold ell
    rw [Real.rpow_zero]
    have hp2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring

/-- **`∏_{2 < p < M} ℓ₀(p) ≤ 1.2338`** (`ℓ₀(p) = p²/(p² − 1)`). -/
theorem prod_ell0_le (M : ℕ) : ∏ p ∈ (Nat.primesBelow M).filter (· ≠ 2), ell 0 p ≤ 1.2338 := by
  obtain ⟨-, hH⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := fodd) (by simp [fodd]) (fun {m n} _ => fodd_mul)
    (fun {p} hp => by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (fodd_nonneg _)]
      by_cases h2 : p = 2
      · subst h2
        refine summable_of_ne_finset_zero (s := {0}) fun e he => ?_
        have : ¬ Odd (2 ^ e) := by
          rw [Nat.not_odd_iff_even]; exact Nat.even_pow.2 ⟨even_two, by simpa using he⟩
        simp [fodd, this]
      · have hodd : Odd p := hp.odd_of_ne_two h2
        have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        have e1 : ∀ e : ℕ, fodd (p ^ e) = (((p : ℝ) ^ 2)⁻¹) ^ e := by
          intro e
          simp only [fodd, if_pos (hodd.pow), Nat.cast_pow]
          rw [one_div, inv_pow]; congr 1; ring
        simp_rw [e1]
        exact summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by nlinarith))) M
  have hprod : ∏ p ∈ M.primesBelow, ∑' e : ℕ, fodd (p ^ e) =
      ∏ p ∈ (Nat.primesBelow M).filter (· ≠ 2), ell 0 p := by
    rw [prod_congr rfl fun p hp => tsum_fodd_pow (Nat.mem_primesBelow.1 hp).2, prod_ite,
      prod_const_one, one_mul]
  rw [← hprod, ← hH.tsum_eq]
  exact (Summable.tsum_subtype_le fodd _ fodd_nonneg
    (hasSum_fodd.summable)).trans tsum_fodd_le

/-- **`∑_{a ≤ A} H_d(a) ≤ 2 · 1.2338 ∏_{p ∣ d} (p+1)/p`** for odd `d`. -/
theorem sum_Hd_le {d : ℕ} (hd : Odd d) (A : ℕ) :
    ∑ a ∈ Icc 1 A, Hd d a ≤ 2 * 1.2338 * ∏ p ∈ d.primeFactors, (((p : ℝ) + 1) / p) := by
  have h := sum_Hd_rpow_le hd (s := 0) le_rfl (by norm_num) A
  simp only [Real.rpow_zero, mul_one] at h
  have hc : cfac 0 2 = 2 := by unfold cfac; rw [Real.rpow_zero]; norm_num
  have hr : ∀ p ∈ d.primeFactors, rho 0 p = ((p : ℝ) + 1) / p := by
    intro p _; unfold rho; rw [Real.rpow_zero]; ring_nf
  rw [hc, prod_congr rfl hr] at h
  have hr0 : 0 ≤ ∏ p ∈ d.primeFactors, (((p : ℝ) + 1) / p) := prod_nonneg fun p _ => by positivity
  refine h.trans ?_
  have := prod_ell0_le (A + 1)
  nlinarith

/-! ### `H_d(a) = σ((a, d))/den₁(a)` -/

theorem kapH_pos (d p : ℕ) : 0 < kapH d p := by unfold kapH; split_ifs <;> positivity

/-- `a H_d(a) = ∏_{p ∣ a} κ_d(p)`. -/
theorem Hd_mul_self {d a : ℕ} (ha : 0 < a) : Hd d a * a = ∏ p ∈ a.primeFactors, kapH d p := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization (Hd d) (isMultiplicative_Hd d)
    ha.ne']
  conv_lhs => rw [show (a : ℝ) = ((a.factorization.prod fun p k => p ^ k : ℕ) : ℝ) by
    rw [Nat.prod_factorization_pow_eq_self ha.ne']]
  unfold Finsupp.prod
  push_cast
  rw [← prod_mul_distrib, Nat.support_factorization]
  refine prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Finsupp.mem_support_iff.1 (by rwa [Nat.support_factorization]))
  rw [hk, Hd_prime_pow hp']
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  rw [Nat.succ_eq_add_one, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ this), mul_one]

theorem Hd_pos {d a : ℕ} (ha : 0 < a) : 0 < Hd d a := by
  have h := Hd_mul_self (d := d) ha
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have : 0 < ∏ p ∈ a.primeFactors, kapH d p := prod_pos fun p _ => kapH_pos d p
  rw [← h] at this
  exact pos_of_mul_pos_left this ha'.le

theorem toFinset_filter_oddPrimes {d a : ℕ} (hd : Odd d) (ha : 0 < a) :
    ((oddPrimes d).filter (fun p => a % p == 0)).toFinset =
      (a.primeFactors.filter (· ≠ 2)).filter (· ∣ d) := by
  ext p
  simp only [List.mem_toFinset, List.mem_filter, mem_oddPrimes hd.pos, beq_iff_eq, mem_filter,
    Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hpd, hp2⟩, hpa⟩
    exact ⟨⟨⟨hp, Nat.dvd_of_mod_eq_zero hpa, ha.ne'⟩, hp2⟩, hpd⟩
  · rintro ⟨⟨⟨hp, hpa, -⟩, hp2⟩, hpd⟩
    exact ⟨⟨hp, hpd, hp2⟩, Nat.mod_eq_zero_of_dvd hpa⟩

/-- **`H_d(a) = σ((a, d))/den₁(a)`** for odd squarefree `d`. -/
theorem Hd_eq {d a : ℕ} (hd : Odd d) (ha : 0 < a) :
    Hd d a = (sgc (oddPrimes d) a : ℝ) / den1 a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  set F := a.primeFactors.filter (· ≠ 2)
  have hcomp : (Nat.cast ∘ fun x : ℕ => x + 1) = (fun p : ℕ => (p : ℝ) + 1) := by
    funext p; simp
  have hden : (den1 a : ℝ) = a * ∏ p ∈ F, ((p : ℝ) + 1) := by
    unfold den1
    rw [Nat.cast_mul, Nat.cast_list_prod, List.map_map, hcomp,
      ← List.prod_toFinset _ (nodup_oddPrimes ha), toFinset_oddPrimes ha]
  have hsg : (sgc (oddPrimes d) a : ℝ) = ∏ p ∈ F.filter (· ∣ d), ((p : ℝ) + 1) := by
    unfold sgc
    rw [Nat.cast_list_prod, List.map_map, hcomp,
      ← List.prod_toFinset _ ((nodup_oddPrimes hd.pos).filter _), toFinset_filter_oddPrimes hd ha]
  have hk : ∏ p ∈ a.primeFactors, kapH d p = ∏ p ∈ F.filter (fun p => ¬ p ∣ d), (1 / ((p : ℝ) + 1)) := by
    unfold kapH
    rw [prod_ite, prod_const_one, mul_one, filter_filter]
  have hpos : ∀ p ∈ F, (0 : ℝ) < (p : ℝ) + 1 := fun p _ => by positivity
  rw [hden, hsg, ← prod_filter_mul_prod_filter_not F (· ∣ d)]
  rw [eq_div_iff (by positivity), ← mul_assoc, mul_comm (Hd d a), mul_assoc, ← mul_assoc _ (Hd d a),
    mul_comm _ (Hd d a), Hd_mul_self ha, hk]
  rw [prod_div_distrib, prod_const_one]
  have : ∏ p ∈ F.filter (fun p => ¬ p ∣ d), ((p : ℝ) + 1) ≠ 0 :=
    (prod_pos fun p hp => hpos p (mem_filter.1 hp).1).ne'
  field_simp

/-! ### `∫ m(⌊t⌋)²/t` -/

/-- `m(K) = ∑_{n ≤ K} μ(n)/n`. -/
noncomputable def mm (K : ℕ) : ℝ := ∑ b ∈ Icc 1 K, (μ b : ℝ) / b

theorem mm_zero : mm 0 = 0 := by simp [mm]

theorem abs_mm_le (K : ℕ) : |mm K| ≤ K := by
  unfold mm
  calc |∑ b ∈ Icc 1 K, (μ b : ℝ) / b| ≤ ∑ b ∈ Icc 1 K, |(μ b : ℝ) / b| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ Icc 1 K, (1 : ℝ) := sum_le_sum fun b hb => by
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (mem_Icc.1 hb).1
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < b)]
        exact (div_le_one (by linarith)).2 ((SmallG2.abs_moebius_le' b).trans hb1)
    _ = K := by simp

/-- `φ(t) = m(⌊t⌋)²/t`. -/
noncomputable def phi (t : ℝ) : ℝ := mm ⌊t⌋₊ ^ 2 / t

theorem measurable_phi : Measurable phi :=
  ((measurable_from_nat (f := fun K => mm K ^ 2)).comp Nat.measurable_floor).div measurable_id

theorem phi_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ phi t := div_nonneg (sq_nonneg _) ht

theorem abs_phi_le {t b : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) : |phi t| ≤ b ^ 2 := by
  rw [abs_of_nonneg (phi_nonneg ht)]
  unfold phi
  rcases lt_or_ge t 1 with h | h
  · rw [Nat.floor_eq_zero.2 h, mm_zero]; simp; positivity
  · have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
    have h1 := abs_mm_le ⌊t⌋₊
    have h2 : mm ⌊t⌋₊ ^ 2 ≤ t ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans hfl) 2
    rw [div_le_iff₀ (by linarith)]
    nlinarith

theorem intervalIntegrable_phi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable phi volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine IntegrableOn.of_bound measure_Ioc_lt_top measurable_phi.aestronglyMeasurable (b ^ 2) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs]
  exact abs_phi_le (ha.trans ht.1.le) ht.2

theorem integral_phi_step (j : ℕ) : ∫ t in (j : ℝ)..(j + 1), phi t = mm j ^ 2 * Real.log (1 + 1 / j) := by
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (j + 1 : ℝ) := by
    rw [ae_iff]; simp [measure_singleton]
  have e : ∫ t in (j : ℝ)..(j + 1), phi t = ∫ t in (j : ℝ)..(j + 1), mm j ^ 2 / t := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with t ht hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have h0 : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg j) hmem.1.le
    have : ⌊t⌋₊ = j := (Nat.floor_eq_iff h0).2 ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht⟩
    unfold phi; rw [this]
  rw [e]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [mm_zero]
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have : ∀ t : ℝ, mm j ^ 2 / t = mm j ^ 2 * t⁻¹ := fun t => div_eq_mul_inv _ _
  simp only [this]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hj0 (by linarith)]
  congr 2
  field_simp

theorem integral_phi_nat : ∀ m : ℕ, ∫ t in (0 : ℝ)..m, phi t = ∑ j ∈ range m, mm j ^ 2 * Real.log (1 + 1 / j) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (m : ℝ))
      (intervalIntegrable_phi le_rfl h0) (intervalIntegrable_phi h0 (by push_cast; linarith)), ih,
      sum_range_succ]
    push_cast
    rw [integral_phi_step]

/-- **`∫_A^B m(⌊t⌋)²/t dt ≤ ∑_{⌊A⌋ ≤ j ≤ ⌊B⌋} m(j)² log(1 + 1/j)`**. -/
theorem integral_phi_le {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    ∫ t in A..B, phi t ≤ ∑ j ∈ Icc ⌊A⌋₊ ⌊B⌋₊, mm j ^ 2 * Real.log (1 + 1 / j) := by
  have h1 : (⌊A⌋₊ : ℝ) ≤ A := Nat.floor_le hA
  have h2 : B ≤ (⌊B⌋₊ + 1 : ℕ) := by push_cast; exact (Nat.lt_floor_add_one B).le
  have hmono : ∫ t in A..B, phi t ≤ ∫ t in (⌊A⌋₊ : ℝ)..((⌊B⌋₊ + 1 : ℕ) : ℝ), phi t :=
    intervalIntegral.integral_mono_interval h1 hAB h2
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht =>
        phi_nonneg (le_trans (Nat.cast_nonneg _) ht.1.le)))
      (intervalIntegrable_phi (Nat.cast_nonneg _) (h1.trans (hAB.trans h2)))
  refine hmono.trans (le_of_eq ?_)
  have hle : ⌊A⌋₊ ≤ ⌊B⌋₊ + 1 := by
    have := Nat.floor_le_floor (a := A) (b := B) hAB; omega
  rw [← intervalIntegral.integral_interval_sub_left (a := (0 : ℝ))
    (intervalIntegrable_phi le_rfl (Nat.cast_nonneg _)) (intervalIntegrable_phi le_rfl (Nat.cast_nonneg _)),
    integral_phi_nat, integral_phi_nat, ← Finset.sum_range_add_sum_Ico _ hle, add_sub_cancel_left]
  rfl

/-! ### `V(k)`: the table and the tail -/

open TernaryGoldbach.Prelim.SmallMoeb (Pt Qt sum_approx)

theorem mm_eq (k : ℕ) : mm k = ∑ n ∈ Icc 1 k, (μ n : ℝ) / n := rfl

theorem tL_le_tU {j : ℕ} (hj : 1 ≤ j) :
    (tL j : ℝ) ≤ 10 ^ 24 * (mm j ^ 2 * Real.log (1 + 1 / j)) ∧
      10 ^ 24 * (mm j ^ 2 * Real.log (1 + 1 / j)) ≤ (tU j : ℝ) := by
  obtain ⟨l1, l2⟩ := log_bounds hj
  have hsa := sum_approx j
  rw [← mm_eq] at hsa
  set a : ℕ := (Pt j - Qt j) + (Qt j - Pt j)
  have ha : (a : ℝ) = |(Pt j : ℝ) - Qt j| := by
    rcases le_total (Pt j) (Qt j) with h | h
    · have h' : (Pt j : ℝ) ≤ Qt j := by exact_mod_cast h
      simp only [a, Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]
      rw [abs_of_nonpos (by linarith)]; ring
    · have h' : (Qt j : ℝ) ≤ Pt j := by exact_mod_cast h
      simp only [a, Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h]
      rw [abs_of_nonneg (by linarith)]
  have hm1 : |1000000000000 * mm j| ≤ a + j := by
    have := abs_sub_abs_le_abs_sub (1000000000000 * mm j) ((Pt j : ℝ) - Qt j)
    rw [← ha] at this; linarith
  have hm2 : (a : ℝ) - j ≤ |1000000000000 * mm j| := by
    have := abs_sub_abs_le_abs_sub ((Pt j : ℝ) - Qt j) (1000000000000 * mm j)
    rw [← ha, abs_sub_comm] at this; linarith
  have hsq : (10 : ℝ) ^ 24 * mm j ^ 2 = |1000000000000 * mm j| ^ 2 := by
    rw [sq_abs]; ring
  have hj0 : (0 : ℝ) ≤ 1 / j := by positivity
  have hlog0 : 0 ≤ Real.log (1 + 1 / j) := Real.log_nonneg (by linarith)
  have hD1 : (0 : ℝ) < lhiD j := by unfold lhiD; positivity
  have hD0 : (0 : ℝ) < lloD j := by unfold lloD; positivity
  constructor
  · unfold tL termL
    have hnat : (((a - j) ^ 2 * lloN j / lloD j : ℕ) : ℝ) ≤ ((a - j : ℕ) : ℝ) ^ 2 * lloN j / lloD j := by
      have := Nat.cast_div_le (α := ℝ) (m := (a - j) ^ 2 * lloN j) (n := lloD j)
      push_cast at this; exact this
    refine hnat.trans ?_
    rw [div_le_iff₀ hD0]
    rcases le_total j a with h | h
    · have hc : ((a - j : ℕ) : ℝ) = a - j := by push_cast [h]; ring
      rw [hc]
      have hja : (j : ℝ) ≤ a := by exact_mod_cast h
      have h3 : ((a : ℝ) - j) ^ 2 ≤ (10 : ℝ) ^ 24 * mm j ^ 2 := by
        rw [hsq]; exact pow_le_pow_left₀ (by linarith) hm2 2
      have h4 : (lloN j : ℝ) ≤ Real.log (1 + 1 / j) * lloD j := by rwa [div_le_iff₀ hD0] at l1
      calc ((a : ℝ) - j) ^ 2 * lloN j ≤ ((10 : ℝ) ^ 24 * mm j ^ 2) * (Real.log (1 + 1 / j) * lloD j) :=
            mul_le_mul h3 h4 (Nat.cast_nonneg _) (by positivity)
        _ = 10 ^ 24 * (mm j ^ 2 * Real.log (1 + 1 / j)) * lloD j := by ring
    · rw [Nat.sub_eq_zero_of_le h]
      have h0 : 0 ≤ 10 ^ 24 * (mm j ^ 2 * Real.log (1 + 1 / j)) * (lloD j : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hlog0)) hD0.le
      refine le_trans (le_of_eq ?_) h0
      simp
  · unfold tU termU cdiv
    have hc : ∀ x y : ℕ, 0 < y → (x : ℝ) / y ≤ (((x + y - 1) / y : ℕ) : ℝ) := by
      intro x y hy
      have hy' : (0 : ℝ) < y := by exact_mod_cast hy
      rw [div_le_iff₀ hy']
      have hn : x ≤ (x + y - 1) / y * y := by
        have := Nat.lt_div_mul_add (a := x + y - 1) hy; omega
      exact_mod_cast hn
    refine le_trans ?_ (hc _ _ (by exact_mod_cast hD1))
    rw [le_div_iff₀ hD1]
    push_cast
    have h3 : (10 : ℝ) ^ 24 * mm j ^ 2 ≤ ((a : ℝ) + j) ^ 2 := by
      rw [hsq]; exact pow_le_pow_left₀ (abs_nonneg _) hm1 2
    have h4 : Real.log (1 + 1 / j) * lhiD j ≤ lhiN j := by rwa [le_div_iff₀ hD1] at l2
    calc 10 ^ 24 * (mm j ^ 2 * Real.log (1 + 1 / j)) * lhiD j =
          ((10 : ℝ) ^ 24 * mm j ^ 2) * (Real.log (1 + 1 / j) * lhiD j) := by ring
      _ ≤ ((a : ℝ) + j) ^ 2 * lhiN j := mul_le_mul h3 h4 (mul_nonneg hlog0 hD1.le) (by positivity)
      _ = _ := by simp only [a]; push_cast; ring

theorem log_11815_ge9' : 9 ≤ Real.log 11815 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have e : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc Real.exp 1 ^ 9 ≤ (2.7182818286 : ℝ) ^ 9 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 9
    _ ≤ 11815 := by norm_num

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens] in
/-- `m(j)² log(1 + 1/j) ≤ 1.00001 c(j) (1/log j − 1/log(j+1))` for `j ≥ 11815`, `c(j) = mprof(j)²`
(`|m(j)| log j ≤ mprof(j)`, `MoebiusProfile.lean`; `log(j+1)/log j ≤ 1.00001`). -/
theorem tail_term_le {j : ℕ} (hj : 11815 ≤ j) :
    mm j ^ 2 * Real.log (1 + 1 / j) ≤
      1.00001 * (Prelim.mprof j ^ 2 * (1 / Real.log j - 1 / Real.log (j + 1))) := by
  have hj' : (11815 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hl9 : 9 ≤ Real.log j := le_trans log_11815_ge9' (Real.log_le_log (by norm_num) hj')
  have hR := Prelim.moebius_log_le hj'
  rw [Nat.floor_natCast, ← mm_eq] at hR
  set c := Prelim.mprof j with hc
  have hc0 : 0 ≤ c := Prelim.mprof_nonneg _
  have hl0 : 0 < Real.log j := by linarith
  have hm2 : mm j ^ 2 ≤ c ^ 2 / Real.log j ^ 2 := by
    rw [← sq_abs, le_div_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hR 2
  have hL : Real.log (1 + 1 / j) = Real.log (j + 1) - Real.log j := by
    rw [← Real.log_div (by positivity) hj0.ne']; congr 1; field_simp
  have hj1 : (0 : ℝ) ≤ 1 / j := by positivity
  have hL0 : 0 ≤ Real.log (1 + 1 / j) := Real.log_nonneg (by linarith)
  have hL1 : Real.log (1 + 1 / j) ≤ 1 / j := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / j by positivity); linarith
  have hlj1 : Real.log j ≤ Real.log (j + 1) := Real.log_le_log hj0 (by linarith)
  have hl1 : 0 < Real.log (j + 1) := by linarith
  have e : 1 / Real.log j - 1 / Real.log (j + 1) =
      Real.log (1 + 1 / j) / (Real.log j * Real.log (j + 1)) := by
    rw [hL]; field_simp
  rw [e]
  have hrat : Real.log (j + 1) ≤ 1.00001 * Real.log j := by
    have : Real.log (j + 1) ≤ Real.log j + 1 / j := by linarith [hL, hL1]
    have h2 : 1 / (j : ℝ) ≤ 0.00001 * 9 := by
      rw [div_le_iff₀ hj0]; nlinarith
    nlinarith
  have hll : Real.log j * Real.log (j + 1) ≤ 1.00001 * Real.log j ^ 2 := by nlinarith
  calc mm j ^ 2 * Real.log (1 + 1 / j) ≤ c ^ 2 / Real.log j ^ 2 * Real.log (1 + 1 / j) :=
        mul_le_mul_of_nonneg_right hm2 hL0
    _ = c ^ 2 * Real.log (1 + 1 / j) / Real.log j ^ 2 := by ring
    _ ≤ 1.00001 * c ^ 2 * Real.log (1 + 1 / j) / (Real.log j * Real.log (j + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ c ^ 2 * Real.log (1 + 1 / j) := by positivity
        nlinarith
    _ = 1.00001 * (c ^ 2 * (Real.log (1 + 1 / j) / (Real.log j * Real.log (j + 1)))) := by ring

/-! ### The tail `∑_{j ≥ K} m(j)² log(1 + 1/j)` -/

/-- `1/log j`. -/
noncomputable def il (j : ℕ) : ℝ := 1 / Real.log j

/-- The first `j` with `log j ≥ 200`. -/
noncomputable def N200 : ℕ := ⌈Real.exp 200⌉₊

/-- `mprof(j)` with the conditions on `j` stated in `ℕ`. -/
noncomputable def cpr (j : ℕ) : ℝ :=
  if j < 2160535 then 0.03 else if j < 10000000 then 0.14 else if j < 49603849 then 0.1
  else if j < 10000000000 then 0.08 else if j < N200 then 0.065 else 0.09

theorem mprof_eq_cpr {j : ℕ} (hj : 1 ≤ j) : Prelim.mprof j = cpr j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hN : j < N200 ↔ Real.log j < 200 := by
    rw [N200, Nat.lt_ceil, Real.log_lt_iff_lt_exp hj0]
  unfold Prelim.mprof cpr
  simp only [hN]
  norm_cast

/-- `B(j) = ∑ over the steps from `j` on of `c (1/log a − 1/log b)``: the telescoping bound. -/
noncomputable def Bt (j : ℕ) : ℝ :=
  let T6 := 0.0081 * il N200
  let T5 := 0.004225 * (il 10000000000 - il N200) + T6
  let T4 := 0.0064 * (il 49603849 - il 10000000000) + T5
  let T3 := 0.01 * (il 10000000 - il 49603849) + T4
  let T2 := 0.0196 * (il 2160535 - il 10000000) + T3
  if j < 2160535 then 0.0009 * (il j - il 2160535) + T2
  else if j < 10000000 then 0.0196 * (il j - il 10000000) + T3
  else if j < 49603849 then 0.01 * (il j - il 49603849) + T4
  else if j < 10000000000 then 0.0064 * (il j - il 10000000000) + T5
  else if j < N200 then 0.004225 * (il j - il N200) + T6
  else 0.0081 * il j

theorem N200_big : 10000000000 < N200 := by
  have h := Prelim.exp_200_ge
  have : ((10000000000 : ℕ) : ℝ) < Real.exp 200 := by norm_num at h ⊢; linarith
  exact Nat.lt_ceil.2 this

theorem Bt_step {j : ℕ} (hj : 2 ≤ j) : Bt j - Bt (j + 1) = cpr j ^ 2 * (il j - il (j + 1)) := by
  have hN := N200_big
  unfold Bt cpr
  simp only
  split_ifs <;> first
    | omega
    | ring1
    | (rw [show j + 1 = 2160535 by omega]; ring1)
    | (rw [show j + 1 = 10000000 by omega]; ring1)
    | (rw [show j + 1 = 49603849 by omega]; ring1)
    | (rw [show j + 1 = 10000000000 by omega]; ring1)
    | (rw [show j + 1 = N200 by omega]; ring1)

theorem il_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : il b ≤ il a := by
  unfold il
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  exact one_div_le_one_div_of_le hla (Real.log_le_log (by linarith) hb')

theorem il_nonneg (j : ℕ) : 0 ≤ il j := by
  unfold il; exact div_nonneg zero_le_one (Real.log_natCast_nonneg j)

theorem Bt_nonneg {j : ℕ} (hj : 2 ≤ j) : 0 ≤ Bt j := by
  have hN := N200_big
  have i1 := il_anti (a := 2160535) (b := 10000000) (by norm_num) (by norm_num)
  have i2 := il_anti (a := 10000000) (b := 49603849) (by norm_num) (by norm_num)
  have i3 := il_anti (a := 49603849) (b := 10000000000) (by norm_num) (by norm_num)
  have i4 := il_anti (a := 10000000000) (b := N200) (by norm_num) hN.le
  have i5 := il_nonneg N200
  have i6 := il_nonneg j
  unfold Bt
  simp only
  split_ifs with h1 h2 h3 h4 h5
  · have := il_anti hj (show j ≤ 2160535 by omega); linarith
  · have := il_anti hj (show j ≤ 10000000 by omega); linarith
  · have := il_anti hj (show j ≤ 49603849 by omega); linarith
  · have := il_anti hj (show j ≤ 10000000000 by omega); linarith
  · have := il_anti hj (show j ≤ N200 by omega); linarith
  · linarith

theorem log_N200_ge : 200 ≤ Real.log N200 := by
  rw [Real.le_log_iff_exp_le (by have := N200_big; positivity)]
  exact Nat.le_ceil _

/-- `B(11815) ≤ 5.0423·10⁻⁴ / 1.00001`. -/
theorem Bt_K_le : 1.00001 * Bt 11815 ≤ (tailV : ℝ) / 10 ^ 24 := by
  have hN := N200_big
  have l1 := Prelim.log_ge_cert (L := 11815) (cN := 93770) (by norm_num) (by decide +kernel)
  have l2 := Prelim.log_ge_cert (L := 2160535) (cN := 145857) (by norm_num) (by decide +kernel)
  have u3 := Prelim.log_le_cert (L := 10000000) (cN := 161182) (by norm_num) (by decide +kernel)
  have u4 := Prelim.log_le_cert (L := 49603849) (cN := 177197) (by norm_num) (by decide +kernel)
  have u5 := Prelim.log_le_cert (L := 10000000000) (cN := 230260) (by norm_num) (by decide +kernel)
  have l6 := log_N200_ge
  have hl3 : 0 < Real.log ((10000000 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log ((49603849 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  have hl5 : 0 < Real.log ((10000000000 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  norm_num at l1 l2 u3 u4 u5
  have k1 : il 11815 ≤ 1 / 9.377 := one_div_le_one_div_of_le (by norm_num) (by norm_num at l1 ⊢; linarith)
  have k2 : il 2160535 ≤ 1 / 14.5857 := one_div_le_one_div_of_le (by norm_num) (by norm_num at l2 ⊢; linarith)
  have k3 : 1 / 16.1182 ≤ il 10000000 := one_div_le_one_div_of_le hl3 (by norm_num at u3 ⊢; linarith)
  have k4 : 1 / 17.7197 ≤ il 49603849 := one_div_le_one_div_of_le hl4 (by norm_num at u4 ⊢; linarith)
  have k5 : 1 / 23.026 ≤ il 10000000000 := one_div_le_one_div_of_le hl5 (by norm_num at u5 ⊢; linarith)
  have k6 : il N200 ≤ 1 / 200 := one_div_le_one_div_of_le (by norm_num) l6
  unfold Bt
  simp only [show (11815 : ℕ) < 2160535 by norm_num, if_true]
  norm_num [tailV] at k1 k2 k3 k4 k5 k6 ⊢
  linarith

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens] in
theorem sum_tail_le (M : ℕ) :
    ∑ j ∈ Icc KK M, mm j ^ 2 * Real.log (1 + 1 / j) ≤ (tailV : ℝ) / 10 ^ 24 := by
  have hK : KK = 11815 := rfl
  have htel : ∀ N : ℕ, ∑ j ∈ Icc KK N, (Bt j - Bt (j + 1)) = Bt KK - Bt (max KK (N + 1)) := by
    intro N
    induction N with
    | zero => rw [hK]; simp
    | succ N ih =>
      by_cases h : KK ≤ N + 1
      · rw [show Icc KK (N + 1) = insert (N + 1) (Icc KK N) by
          ext x; simp only [mem_insert, mem_Icc]; omega, sum_insert (by simp), ih]
        rw [show max KK (N + 1 + 1) = N + 1 + 1 by omega]
        rcases Nat.lt_or_ge N KK with h' | h'
        · rw [show max KK (N + 1) = N + 1 by omega]; ring
        · rw [show max KK (N + 1) = N + 1 by omega]; ring
      · rw [show Icc KK (N + 1) = ∅ by ext x; simp; omega, sum_empty,
          show max KK (N + 1 + 1) = KK by omega]; ring
  calc ∑ j ∈ Icc KK M, mm j ^ 2 * Real.log (1 + 1 / j)
      ≤ ∑ j ∈ Icc KK M, 1.00001 * (Bt j - Bt (j + 1)) := by
        refine sum_le_sum fun j hj => ?_
        have hj1 : 11815 ≤ j := by have := (mem_Icc.1 hj).1; rw [hK] at this; exact this
        have h := tail_term_le hj1
        rw [mprof_eq_cpr (by omega)] at h
        rw [Bt_step (by omega)]
        unfold il; push_cast; exact h
    _ = 1.00001 * (Bt KK - Bt (max KK (M + 1))) := by rw [← mul_sum, htel]
    _ ≤ 1.00001 * Bt 11815 := by
        have := Bt_nonneg (j := max KK (M + 1)) (by rw [hK]; omega)
        rw [hK] at *; nlinarith
    _ ≤ (tailV : ℝ) / 10 ^ 24 := Bt_K_le

theorem F_nonneg (j : ℕ) : 0 ≤ mm j ^ 2 * Real.log (1 + 1 / j) := by
  have : (0 : ℝ) ≤ 1 / j := by positivity
  exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith))

/-- The kernel facts: `∑_{j < K} termU(j) = cP` and the table. -/
theorem sum_tU : ∑ j ∈ Icc 1 (KK - 1), tU j = cP := by
  have h := sV_spec.2.2.2.1
  have h2 : sV.Phi = cP := (Prod.mk.inj tail_ok).1
  rw [← h2, h]

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens] in
/-- **`∑_{j=k}^M m(j)² log(1 + 1/j) ≤ V(k)/10²⁴`** for `1 ≤ k ≤ 10⁴`. -/
theorem sum_mm_le_Vt {k M : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ XX) :
    ∑ j ∈ Icc k M, mm j ^ 2 * Real.log (1 + 1 / j) ≤ (Vt k : ℝ) / 10 ^ 24 := by
  have hK : KK = 11815 := rfl
  have hX : XX = 10000 := rfl
  set F := fun j : ℕ => mm j ^ 2 * Real.log (1 + 1 / j)
  -- split at `K`
  have hsplit : ∑ j ∈ Icc k M, F j ≤ ∑ j ∈ Icc k (KK - 1), F j + ∑ j ∈ Icc KK M, F j := by
    rw [← sum_union (by
      rw [disjoint_left]; intro x h1 h2; simp only [mem_Icc] at h1 h2; omega)]
    exact sum_le_sum_of_subset_of_nonneg (by
      intro x hx; simp only [mem_union, mem_Icc] at hx ⊢; omega) fun j _ _ => F_nonneg j
  -- the part below `K` through the kernel
  have hlow : (10 : ℝ) ^ 24 * ∑ j ∈ Icc k (KK - 1), F j ≤
      (cP : ℝ) - ∑ j ∈ Icc 1 (k - 1), (tL j : ℝ) := by
    have hU : (10 : ℝ) ^ 24 * ∑ j ∈ Icc 1 (KK - 1), F j ≤ cP := by
      rw [← sum_tU]; push_cast; rw [mul_sum]
      exact sum_le_sum fun j hj => (tL_le_tU (mem_Icc.1 hj).1).2
    have hL : ∑ j ∈ Icc 1 (k - 1), (tL j : ℝ) ≤ (10 : ℝ) ^ 24 * ∑ j ∈ Icc 1 (k - 1), F j := by
      rw [mul_sum]; exact sum_le_sum fun j hj => (tL_le_tU (mem_Icc.1 hj).1).1
    have e : ∑ j ∈ Icc 1 (KK - 1), F j = ∑ j ∈ Icc 1 (k - 1), F j + ∑ j ∈ Icc k (KK - 1), F j := by
      rw [← sum_union (by rw [disjoint_left]; intro x h1 h2; simp only [mem_Icc] at h1 h2; omega)]
      congr 1; ext x; simp only [mem_union, mem_Icc]; omega
    rw [e, mul_add] at hU
    linarith
  -- `Vt k` as a real number
  have hLle : ∑ j ∈ Icc 1 (k - 1), tL j ≤ cP + tailV := by
    have : ∑ j ∈ Icc 1 (k - 1), tL j ≤ ∑ j ∈ Icc 1 (KK - 1), tU j := by
      refine (sum_le_sum fun j hj => ?_).trans (sum_le_sum_of_subset (by
        intro x hx; simp only [mem_Icc] at hx ⊢; omega))
      have h := tL_le_tU (j := j) (mem_Icc.1 hj).1
      exact_mod_cast h.1.trans h.2
    rw [sum_tU] at this; omega
  have hVt : (Vt k : ℝ) = cP + tailV - ∑ j ∈ Icc 1 (k - 1), (tL j : ℝ) := by
    unfold Vt; rw [Nat.cast_sub hLle]; push_cast; ring
  have ht := sum_tail_le M
  rw [hVt]
  have : ∑ j ∈ Icc k M, F j ≤ ((cP : ℝ) - ∑ j ∈ Icc 1 (k - 1), (tL j : ℝ)) / 10 ^ 24 + (tailV : ℝ) / 10 ^ 24 := by
    refine hsplit.trans (add_le_add ?_ ht)
    rw [le_div_iff₀ (by norm_num)]; linarith
  rw [add_sub_right_comm, add_div]
  linarith

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens] in
/-- **`∫_X^S m(⌊y/u⌋)²/y dy ≤ V(⌊X/u⌋)/10²⁴`** (`⌊X/u⌋` replaced by `1` when it is `0`). -/
theorem integral_mm_le {u : ℕ} (hu : 1 ≤ u) {S : ℝ} (hS : 10000 ≤ S) :
    ∫ y in (10000 : ℝ)..S, mm ⌊y / u⌋₊ ^ 2 / y ≤
      (Vt (if u ≤ XX then XX / u else 1) : ℝ) / 10 ^ 24 := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have e : ∀ y : ℝ, mm ⌊y / u⌋₊ ^ 2 / y = (u : ℝ)⁻¹ * phi (y / u) := by
    intro y; unfold phi
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div phi hu0.ne', smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hu0.ne', one_mul]
  have hA : (0 : ℝ) ≤ 10000 / u := by positivity
  refine (integral_phi_le hA (div_le_div_of_nonneg_right hS hu0.le)).trans ?_
  have hfl : ⌊(10000 : ℝ) / u⌋₊ = XX / u := by
    rw [show (10000 : ℝ) = ((10000 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast, Nat.floor_natCast]; rfl
  rw [hfl]
  by_cases hux : u ≤ XX
  · rw [if_pos hux]
    exact sum_mm_le_Vt (Nat.div_pos hux hu) (Nat.div_le_self _ _)
  · rw [if_neg hux, Nat.div_eq_of_lt (by omega)]
    calc ∑ j ∈ Icc 0 ⌊S / (u : ℝ)⌋₊, mm j ^ 2 * Real.log (1 + 1 / j)
        = ∑ j ∈ Icc 1 ⌊S / (u : ℝ)⌋₊, mm j ^ 2 * Real.log (1 + 1 / j) := by
          rw [show Icc 0 ⌊S / (u : ℝ)⌋₊ = insert 0 (Icc 1 ⌊S / (u : ℝ)⌋₊) by
            ext x; simp only [mem_insert, mem_Icc]; omega, sum_insert (by simp), mm_zero]; simp
      _ ≤ _ := sum_mm_le_Vt le_rfl (by decide)

/-! ### Weights, the pointwise bound, and integration -/

/-- `k(u) = ⌊X/u⌋` for `u ≤ X`, `1` beyond. -/
def kk (u : ℕ) : ℕ := if u ≤ XX then XX / u else 1

theorem kk_mem {u : ℕ} (hu : 1 ≤ u) : 1 ≤ kk u ∧ kk u ≤ XX := by
  unfold kk
  split_ifs with h
  · exact ⟨Nat.div_pos h hu, Nat.div_le_self _ _⟩
  · exact ⟨le_rfl, by decide⟩

theorem tv_kk {u : ℕ} (hu : 1 ≤ u) :
    sV.tv.get (1, 0) (kk u) = (lam2 (Vt (kk u)), cdiv (Vt (kk u)) (lam2 (Vt (kk u)))) := by
  obtain ⟨h1, h2⟩ := kk_mem hu
  exact sV_spec.2.2.2.2.1 (kk u) h1 (by rw [show min (KK - 1) XX = XX from rfl]; exact h2)

/-- `λ(u)`, `w(u)` from the trie. -/
noncomputable def lamR (u : ℕ) : ℝ := ((sV.tv.get (1, 0) (kk u)).1 : ℝ) / 10 ^ 12
noncomputable def wR (u : ℕ) : ℝ := ((sV.tv.get (1, 0) (kk u)).2 : ℝ) / 10 ^ 12

theorem lam2_pos (v : ℕ) : 0 < lam2 v := by unfold lam2; positivity

theorem lamR_pos {u : ℕ} (hu : 1 ≤ u) : 0 < lamR u := by
  unfold lamR; rw [tv_kk hu]
  have := lam2_pos (Vt (kk u))
  positivity

theorem wR_nonneg (u : ℕ) : 0 ≤ wR u := by unfold wR; positivity

theorem cdiv_ge (x y : ℕ) (hy : 0 < y) : (x : ℝ) / y ≤ (cdiv x y : ℝ) := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  rw [div_le_iff₀ hy']
  have hn : x ≤ cdiv x y * y := by
    unfold cdiv; have := Nat.lt_div_mul_add (a := x + y - 1) hy; omega
  exact_mod_cast hn

theorem V_div_lam_le {u : ℕ} (hu : 1 ≤ u) : (Vt (kk u) : ℝ) / 10 ^ 24 / lamR u ≤ wR u := by
  unfold lamR wR; rw [tv_kk hu]
  have hl := lam2_pos (Vt (kk u))
  have hl' : (0 : ℝ) < lam2 (Vt (kk u)) := by exact_mod_cast hl
  have := cdiv_ge (Vt (kk u)) (lam2 (Vt (kk u))) hl
  rw [div_div_eq_mul_div, show (Vt (kk u) : ℝ) / 10 ^ 24 * 10 ^ 12 / (lam2 (Vt (kk u)) : ℝ) =
    ((Vt (kk u) : ℝ) / lam2 (Vt (kk u))) / 10 ^ 12 by field_simp]
  exact div_le_div_of_nonneg_right this (by norm_num)

theorem mm_floor_div {y : ℝ} (hy : 0 ≤ y) (d a : ℕ) :
    mm (⌊y⌋₊ / d / a) = mm ⌊y / ((d * a : ℕ) : ℝ)⌋₊ := by
  rw [Nat.div_div_eq_div_mul, Nat.floor_div_natCast]

/-- **Pointwise**: `|g₂(y)| ≤ ∑_d f(d)² Λ_d ∑_a H_d(a)/λ(da) m(⌊y/(da)⌋)²`. -/
theorem g2_le_pointwise {y S : ℝ} (hy : 1 ≤ y) (hyS : y ≤ S) :
    |g2 y| ≤ ∑ d ∈ Icc 1 ⌊S⌋₊, fo d ^ 2 * (∑ a ∈ Icc 1 (⌊S⌋₊ / d), Hd d a * lamR (d * a)) *
      ∑ a ∈ Icc 1 (⌊S⌋₊ / d), Hd d a / lamR (d * a) * mm ⌊y / ((d * a : ℕ) : ℝ)⌋₊ ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  set N := ⌊y⌋₊
  set NS := ⌊S⌋₊
  have hN : N ≤ NS := Nat.floor_le_floor hyS
  refine (abs_g2_le_sum y).trans ?_
  have hsub : Icc 1 N ⊆ Icc 1 NS := Icc_subset_Icc le_rfl hN
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)).trans ?_
  refine sum_le_sum fun d hd => ?_
  have hd1 := (mem_Icc.1 hd).1
  have hsubA : Icc 1 (N / d) ⊆ Icc 1 (NS / d) := Icc_subset_Icc le_rfl (Nat.div_le_div_right hN)
  have hpos : ∀ a ∈ Icc 1 (N / d), 0 < Hd d a * lamR (d * a) := fun a ha =>
    mul_pos (Hd_pos (mem_Icc.1 ha).1) (lamR_pos (Nat.mul_pos hd1 (mem_Icc.1 ha).1))
  have hL0 : 0 ≤ ∑ a ∈ Icc 1 (NS / d), Hd d a * lamR (d * a) := sum_nonneg fun a ha =>
    (mul_pos (Hd_pos (mem_Icc.1 ha).1) (lamR_pos (Nat.mul_pos hd1 (mem_Icc.1 ha).1))).le
  have hX0 : 0 ≤ ∑ a ∈ Icc 1 (NS / d), Hd d a / lamR (d * a) * mm ⌊y / ((d * a : ℕ) : ℝ)⌋₊ ^ 2 :=
    sum_nonneg fun a ha => mul_nonneg (div_nonneg (Hd_pos (mem_Icc.1 ha).1).le
      (lamR_pos (Nat.mul_pos hd1 (mem_Icc.1 ha).1)).le) (sq_nonneg _)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Sd_eq]
  rcases (Icc 1 (N / d)).eq_empty_or_nonempty with he | hne
  · rw [he, sum_empty]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hL0 hX0
  -- Cauchy–Schwarz
  have hcs := sq_sum_div_le_sum_sq_div (Icc 1 (N / d))
    (fun a => Hd d a * ∑ b ∈ Icc 1 (N / d / a), (μ b : ℝ) / b) hpos
  have hg : 0 < ∑ a ∈ Icc 1 (N / d), Hd d a * lamR (d * a) := sum_pos hpos hne
  rw [div_le_iff₀ hg] at hcs
  refine hcs.trans ?_
  rw [mul_comm]
  refine mul_le_mul (sum_le_sum_of_subset_of_nonneg hsubA fun a ha _ =>
    (mul_pos (Hd_pos (mem_Icc.1 ha).1) (lamR_pos (Nat.mul_pos hd1 (mem_Icc.1 ha).1))).le) ?_ ?_ hL0
  · refine le_trans (le_of_eq (sum_congr rfl fun a ha => ?_))
      (sum_le_sum_of_subset_of_nonneg hsubA fun a ha _ => mul_nonneg (div_nonneg
        (Hd_pos (mem_Icc.1 ha).1).le (lamR_pos (Nat.mul_pos hd1 (mem_Icc.1 ha).1)).le) (sq_nonneg _))
    have hH := (Hd_pos (d := d) (mem_Icc.1 ha).1).ne'
    have hl := (lamR_pos (Nat.mul_pos hd1 (mem_Icc.1 ha).1)).ne'
    rw [← mm_eq, mm_floor_div hy0]
    field_simp
  · exact sum_nonneg fun a ha => div_nonneg (sq_nonneg _) (hpos a ha).le

theorem intervalIntegrable_mm_div {u : ℕ} (hu : 1 ≤ u) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => mm ⌊y / (u : ℝ)⌋₊ ^ 2 / y) volume a b := by
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hmeas : Measurable (fun y : ℝ => mm ⌊y / (u : ℝ)⌋₊ ^ 2 / y) :=
    ((measurable_from_nat (f := fun K => mm K ^ 2)).comp
      (Nat.measurable_floor.comp (measurable_id.div_const _))).div measurable_id
  refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable (b ^ 2 / a) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
  have hy0 : 0 < y := lt_trans ha hy.1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0, abs_of_nonneg (sq_nonneg _)]
  have h1 := abs_mm_le ⌊y / (u : ℝ)⌋₊
  have h2 : (⌊y / (u : ℝ)⌋₊ : ℝ) ≤ b := by
    refine (Nat.floor_le (by positivity)).trans ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith [hy.2]
  have h3 : mm ⌊y / (u : ℝ)⌋₊ ^ 2 ≤ b ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
  rw [div_le_div_iff₀ hy0 ha]
  nlinarith [hy.1, sq_nonneg b]

theorem intervalIntegrable_abs_g2_div {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => |g2 y| / y) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Integrable.mul_bdd (integrableOn_g2_Ioc a b (by linarith)).abs
    (by fun_prop : Measurable fun y : ℝ => y⁻¹).aestronglyMeasurable (c := 1)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => by
      have : 1 < y := lt_of_le_of_lt ha hy.1
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; exact inv_le_one_of_one_le₀ this.le))
  |>.congr (Filter.Eventually.of_forall fun y => by simp [div_eq_mul_inv])

/-- `Λ_d = ∑_a H_d(a) λ(da)`, `Ξ_d = ∑_a H_d(a) w(da)` over `a ≤ ⌊S⌋/d`. -/
noncomputable def Lam (NS d : ℕ) : ℝ := ∑ a ∈ Icc 1 (NS / d), Hd d a * lamR (d * a)
noncomputable def Xi (NS d : ℕ) : ℝ := ∑ a ∈ Icc 1 (NS / d), Hd d a * wR (d * a)

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens] in
/-- **`∫_X^S |g₂|/y ≤ ∑_d f(d)² Λ_d Ξ_d`**. -/
theorem tail_le_sum {S : ℝ} (hS : 10000 ≤ S) :
    ∫ y in (10000 : ℝ)..S, |g2 y| / y ≤ ∑ d ∈ Icc 1 ⌊S⌋₊, fo d ^ 2 * Lam ⌊S⌋₊ d * Xi ⌊S⌋₊ d := by
  set NS := ⌊S⌋₊
  have hint : ∀ d ∈ Icc 1 NS, ∀ a ∈ Icc 1 (NS / d),
      IntervalIntegrable (fun y => mm ⌊y / ((d * a : ℕ) : ℝ)⌋₊ ^ 2 / y) volume 10000 S :=
    fun d hd a ha => intervalIntegrable_mm_div (Nat.mul_pos (mem_Icc.1 hd).1 (mem_Icc.1 ha).1)
      (by norm_num) hS
  -- the pointwise bound, divided by `y`
  set T : ℕ → ℕ → ℝ → ℝ := fun d a y => Hd d a / lamR (d * a) * (mm ⌊y / ((d * a : ℕ) : ℝ)⌋₊ ^ 2 / y)
  set Rd : ℕ → ℝ → ℝ := fun d y => fo d ^ 2 * Lam NS d * ∑ a ∈ Icc 1 (NS / d), T d a y
  have hT : ∀ d ∈ Icc 1 NS, ∀ a ∈ Icc 1 (NS / d), IntervalIntegrable (T d a) volume 10000 S :=
    fun d hd a ha => (hint d hd a ha).const_mul _
  have hsumT : ∀ d ∈ Icc 1 NS, IntervalIntegrable (fun y => ∑ a ∈ Icc 1 (NS / d), T d a y) volume 10000 S := by
    intro d hd
    have := IntervalIntegrable.sum (Icc 1 (NS / d)) (hT d hd)
    have e : (∑ a ∈ Icc 1 (NS / d), T d a) = fun y => ∑ a ∈ Icc 1 (NS / d), T d a y := by
      funext y; simp [Finset.sum_apply]
    rwa [e] at this
  have hRd : ∀ d ∈ Icc 1 NS, IntervalIntegrable (Rd d) volume 10000 S :=
    fun d hd => (hsumT d hd).const_mul _
  have hR : IntervalIntegrable (fun y => ∑ d ∈ Icc 1 NS, Rd d y) volume 10000 S := by
    have := IntervalIntegrable.sum (Icc 1 NS) hRd
    have e : (∑ d ∈ Icc 1 NS, Rd d) = fun y => ∑ d ∈ Icc 1 NS, Rd d y := by
      funext y; simp [Finset.sum_apply]
    rwa [e] at this
  have hpt : ∀ y ∈ Set.Icc (10000 : ℝ) S, |g2 y| / y ≤ ∑ d ∈ Icc 1 NS, Rd d y := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have := g2_le_pointwise (S := S) (by linarith [hy.1]) hy.2
    rw [div_le_iff₀ hy0]
    have e : (∑ d ∈ Icc 1 NS, Rd d y) * y = ∑ d ∈ Icc 1 NS, fo d ^ 2 * Lam NS d *
        ∑ a ∈ Icc 1 (NS / d), Hd d a / lamR (d * a) * mm ⌊y / ((d * a : ℕ) : ℝ)⌋₊ ^ 2 := by
      rw [sum_mul]
      refine sum_congr rfl fun d _ => ?_
      simp only [Rd, T]
      rw [mul_assoc (fo d ^ 2 * Lam NS d), sum_mul]
      congr 1
      refine sum_congr rfl fun a _ => ?_
      field_simp
    rw [e]; exact this
  have h1 : ∫ y in (10000 : ℝ)..S, |g2 y| / y ≤ ∫ y in (10000 : ℝ)..S, ∑ d ∈ Icc 1 NS, Rd d y :=
    intervalIntegral.integral_mono_on hS (intervalIntegrable_abs_g2_div (by norm_num) hS) hR hpt
  refine h1.trans ?_
  rw [intervalIntegral.integral_finset_sum hRd]
  refine sum_le_sum fun d hd => ?_
  have hd1 := (mem_Icc.1 hd).1
  simp only [Rd]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum (hT d hd)]
  have hL0 : 0 ≤ Lam NS d := sum_nonneg fun a ha =>
    (mul_pos (Hd_pos (mem_Icc.1 ha).1) (lamR_pos (Nat.mul_pos hd1 (mem_Icc.1 ha).1))).le
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hL0)
  unfold Xi
  refine sum_le_sum fun a ha => ?_
  have ha1 := (mem_Icc.1 ha).1
  have hu : 1 ≤ d * a := Nat.mul_pos hd1 ha1
  simp only [T]
  rw [intervalIntegral.integral_const_mul]
  have hI := integral_mm_le hu hS
  have hH := Hd_pos (d := d) ha1
  have hl := lamR_pos hu
  calc Hd d a / lamR (d * a) * ∫ y in (10000 : ℝ)..S, mm ⌊y / ((d * a : ℕ) : ℝ)⌋₊ ^ 2 / y
      ≤ Hd d a / lamR (d * a) * ((Vt (kk (d * a)) : ℝ) / 10 ^ 24) :=
        mul_le_mul_of_nonneg_left hI (div_nonneg hH.le hl.le)
    _ = Hd d a * ((Vt (kk (d * a)) : ℝ) / 10 ^ 24 / lamR (d * a)) := by ring
    _ ≤ Hd d a * wR (d * a) := mul_le_mul_of_nonneg_left (V_div_lam_le hu) hH.le

/-! ### Evaluating `∑_d f(d)² Λ_d Ξ_d` -/

theorem fo_eq_zero_of {d : ℕ} (h : ¬ (d % 2 = 1 ∧ (oddPrimes d).prod = d)) : fo d = 0 := by
  unfold fo
  by_cases ho : Odd d
  · rw [if_pos ho]
    have hsq : ¬ Squarefree d := fun hs =>
      h ⟨Nat.odd_iff.1 ho, (squarefree_iff_prod_oddPrimes ho).1 hs⟩
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
  · rw [if_neg ho]

/-- `σ(d) = ∏ (p + 1)` over the odd primes of `d`. -/
noncomputable def sgd (d : ℕ) : ℕ := ((oddPrimes d).map (· + 1)).prod

theorem fo_sq_eq {d : ℕ} (hd : d % 2 = 1) (hsq : (oddPrimes d).prod = d) :
    fo d ^ 2 = 1 / (sgd d : ℝ) ^ 2 := by
  have hodd : Odd d := Nat.odd_iff.2 hd
  have hnd := nodup_oddPrimes hodd.pos
  have hpr : ∀ p ∈ oddPrimes d, p.Prime := fun p hp => ((mem_oddPrimes hodd.pos).1 hp).1
  unfold fo
  rw [if_pos hodd]
  conv_lhs => rw [← hsq]
  rw [moebius_prod_primes _ hnd hpr, sigma_prod_primes _ hnd hpr]
  push_cast
  rw [div_pow, ← pow_mul, mul_comm _ 2, pow_mul]
  simp [sgd]

theorem prod_ratio_eq {d : ℕ} (hd : d % 2 = 1) (hsq : (oddPrimes d).prod = d) :
    ∏ p ∈ d.primeFactors, (((p : ℝ) + 1) / p) = (sgd d : ℝ) / d := by
  have hodd : Odd d := Nat.odd_iff.2 hd
  have hnd := nodup_oddPrimes hodd.pos
  have hpf : d.primeFactors = (oddPrimes d).toFinset := by
    rw [toFinset_oddPrimes hodd.pos, filter_true_of_mem]
    intro p hp h2; subst h2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  rw [prod_div_distrib, hpf, List.prod_toFinset _ hnd, List.prod_toFinset _ hnd]
  have h1 : ((oddPrimes d).map (fun p : ℕ => (p : ℝ) + 1)).prod = (sgd d : ℝ) := by
    unfold sgd; rw [Nat.cast_list_prod, List.map_map]
    congr 1; exact List.map_congr_left fun p _ => by simp
  have h2 : ((oddPrimes d).map (fun p : ℕ => (p : ℝ))).prod = (d : ℝ) := by
    rw [← Nat.cast_list_prod, hsq]
  rw [h1, h2]

/-- `B_d = 2 · 1.2338 σ(d)/d`. -/
theorem sum_Hd_le' {d : ℕ} (hd : d % 2 = 1) (hsq : (oddPrimes d).prod = d) (A : ℕ) :
    ∑ a ∈ Icc 1 A, Hd d a ≤ 2 * 1.2338 * ((sgd d : ℝ) / d) := by
  rw [← prod_ratio_eq hd hsq]; exact sum_Hd_le (Nat.odd_iff.2 hd) A

theorem lamR_of_le {u : ℕ} (hu : 1 ≤ u) (h : u ≤ XX) :
    lamR u = ((sV.tv.get (1, 0) (XX / u)).1 : ℝ) / 10 ^ 12 := by
  unfold lamR kk; rw [if_pos h]

theorem lamR_of_gt {u : ℕ} (h : XX < u) : lamR u = ((sV.tv.get (1, 0) 1).1 : ℝ) / 10 ^ 12 := by
  unfold lamR kk; rw [if_neg (by omega)]

theorem wR_of_le {u : ℕ} (hu : 1 ≤ u) (h : u ≤ XX) :
    wR u = ((sV.tv.get (1, 0) (XX / u)).2 : ℝ) / 10 ^ 12 := by
  unfold wR kk; rw [if_pos h]

theorem wR_of_gt {u : ℕ} (h : XX < u) : wR u = ((sV.tv.get (1, 0) 1).2 : ℝ) / 10 ^ 12 := by
  unfold wR kk; rw [if_neg (by omega)]

theorem sum_Icc_eq_range (n : ℕ) (f : ℕ → ℝ) : ∑ a ∈ Icc 1 n, f a = ∑ i ∈ range n, f (1 + i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ, add_comm 1 n]

theorem dl_get (i : ℕ) (hi : i < XX) : sV.dl.reverse[i]? = some (den1 (1 + i)) := by
  rw [sV_spec.2.2.2.2.2, List.reverse_reverse, show min (KK - 1) XX = XX from rfl]
  simp [List.getElem?_map, List.getElem?_range hi, add_comm]

theorem SH_R : (SH : ℝ) = 10 ^ 20 := by norm_num [SH]

theorem sum_split (f : ℕ → ℝ) {A N : ℕ} (h1 : 1 ≤ A) (h2 : A ≤ N) :
    ∑ a ∈ Icc 1 N, f a = ∑ a ∈ Icc 1 A, f a + ∑ a ∈ Ioc A N, f a := by
  have e : Icc 1 N = Icc 1 A ∪ Ioc A N := by
    ext x; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  rw [e, sum_union]
  rw [disjoint_left]; intro x hx1 hx2
  exact absurd (mem_Icc.1 hx1).2 (not_le.2 (mem_Ioc.1 hx2).1)

/-- **The term for odd squarefree `d ≤ X`** is at most `termC(d)/10⁶⁴`. -/
theorem term_le_termC {d NS : ℕ} (hd1 : 1 ≤ d) (hdX : d ≤ XX) (hNS : XX ≤ NS) (hd : d % 2 = 1)
    (hsq : (oddPrimes d).prod = d) :
    fo d ^ 2 * Lam NS d * Xi NS d ≤ (termC sV.tv sV.dl.reverse d : ℝ) / 10 ^ 64 := by
  have hodd : Odd d := Nat.odd_iff.2 hd
  set ps := oddPrimes d
  set sg := sgd d
  have hsg0 : 0 < sg := by
    unfold sg sgd; refine List.prod_pos fun x hx => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx; omega
  have hsg0' : (0 : ℝ) < sg := by exact_mod_cast hsg0
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  -- the kernel's inner sums
  set A := XX / d
  have hAN : A ≤ NS / d := Nat.div_le_div_right hNS
  have hr := innerC_spec sV.tv d ps A 1 sV.dl.reverse (0, 0, 0, 0, A) (fun i hi => by
    rw [dl_get i (by have : A ≤ XX := Nat.div_le_self _ _; omega)])
  simp only [G2TailNum.val, zero_mul, add_zero, zero_add] at hr
  -- `H_d(a) = sgc/den1`
  have hH : ∀ a, 1 ≤ a → Hd d a = (sgc ps a : ℝ) / den1 a := fun a ha => Hd_eq hodd ha
  have hden : ∀ a, 1 ≤ a → 0 < den1 a := fun a ha => by
    unfold den1; refine Nat.mul_pos ha (List.prod_pos fun x hx => ?_)
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx; omega
  have hdaX : ∀ a ∈ Icc 1 A, d * a ≤ XX := fun a ha => by
    have := (mem_Icc.1 ha).2; rw [Nat.le_div_iff_mul_le hd1] at this; linarith [mul_comm d a]
  -- real sums
  set s1 := ∑ a ∈ Icc 1 A, Hd d a with hs1
  set sl := ∑ a ∈ Icc 1 A, Hd d a * ((sV.tv.get (1, 0) (XX / (d * a))).1 : ℝ) with hsl
  set sv := ∑ a ∈ Icc 1 A, Hd d a * ((sV.tv.get (1, 0) (XX / (d * a))).2 : ℝ) with hsv
  set r := innerC sV.tv d ps A 1 sV.dl.reverse (0, 0, 0, 0, A)
  have hr1 : (r.1 : ℝ) ≤ SH * s1 := by
    rw [hr, hs1, sum_Icc_eq_range, mul_sum]; push_cast
    refine sum_le_sum fun i _ => ?_
    rw [hH (1 + i) (by omega)]
    have := Nat.cast_div_le (α := ℝ) (m := SH * sgc ps (1 + i)) (n := den1 (1 + i))
    push_cast at this; rw [mul_div_assoc] at this; exact this
  have hr2 : SH * sl ≤ (r.2.1 : ℝ) := by
    rw [hr, hsl, sum_Icc_eq_range, mul_sum]; push_cast
    refine sum_le_sum fun i _ => ?_
    rw [hH (1 + i) (by omega), ← mul_assoc, ← mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast cdiv_ge _ _ (hden (1 + i) (by omega)))
      (Nat.cast_nonneg _)
  have hr3 : SH * sv ≤ (r.2.2 : ℝ) := by
    rw [hr, hsv, sum_Icc_eq_range, mul_sum]; push_cast
    refine sum_le_sum fun i _ => ?_
    rw [hH (1 + i) (by omega), ← mul_assoc, ← mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast cdiv_ge _ _ (hden (1 + i) (by omega)))
      (Nat.cast_nonneg _)
  -- `B_d` and the rest of the `a`-sum
  set B := cdiv (2 * P1n * sg * SH) (P1d * d)
  have hB : (SH : ℝ) * (2 * 1.2338 * ((sg : ℝ) / d)) ≤ B := by
    refine le_trans (le_of_eq ?_) (cdiv_ge _ _ (Nat.mul_pos (by norm_num [P1d]) hd1))
    simp only [P1n, P1d]; push_cast; field_simp; ring
  set rest := ∑ a ∈ Ioc A (NS / d), Hd d a
  have hA1 : 1 ≤ A := Nat.div_pos hdX hd1
  have hsplit : ∑ a ∈ Icc 1 (NS / d), Hd d a = s1 + rest := sum_split _ hA1 hAN
  have hrest : (SH : ℝ) * rest ≤ ((B - r.1 : ℕ) : ℝ) := by
    have h1 := sum_Hd_le' hd hsq (NS / d)
    rw [hsplit] at h1
    refine le_trans ?_ (Nat.cast_le.2 (le_refl _) |>.trans' (le_of_eq rfl))
    have h2 : (B : ℝ) - r.1 ≤ ((B - r.1 : ℕ) : ℝ) := by
      rcases le_total r.1 B with h | h
      · rw [Nat.cast_sub h]
      · rw [Nat.sub_eq_zero_of_le h]; push_cast; linarith [(Nat.cast_le (α := ℝ)).2 h]
    have hSH : (0 : ℝ) < SH := by rw [SH_R]; norm_num
    nlinarith
  set tH := B - r.1
  -- `Λ`, `Ξ` in fixed point
  have hLam : (SH : ℝ) * 10 ^ 12 * Lam NS d ≤ (r.2.1 : ℝ) + ((sV.tv.get (1, 0) 1).1 : ℝ) * tH := by
    unfold Lam
    rw [sum_split _ hA1 hAN]
    have e1 : ∑ a ∈ Icc 1 A, Hd d a * lamR (d * a) = sl / 10 ^ 12 := by
      rw [sum_div]; refine sum_congr rfl fun a ha => ?_
      rw [lamR_of_le (Nat.mul_pos hd1 (mem_Icc.1 ha).1) (hdaX a ha)]; ring
    have e2 : ∑ a ∈ Ioc A (NS / d), Hd d a * lamR (d * a) = rest * (((sV.tv.get (1, 0) 1).1 : ℝ) / 10 ^ 12) := by
      rw [sum_mul]; refine sum_congr rfl fun a ha => ?_
      rw [lamR_of_gt]
      have := (mem_Ioc.1 ha).1
      rw [Nat.div_lt_iff_lt_mul hd1] at this; linarith [mul_comm d a]
    rw [e1, e2]
    have hl0 : (0 : ℝ) ≤ (sV.tv.get (1, 0) 1).1 := Nat.cast_nonneg _
    have : (SH : ℝ) * 10 ^ 12 * (sl / 10 ^ 12 + rest * (((sV.tv.get (1, 0) 1).1 : ℝ) / 10 ^ 12)) =
        SH * sl + ((sV.tv.get (1, 0) 1).1 : ℝ) * (SH * rest) := by ring
    rw [this]
    exact add_le_add hr2 (mul_le_mul_of_nonneg_left hrest hl0)
  have hXi : (SH : ℝ) * 10 ^ 12 * Xi NS d ≤ (r.2.2 : ℝ) + ((sV.tv.get (1, 0) 1).2 : ℝ) * tH := by
    unfold Xi
    rw [sum_split _ hA1 hAN]
    have e1 : ∑ a ∈ Icc 1 A, Hd d a * wR (d * a) = sv / 10 ^ 12 := by
      rw [sum_div]; refine sum_congr rfl fun a ha => ?_
      rw [wR_of_le (Nat.mul_pos hd1 (mem_Icc.1 ha).1) (hdaX a ha)]; ring
    have e2 : ∑ a ∈ Ioc A (NS / d), Hd d a * wR (d * a) = rest * (((sV.tv.get (1, 0) 1).2 : ℝ) / 10 ^ 12) := by
      rw [sum_mul]; refine sum_congr rfl fun a ha => ?_
      rw [wR_of_gt]
      have := (mem_Ioc.1 ha).1
      rw [Nat.div_lt_iff_lt_mul hd1] at this; linarith [mul_comm d a]
    rw [e1, e2]
    have hl0 : (0 : ℝ) ≤ (sV.tv.get (1, 0) 1).2 := Nat.cast_nonneg _
    have : (SH : ℝ) * 10 ^ 12 * (sv / 10 ^ 12 + rest * (((sV.tv.get (1, 0) 1).2 : ℝ) / 10 ^ 12)) =
        SH * sv + ((sV.tv.get (1, 0) 1).2 : ℝ) * (SH * rest) := by ring
    rw [this]
    exact add_le_add hr3 (mul_le_mul_of_nonneg_left hrest hl0)
  -- assemble
  have hL0 : 0 ≤ Lam NS d := sum_nonneg fun a ha =>
    (mul_pos (Hd_pos (mem_Icc.1 ha).1) (lamR_pos (Nat.mul_pos hd1 (mem_Icc.1 ha).1))).le
  have hX0 : 0 ≤ Xi NS d := sum_nonneg fun a ha =>
    mul_nonneg (Hd_pos (mem_Icc.1 ha).1).le (wR_nonneg _)
  have hterm : (termC sV.tv sV.dl.reverse d : ℝ) =
      (cdiv ((r.2.1 + (sV.tv.get (1, 0) 1).1 * tH) * (r.2.2 + (sV.tv.get (1, 0) 1).2 * tH)) (sg * sg) : ℕ) := by
    unfold termC; rw [if_pos hsq]; rfl
  rw [hterm, fo_sq_eq hd hsq]
  refine le_trans ?_ (div_le_div_of_nonneg_right (cdiv_ge _ _ (Nat.mul_pos hsg0 hsg0)) (by norm_num))
  push_cast
  have hSH : (SH : ℝ) * 10 ^ 12 = 10 ^ 32 := by rw [SH_R]; norm_num
  rw [div_div, le_div_iff₀ (by positivity)]
  have hprod := mul_le_mul hLam hXi (by positivity) (by positivity)
  rw [hSH] at hprod
  have : 1 / (sg : ℝ) ^ 2 * Lam NS d * Xi NS d * ((sg : ℝ) * sg * 10 ^ 64) =
      10 ^ 32 * Lam NS d * (10 ^ 32 * Xi NS d) := by field_simp
  rw [this]
  exact hprod

theorem sum_inv_sq_le {a : ℕ} (ha : 1 ≤ a) : ∀ b : ℕ, ∑ d ∈ Ioc a b, 1 / (d : ℝ) ^ 2 ≤ 1 / (a : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have key : ∀ b : ℕ, a ≤ b → ∑ d ∈ Ioc a b, 1 / (d : ℝ) ^ 2 ≤ 1 / (a : ℝ) - 1 / (b : ℝ) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [show Ioc a (b + 1) = insert (b + 1) (Ioc a b) by
        ext x; simp only [mem_insert, mem_Ioc]; omega, sum_insert (by simp)]
      have hb' : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < a) hb)
      have : 1 / ((b + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ hb'.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at this ⊢
      linarith
  intro b
  rcases le_or_gt a b with h | h
  · have := key b h
    have : 0 ≤ 1 / (b : ℝ) := by positivity
    linarith
  · rw [Ioc_eq_empty (by omega), sum_empty]; positivity

/-- `λ(1) w(1)` from the trie. -/
noncomputable def l1w1 : ℝ := ((sV.tv.get (1, 0) 1).1 : ℝ) / 10 ^ 12 * (((sV.tv.get (1, 0) 1).2 : ℝ) / 10 ^ 12)

theorem term_le_big {d NS : ℕ} (hdX : XX < d) :
    fo d ^ 2 * Lam NS d * Xi NS d ≤ l1w1 * (4 * 1.2338 ^ 2) / (d : ℝ) ^ 2 := by
  have hd1 : 1 ≤ d := by have : 0 < XX := by decide
                         omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hC : 0 ≤ l1w1 * (4 * 1.2338 ^ 2) / (d : ℝ) ^ 2 := by unfold l1w1; positivity
  by_cases h : d % 2 = 1 ∧ (oddPrimes d).prod = d
  · obtain ⟨hd, hsq⟩ := h
    have hlam : ∀ a ∈ Icc 1 (NS / d), lamR (d * a) = ((sV.tv.get (1, 0) 1).1 : ℝ) / 10 ^ 12 :=
      fun a ha => lamR_of_gt (lt_of_lt_of_le hdX (Nat.le_mul_of_pos_right d (mem_Icc.1 ha).1))
    have hw : ∀ a ∈ Icc 1 (NS / d), wR (d * a) = ((sV.tv.get (1, 0) 1).2 : ℝ) / 10 ^ 12 :=
      fun a ha => wR_of_gt (lt_of_lt_of_le hdX (Nat.le_mul_of_pos_right d (mem_Icc.1 ha).1))
    have hB := sum_Hd_le' hd hsq (NS / d)
    have hS0 : 0 ≤ ∑ a ∈ Icc 1 (NS / d), Hd d a := sum_nonneg fun a ha => (Hd_pos (mem_Icc.1 ha).1).le
    have eL : Lam NS d = (∑ a ∈ Icc 1 (NS / d), Hd d a) * (((sV.tv.get (1, 0) 1).1 : ℝ) / 10 ^ 12) := by
      unfold Lam; rw [sum_mul]; exact sum_congr rfl fun a ha => by rw [hlam a ha]
    have eX : Xi NS d = (∑ a ∈ Icc 1 (NS / d), Hd d a) * (((sV.tv.get (1, 0) 1).2 : ℝ) / 10 ^ 12) := by
      unfold Xi; rw [sum_mul]; exact sum_congr rfl fun a ha => by rw [hw a ha]
    rw [eL, eX, fo_sq_eq hd hsq]
    have hsg0 : (0 : ℝ) < sgd d := by
      have : 0 < sgd d := by
        unfold sgd; refine List.prod_pos fun x hx => ?_
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx; omega
      exact_mod_cast this
    set T := ∑ a ∈ Icc 1 (NS / d), Hd d a
    have hT2 : T ^ 2 ≤ (2 * 1.2338 * ((sgd d : ℝ) / d)) ^ 2 := pow_le_pow_left₀ hS0 hB 2
    have e : 1 / (sgd d : ℝ) ^ 2 * (T * (((sV.tv.get (1, 0) 1).1 : ℝ) / 10 ^ 12)) *
        (T * (((sV.tv.get (1, 0) 1).2 : ℝ) / 10 ^ 12)) = l1w1 * T ^ 2 / (sgd d : ℝ) ^ 2 := by
      unfold l1w1; ring
    rw [e]
    have hl : 0 ≤ l1w1 := by unfold l1w1; positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * 1.2338 * ((sgd d : ℝ) / d)) ^ 2 * (d : ℝ) ^ 2 = 4 * 1.2338 ^ 2 * (sgd d : ℝ) ^ 2 := by
      field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hT2 hl]
  · rw [fo_eq_zero_of h]; simpa using hC

/-- **`∑_d f(d)² Λ_d Ξ_d ≤ Macc/10⁶⁴ + λ(1) w(1) · 4 · 1.2338²/X`**. -/
theorem sum_terms_le {S : ℝ} (hS : 10000 ≤ S) :
    ∑ d ∈ Icc 1 ⌊S⌋₊, fo d ^ 2 * Lam ⌊S⌋₊ d * Xi ⌊S⌋₊ d ≤
      (Macc : ℝ) / 10 ^ 64 + l1w1 * (4 * 1.2338 ^ 2) / 10000 := by
  set NS := ⌊S⌋₊
  have hNS : XX ≤ NS := Nat.le_floor (by norm_num [XX]; exact hS)
  rw [sum_split _ (by decide : 1 ≤ XX) hNS]
  refine add_le_add ?_ ?_
  · -- `d ≤ X` through the kernel
    have h1 : ∀ d ∈ Icc 1 XX, fo d ^ 2 * Lam NS d * Xi NS d ≤
        if d % 2 = 1 then (termC sV.tv sV.dl.reverse d : ℝ) / 10 ^ 64 else 0 := by
      intro d hd
      by_cases h : d % 2 = 1 ∧ (oddPrimes d).prod = d
      · rw [if_pos h.1]; exact term_le_termC (mem_Icc.1 hd).1 (mem_Icc.1 hd).2 hNS h.1 h.2
      · rw [fo_eq_zero_of h]
        split_ifs
        · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]; positivity
        · simp
    refine (sum_le_sum h1).trans (le_of_eq ?_)
    rw [← sum_filter]
    have hX : XX = 10000 := rfl
    have hfil : (Icc 1 XX).filter (fun d => d % 2 = 1) = (range 5000).image (fun i => 2 * i + 1) := by
      ext d; simp only [mem_filter, mem_Icc, mem_image, mem_range, hX]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨d / 2, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [hfil, sum_image (fun a _ b _ h => by omega), ← sum_div]
    have := outerC_eq sV.tv sV.dl.reverse 5000
    rw [(Prod.mk.inj tail_ok).2] at this
    rw [this]; push_cast; rfl
  · -- `d > X`
    calc ∑ d ∈ Ioc XX NS, fo d ^ 2 * Lam NS d * Xi NS d
        ≤ ∑ d ∈ Ioc XX NS, l1w1 * (4 * 1.2338 ^ 2) * (1 / (d : ℝ) ^ 2) :=
          sum_le_sum fun d hd => by
            have := term_le_big (NS := NS) (mem_Ioc.1 hd).1
            rw [mul_one_div]; exact this
      _ = l1w1 * (4 * 1.2338 ^ 2) * ∑ d ∈ Ioc XX NS, 1 / (d : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ l1w1 * (4 * 1.2338 ^ 2) * (1 / (XX : ℕ)) := by
          refine mul_le_mul_of_nonneg_left (sum_inv_sq_le (by decide) NS) ?_
          unfold l1w1; positivity
      _ = l1w1 * (4 * 1.2338 ^ 2) / 10000 := by norm_num [XX]; ring

theorem tv_one : sV.tv.get (1, 0) 1 = (549755813888, 1483286220167) := by
  rw [sV_spec.2.2.2.2.1 1 le_rfl (by decide)]
  have hV : Vt 1 = cP + tailV := by simp [Vt]
  rw [hV]
  decide +kernel

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens] in
/-- **`∫_{10⁴}^S |g₂(y)|/y dy ≤ 0.0082`** for `S ≥ 10⁴`. -/
theorem tail_integral_le {S : ℝ} (hS : 10000 ≤ S) : ∫ y in (10000 : ℝ)..S, |g2 y| / y ≤ 0.0082 := by
  refine (tail_le_sum hS).trans ((sum_terms_le hS).trans ?_)
  unfold l1w1
  rw [tv_one, Macc]
  norm_num

end TernaryGoldbach.MinorArcs.G2Tail
