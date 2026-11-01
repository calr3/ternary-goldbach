import Mathlib
import TernaryGoldbach.Prelim.SmallFsq

/-!
# Squarefree integers coprime to `P` in an interval [B, proof of Lemma 5.1.1]

* `sum_moebius_sq_dvd`: `∑_{m² | l} μ(m) = [l squarefree]`;
* `sum_Ioc_dvd`: the number of multiples of `D` in `(a, b]` is `(b - a)/D + O*(1)`, and `0` when
  `D > b`;
-/

open Finset
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma LSeries.notation

namespace TernaryGoldbach.Prelim

/-- `m² ∣ b² a` with `a` squarefree implies `m ∣ b`. -/
theorem dvd_of_sq_dvd_sq_mul {m b a : ℕ} (ha : Squarefree a) (hb : b ≠ 0)
    (h : m * m ∣ b ^ 2 * a) : m ∣ b := by
  set g := Nat.gcd m b
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hb)
  obtain ⟨m', hm'⟩ : g ∣ m := Nat.gcd_dvd_left m b
  obtain ⟨b', hb'⟩ : g ∣ b := Nat.gcd_dvd_right m b
  have hcop : Nat.Coprime m' b' := by
    have := Nat.coprime_div_gcd_div_gcd (m := m) (n := b) hg
    rwa [show m / g = m' by rw [hm', Nat.mul_div_cancel_left _ hg],
      show b / g = b' by rw [hb', Nat.mul_div_cancel_left _ hg]] at this
  clear_value g
  have h2 : m' * m' ∣ b' ^ 2 * a := by
    rw [hm', hb'] at h
    have : g * g * (m' * m') ∣ g * g * (b' ^ 2 * a) := by
      convert h using 1 <;> ring
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) this
  have h3 : m' * m' ∣ a :=
    (Nat.coprime_mul_iff_left.2 ⟨hcop.pow_right 2, hcop.pow_right 2⟩).dvd_of_dvd_mul_left h2
  have h4 : m' = 1 := Nat.isUnit_iff.1 (ha m' h3)
  rw [hm', h4, mul_one, hb']
  exact dvd_mul_right _ _

/-- `∑_{m ≥ 1, m² | l} μ(m) = [l squarefree]` (for `l ≥ 1`). -/
theorem sum_moebius_sq_dvd {l : ℕ} (hl : l ≠ 0) :
    ∑ m ∈ l.divisors.filter (fun m => m * m ∣ l), (μ m : ℝ) = if Squarefree l then 1 else 0 := by
  obtain ⟨b, a, hba, ha⟩ := exists_sq_mul_squarefree l
  have hb : b ≠ 0 := by rintro rfl; simp at hba; exact hl hba.symm
  have hset : l.divisors.filter (fun m => m * m ∣ l) = b.divisors := by
    ext m
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨dvd_of_sq_dvd_sq_mul ha hb (hba ▸ h), hb⟩
    · rintro ⟨h, _⟩
      have hmm : m * m ∣ l := hba ▸ dvd_mul_of_dvd_left (by rw [sq]; exact mul_dvd_mul h h) a
      exact ⟨⟨(dvd_mul_right m m).trans hmm, hl⟩, hmm⟩
  rw [hset]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f b)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simp only [ArithmeticFunction.intCoe_apply] at h
  rw [h]
  by_cases hb1 : b = 1
  · subst hb1; simp at hba; subst hba; simp [ha]
  · rw [if_neg hb1, if_neg]
    intro hsq
    exact hb1 (Nat.isUnit_iff.1 (hsq b (hba ▸ dvd_mul_of_dvd_left (by rw [sq]) a)))

/-- The number of multiples of `D ≥ 1` in `(⌊a⌋, ⌊b⌋]` is `(b - a)/D + O*(1)`. -/
theorem sum_Ioc_dvd_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {D : ℕ} (hD : 1 ≤ D) :
    |(∑ l ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if D ∣ l then (1 : ℝ) else 0) - (b - a) / D| < 1 := by
  have hcount : (∑ l ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if D ∣ l then (1 : ℝ) else 0) =
      (⌊b / D⌋₊ : ℝ) - ⌊a / D⌋₊ := by
    rw [sum_boole]
    have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
    have hsplit : (Ioc 0 ⌊b⌋₊).filter (D ∣ ·) =
        (Ioc 0 ⌊a⌋₊).filter (D ∣ ·) ∪ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (D ∣ ·) := by
      rw [← filter_union, Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hfl]
    have hdisj : Disjoint ((Ioc 0 ⌊a⌋₊).filter (D ∣ ·)) ((Ioc ⌊a⌋₊ ⌊b⌋₊).filter (D ∣ ·)) :=
      disjoint_filter_filter (Ioc_disjoint_Ioc_of_le le_rfl)
    have := card_union_of_disjoint hdisj
    rw [← hsplit, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at this
    rw [Nat.floor_div_natCast, Nat.floor_div_natCast]
    have hle : ⌊a⌋₊ / D ≤ ⌊b⌋₊ / D := Nat.div_le_div_right hfl
    rw [this, Nat.cast_add]; ring
  rw [hcount]
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 := Nat.floor_le (div_nonneg ha hD0.le)
  have h2 := Nat.lt_floor_add_one (a / D)
  have h3 := Nat.floor_le (div_nonneg (ha.trans hab) hD0.le)
  have h4 := Nat.lt_floor_add_one (b / D)
  have : (b - a) / D = b / D - a / D := sub_div _ _ _
  rw [abs_lt]; constructor <;> linarith

/-- No multiples of `D` in `(⌊a⌋, ⌊b⌋]` when `b < D`. -/
theorem sum_Ioc_dvd_eq_zero {a b : ℝ} {D : ℕ} (hD : b < D) :
    (∑ l ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if D ∣ l then (1 : ℝ) else 0) = 0 := by
  refine sum_eq_zero fun l hl => if_neg ?_
  rintro ⟨k, rfl⟩
  rw [mem_Ioc] at hl
  have hk : k ≠ 0 := by rintro rfl; simp at hl
  have h1 : ((D * k : ℕ) : ℝ) ≤ b := by
    rcases le_or_gt 0 b with hb | hb
    · exact (Nat.cast_le.2 hl.2).trans (Nat.floor_le hb)
    · simp [Nat.floor_of_nonpos hb.le] at hl
      rcases hl.2 with h | h <;> simp_all
  have : (D : ℝ) ≤ ((D * k : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right D (Nat.pos_of_ne_zero hk)
  linarith

/-! ### The constant `∑_{e | P} μ(e)/e · ∑_{(m, P) = 1} μ(m)/m² = (6/π²) P/σ(P)` -/

/-- `∑_{(m, P) = 1} μ(m)/m² = (6/π²) / ∏_{p | P} (1 - 1/p²)`, via `L(μ·1_P, 2) = 1/L(1_P, 2)`. -/
theorem tsum_coprime_moebius_div_sq {P : ℕ} (hP : P ≠ 0) :
    ∑' m : ℕ, (if Nat.Coprime m P then (μ m : ℝ) / (m : ℝ) ^ 2 else 0) =
      6 / Real.pi ^ 2 / ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
  haveI : NeZero P := ⟨hP⟩
  set χ : DirichletCharacter ℂ P := 1
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h1 := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have h2 : LSeries (fun n => χ n) 2 =
      (∏ p ∈ P.primeFactors, (1 - (p : ℂ) ^ (-(2:ℂ)))) * riemannZeta 2 := by
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by norm_num)
  have hterm : ∀ n : ℕ, LSeries.term (↗χ * ↗μ) 2 n =
      ((if Nat.Coprime n P then (μ n : ℝ) / (n : ℝ) ^ 2 else 0 : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn]
    by_cases hc : Nat.Coprime n P
    · have hu : IsUnit (n : ZMod P) := (ZMod.isUnit_iff_coprime n P).2 hc
      rw [if_pos hc, Pi.mul_apply, MulChar.one_apply hu]
      push_cast
      simp
    · have hu : ¬ IsUnit (n : ZMod P) := mt (ZMod.isUnit_iff_coprime n P).1 hc
      rw [if_neg hc, Pi.mul_apply, MulChar.map_nonunit _ hu]; simp
  have h3 : LSeries (↗χ * ↗μ) 2 =
      ((∑' m : ℕ, (if Nat.Coprime m P then (μ m : ℝ) / (m : ℝ) ^ 2 else 0) : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]; exact tsum_congr hterm
  have hprod : (∏ p ∈ P.primeFactors, (1 - (p : ℂ) ^ (-(2:ℂ)))) =
      ((∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2) : ℝ) : ℂ) := by
    push_cast
    refine prod_congr rfl fun p _ => ?_
    rw [Complex.cpow_neg]; simp
  rw [h2, h3, hprod, riemannZeta_two] at h1
  have hpos : (0 : ℝ) < ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
    refine prod_pos fun p hp => ?_
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  set T := ∑' m : ℕ, (if Nat.Coprime m P then (μ m : ℝ) / (m : ℝ) ^ 2 else 0)
  set Q := ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2)
  have h4 : Q * (Real.pi ^ 2 / 6) * T = 1 := by exact_mod_cast h1
  field_simp
  linear_combination 6 * h4

theorem summable_coprime_moebius_div_sq (P : ℕ) :
    Summable (fun m : ℕ => if Nat.Coprime m P then (μ m : ℝ) / (m : ℝ) ^ 2 else 0) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => 1 / (m : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.2 one_lt_two) fun m => ?_
  split_ifs
  · rw [norm_div, norm_pow, Real.norm_natCast, one_div]
    have : ‖(μ m : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) this
  · simp

/-- `n ↦ 1/n` as a multiplicative arithmetic function. -/
noncomputable def invFun : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩

theorem isMultiplicative_invFun : invFun.IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.2 ⟨by simp [invFun], fun hm hn _ => ?_⟩
  simp [invFun, mul_comm]

theorem sum_moebius_div_eq_prod {P : ℕ} (hP : Squarefree P) :
    ∑ e ∈ P.divisors, (μ e : ℝ) / e = ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ)) := by
  have := isMultiplicative_invFun.prodPrimeFactors_one_sub_of_squarefree _ hP
  simp only [invFun, ArithmeticFunction.coe_mk, one_div] at this ⊢
  rw [this]; simp [div_eq_mul_inv]

theorem sigma_eq_prod {P : ℕ} (hP : Squarefree P) :
    (σ 1 P : ℝ) = ∏ p ∈ P.primeFactors, ((p : ℝ) + 1) := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hP]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime _
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  push_cast
  refine prod_congr rfl fun p hp => ?_
  have := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) (Nat.prime_of_mem_primeFactors hp)
  simp only [pow_one] at this
  rw [this]; simp [sum_range_succ]; ring

/-- The main-term constant: `(∑_{e|P} μ(e)/e) · ∑_{(m,P)=1} μ(m)/m² = (6/π²) · P/σ(P)`. -/
theorem sqfree_density {P : ℕ} (hP : Squarefree P) :
    (∑ e ∈ P.divisors, (μ e : ℝ) / e) *
      ∑' m : ℕ, (if Nat.Coprime m P then (μ m : ℝ) / (m : ℝ) ^ 2 else 0) =
      6 / Real.pi ^ 2 * (P / σ 1 P) := by
  rw [sum_moebius_div_eq_prod hP, tsum_coprime_moebius_div_sq hP.ne_zero, sigma_eq_prod hP]
  have hP' : (P : ℝ) = ∏ p ∈ P.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hP]
  rw [hP']
  have hp2 : ∀ p ∈ P.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hne : ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2) ≠ 0 :=
    prod_ne_zero_iff.2 fun p hp => by
      have := hp2 p hp
      have : 1 / (p : ℝ) ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
      linarith
  have hne2 : ∏ p ∈ P.primeFactors, ((p : ℝ) + 1) ≠ 0 :=
    prod_ne_zero_iff.2 fun p hp => by have := hp2 p hp; positivity
  have key : (∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ))) * ∏ p ∈ P.primeFactors, ((p : ℝ) + 1) =
      (∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2)) * ∏ p ∈ P.primeFactors, (p : ℝ) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have := hp2 p hp
    field_simp
    ring
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  field_simp
  linear_combination key

/-! ### Counting squarefree `l ∈ (a, b]` coprime to `P` -/

/-- `f(X) = ∑_{m ≤ X sq-free} 1 + ½ ∑_{m > X sq-free} X²/m²` [B, p. 83]. -/
noncomputable def fsq (X : ℝ) : ℝ :=
  ∑' m : ℕ, if Squarefree m ∧ m ≠ 0 then (if (m : ℝ) ≤ X then 1 else X ^ 2 / (2 * (m : ℝ) ^ 2))
    else 0

/-- [B, p. 83]: `f(X) ≤ 1.27 X` for `X ≥ 0`. Proved in `Prelim/SmallFsq.lean` (kernel-checked
numerics for `⌊X⌋ < 200`, an elementary bound above); the maximum is `f(2)/2 = 15/π² − 1/4 = 1.26982…`. -/
theorem fsq_le {X : ℝ} (hX : 0 ≤ X) : fsq X ≤ 1.27 * X := Small.fsq_le' hX

theorem summable_fsq_term (X : ℝ) :
    Summable (fun m : ℕ => if Squarefree m ∧ m ≠ 0 then
      (if (m : ℝ) ≤ X then (1 : ℝ) else X ^ 2 / (2 * (m : ℝ) ^ 2)) else 0) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left (1 + X ^ 2))
  · split_ifs <;> positivity
  · split_ifs with h1 h2
    · have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h1.2
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      have : (m : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      linarith
    · have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h1.2
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg X, sq_nonneg (m : ℝ)]
    · positivity

theorem sum_moebius_divisors_real (g : ℕ) (hg : 1 ≤ g) :
    ∑ d ∈ g.divisors, (μ d : ℝ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f g)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← h]
  simp [ArithmeticFunction.intCoe_apply]

/-- `[(l, P) = 1] = ∑_{e | P, e | l} μ(e)`. -/
theorem coprime_indicator {l P : ℕ} (hl : l ≠ 0) (hP : P ≠ 0) :
    (if Nat.Coprime l P then (1 : ℝ) else 0) =
      ∑ e ∈ P.divisors, if e ∣ l then (μ e : ℝ) else 0 := by
  rw [← sum_filter]
  have hfilt : P.divisors.filter (· ∣ l) = (Nat.gcd l P).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, h1⟩, Nat.gcd_ne_zero_left hl⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, hP⟩, h1⟩
  rw [hfilt, sum_moebius_divisors_real _ (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hl))]

/-- The number of squarefree `l ∈ (⌊a⌋, ⌊b⌋]` coprime to `P`. -/
noncomputable def cntSq (P : ℕ) (a b : ℝ) : ℝ :=
  ∑ l ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if Squarefree l ∧ Nat.Coprime l P then 1 else 0

theorem abs_moebius_le_one_real (m : ℕ) : |(μ m : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **Squarefree integers coprime to `P` in `(a, b]`** [B, proof of Lemma 5.1.1, (5.12)–(5.17)]:
for squarefree `P` and `b/2 ≤ a ≤ b`,
`#{l ∈ (a, b] : l sq-free, (l, P) = 1} = (b - a)(6/π²) P/σ(P) + O*(∑_{e | P} f(√(b/e)))`. -/
theorem cntSq_approx {P : ℕ} (hP : Squarefree P) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb2 : b ≤ 2 * a) :
    |cntSq P a b - (b - a) * (6 / Real.pi ^ 2 * (P / σ 1 P))| ≤
      ∑ e ∈ P.divisors, fsq (Real.sqrt (b / e)) := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hb0 : 0 ≤ b := ha.trans hab
  set N := ⌊b⌋₊
  set I := Ioc ⌊a⌋₊ N
  set C : ℕ → ℝ := fun D => ∑ l ∈ I, if D ∣ l then (1 : ℝ) else 0 with hC
  set w : ℕ → ℝ := fun m => if Nat.Coprime m P then (μ m : ℝ) else 0 with hw
  have hw1 : ∀ m, |w m| ≤ 1 := fun m => by
    simp only [hw]; split_ifs
    · exact abs_moebius_le_one_real m
    · simp
  -- Pointwise Möbius identity.
  have hpt : ∀ l ∈ I, (if Squarefree l ∧ Nat.Coprime l P then (1 : ℝ) else 0) =
      ∑ e ∈ P.divisors, (μ e : ℝ) *
        ∑ m ∈ range (N + 1), w m * (if e * (m * m) ∣ l then 1 else 0) := by
    intro l hl
    have hl0 : l ≠ 0 := by
      have := (mem_Ioc.1 hl).1; omega
    have hlN : l ≤ N := (mem_Ioc.1 hl).2
    have hfac : ∀ e ∈ P.divisors, (μ e : ℝ) *
        ∑ m ∈ range (N + 1), w m * (if e * (m * m) ∣ l then 1 else 0) =
        (if e ∣ l then (μ e : ℝ) else 0) *
          ∑ m ∈ range (N + 1), w m * (if m * m ∣ l then 1 else 0) := by
      intro e he
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun m _ => ?_
      simp only [hw]
      by_cases hm : Nat.Coprime m P
      · have hce : Nat.Coprime e (m * m) :=
          Nat.Coprime.mul_right (hm.symm.coprime_dvd_left (Nat.dvd_of_mem_divisors he))
            (hm.symm.coprime_dvd_left (Nat.dvd_of_mem_divisors he))
        have : e * (m * m) ∣ l ↔ e ∣ l ∧ m * m ∣ l :=
          ⟨fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩,
            fun h => hce.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
        simp only [hm, if_true, this]
        by_cases h1 : e ∣ l <;> by_cases h2 : m * m ∣ l <;> simp [h1, h2]
      · simp [hm]
    rw [sum_congr rfl hfac, ← sum_mul, ← coprime_indicator hl0 hP0]
    by_cases hc : Nat.Coprime l P
    · rw [if_pos hc, one_mul]
      have hset : (range (N + 1)).filter (fun m => m * m ∣ l) =
          l.divisors.filter (fun m => m * m ∣ l) := by
        ext m
        simp only [mem_filter, mem_range, Nat.mem_divisors]
        constructor
        · rintro ⟨_, h⟩; exact ⟨⟨(dvd_mul_right m m).trans h, hl0⟩, h⟩
        · rintro ⟨⟨h1, _⟩, h2⟩
          exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) h1).trans hlN), h2⟩
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← sum_filter, hset]
      rw [show ∑ m ∈ l.divisors.filter (fun m => m * m ∣ l), w m =
          ∑ m ∈ l.divisors.filter (fun m => m * m ∣ l), (μ m : ℝ) from
        sum_congr rfl fun m hm => by
          have hmd : m ∣ l := Nat.dvd_of_mem_divisors (mem_filter.1 hm).1
          simp only [hw, if_pos (Nat.Coprime.coprime_dvd_left hmd hc)],
        sum_moebius_sq_dvd hl0]
      exact if_congr ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩ rfl rfl
    · simp [hc]
  -- Swap sums: `cnt = ∑_e μ(e) ∑_m w(m) C(e m²)`.
  have hcnt : cntSq P a b = ∑ e ∈ P.divisors, (μ e : ℝ) * ∑ m ∈ range (N + 1), w m * C (e * (m * m)) := by
    rw [cntSq, sum_congr rfl hpt, sum_comm]
    refine sum_congr rfl fun e _ => ?_
    rw [← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [← mul_sum]
  -- Main term.
  have hT : ∑' m : ℕ, (if Nat.Coprime m P then (μ m : ℝ) / (m : ℝ) ^ 2 else 0) =
      ∑' m : ℕ, w m / (m : ℝ) ^ 2 := tsum_congr fun m => by simp only [hw]; split_ifs <;> simp
  have hsumT : Summable fun m : ℕ => w m / (m : ℝ) ^ 2 := by
    have := summable_coprime_moebius_div_sq P
    refine this.congr fun m => ?_
    simp only [hw]; split_ifs <;> simp
  have hmain : (b - a) * (6 / Real.pi ^ 2 * (P / σ 1 P)) = ∑ e ∈ P.divisors, (μ e : ℝ) *
      ∑' m : ℕ, w m * ((b - a) / (e * (m : ℝ) ^ 2)) := by
    rw [← sqfree_density hP, hT, sum_mul, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [← tsum_mul_left]
    have : ∑' m : ℕ, w m * ((b - a) / (e * (m : ℝ) ^ 2)) = ∑' m : ℕ, (b - a) / e * (w m / m ^ 2) :=
      tsum_congr fun m => by
        rcases eq_or_ne (e : ℝ) 0 with h | h
        · simp [h]
        rcases eq_or_ne (m : ℝ) 0 with h' | h'
        · simp [h']
        field_simp
    rw [this, tsum_mul_left, tsum_mul_left]; ring
  rw [hcnt, hmain, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e he => ?_)
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt (Nat.pos_of_mem_divisors he))
  have he0 : (0 : ℝ) < e := by exact_mod_cast he1
  rw [← mul_sub, abs_mul]
  refine (mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_le_one_real e)).trans ?_
  -- Per-`e` error.
  have hfin : ∑ m ∈ range (N + 1), w m * C (e * (m * m)) = ∑' m : ℕ, w m * C (e * (m * m)) := by
    refine (tsum_eq_sum fun m hm => ?_).symm
    rw [mem_range, not_lt] at hm
    have hbm : b < ((e * (m * m) : ℕ) : ℝ) := by
      have h1 : b < (N : ℝ) + 1 := Nat.lt_floor_add_one b
      have h2 : N + 1 ≤ e * (m * m) := by
        have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 N) hm
        calc N + 1 ≤ m := hm
          _ ≤ m * m := Nat.le_mul_of_pos_left m hm1
          _ ≤ e * (m * m) := Nat.le_mul_of_pos_left _ he1
      exact lt_of_lt_of_le h1 (by exact_mod_cast h2)
    simp only [hC]; rw [sum_Ioc_dvd_eq_zero hbm, mul_zero]
  have hs1 : Summable fun m : ℕ => w m * C (e * (m * m)) :=
    summable_of_ne_finset_zero (s := range (N + 1)) fun m hm => by
      rw [mem_range, not_lt] at hm
      have hbm : b < ((e * (m * m) : ℕ) : ℝ) := by
        have h1 : b < (N : ℝ) + 1 := Nat.lt_floor_add_one b
        have h2 : N + 1 ≤ e * (m * m) := by
          have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 N) hm
          calc N + 1 ≤ m := hm
            _ ≤ m * m := Nat.le_mul_of_pos_left m hm1
            _ ≤ e * (m * m) := Nat.le_mul_of_pos_left _ he1
        exact lt_of_lt_of_le h1 (by exact_mod_cast h2)
      simp only [hC]; rw [sum_Ioc_dvd_eq_zero hbm, mul_zero]
  have hs2 : Summable fun m : ℕ => w m * ((b - a) / (e * (m : ℝ) ^ 2)) := by
    refine (hsumT.mul_left ((b - a) / e)).congr fun m => ?_
    rcases eq_or_ne (m : ℝ) 0 with h' | h'
    · simp [h']
    field_simp
  rw [hfin, ← hs1.tsum_sub hs2]
  refine (norm_tsum_le_tsum_norm (hs1.sub hs2).norm).trans ?_
  refine (hs1.sub hs2).norm.tsum_le_tsum (fun m => ?_) (summable_fsq_term _)
  set X := Real.sqrt (b / e)
  have hX2 : X ^ 2 = b / e := Real.sq_sqrt (div_nonneg hb0 he0.le)
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
  by_cases hm : Squarefree m ∧ m ≠ 0
  · rw [if_pos hm]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm.2
    have hD : ((e * (m * m) : ℕ) : ℝ) = e * (m : ℝ) ^ 2 := by push_cast; ring
    refine (mul_le_of_le_one_left (abs_nonneg _) (hw1 m)).trans ?_
    split_ifs with hmX
    · have h := sum_Ioc_dvd_sub ha hab (D := e * (m * m))
        (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero hm.2 hm.2)))
      rw [hD] at h; exact h.le
    · push Not at hmX
      have hbm : b < ((e * (m * m) : ℕ) : ℝ) := by
        rw [hD]
        have : X ^ 2 < (m : ℝ) ^ 2 := pow_lt_pow_left₀ hmX (Real.sqrt_nonneg _) two_ne_zero
        rw [hX2, div_lt_iff₀ he0] at this; linarith
      simp only [hC]
      rw [sum_Ioc_dvd_eq_zero hbm, zero_sub, abs_neg, abs_of_nonneg (by
        have : 0 ≤ b - a := by linarith
        positivity), hX2]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h0 : 0 ≤ (m : ℝ) ^ 2 := by positivity
      have h1 : (e : ℝ) * (m : ℝ) ^ 2 * (b / e) = b * m ^ 2 := by field_simp
      nlinarith [h1, mul_le_mul_of_nonneg_right hb2 h0]
  · rw [if_neg hm]
    have : w m = 0 := by
      simp only [hw]; split_ifs
      · rcases not_and_or.1 hm with h | h
        · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
        · push Not at h; simp [h]
      · rfl
    simp [this]

end TernaryGoldbach.Prelim
