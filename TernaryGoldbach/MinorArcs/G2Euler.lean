import TernaryGoldbach.MinorArcs.G2Moebius

/-!
# Euler-product bound for `∑_{a ≤ A} H_d(a) a^s`

For `0 ≤ s < 1`, with `c_s(p) = p/(p − p^s)`, `ℓ_s(p) = 1 + p^s/((p+1)(p − p^s))`,
`ρ_s(p) = (p+1)/(p+1−p^s)` (so `ℓ_s(p) ρ_s(p) = c_s(p)`):
`∑_{a ≤ A} H_d(a) a^s ≤ c_s(2) ∏_{2 < p ≤ A} ℓ_s(p) ∏_{p ∣ d} ρ_s(p)` for odd `d` (`sum_Hd_rpow_le`).
-/

open Real Finset
open ArithmeticFunction (moebius sigma IsMultiplicative)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs

/-- `c_s(p) = p/(p − p^s)`. -/
noncomputable def cfac (s : ℝ) (p : ℕ) : ℝ := p / (p - (p : ℝ) ^ s)

/-- `ℓ_s(p) = 1 + p^s/((p+1)(p − p^s))`. -/
noncomputable def ell (s : ℝ) (p : ℕ) : ℝ := 1 + (p : ℝ) ^ s / ((p + 1) * (p - (p : ℝ) ^ s))

/-- `ρ_s(p) = (p+1)/(p+1−p^s)`. -/
noncomputable def rho (s : ℝ) (p : ℕ) : ℝ := (p + 1) / (p + 1 - (p : ℝ) ^ s)

section Facts
variable {s : ℝ} {p : ℕ}

theorem rpow_lt_self' (hs1 : s < 1) (hp : 2 ≤ p) : (p : ℝ) ^ s < p := by
  have : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  exact Real.rpow_lt_self_of_one_lt this hs1

theorem one_le_rpow' (hs0 : 0 ≤ s) (hp : 1 ≤ p) : 1 ≤ (p : ℝ) ^ s :=
  Real.one_le_rpow (by exact_mod_cast hp) hs0

theorem one_le_ell (hs1 : s < 1) (hp : 2 ≤ p) : 1 ≤ ell s p := by
  have h := rpow_lt_self' hs1 hp
  unfold ell
  have : 0 ≤ (p : ℝ) ^ s / ((p + 1) * (p - (p : ℝ) ^ s)) := by
    apply div_nonneg (by positivity); apply mul_nonneg (by positivity); linarith
  linarith

theorem one_le_rho (hs0 : 0 ≤ s) (hs1 : s < 1) (hp : 2 ≤ p) : 1 ≤ rho s p := by
  have h := rpow_lt_self' hs1 hp
  have h1 := one_le_rpow' hs0 (by omega : 1 ≤ p)
  unfold rho
  rw [le_div_iff₀ (by linarith)]; linarith

theorem one_le_cfac (hs0 : 0 ≤ s) (hs1 : s < 1) (hp : 2 ≤ p) : 1 ≤ cfac s p := by
  have h := rpow_lt_self' hs1 hp
  have h1 := one_le_rpow' hs0 (by omega : 1 ≤ p)
  unfold cfac
  rw [le_div_iff₀ (by linarith)]; linarith

theorem ell_mul_rho (hs1 : s < 1) (hp : 2 ≤ p) : ell s p * rho s p = cfac s p := by
  have h := rpow_lt_self' hs1 hp
  have h1 : (p : ℝ) - (p : ℝ) ^ s ≠ 0 := ne_of_gt (sub_pos.2 h)
  have h2 : (p : ℝ) + 1 - (p : ℝ) ^ s ≠ 0 := by linarith
  have h3 : (p : ℝ) + 1 ≠ 0 := by positivity
  unfold ell rho cfac
  field_simp
  ring

end Facts

/-! ### `∑_{a ≤ A} H_d(a) a^s` -/

theorem Hd_rpow_prime_pow {d p : ℕ} (hp : p.Prime) (s : ℝ) (k : ℕ) :
    Hd d (p ^ (k + 1)) * ((p ^ (k + 1) : ℕ) : ℝ) ^ s = kapH d p * ((p : ℝ) ^ s / p) ^ (k + 1) := by
  rw [Hd_prime_pow hp, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _), mul_assoc, ← mul_pow,
    div_eq_inv_mul]

theorem summable_Hd_rpow {d p : ℕ} (hp : p.Prime) {s : ℝ} (hs1 : s < 1) :
    Summable fun e => Hd d (p ^ e) * ((p ^ e : ℕ) : ℝ) ^ s := by
  have hlt := rpow_lt_self' hs1 hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set r := (p : ℝ) ^ s / p with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hp0]; exact hlt
  rw [← summable_nat_add_iff 1]
  simp_rw [Hd_rpow_prime_pow hp s, ← hr, pow_succ]
  exact ((summable_geometric_of_lt_one hr0 hr1).mul_right r).mul_left (kapH d p)

theorem tsum_Hd_rpow {d p : ℕ} (hp : p.Prime) {s : ℝ} (hs1 : s < 1) :
    ∑' e, Hd d (p ^ e) * ((p ^ e : ℕ) : ℝ) ^ s = if p ≠ 2 ∧ ¬ p ∣ d then ell s p else cfac s p := by
  have hlt := rpow_lt_self' hs1 hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set r := (p : ℝ) ^ s / p with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hp0]; exact hlt
  rw [(summable_Hd_rpow hp hs1).tsum_eq_zero_add]
  simp only [pow_zero, (isMultiplicative_Hd d).map_one, Nat.cast_one, Real.one_rpow, mul_one]
  simp_rw [Hd_rpow_prime_pow hp s, ← hr]
  rw [tsum_mul_left]
  have hg : ∑' e : ℕ, r ^ (e + 1) = r / (1 - r) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, div_eq_inv_mul]
  rw [hg, hr]
  have h1 : (p : ℝ) - (p : ℝ) ^ s ≠ 0 := ne_of_gt (sub_pos.2 hlt)
  have h3 : (p : ℝ) + 1 ≠ 0 := by positivity
  unfold kapH ell cfac
  split_ifs
  all_goals field_simp
  all_goals ring

/-- **`∑_{a ≤ A} H_d(a) a^s ≤ c_s(2) ∏_{2 < p ≤ A} ℓ_s(p) ∏_{p ∣ d} ρ_s(p)`** (odd `d`). -/
theorem sum_Hd_rpow_le {d : ℕ} (hd : Odd d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (A : ℕ) :
    ∑ a ∈ Icc 1 A, Hd d a * (a : ℝ) ^ s ≤
      cfac s 2 * (∏ p ∈ (Nat.primesBelow (A + 1)).filter (· ≠ 2), ell s p) *
        ∏ p ∈ d.primeFactors, rho s p := by
  have h := sum_le_euler (f := fun a => Hd d a * (a : ℝ) ^ s)
    (fun n => mul_nonneg (Hd_nonneg d n) (by positivity))
    (by simp [(isMultiplicative_Hd d).map_one])
    (fun {m n} hmn => by
      simp only [(isMultiplicative_Hd d).map_mul_of_coprime hmn, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]; ring)
    (fun hp => by
      simpa only [Real.norm_eq_abs] using (summable_Hd_rpow (d := d) hp hs1).abs) A
  refine h.trans ?_
  rw [prod_congr rfl fun p hp => tsum_Hd_rpow (d := d) (Nat.mem_primesBelow.1 hp).2 hs1]
  have hd2 : ¬ 2 ∣ d := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hd
  have hfac : ∀ p ∈ Nat.primesBelow (A + 1), (if p ≠ 2 ∧ ¬ p ∣ d then ell s p else cfac s p) =
      (if p = 2 then cfac s 2 else ell s p) * (if p ∣ d then rho s p else 1) := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.1 hp).2
    by_cases h2 : p = 2
    · subst h2; simp [hd2]
    · by_cases hpd : p ∣ d
      · simp [h2, hpd, ell_mul_rho hs1 hpp.two_le]
      · simp [h2, hpd]
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_ite, ← prod_filter]
  set P := Nat.primesBelow (A + 1)
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => (Nat.mem_primesBelow.1 hp).2.two_le
  have hc1 := one_le_cfac hs0 hs1 (le_refl 2)
  have hA1 : ∏ p ∈ P.filter (· = 2), cfac s 2 ≤ cfac s 2 := by
    rw [prod_const]
    have hcard : (P.filter (· = 2)).card ≤ 1 :=
      card_le_one.2 fun a ha b hb => by
        simp only [mem_filter] at ha hb; rw [ha.2, hb.2]
    calc cfac s 2 ^ (P.filter (· = 2)).card ≤ cfac s 2 ^ 1 := pow_le_pow_right₀ hc1 hcard
      _ = cfac s 2 := pow_one _
  have hA3 : ∏ p ∈ P.filter (· ∣ d), rho s p ≤ ∏ p ∈ d.primeFactors, rho s p := by
    refine prod_le_prod_of_subset_of_one_le₀ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter] at hp
      exact Nat.mem_primeFactors.2 ⟨(Nat.mem_primesBelow.1 hp.1).2, hp.2, by
        rintro rfl; exact hd2 (dvd_zero 2)⟩
    · intro p hp
      linarith [one_le_rho hs0 hs1 (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le]
    · intro p hp _
      exact one_le_rho hs0 hs1 (Nat.prime_of_mem_primeFactors hp).two_le
  have hell0 : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ p = 2), ell s p :=
    prod_nonneg fun p hp => by
      linarith [one_le_ell hs1 (hP2 p (mem_filter.1 hp).1)]
  have hrho0 : 0 ≤ ∏ p ∈ P.filter (· ∣ d), rho s p :=
    prod_nonneg fun p hp => by
      linarith [one_le_rho hs0 hs1 (hP2 p (mem_filter.1 hp).1)]
  have hc0 : 0 ≤ ∏ p ∈ P.filter (· = 2), cfac s 2 := prod_nonneg fun _ _ => by linarith
  calc (∏ p ∈ P.filter (· = 2), cfac s 2) * (∏ p ∈ P.filter (fun p => ¬ p = 2), ell s p) *
        ∏ p ∈ P.filter (· ∣ d), rho s p
      ≤ cfac s 2 * (∏ p ∈ P.filter (fun p => ¬ p = 2), ell s p) * ∏ p ∈ d.primeFactors, rho s p := by
        gcongr
    _ = _ := rfl

end TernaryGoldbach.MinorArcs
