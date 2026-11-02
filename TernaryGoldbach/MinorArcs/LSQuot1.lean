import TernaryGoldbach.MinorArcs.LargeSievePrimes
import TernaryGoldbach.Prelim.MertensProduct
import TernaryGoldbach.Prelim.Ramare

/-!
# [B, Prop 12.2.4], part 1: definitions, Ramaré's estimate, and two inequalities for `G_q`

* `S_q = ∑_{p ∣ q} log p/p`, `f₁(q) = ∏_{p ∣ q} f₁(p)` [B, (12.13)];
* Ramaré's estimate (12.12) ([Ram95, Lemma 3.4], proved as `Prelim.ramare_Gq`);
* `G_q(R) G_P(t) ≤ G_q(tR)` if every prime `≤ R` or dividing `q` divides `P` (`Gq_mul_le`);
* `G(t) ≤ (P/φ(P)) G_P(t)` for squarefree `P` (`G_le_mul_Gq`, the lower half of [B, (12.11)]).
-/

open Real Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

/-- `S_q = ∑_{p ∣ q} log p / p`. -/
noncomputable def Sq (q : ℕ) : ℝ := ∑ p ∈ q.primeFactors, Real.log p / p

/-- The local factor of `f₁` [B, (12.13)]: `(1 + p^{−2/3}) (1 + (p^{1/3} + p^{2/3})/(p(p−1)))⁻¹`. -/
noncomputable def f1p (p : ℕ) : ℝ :=
  (1 + (p : ℝ) ^ (-(2 / 3 : ℝ))) /
    (1 + ((p : ℝ) ^ (1 / 3 : ℝ) + (p : ℝ) ^ (2 / 3 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 1)))

/-- `f₁(q) = ∏_{p ∣ q} f₁(p)` [B, (12.13)]. -/
noncomputable def f1q (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, f1p p

/-- Ramaré's estimate [B, (12.12)] (`Prelim.ramare_Gq`), for our `Gq`, `Sq`, `f1q`. -/
theorem ramare_Gq : ∃ c : ℝ, 1.3325822 ≤ c ∧ c ≤ 1.3325823 ∧ ∀ d : ℕ, 1 ≤ d → ∀ R : ℝ, 1 ≤ R →
    |Gq d R - (Nat.totient d / d) * (Real.log R + c + Sq d)| ≤ 7.284 * R ^ (-(1 / 3 : ℝ)) * f1q d :=
  TernaryGoldbach.Prelim.ramare_Gq

/-! ### Basic facts -/

/-- `μ²(r)/φ(r)`. -/
noncomputable def gf (r : ℕ) : ℝ := ((μ r : ℝ)) ^ 2 / Nat.totient r

theorem gf_nonneg (r : ℕ) : 0 ≤ gf r := by unfold gf; positivity

theorem gf_mul {a b : ℕ} (h : a.Coprime b) : gf (a * b) = gf a * gf b := by
  unfold gf
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast; rw [mul_pow, div_mul_div_comm]

theorem Gq_eq (q : ℕ) (R : ℝ) :
    Gq q R = ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q), gf r := rfl

theorem Gq_nonneg_q (q : ℕ) (R : ℝ) : 0 ≤ Gq q R := by
  rw [Gq_eq]; exact sum_nonneg fun r _ => gf_nonneg r

theorem Sq_nonneg (q : ℕ) : 0 ≤ Sq q := by
  unfold Sq
  exact sum_nonneg fun p hp => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- `S_q ≤ log q`. -/
theorem Sq_le_log {q : ℕ} (hq : 1 ≤ q) : Sq q ≤ Real.log q := by
  have h1 : Sq q ≤ ∑ p ∈ q.primeFactors, Real.log p := by
    unfold Sq
    refine sum_le_sum fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact div_le_self (Real.log_natCast_nonneg p) hp1
  refine h1.trans ?_
  rw [← Real.log_prod (fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).pos; positivity)]
  apply Real.log_le_log (by
    exact prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
  have : ∏ p ∈ q.primeFactors, p ≤ q :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have h2 : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by exact_mod_cast this
  simpa [Nat.cast_prod] using h2

/-! ### `G_q(R) G_P(t) ≤ G_q(tR)` -/

/-- **`G_q(R) G_P(t) ≤ G_q(tR)`** if every prime `≤ R`, and every prime dividing `q`, divides `P`. -/
theorem Gq_mul_le {q P : ℕ} {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hPR : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ R → p ∣ P) (hPq : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ P) :
    Gq q R * Gq P t ≤ Gq q (t * R) := by
  set A := (Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q)
  set B := (Icc 1 ⌊t⌋₊).filter (fun r => Nat.Coprime r P)
  set C := (Icc 1 ⌊t * R⌋₊).filter (fun r => Nat.Coprime r q)
  -- elements of `A` and `B` are coprime
  have hcop : ∀ a ∈ A, ∀ b ∈ B, Nat.Coprime a b := by
    intro a ha b hb
    simp only [A, B, mem_filter, mem_Icc] at ha hb
    refine Nat.coprime_of_dvd fun p hp hpa hpb => ?_
    have hpa' : p ≤ a := Nat.le_of_dvd (by omega) hpa
    have hpR : (p : ℝ) ≤ R :=
      (by exact_mod_cast hpa'.trans ha.1.2 : (p : ℝ) ≤ ⌊R⌋₊).trans (Nat.floor_le hR)
    have h1 : Nat.Coprime p b := (Nat.Coprime.coprime_dvd_left (hPR p hp hpR) hb.2.symm)
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h1 hpb
  rw [Gq_eq, Gq_eq, Gq_eq, sum_mul_sum, ← sum_product']
  rw [sum_congr rfl fun x hx => (gf_mul (hcop x.1 (mem_product.1 hx).1 x.2 (mem_product.1 hx).2)).symm]
  -- the map `(a, b) ↦ ab` is injective on `A × B`
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (A ×ˢ B : Finset (ℕ × ℕ)) := by
    intro x hx y hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe] at hx hy
    simp only at hxy
    have hx1 : 0 < x.1 := by simp only [A, mem_filter, mem_Icc] at hx; omega
    have hy1 : 0 < y.1 := by simp only [A, mem_filter, mem_Icc] at hy; omega
    have d1 : x.1 ∣ y.1 := (hcop x.1 hx.1 y.2 hy.2).dvd_of_dvd_mul_right ⟨x.2, by rw [← hxy]⟩
    have d2 : y.1 ∣ x.1 := (hcop y.1 hy.1 x.2 hx.2).dvd_of_dvd_mul_right ⟨y.2, by rw [hxy]⟩
    have e1 : x.1 = y.1 := Nat.dvd_antisymm d1 d2
    have e2 : x.2 = y.2 := by
      rw [e1] at hxy; exact Nat.eq_of_mul_eq_mul_left hy1 hxy
    exact Prod.ext e1 e2
  rw [← sum_image (f := gf) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => gf_nonneg r
  intro m hm
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hm
  have ha := (mem_product.1 hab).1
  have hb := (mem_product.1 hab).2
  simp only [A, B, mem_filter, mem_Icc] at ha hb
  simp only [C, mem_filter, mem_Icc]
  refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩, ?_⟩
  · apply Nat.le_floor
    push_cast
    have h1 : (a : ℝ) ≤ R := (by exact_mod_cast ha.1.2 : (a : ℝ) ≤ ⌊R⌋₊).trans (Nat.floor_le hR)
    have h2 : (b : ℝ) ≤ t := (by exact_mod_cast hb.1.2 : (b : ℝ) ≤ ⌊t⌋₊).trans (Nat.floor_le ht)
    rw [mul_comm (a : ℝ)]
    exact mul_le_mul h2 h1 (Nat.cast_nonneg _) ht
  · refine Nat.coprime_mul_iff_left.2 ⟨ha.2, ?_⟩
    refine Nat.coprime_of_dvd fun p hp hpb hpq => ?_
    have h1 : Nat.Coprime p b := Nat.Coprime.coprime_dvd_left (hPq p hp hpq) hb.2.symm
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h1 hpb

/-! ### `G(t) ≤ (P/φ(P)) G_P(t)` -/

/-- `μ²/φ` as an arithmetic function. -/
noncomputable def gfA : ArithmeticFunction ℝ := ⟨gf, by simp [gf]⟩

theorem isMultiplicative_gfA : ArithmeticFunction.IsMultiplicative gfA :=
  ⟨by simp [gfA, gf], fun h => gf_mul h⟩

/-- `∑_{d ∣ P} μ²(d)/φ(d) = P/φ(P)` for squarefree `P`. -/
theorem sum_divisors_gf {P : ℕ} (hP : Squarefree P) :
    ∑ d ∈ P.divisors, gf d = (P : ℝ) / Nat.totient P := by
  have h := isMultiplicative_gfA.prodPrimeFactors_one_add_of_squarefree hP
  have e : ∀ d, gfA d = gf d := fun _ => rfl
  simp only [e] at h
  rw [← h, TernaryGoldbach.Prelim.div_totient_eq_prod (Nat.one_le_iff_ne_zero.2 hP.ne_zero)]
  refine prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  unfold gf
  rw [ArithmeticFunction.moebius_apply_prime hpp, Nat.totient_prime hpp,
    Nat.cast_sub hpp.one_le]
  push_cast
  field_simp
  ring

/-- **`G(t) ≤ (P/φ(P)) G_P(t)`** for squarefree `P` ([B, (12.11)]). -/
theorem G_le_mul_Gq {P : ℕ} (hP : Squarefree P) {t : ℝ} :
    Gq 1 t ≤ (P : ℝ) / Nat.totient P * Gq P t := by
  rw [← sum_divisors_gf hP, Gq_eq, Gq_eq, sum_mul_sum, ← sum_product']
  set B := (Icc 1 ⌊t⌋₊).filter (fun r => Nat.Coprime r P)
  -- restrict to squarefree `m`
  have hsq : ∑ m ∈ (Icc 1 ⌊t⌋₊).filter (fun r => Nat.Coprime r 1), gf m =
      ∑ m ∈ ((Icc 1 ⌊t⌋₊).filter (fun r => Nat.Coprime r 1)).filter Squarefree, gf m := by
    refine (sum_filter_of_ne fun m _ h => ?_).symm
    by_contra hs
    exact h (by simp [gf, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs])
  rw [hsq]
  set D := ((Icc 1 ⌊t⌋₊).filter (fun r => Nat.Coprime r 1)).filter Squarefree
  -- `m ↦ (gcd(m, P), m / gcd(m, P))`
  set φm : ℕ → ℕ × ℕ := fun m => (Nat.gcd m P, m / Nat.gcd m P)
  have hmem : ∀ m ∈ D, φm m ∈ P.divisors ×ˢ B := by
    intro m hm
    simp only [D, mem_filter, mem_Icc] at hm
    obtain ⟨⟨⟨h1, h2⟩, -⟩, hsqf⟩ := hm
    have hg : 0 < Nat.gcd m P := Nat.gcd_pos_of_pos_left _ (by omega)
    refine mem_product.2 ⟨Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right m P, hP.ne_zero⟩, ?_⟩
    simp only [B, mem_filter, mem_Icc]
    refine ⟨⟨?_, (Nat.div_le_self _ _).trans h2⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left m P)) hg
    · -- `m/gcd(m,P)` is coprime to `P` since `m` is squarefree
      refine Nat.coprime_of_dvd fun p hp hp1 hp2 => ?_
      have hpm : p ∣ m := hp1.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m P))
      have hpg : p ∣ Nat.gcd m P := Nat.dvd_gcd hpm hp2
      have : p * p ∣ m := by
        have e : m = Nat.gcd m P * (m / Nat.gcd m P) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left m P)).symm
        rw [e]; exact Nat.mul_dvd_mul hpg hp1
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsqf p this))
  have hval : ∀ m ∈ D, gf m = gf (φm m).1 * gf (φm m).2 := by
    intro m hm
    simp only [D, mem_filter] at hm
    have hcop : Nat.Coprime (Nat.gcd m P) (m / Nat.gcd m P) := by
      have hB := (mem_product.1 (hmem m (by simp only [D, mem_filter]; exact hm))).2
      simp only [B, mem_filter] at hB
      exact (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right m P) hB.2.symm)
    rw [← gf_mul hcop, Nat.mul_div_cancel' (Nat.gcd_dvd_left m P)]
  have hinj : Set.InjOn φm (D : Set ℕ) := by
    intro x _ y _ hxy
    have e1 := congrArg (fun z : ℕ × ℕ => z.1 * z.2) hxy
    simp only [φm, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ P)] at e1
    exact e1
  rw [sum_congr rfl hval, ← sum_image (f := fun x : ℕ × ℕ => gf x.1 * gf x.2) hinj]
  exact sum_le_sum_of_subset_of_nonneg (fun x hx => by
    obtain ⟨m, hm, rfl⟩ := mem_image.1 hx; exact hmem m hm)
    fun x _ _ => mul_nonneg (gf_nonneg _) (gf_nonneg _)

end TernaryGoldbach.MinorArcs
