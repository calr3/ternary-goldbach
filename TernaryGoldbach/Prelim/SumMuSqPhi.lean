import Mathlib

/-!
# Lower bounds for `∑ μ(r)²/φ(r)` [B, (5.41)]

* `sum_inv_le_sum_inv_totient`: `∑_{n ≤ N} 1/n ≤ ∑_{r ≤ N, r squarefree} 1/φ(r)`;
* `sum_sqfree_div_totient_le`: for antitone `w ≥ 0`,
  `∑_{r ≤ N sq-free} w(r)/φ(r) ≤ (q/φ(q)) ∑_{r ≤ N sq-free, (r,q)=1} w(r)/φ(r)`;
* `log_le_sum_coprime`: `(φ(q)/q) log R ≤ ∑_{r ≤ R, (r,q)=1} μ(r)²/φ(r)` [B, (5.41)].
-/

open Finset
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.Prelim

/-! ### `∑_{k | r^M} 1/k ≤ r/φ(r)` for squarefree `r` -/

theorem geom_mul_pred_le (p M : ℕ) (hp : 1 ≤ p) :
    (∑ k ∈ range (M + 1), p ^ k) * (p - 1) ≤ p ^ M * p := by
  have h : (∑ k ∈ range (M + 1), p ^ k) * (p - 1) + 1 = p ^ (M + 1) := by
    induction M with
    | zero => simp; omega
    | succ M ih =>
      rw [sum_range_succ, add_mul, add_right_comm, ih,
        show p ^ (M + 1) + p ^ (M + 1) * (p - 1) = p ^ (M + 1) * (1 + (p - 1)) by ring,
        Nat.add_sub_cancel' hp, ← pow_succ]
  rw [← pow_succ]; omega

theorem sigma_pow_mul_totient_le (M : ℕ) :
    ∀ r : ℕ, Squarefree r → σ 1 (r ^ M) * Nat.totient r ≤ r ^ M * r := by
  intro r
  induction r using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro hsq
    have hn1 : n = 1 := by
      by_contra h
      have : p * p ∣ p ^ n := by
        rw [← pow_two]; exact pow_dvd_pow p (by omega)
      exact hp.not_isUnit (hsq p this)
    subst hn1
    rw [pow_one, ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.totient_prime hp]
    exact geom_mul_pred_le p M hp.one_le
  | zero => intro h; exact absurd h not_squarefree_zero
  | one => intro _; simp
  | coprime a b _ _ hab iha ihb =>
    intro hsq
    have ha := iha (Squarefree.of_mul_left hsq)
    have hb := ihb (Squarefree.of_mul_right hsq)
    rw [mul_pow, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hab.pow M M),
      Nat.totient_mul hab]
    calc σ 1 (a ^ M) * σ 1 (b ^ M) * (Nat.totient a * Nat.totient b)
        = (σ 1 (a ^ M) * Nat.totient a) * (σ 1 (b ^ M) * Nat.totient b) := by ring
      _ ≤ (a ^ M * a) * (b ^ M * b) := Nat.mul_le_mul ha hb
      _ = a ^ M * b ^ M * (a * b) := by ring

theorem sum_inv_divisors_eq (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ n.divisors, (1 / k : ℝ) = σ 1 n / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors n (fun d => d), eq_div_iff hn0,
    sum_mul]
  push_cast
  refine sum_congr rfl fun k hk => ?_
  have hk' := Nat.dvd_of_mem_divisors hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
  rw [Nat.cast_div hk' hk0]; field_simp

theorem sum_inv_divisors_pow_le {r : ℕ} (hr : Squarefree r) (M : ℕ) :
    ∑ k ∈ (r ^ M).divisors, (1 / k : ℝ) ≤ r / Nat.totient r := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hr0)
  rw [sum_inv_divisors_eq _ (pow_ne_zero _ hr0), div_le_div_iff₀ (by positivity) hφ]
  have := sigma_pow_mul_totient_le M r hr
  have : ((σ 1 (r ^ M) * Nat.totient r : ℕ) : ℝ) ≤ ((r ^ M * r : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at this ⊢; linarith

/-! ### The radical -/

/-- `rad n = ∏_{p | n} p`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

theorem squarefree_rad (n : ℕ) : Squarefree (rad n) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (Nat.prime_of_mem_primeFactors hp).prime.squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq

theorem primeFactors_rad (n : ℕ) : (rad n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod_primeFactors n

theorem rad_pos {n : ℕ} (hn : n ≠ 0) : 0 < rad n :=
  Nat.pos_of_ne_zero fun h => hn (Nat.eq_zero_of_zero_dvd (h ▸ rad_dvd n))

/-- `n ∣ (rad n)^N` for `N ≥ n`. -/
theorem dvd_rad_pow {n N : ℕ} (hn : n ≠ 0) (hN : n ≤ N) : n ∣ rad n ^ N := by
  rw [← Nat.factorization_le_iff_dvd hn (pow_ne_zero _ (rad_pos hn).ne')]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p ∈ n.primeFactors
  · have h1 : (rad n).factorization p = 1 := by
      have hsq := squarefree_rad n
      have hle := hsq.natFactorization_le_one p
      have hpos : 0 < (rad n).factorization p := by
        rw [← primeFactors_rad] at hp
        exact Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp)
          (rad_pos hn).ne' (Nat.dvd_of_mem_primeFactors hp)
      omega
    rw [h1, mul_one]
    exact (Nat.factorization_lt p hn).le.trans hN
  · rw [Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])]
    exact Nat.zero_le _

/-- `∑_{n ≤ N} 1/n ≤ ∑_{r ≤ N, r squarefree} 1/φ(r)` (group `n` by `rad n`). -/
theorem sum_inv_le_sum_inv_totient (N : ℕ) :
    ∑ n ∈ Icc 1 N, (1 / n : ℝ) ≤ ∑ r ∈ (Icc 1 N).filter Squarefree, (1 / Nat.totient r : ℝ) := by
  have hmaps : ∀ n ∈ Icc 1 N, rad n ∈ (Icc 1 N).filter Squarefree := by
    intro n hn
    rw [mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    rw [mem_filter, mem_Icc]
    exact ⟨⟨rad_pos hn0, (Nat.le_of_dvd (by omega) (rad_dvd n)).trans hn.2⟩, squarefree_rad n⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun r hr => ?_
  rw [mem_filter, mem_Icc] at hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  set F := (Icc 1 N).filter (fun n => rad n = r)
  have hdvd : ∀ n ∈ F, r ∣ n := by
    intro n hn; rw [mem_filter] at hn; rw [← hn.2]; exact rad_dvd n
  have h1 : ∑ n ∈ F, (1 / n : ℝ) = 1 / r * ∑ k ∈ F.image (· / r), (1 / k : ℝ) := by
    rw [sum_image (fun n hn n' hn' h => by
      rw [← Nat.div_mul_cancel (hdvd n hn), h, Nat.div_mul_cancel (hdvd n' hn')]),
      mul_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [Nat.cast_div (hdvd n hn) hr0]
    have : (n : ℝ) ≠ 0 := by
      have := (mem_Icc.1 (mem_filter.1 hn).1).1; exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hsub : F.image (· / r) ⊆ (r ^ N).divisors := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    have hn' := mem_filter.1 hn
    have hn1 := mem_Icc.1 hn'.1
    rw [Nat.mem_divisors]
    refine ⟨(Nat.div_dvd_of_dvd (hdvd n hn)).trans ?_, pow_ne_zero _ (by omega)⟩
    rw [← hn'.2]; exact dvd_rad_pow (by omega) hn1.2
  rw [h1]
  have h2 := sum_le_sum_of_subset_of_nonneg hsub (f := fun k : ℕ => (1 / k : ℝ))
    (fun _ _ _ => by positivity)
  have h3 := sum_inv_divisors_pow_le hr.2 N
  have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 (by omega)
  calc 1 / (r : ℝ) * ∑ k ∈ F.image (· / r), (1 / k : ℝ) ≤ 1 / r * (r / Nat.totient r) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = _ := by field_simp

/-! ### The coprime reduction -/

/-- `μ/φ` as a multiplicative arithmetic function. -/
noncomputable def muDivPhi : ArithmeticFunction ℝ :=
  ⟨fun d => (μ d : ℝ) / Nat.totient d, by simp⟩

theorem muDivPhi_apply (d : ℕ) : muDivPhi d = (μ d : ℝ) / Nat.totient d := rfl

theorem isMultiplicative_muDivPhi : muDivPhi.IsMultiplicative := by
  refine ⟨by simp [muDivPhi_apply], fun {m n} hmn => ?_⟩
  simp only [muDivPhi_apply]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast; rw [div_mul_div_comm]

/-- `∑_{d | q, d squarefree} 1/φ(d) ≤ q/φ(q)` (in fact equality). -/
theorem sum_sqfree_divisors_inv_totient_le (q : ℕ) (hq : 1 ≤ q) :
    ∑ d ∈ q.divisors.filter Squarefree, (1 / Nat.totient d : ℝ) ≤ q / Nat.totient q := by
  have hq0 : q ≠ 0 := by omega
  set s := rad q
  have hs := squarefree_rad q
  have key := isMultiplicative_muDivPhi.prodPrimeFactors_one_sub_of_squarefree _ hs
  -- The left side is a sub-sum of `∑_{d | rad q} μ(d)²/φ(d)`.
  have hsub : q.divisors.filter Squarefree ⊆ s.divisors := by
    intro d hd
    rw [mem_filter, Nat.mem_divisors] at hd
    rw [Nat.mem_divisors]
    refine ⟨?_, (rad_pos hq0).ne'⟩
    have hd0 : d ≠ 0 := hd.2.ne_zero
    rw [← Nat.prod_primeFactors_of_squarefree hd.2]
    rw [Nat.prod_primeFactors_dvd_iff (rad_pos hq0).ne', primeFactors_rad]
    exact Nat.primeFactors_mono hd.1.1 hq0
  have h1 : ∑ d ∈ q.divisors.filter Squarefree, (1 / Nat.totient d : ℝ) ≤
      ∑ d ∈ s.divisors, (μ d : ℝ) * muDivPhi d := by
    refine le_trans (le_of_eq (sum_congr rfl fun d hd => ?_))
      (sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => ?_)
    · rw [muDivPhi_apply, ← mul_div_assoc, ← sq]
      have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (mem_filter.1 hd).2
      rw [show ((μ d : ℝ)) ^ 2 = ((μ d ^ 2 : ℤ) : ℝ) by push_cast; ring, this]; simp
    · rw [muDivPhi_apply, ← mul_div_assoc]; exact div_nonneg (by nlinarith) (Nat.cast_nonneg _)
  rw [← key, primeFactors_rad] at h1
  refine h1.trans (le_of_eq ?_)
  -- `∏_{p | q} (1 + 1/(p-1)) = q/φ(q)`.
  have hφ := Nat.totient_mul_prod_primeFactors q
  have hφ0 : (Nat.totient q : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (by omega)).ne'
  have hprod : ∀ p ∈ q.primeFactors, (1 - muDivPhi p) = (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [muDivPhi_apply, ArithmeticFunction.moebius_apply_prime hpp, Nat.totient_prime hpp]
    have : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show p - 1 ≠ 0 by have := hpp.two_le; omega)
    field_simp
    push_cast [hpp.one_le]; ring
  rw [prod_congr rfl hprod, prod_div_distrib, eq_div_iff hφ0]
  have hpos : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    rw [prod_ne_zero_iff]; intro p hp
    exact_mod_cast (show p - 1 ≠ 0 by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
  rw [div_mul_eq_mul_div, div_eq_iff hpos]
  have : ((Nat.totient q * ∏ p ∈ q.primeFactors, p : ℕ) : ℝ) =
      ((q * ∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [hφ]
  push_cast at this ⊢
  linarith

set_option maxHeartbeats 1000000 in
/-- **Coprime reduction**: for antitone `w ≥ 0`,
`∑_{r ≤ N sq-free} w(r)/φ(r) ≤ (q/φ(q)) ∑_{r ≤ N sq-free, (r,q)=1} w(r)/φ(r)`
(write `r = d r'`, `d = (r, q)`). -/
theorem sum_sqfree_div_totient_le {q : ℕ} (hq : 1 ≤ q) (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hw : ∀ m n, m ≤ n → w n ≤ w m) (N : ℕ) :
    ∑ r ∈ (Icc 1 N).filter Squarefree, w r / Nat.totient r ≤
      q / Nat.totient q * ∑ r ∈ (Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
        w r / Nat.totient r := by
  have hq0 : q ≠ 0 := by omega
  set D := q.divisors.filter Squarefree
  set C := (Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r q)
  set S := (Icc 1 N).filter Squarefree
  set g : ℕ → ℕ × ℕ := fun r => (Nat.gcd r q, r / Nat.gcd r q)
  have hfacts : ∀ r ∈ S, g r ∈ D ×ˢ C ∧ r = (g r).1 * (g r).2 ∧
      Nat.totient r = Nat.totient (g r).1 * Nat.totient (g r).2 := by
    intro r hr
    rw [mem_filter, mem_Icc] at hr
    have hr0 : r ≠ 0 := by omega
    have hd0 : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_left _ (by omega)
    have hdr : Nat.gcd r q ∣ r := Nat.gcd_dvd_left r q
    have hrr : r = Nat.gcd r q * (r / Nat.gcd r q) := (Nat.mul_div_cancel' hdr).symm
    have hr'0 : r / Nat.gcd r q ≠ 0 := by
      intro h; rw [h, mul_zero] at hrr; omega
    have hcop : Nat.Coprime (r / Nat.gcd r q) q := by
      rw [← Nat.disjoint_primeFactors hr'0 hq0, Nat.primeFactors_div_gcd hr.2 hq0]
      exact disjoint_sdiff_self_left
    have hcop2 : Nat.Coprime (Nat.gcd r q) (r / Nat.gcd r q) :=
      (hcop.coprime_dvd_right (Nat.gcd_dvd_right r q)).symm
    refine ⟨mem_product.2 ⟨?_, ?_⟩, hrr, ?_⟩
    · rw [mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.gcd_dvd_right r q, hq0⟩, hr.2.squarefree_of_dvd hdr⟩
    · rw [mem_filter, mem_Icc]
      refine ⟨⟨Nat.pos_of_ne_zero hr'0, (Nat.div_le_self r _).trans hr.1.2⟩, ?_, hcop⟩
      exact hr.2.squarefree_of_dvd (Nat.div_dvd_of_dvd hdr)
    · conv_lhs => rw [hrr]
      exact Nat.totient_mul hcop2
  have hinj : Set.InjOn g S := by
    intro r hr r' hr' h
    rw [(hfacts r hr).2.1, (hfacts r' hr').2.1, h]
  -- Termwise bound.
  have hterm : ∀ r ∈ S, w r / Nat.totient r ≤
      (fun p : ℕ × ℕ => (1 / Nat.totient p.1 : ℝ) * (w p.2 / Nat.totient p.2)) (g r) := by
    intro r hr
    obtain ⟨hmem, hrr, hφ⟩ := hfacts r hr
    have hle : (g r).2 ≤ r := Nat.div_le_self r _
    have hd := (mem_product.1 hmem)
    have hφ1 : (0 : ℝ) < Nat.totient (g r).1 := by
      exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_mem_divisors (mem_filter.1 hd.1).1)
    have hφ2 : (0 : ℝ) < Nat.totient (g r).2 := by
      exact_mod_cast Nat.totient_pos.2 (mem_Icc.1 (mem_filter.1 hd.2).1).1
    simp only
    rw [hφ]; push_cast
    rw [one_div_mul_eq_div, div_div, mul_comm ((Nat.totient (g r).2 : ℝ))]
    exact div_le_div_of_nonneg_right (hw _ _ hle) (by positivity)
  calc ∑ r ∈ S, w r / Nat.totient r
      ≤ ∑ r ∈ S, (fun p : ℕ × ℕ => (1 / Nat.totient p.1 : ℝ) * (w p.2 / Nat.totient p.2)) (g r) :=
        sum_le_sum hterm
    _ = ∑ p ∈ S.image g, (1 / Nat.totient p.1 : ℝ) * (w p.2 / Nat.totient p.2) :=
        (sum_image (f := fun p : ℕ × ℕ => (1 / Nat.totient p.1 : ℝ) * (w p.2 / Nat.totient p.2))
          hinj).symm
    _ ≤ ∑ p ∈ D ×ˢ C, (1 / Nat.totient p.1 : ℝ) * (w p.2 / Nat.totient p.2) := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
        · intro p hp; rw [mem_image] at hp; obtain ⟨r, hr, rfl⟩ := hp; exact (hfacts r hr).1
        · exact mul_nonneg (by positivity) (div_nonneg (hw0 _) (Nat.cast_nonneg _))
    _ = (∑ d ∈ D, (1 / Nat.totient d : ℝ)) * ∑ r ∈ C, w r / Nat.totient r := by
        rw [sum_product, sum_mul]; simp_rw [mul_sum]
    _ ≤ q / Nat.totient q * ∑ r ∈ C, w r / Nat.totient r :=
        mul_le_mul_of_nonneg_right (sum_sqfree_divisors_inv_totient_le q hq)
          (sum_nonneg fun r _ => div_nonneg (hw0 r) (Nat.cast_nonneg _))

/-- **[B, (5.41)]**: `(φ(q)/q) log R ≤ ∑_{r ≤ R, (r,q)=1} μ(r)²/φ(r)` for `R ≥ 0`. -/
theorem log_le_sum_coprime {q : ℕ} (hq : 1 ≤ q) {R : ℝ} (hR : 0 ≤ R) :
    Nat.totient q / q * Real.log R ≤
      ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
        (1 / Nat.totient r : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have h1 := log_le_harmonic_floor R hR
  rw [harmonic_eq_sum_Icc] at h1
  push_cast at h1
  have h2 := sum_inv_le_sum_inv_totient ⌊R⌋₊
  have h3 := sum_sqfree_div_totient_le hq (fun _ => 1) (fun _ => zero_le_one) (fun _ _ _ => le_rfl)
    ⌊R⌋₊
  simp only [one_div] at h2 h3 ⊢
  have h4 : Real.log R ≤ q / Nat.totient q *
      ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q), (Nat.totient r : ℝ)⁻¹ := by
    have := h3
    simp only [div_eq_mul_inv, one_mul] at this ⊢
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hq0]
  calc (Nat.totient q : ℝ) * Real.log R ≤ Nat.totient q * (q / Nat.totient q *
      ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q), (Nat.totient r : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left h4 hφ.le
    _ = _ := by field_simp

end TernaryGoldbach.Prelim
