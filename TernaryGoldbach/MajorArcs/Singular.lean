import TernaryGoldbach.MinorArcs.Montgomery
import TernaryGoldbach.MajorArcs.SumMuPhi

/-!
# The singular series of [B, §10.2] for `r = 150000`

* `ramanujan_sum`: `c_q(n) = Σ_{a<q, (a,q)=1} e(an/q) = Σ_{d∣q} μ(d) (q/d) [q/d ∣ n]`;
* for squarefree `q`, `μ(q) c_q(n) = ∏_{p∣q} (1 − [p∣n] p)`, so the main-term coefficient
  `(μ(q)/φ(q))³ c_q(−N)` equals `∏_{p∣q} a_p` with `a_p = −1/(p−1)²` (`p ∣ N`), `1/(p−1)³` (`p ∤ N`).
-/

open Finset
open ArithmeticFunction (moebius)
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach (e)

/-- **Ramanujan's sum**: `Σ_{a<q, (a,q)=1} e(an/q) = Σ_{d∣q} μ(d) (q/d) [q/d ∣ n]`. -/
theorem ramanujan_sum (q n : ℕ) (hq : 1 ≤ q) :
    ∑ a ∈ (range q).filter q.Coprime, e (a * n / q) =
      ∑ d ∈ q.divisors, (μ d : ℂ) * (if q / d ∣ n then ((q / d : ℕ) : ℂ) else 0) := by
  rw [sum_filter]
  have h1 : ∀ a ∈ range q, (if q.Coprime a then e (a * n / q) else 0) =
      ∑ d ∈ q.divisors, if d ∣ a then (μ d : ℂ) * e (a * n / q) else 0 := by
    intro a _
    have hg : 1 ≤ Nat.gcd q a := Nat.gcd_pos_of_pos_left _ (by omega)
    have := TernaryGoldbach.sum_moebius_divisors (Nat.gcd q a) hg
    rw [← sum_filter]
    have hfilt : q.divisors.filter (· ∣ a) = (Nat.gcd q a).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h1, h2⟩, by omega⟩
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h1, by omega⟩, h2⟩
    rw [hfilt, ← sum_mul, this]
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [Nat.mem_divisors] at hd
  obtain ⟨⟨m, hm⟩, _⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hqd : q / d = m := by rw [hm, Nat.mul_div_cancel_left _ hd0]
  rw [← sum_filter, ← mul_sum]
  have himg : (range q).filter (d ∣ ·) = (range m).map ⟨(d * ·), mul_right_injective₀ hd0.ne'⟩ := by
    ext a
    simp only [mem_filter, mem_range, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨ha, ⟨b, rfl⟩⟩
      exact ⟨b, by rw [hm] at ha; exact (Nat.mul_lt_mul_left hd0).1 ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by rw [hm]; exact (Nat.mul_lt_mul_left hd0).2 hb, dvd_mul_right _ _⟩
  rw [himg, sum_map]
  have h3 : ∀ b ∈ range m, e (((d * b : ℕ) : ℝ) * n / q) = e (b * n / m) := by
    intro b _
    congr 1; rw [hm]; push_cast
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    field_simp
  simp only [Function.Embedding.coeFn_mk]
  rw [sum_congr rfl h3, TernaryGoldbach.sum_e_range m n hm1, hqd]

/-- `d ↦ d [d ∣ n]` (multiplicative). -/
noncomputable def divW (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ∣ n then (d : ℝ) else 0, by simp⟩

theorem divW_apply (n d : ℕ) : divW n d = if d ∣ n then (d : ℝ) else 0 := rfl

theorem isMultiplicative_divW (n : ℕ) : (divW n).IsMultiplicative := by
  refine ⟨by simp [divW_apply], fun {a b} hab => ?_⟩
  simp only [divW_apply]
  by_cases ha : a ∣ n <;> by_cases hb : b ∣ n
  · rw [if_pos (hab.mul_dvd_of_dvd_of_dvd ha hb), if_pos ha, if_pos hb]; push_cast; ring
  · rw [if_neg (fun h => hb ((dvd_mul_left b a).trans h)), if_neg hb, mul_zero]
  · rw [if_neg (fun h => ha ((dvd_mul_right a b).trans h)), if_neg ha, zero_mul]
  · rw [if_neg (fun h => ha ((dvd_mul_right a b).trans h)), if_neg ha, zero_mul]

theorem moebius_div_mul_moebius {q d : ℕ} (hq : Squarefree q) (hd : d ∣ q) :
    (μ (q / d) : ℝ) * μ q = μ d := by
  obtain ⟨k, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  rw [Nat.mul_div_cancel_left _ hd0]
  have hcop : Nat.Coprime d k := Nat.coprime_of_squarefree_mul hq
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  have hk : Squarefree k := Squarefree.of_mul_right hq
  have : (μ k : ℝ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hk]; push_cast
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  push_cast
  linear_combination (μ d : ℝ) * this

/-- **`μ(q) c_q(n) = ∏_{p∣q} (1 − [p∣n] p)`** for squarefree `q`. -/
theorem moebius_mul_ramanujan {q : ℕ} (hq : Squarefree q) (n : ℕ) :
    (μ q : ℂ) * ∑ a ∈ (range q).filter q.Coprime, e (a * n / q) =
      ((∏ p ∈ q.primeFactors, (1 - divW n p) : ℝ) : ℂ) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  rw [ramanujan_sum q n hq1,
    (isMultiplicative_divW n).prodPrimeFactors_one_sub_of_squarefree _ hq, mul_sum]
  push_cast
  rw [← Nat.sum_div_divisors q (fun d => (μ d : ℂ) * ((divW n d : ℝ) : ℂ))]
  refine sum_congr rfl fun d hd => ?_
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hqd : q / (q / d) = d := Nat.div_div_self hdq (by omega)
  have hm := moebius_div_mul_moebius hq (Nat.div_dvd_of_dvd hdq)
  rw [hqd] at hm
  have hm' : (μ q : ℂ) * μ d = μ (q / d) := by rw [mul_comm]; exact_mod_cast hm
  rw [divW_apply, ← hm']
  split_ifs with h
  · push_cast; ring
  · simp

/-! ## The coefficients `∏_{p∣q} a_p(N)` -/

/-- `a_p(N) = (1 − [p∣N] p)/(p − 1)³`. -/
noncomputable def aP (N p : ℕ) : ℝ := (1 - divW N p) / ((p : ℝ) - 1) ^ 3

/-- `μ(q) c_q(N)/φ(q)³ = ∏_{p∣q} a_p(N)` for squarefree `q`, `0` otherwise. -/
noncomputable def coefN (N q : ℕ) : ℝ := if Squarefree q then ∏ p ∈ q.primeFactors, aP N p else 0

theorem totient_of_squarefree {q : ℕ} (hq : Squarefree q) :
    (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  rw [Nat.totient_eq_div_primeFactors_mul q, Nat.prod_primeFactors_of_squarefree hq,
    Nat.div_self hq0, one_mul]
  push_cast
  refine prod_congr rfl fun p hp => ?_
  have := (Nat.prime_of_mem_primeFactors hp).one_le
  push_cast [Nat.cast_sub this]; ring

theorem moebius_cube {q : ℕ} : (μ q : ℂ) ^ 3 = μ q := by
  by_cases hq : Squarefree q
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hq]; push_cast
    rw [← pow_mul, show ArithmeticFunction.cardFactors q * 3 = ArithmeticFunction.cardFactors q +
      2 * ArithmeticFunction.cardFactors q by ring, pow_add, pow_mul]; norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]; simp

theorem e_neg_eq_conj (t : ℝ) : e (-t) = (starRingEnd ℂ) (e t) := by
  unfold TernaryGoldbach.e
  rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

/-- **The main-term coefficient**: `(μ(q)/φ(q))³ Σ_{b ∈ Bset q} e(−N b/q) = ∏_{p∣q} a_p(N)`. -/
theorem coef_eq {N q : ℕ} (hq : 1 ≤ q) :
    ((μ q : ℂ) / q.totient) ^ 3 * ∑ b ∈ TernaryGoldbach.MinorArcs.Bset q, e (-(N * ((b : ℝ) / q))) =
      (coefN N q : ℂ) := by
  unfold coefN
  split_ifs with hsq
  · have hR := moebius_mul_ramanujan hsq N
    have hB : TernaryGoldbach.MinorArcs.Bset q = (range q).filter q.Coprime := by
      unfold TernaryGoldbach.MinorArcs.Bset
      exact filter_congr fun b _ => Nat.coprime_comm
    have hsum : ∑ b ∈ TernaryGoldbach.MinorArcs.Bset q, e (-(N * ((b : ℝ) / q))) =
        (starRingEnd ℂ) (∑ a ∈ (range q).filter q.Coprime, e (a * N / q)) := by
      rw [hB, map_sum]; refine sum_congr rfl fun b _ => ?_
      rw [← e_neg_eq_conj]; congr 1; ring
    have hconj : (μ q : ℂ) * ∑ b ∈ TernaryGoldbach.MinorArcs.Bset q, e (-(N * ((b : ℝ) / q))) =
        ((∏ p ∈ q.primeFactors, (1 - divW N p) : ℝ) : ℂ) := by
      rw [hsum, show (μ q : ℂ) = (starRingEnd ℂ) (μ q) by simp, ← map_mul, hR, Complex.conj_ofReal]
    rw [div_pow, moebius_cube, div_mul_eq_mul_div, hconj]
    have ht : ((q.totient : ℕ) : ℂ) = ((∏ p ∈ q.primeFactors, ((p : ℝ) - 1) : ℝ) : ℂ) := by
      rw [← totient_of_squarefree hsq]; push_cast; rfl
    rw [ht]
    unfold aP
    rw [prod_div_distrib, prod_pow]
    push_cast; ring
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp

theorem divW_two_of_odd {N : ℕ} (hN : Odd N) : divW N 2 = 0 := by
  rw [divW_apply, if_neg]; exact fun h => (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h)

theorem coefN_two_mul {N : ℕ} (hN : Odd N) (q : ℕ) : coefN N (2 * q) = if Odd q then coefN N q else 0 := by
  split_ifs with ho
  · have hcop : Nat.Coprime 2 q := (Nat.coprime_two_left).2 ho
    have hsq : Squarefree (2 * q) ↔ Squarefree q := by
      rw [Nat.squarefree_mul hcop]; simp [Nat.squarefree_two]
    unfold coefN
    by_cases h : Squarefree q
    · rw [if_pos (hsq.2 h), if_pos h, Nat.primeFactors_mul (by norm_num) (by rintro rfl; simp at ho),
        Nat.Prime.primeFactors Nat.prime_two]
      have h2 : 2 ∉ q.primeFactors := fun hm =>
        (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hm))
      rw [show ({2} : Finset ℕ) ∪ q.primeFactors = insert 2 q.primeFactors by rfl, prod_insert h2]
      unfold aP; rw [divW_two_of_odd hN]; norm_num
    · rw [if_neg (fun h' => h (hsq.1 h')), if_neg h]
  · have he : Even q := Nat.not_odd_iff_even.1 ho
    obtain ⟨k, rfl⟩ := he
    have hns : ¬Squarefree (2 * (k + k)) := by
      intro hs
      have h4 : 2 * 2 ∣ 2 * (k + k) := ⟨k, by ring⟩
      have := hs 2 h4
      norm_num at this
    unfold coefN; rw [if_neg hns]

/-- The pairing of even and odd moduli: `Σ_{q ∈ Qset r₀} f(q) = 2 Σ_{q ≤ r₀ odd} f(q)` when
`f(2q) = [q odd] f(q)`. -/
theorem sum_Qset_of_two_mul {f : ℕ → ℝ} (hf : ∀ q, f (2 * q) = if Odd q then f q else 0) :
    ∑ q ∈ TernaryGoldbach.MinorArcs.Qset 150000, f q = 2 * ∑ q ∈ (Icc 1 150000).filter Odd, f q := by
  open TernaryGoldbach.MinorArcs in
  have hQ : Qset 150000 = (Icc 1 300000).filter fun q => (qt q : ℝ) ≤ 2 * 150000 := by
    unfold Qset; congr 1; norm_num
  rw [hQ, ← Finset.sum_filter_add_sum_filter_not _ Odd]
  have h1 : ((Icc 1 300000).filter fun q => (TernaryGoldbach.MinorArcs.qt q : ℝ) ≤ 2 * 150000).filter Odd =
      (Icc 1 150000).filter Odd := by
    ext q
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    unfold TernaryGoldbach.MinorArcs.qt
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h2⟩, ho⟩
      rw [if_neg (Nat.not_even_iff_odd.2 ho)] at h2
      have : q ≤ 150000 := by exact_mod_cast (by push_cast at h2; linarith : (q : ℝ) ≤ 150000)
      exact ⟨⟨h1, this⟩, ho⟩
    · rintro ⟨⟨h1, h2⟩, ho⟩
      refine ⟨⟨⟨h1, by omega⟩, ?_⟩, ho⟩
      rw [if_neg (Nat.not_even_iff_odd.2 ho)]
      have : (q : ℝ) ≤ 150000 := by exact_mod_cast h2
      push_cast; linarith
  have h2 : ((Icc 1 300000).filter fun q => (TernaryGoldbach.MinorArcs.qt q : ℝ) ≤ 2 * 150000).filter
      (fun q => ¬Odd q) = (Icc 1 150000).image (fun q => 2 * q) := by
    ext q
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Nat.not_odd_iff_even]
    simp only [Finset.mem_Icc]
    unfold TernaryGoldbach.MinorArcs.qt
    constructor
    · rintro ⟨⟨⟨h1, h3⟩, -⟩, ⟨k, rfl⟩⟩
      exact ⟨k, ⟨by omega, by omega⟩, by ring⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, ⟨k, by ring⟩⟩
      rw [if_pos ⟨k, by ring⟩]
      have : (k : ℝ) ≤ 150000 := by exact_mod_cast hk2
      push_cast; linarith
  rw [h1, h2, sum_image (fun a _ b _ h => by omega)]
  simp_rw [hf]
  rw [← sum_filter]
  ring

/-! ## The product expansion and the Rankin tail -/

/-- The odd primes `≤ R`. -/
def oddPrimes (R : ℕ) : Finset ℕ := (Icc 3 R).filter Nat.Prime

theorem mem_oddPrimes {R p : ℕ} : p ∈ oddPrimes R ↔ (3 ≤ p ∧ p ≤ R) ∧ p.Prime := by
  unfold oddPrimes; rw [mem_filter, mem_Icc]

theorem sum_odd_coefN_eq (N R : ℕ) :
    ∑ q ∈ (Icc 1 R).filter Odd, coefN N q =
      ∑ t ∈ (oddPrimes R).powerset.filter (fun t => ∏ p ∈ t, p ≤ R), ∏ p ∈ t, aP N p := by
  have e1 : ∑ q ∈ (Icc 1 R).filter Odd, coefN N q =
      ∑ q ∈ ((Icc 1 R).filter Odd).filter Squarefree, ∏ p ∈ q.primeFactors, aP N p := by
    symm; rw [sum_filter]; rfl
  rw [e1]
  refine sum_bij' (fun q _ => q.primeFactors) (fun t _ => ∏ p ∈ t, p) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, mem_Icc] at hq
    obtain ⟨⟨⟨h1, h2⟩, ho⟩, hsq⟩ := hq
    rw [mem_filter, mem_powerset, Nat.prod_primeFactors_of_squarefree hsq]
    refine ⟨fun p hp => ?_, h2⟩
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpq := Nat.dvd_of_mem_primeFactors hp
    rw [mem_oddPrimes]
    refine ⟨⟨?_, (Nat.le_of_dvd (by omega) hpq).trans h2⟩, hpp⟩
    have h2p := hpp.two_le
    by_contra h3
    have : p = 2 := by omega
    subst this
    exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 hpq)
  · intro t ht
    rw [mem_filter, mem_powerset] at ht
    obtain ⟨hts, hle⟩ := ht
    have hprime : ∀ p ∈ t, p.Prime := fun p hp => (mem_oddPrimes.1 (hts hp)).2
    have hpos : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (hprime p hp).pos
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨⟨hpos, hle⟩, ?_⟩, ?_⟩
    · refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp => ?_
      have h3 := (mem_oddPrimes.1 (hts hp)).1.1
      exact (hprime p hp).odd_of_ne_two (by omega)
    · refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp => (hprime p hp).squarefree
      intro a ha b hb hab
      exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hprime a ha) (hprime b hb)).2 hab)
  · intro q hq
    simp only [mem_filter] at hq
    exact Nat.prod_primeFactors_of_squarefree hq.2
  · intro t ht
    rw [mem_filter, mem_powerset] at ht
    exact Nat.primeFactors_prod fun p hp => (mem_oddPrimes.1 (ht.1 hp)).2
  · intro q _; rfl

/-- **Rankin's trick**: the terms with `∏ t > R` are at most `R⁻¹ ∏_p (1 + p |a_p|)`. -/
theorem expansion_ge (N R : ℕ) (hR : 0 < R) :
    ∏ p ∈ oddPrimes R, (1 + aP N p) - (1 / (R : ℝ)) * ∏ p ∈ oddPrimes R, (1 + p * |aP N p|) ≤
      ∑ t ∈ (oddPrimes R).powerset.filter (fun t => ∏ p ∈ t, p ≤ R), ∏ p ∈ t, aP N p := by
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  set ps := (oddPrimes R).powerset
  have hexp : ∏ p ∈ oddPrimes R, (1 + aP N p) = ∑ t ∈ ps, ∏ p ∈ t, aP N p := prod_one_add _
  have hsplit : ∑ t ∈ ps, ∏ p ∈ t, aP N p =
      ∑ t ∈ ps.filter (fun t => ∏ p ∈ t, p ≤ R), ∏ p ∈ t, aP N p +
        ∑ t ∈ ps, (if ∏ p ∈ t, p ≤ R then 0 else ∏ p ∈ t, aP N p) := by
    rw [sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_; split_ifs <;> ring
  have htail : |∑ t ∈ ps, (if ∏ p ∈ t, p ≤ R then 0 else ∏ p ∈ t, aP N p)| ≤
      (1 / (R : ℝ)) * ∏ p ∈ oddPrimes R, (1 + p * |aP N p|) := by
    calc |∑ t ∈ ps, (if ∏ p ∈ t, p ≤ R then 0 else ∏ p ∈ t, aP N p)|
        ≤ ∑ t ∈ ps, |(if ∏ p ∈ t, p ≤ R then 0 else ∏ p ∈ t, aP N p)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ ps, (∏ p ∈ t, |aP N p|) * ((∏ p ∈ t, (p : ℝ)) / R) := by
          refine sum_le_sum fun t _ => ?_
          have h0 : 0 ≤ ∏ p ∈ t, |aP N p| := prod_nonneg fun _ _ => abs_nonneg _
          have hP0 : 0 ≤ (∏ p ∈ t, (p : ℝ)) / R :=
            div_nonneg (prod_nonneg fun _ _ => Nat.cast_nonneg _) hRr.le
          split_ifs with h
          · rw [abs_zero]; exact mul_nonneg h0 hP0
          · rw [abs_prod]
            have h1 : (1 : ℝ) ≤ (∏ p ∈ t, (p : ℝ)) / R := by
              rw [le_div_iff₀ hRr, one_mul, ← Nat.cast_prod]
              exact_mod_cast (not_le.1 h).le
            nlinarith
      _ = (1 / (R : ℝ)) * ∏ p ∈ oddPrimes R, (1 + p * |aP N p|) := by
          rw [prod_one_add, mul_sum]
          refine sum_congr rfl fun t _ => ?_
          rw [prod_mul_distrib]; field_simp
  have := le_abs_self (∑ t ∈ ps, (if ∏ p ∈ t, p ≤ R then 0 else ∏ p ∈ t, aP N p))
  rw [hexp, hsplit]
  linarith

end TernaryGoldbach.MajorArcs
