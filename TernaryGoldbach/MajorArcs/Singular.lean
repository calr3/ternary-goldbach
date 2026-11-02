import TernaryGoldbach.MinorArcs.Montgomery
import TernaryGoldbach.MajorArcs.SumMuPhi
import TernaryGoldbach.MajorArcs.Cor713
import TernaryGoldbach.Prelim.MertensProduct

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

theorem sum_odd_sqfree_eq (g : ℕ → ℝ) (R : ℕ) :
    ∑ q ∈ (Icc 1 R).filter Odd, (if Squarefree q then ∏ p ∈ q.primeFactors, g p else 0) =
      ∑ t ∈ (oddPrimes R).powerset.filter (fun t => ∏ p ∈ t, p ≤ R), ∏ p ∈ t, g p := by
  have e1 : ∑ q ∈ (Icc 1 R).filter Odd, (if Squarefree q then ∏ p ∈ q.primeFactors, g p else 0) =
      ∑ q ∈ ((Icc 1 R).filter Odd).filter Squarefree, ∏ p ∈ q.primeFactors, g p := by
    symm; rw [sum_filter]
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

theorem sum_odd_coefN_eq (N R : ℕ) :
    ∑ q ∈ (Icc 1 R).filter Odd, coefN N q =
      ∑ t ∈ (oddPrimes R).powerset.filter (fun t => ∏ p ∈ t, p ≤ R), ∏ p ∈ t, aP N p :=
  sum_odd_sqfree_eq (aP N) R

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

/-! ## Numerics: `Σ_{q ≤ r₀ odd} ∏_{p∣q} a_p(N) ≥ 0.657` -/

theorem oddPrimes_200 : oddPrimes 200 = {3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199} := by
  ext p
  rw [mem_oddPrimes]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    interval_cases p <;> revert hp <;> norm_num
  · rintro (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> norm_num

theorem prod_200_lower : (0.6606 : ℝ) ≤ ∏ p ∈ oddPrimes 200, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [oddPrimes_200]; norm_num

theorem prod_200_upper : ∏ p ∈ oddPrimes 200, (1 + 1 / ((p : ℝ) - 1) ^ 2) ≤ 1.4122 := by
  rw [oddPrimes_200]; norm_num

theorem aP_cases {N p : ℕ} (hp : 3 ≤ p) :
    aP N p = -(1 / ((p : ℝ) - 1) ^ 2) ∨ (0 ≤ aP N p ∧ aP N p ≤ 1 / ((p : ℝ) - 1) ^ 2) := by
  have hp1 : (2 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  unfold aP; rw [divW_apply]
  split_ifs with h
  · left; field_simp; ring
  · right
    rw [sub_zero]
    constructor
    · positivity
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

theorem aP_ge {N p : ℕ} (hp : 3 ≤ p) : -(1 / ((p : ℝ) - 1) ^ 2) ≤ aP N p := by
  rcases aP_cases (N := N) hp with h | ⟨h0, -⟩
  · rw [h]
  · have : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith

theorem abs_aP_le {N p : ℕ} (hp : 3 ≤ p) : |aP N p| ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  rcases aP_cases (N := N) hp with h | ⟨h0, h1⟩
  · rw [h, abs_neg, abs_of_nonneg (by positivity)]
  · rw [abs_of_nonneg h0]; exact h1

theorem prod_one_sub_ge {s : Finset ℕ} {x : ℕ → ℝ} (h0 : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∀ i ∈ s, x i ≤ 1) : 1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have ha0 := h0 a (mem_insert_self a s)
    have ha1 := h1 a (mem_insert_self a s)
    have hS : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 ha1)]

theorem sum_rest_le {R : ℕ} (hR : 200 ≤ R) :
    ∑ p ∈ oddPrimes R \ oddPrimes 200, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 199 := by
  set rest := oddPrimes R \ oddPrimes 200
  have hmem : ∀ p ∈ rest, 201 ≤ p ∧ p ≤ R := by
    intro p hp
    rw [mem_sdiff, mem_oddPrimes, mem_oddPrimes] at hp
    obtain ⟨⟨⟨h3, hR'⟩, hpr⟩, hn⟩ := hp
    refine ⟨?_, hR'⟩
    by_contra h
    exact hn ⟨⟨h3, by omega⟩, hpr⟩
  set g : ℕ → ℝ := fun m => 1 / ((m : ℝ) * ((m : ℝ) - 1)) with hg
  have hle : ∀ p ∈ rest, 1 / ((p : ℝ) - 1) ^ 2 ≤ g (p - 1) := by
    intro p hp
    obtain ⟨h1, -⟩ := hmem p hp
    have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
    simp only [hg, hc]
    have hp' : (201 : ℝ) ≤ p := by exact_mod_cast h1
    rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]; nlinarith
  have hinj : ∀ a ∈ rest, ∀ b ∈ rest, a - 1 = b - 1 → a = b := by
    intro a ha b hb hab
    have := (hmem a ha).1; have := (hmem b hb).1
    omega
  have hsub : rest.image (· - 1) ⊆ Ioc 199 R := by
    intro m hm
    rw [mem_image] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    obtain ⟨h1, h2⟩ := hmem p hp
    rw [mem_Ioc]; constructor <;> omega
  have hg0 : ∀ m ∈ Ioc 199 R, 0 ≤ g m := by
    intro m hm
    rw [mem_Ioc] at hm
    have : (200 : ℝ) ≤ m := by exact_mod_cast hm.1
    simp only [hg]
    have : 0 < (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
    positivity
  have htel : ∑ m ∈ Ioc 199 R, g m ≤ 1 / 199 - 1 / R :=
    TernaryGoldbach.Prelim.sum_inv_mul_pred_le (by norm_num) (by omega)
  have hR0 : (0 : ℝ) ≤ 1 / R := by positivity
  calc ∑ p ∈ rest, 1 / ((p : ℝ) - 1) ^ 2 ≤ ∑ p ∈ rest, g (p - 1) := sum_le_sum hle
    _ = ∑ m ∈ rest.image (· - 1), g m := (sum_image hinj).symm
    _ ≤ ∑ m ∈ Ioc 199 R, g m := sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => hg0 m hm
    _ ≤ 1 / 199 := by linarith

theorem oddPrimes_200_subset {R : ℕ} (hR : 200 ≤ R) : oddPrimes 200 ⊆ oddPrimes R := by
  intro p hp; rw [mem_oddPrimes] at hp ⊢; exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩

theorem three_le_of_mem {R p : ℕ} (hp : p ∈ oddPrimes R) : 3 ≤ p := (mem_oddPrimes.1 hp).1.1

theorem two_le_sub_one {p : ℕ} (hp : 3 ≤ p) : (2 : ℝ) ≤ (p : ℝ) - 1 := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

theorem prod_lower_bound {R : ℕ} (hR : 200 ≤ R) :
    0.6606 * (1 - 1 / 199) ≤ ∏ p ∈ oddPrimes R, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [← prod_sdiff (oddPrimes_200_subset hR)]
  have hx0 : ∀ p ∈ oddPrimes R \ oddPrimes 200, (0:ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := fun p _ => by
    positivity
  have hx1 : ∀ p ∈ oddPrimes R \ oddPrimes 200, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
    intro p hp
    have h2 := two_le_sub_one (three_le_of_mem (mem_sdiff.1 hp).1)
    rw [div_le_one (by positivity)]; nlinarith
  have h1 := prod_one_sub_ge hx0 hx1
  have h2 := sum_rest_le hR
  have h3 := prod_200_lower
  have hA : 1 - 1 / 199 ≤ ∏ p ∈ oddPrimes R \ oddPrimes 200, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    linarith
  calc (0.6606 : ℝ) * (1 - 1 / 199) = (1 - 1 / 199) * 0.6606 := by ring
    _ ≤ (∏ p ∈ oddPrimes R \ oddPrimes 200, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
          ∏ p ∈ oddPrimes 200, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
        mul_le_mul hA h3 (by norm_num) (by linarith)

theorem prod_upper_bound {R : ℕ} (hR : 200 ≤ R) :
    ∏ p ∈ oddPrimes R, (1 + 1 / ((p : ℝ) - 1) ^ 2) ≤ 1.4122 * Real.exp (1 / 199) := by
  rw [← prod_sdiff (oddPrimes_200_subset hR)]
  have hrest : ∏ p ∈ oddPrimes R \ oddPrimes 200, (1 + 1 / ((p : ℝ) - 1) ^ 2) ≤ Real.exp (1 / 199) := by
    calc ∏ p ∈ oddPrimes R \ oddPrimes 200, (1 + 1 / ((p : ℝ) - 1) ^ 2)
        ≤ ∏ p ∈ oddPrimes R \ oddPrimes 200, Real.exp (1 / ((p : ℝ) - 1) ^ 2) := by
          refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => ?_)
          have := Real.add_one_le_exp (1 / ((p : ℝ) - 1) ^ 2); linarith
      _ = Real.exp (∑ p ∈ oddPrimes R \ oddPrimes 200, 1 / ((p : ℝ) - 1) ^ 2) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (1 / 199) := Real.exp_le_exp.2 (sum_rest_le hR)
  calc (∏ p ∈ oddPrimes R \ oddPrimes 200, (1 + 1 / ((p : ℝ) - 1) ^ 2)) *
        ∏ p ∈ oddPrimes 200, (1 + 1 / ((p : ℝ) - 1) ^ 2)
      ≤ Real.exp (1 / 199) * 1.4122 := mul_le_mul hrest prod_200_upper (by positivity) (by positivity)
    _ = 1.4122 * Real.exp (1 / 199) := by ring

theorem one_le_prod_of_one_le {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ i ∈ s, (1 : ℝ) := by simp
    _ ≤ ∏ i ∈ s, f i := Finset.prod_le_prod₀ (fun _ _ => by norm_num) h

/-- `∏_{3 ≤ p ≤ r₀} p/(p − 1) ≤ 15.5` (from [RS62, Thm 15], `Prelim.F_all`, at `150001`). -/
theorem prod_p_div_le : ∏ p ∈ oddPrimes 150000, ((p : ℝ) / (p - 1)) ≤ 15.5 := by
  have hpr : Nat.Prime 150001 := by norm_num
  have hM : ∏ p ∈ (Icc 1 150001).filter Nat.Prime, ((p : ℝ) / (p - 1)) <
      Real.exp Real.eulerMascheroniConstant *
          Real.log (∑ p ∈ (Icc 1 150001).filter Nat.Prime, Real.log p) +
        2.50637 / Real.log (∑ p ∈ (Icc 1 150001).filter Nat.Prime, Real.log p) :=
    TernaryGoldbach.Prelim.F_all hpr (by norm_num)
  set A := (Icc 1 150001).filter Nat.Prime with hA
  set θ := ∑ p ∈ A, Real.log p with hθ
  have hsub : insert 2 (oddPrimes 150000) ⊆ A := by
    intro p hp
    rw [mem_insert] at hp
    rw [hA, mem_filter, mem_Icc]
    rcases hp with rfl | hp
    · exact ⟨⟨by norm_num, by norm_num⟩, Nat.prime_two⟩
    · rw [mem_oddPrimes] at hp; exact ⟨⟨by omega, by omega⟩, hp.2⟩
  have h2 : 2 ∉ oddPrimes 150000 := fun h => by have := three_le_of_mem h; omega
  have hone : ∀ p ∈ A, (1 : ℝ) ≤ (p : ℝ) / (p - 1) := by
    intro p hp
    rw [hA, mem_filter] at hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    rw [le_div_iff₀ (by linarith)]; linarith
  have hsplit := Finset.prod_sdiff (f := fun p : ℕ => (p : ℝ) / (p - 1)) hsub
  have hrest : 1 ≤ ∏ p ∈ A \ insert 2 (oddPrimes 150000), (p : ℝ) / (p - 1) :=
    one_le_prod_of_one_le fun p hp => hone p (mem_sdiff.1 hp).1
  rw [prod_insert h2] at hsplit
  have hodd0 : 0 ≤ ∏ p ∈ oddPrimes 150000, (p : ℝ) / (p - 1) :=
    prod_nonneg fun p hp => by
      have := two_le_sub_one (three_le_of_mem hp); positivity
  have he2 : ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = 2 := by norm_num
  have hle : 2 * ∏ p ∈ oddPrimes 150000, (p : ℝ) / (p - 1) ≤ ∏ p ∈ A, (p : ℝ) / (p - 1) := by
    calc 2 * ∏ p ∈ oddPrimes 150000, (p : ℝ) / (p - 1)
        = 1 * (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) * ∏ p ∈ oddPrimes 150000, (p : ℝ) / (p - 1)) := by
          rw [he2]; ring
      _ ≤ (∏ p ∈ A \ insert 2 (oddPrimes 150000), (p : ℝ) / (p - 1)) *
            (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) * ∏ p ∈ oddPrimes 150000, (p : ℝ) / (p - 1)) :=
          mul_le_mul_of_nonneg_right hrest (by rw [he2]; positivity)
      _ = ∏ p ∈ A, (p : ℝ) / (p - 1) := hsplit
  -- bounds on `log θ`
  have hlog : Real.log 150001 ≤ 12.62 :=
    (Real.log_le_log (by norm_num) (by norm_num)).trans TernaryGoldbach.MajorArcs.log_3e5_le
  have hlog8 : 8 ≤ Real.log 150001 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    calc Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 8 := by gcongr
      _ ≤ 150001 := by norm_num
  have hθlo : 8 ≤ θ := by
    have h150 : (150001 : ℕ) ∈ A := by rw [hA, mem_filter, mem_Icc]; exact ⟨⟨by norm_num, le_rfl⟩, hpr⟩
    have := single_le_sum (f := fun p : ℕ => Real.log p) (fun p hp => Real.log_natCast_nonneg p) h150
    push_cast at this; linarith
  have hθhi : θ ≤ 150001 * 12.62 := by
    calc θ ≤ ∑ p ∈ A, (12.62 : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          rw [hA, mem_filter, mem_Icc] at hp
          have : (p : ℝ) ≤ 150001 := by exact_mod_cast hp.1.2
          exact (Real.log_le_log (by exact_mod_cast hp.2.pos) this).trans hlog
      _ = A.card * 12.62 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 150001 * 12.62 := by
          gcongr
          have : A.card ≤ 150001 := (card_filter_le _ _).trans (by simp)
          exact_mod_cast this
  have hθpos : 0 < θ := by linarith
  have ht_lo : 2 ≤ Real.log θ := by
    rw [Real.le_log_iff_exp_le hθpos]
    have := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 2 := by gcongr
      _ ≤ 8 := by norm_num
      _ ≤ θ := hθlo
  have ht_hi : Real.log θ ≤ 15.22 := by
    rw [Real.log_le_iff_le_exp hθpos]
    have h := TernaryGoldbach.MajorArcs.exp_split_ge 15 (u := 0.22) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hG := TernaryGoldbach.Prelim.exp_gamma_lt
  have hf : Real.exp Real.eulerMascheroniConstant * Real.log θ + 2.50637 / Real.log θ ≤ 30.94 := by
    have h1 : Real.exp Real.eulerMascheroniConstant * Real.log θ ≤ 1.95 * 15.22 :=
      mul_le_mul hG.le ht_hi (by linarith) (by norm_num)
    have h2 : 2.50637 / Real.log θ ≤ 2.50637 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht_lo
    linarith
  have hM' : ∏ p ∈ A, (p : ℝ) / (p - 1) < 30.94 := lt_of_lt_of_le hM hf
  linarith

theorem exp_inv199_le : Real.exp (1 / 199) ≤ 1.006 := by
  have h := Real.add_one_le_exp (-(1 / 199))
  have hp := Real.exp_pos (1 / 199)
  have : Real.exp (-(1 / 199)) * Real.exp (1 / 199) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

theorem prod_one_add_p_abs_le (N : ℕ) :
    ∏ p ∈ oddPrimes 150000, (1 + p * |aP N p|) ≤ 22.1 := by
  have hpt : ∀ p ∈ oddPrimes 150000, 1 + p * |aP N p| ≤ ((p : ℝ) / (p - 1)) * (1 + 1 / ((p : ℝ) - 1) ^ 2) := by
    intro p hp
    have h3 := three_le_of_mem hp
    have h2 := two_le_sub_one h3
    have ha := abs_aP_le (N := N) h3
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    calc 1 + p * |aP N p| ≤ 1 + p * (1 / ((p : ℝ) - 1) ^ 2) := by gcongr
      _ ≤ ((p : ℝ) / (p - 1)) * (1 + 1 / ((p : ℝ) - 1) ^ 2) := by
          rw [← sub_nonneg]
          have e : ((p : ℝ) / (p - 1)) * (1 + 1 / ((p : ℝ) - 1) ^ 2) - (1 + p * (1 / ((p : ℝ) - 1) ^ 2)) =
              1 / ((p : ℝ) - 1) ^ 3 := by
            have : (p : ℝ) - 1 ≠ 0 := by linarith
            field_simp; ring
          rw [e]; positivity
  have h1 : ∏ p ∈ oddPrimes 150000, (1 + p * |aP N p|) ≤
      ∏ p ∈ oddPrimes 150000, (((p : ℝ) / (p - 1)) * (1 + 1 / ((p : ℝ) - 1) ^ 2)) :=
    Finset.prod_le_prod₀ (fun p _ => by positivity) hpt
  rw [prod_mul_distrib] at h1
  have hA := prod_p_div_le
  have hB := prod_upper_bound (R := 150000) (by norm_num)
  have hE := exp_inv199_le
  have hB' : ∏ p ∈ oddPrimes 150000, (1 + 1 / ((p : ℝ) - 1) ^ 2) ≤ 1.4122 * 1.006 :=
    hB.trans (by gcongr)
  have hA0 : 0 ≤ ∏ p ∈ oddPrimes 150000, ((p : ℝ) / (p - 1)) :=
    prod_nonneg fun p hp => by have := two_le_sub_one (three_le_of_mem hp); positivity
  have := mul_le_mul hA hB' (prod_nonneg fun p _ => by positivity) (by norm_num)
  linarith

/-- **The singular series over odd moduli**: `Σ_{q ≤ r₀ odd} ∏_{p∣q} a_p(N) ≥ 0.657`. -/
theorem sum_odd_coefN_ge (N : ℕ) : 0.657 ≤ ∑ q ∈ (Icc 1 150000).filter Odd, coefN N q := by
  rw [sum_odd_coefN_eq]
  have hexp := expansion_ge N 150000 (by norm_num)
  have hlow : ∏ p ∈ oddPrimes 150000, (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
      ∏ p ∈ oddPrimes 150000, (1 + aP N p) := by
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have h2 := two_le_sub_one (three_le_of_mem hp)
      have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      linarith
    · have := aP_ge (N := N) (three_le_of_mem hp); linarith
  have hlb := prod_lower_bound (R := 150000) (by norm_num)
  have hub := prod_one_add_p_abs_le N
  have : (1 / (150000 : ℝ)) * ∏ p ∈ oddPrimes 150000, (1 + p * |aP N p|) ≤ (1 / 150000) * 22.1 :=
    mul_le_mul_of_nonneg_left hub (by norm_num)
  push_cast at hexp
  linarith

/-- **The singular series over `𝔐_{8,r₀}`**: `Σ_{q ∈ Qset r₀} (μ(q)/φ(q))³ c_q(N) ≥ 1.314` for odd `N`. -/
theorem sum_Qset_coefN_ge {N : ℕ} (hN : Odd N) :
    1.314 ≤ ∑ q ∈ TernaryGoldbach.MinorArcs.Qset 150000, coefN N q := by
  rw [sum_Qset_of_two_mul (coefN_two_mul hN)]
  have := sum_odd_coefN_ge N
  linarith

/-! ## `Σ μ²/φ²` -/

/-- `μ²(q)/φ(q)²`. -/
noncomputable def mPhi2 (q : ℕ) : ℝ := (if Squarefree q then (1 : ℝ) else 0) / (q.totient : ℝ) ^ 2

theorem mPhi2_eq (q : ℕ) :
    mPhi2 q = if Squarefree q then ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) - 1) ^ 2 else 0 := by
  unfold mPhi2
  split_ifs with h
  · rw [totient_of_squarefree h, ← prod_pow, one_div, ← prod_inv_distrib]
    refine prod_congr rfl fun p _ => by rw [one_div]
  · simp

theorem mPhi2_two_mul (q : ℕ) : mPhi2 (2 * q) = if Odd q then mPhi2 q else 0 := by
  split_ifs with ho
  · have hcop : Nat.Coprime 2 q := (Nat.coprime_two_left).2 ho
    have hsq : Squarefree (2 * q) ↔ Squarefree q := by
      rw [Nat.squarefree_mul hcop]; simp [Nat.squarefree_two]
    unfold mPhi2
    rw [Nat.totient_mul hcop, Nat.totient_two, one_mul]
    simp only [hsq]
  · have he : Even q := Nat.not_odd_iff_even.1 ho
    obtain ⟨k, rfl⟩ := he
    have hns : ¬Squarefree (2 * (k + k)) := by
      intro hs
      have h4 : 2 * 2 ∣ 2 * (k + k) := ⟨k, by ring⟩
      have := hs 2 h4
      norm_num at this
    unfold mPhi2; rw [if_neg hns, zero_div]

theorem sum_Qset_mPhi2_le : ∑ q ∈ TernaryGoldbach.MinorArcs.Qset 150000, mPhi2 q ≤ 2.85 := by
  rw [sum_Qset_of_two_mul mPhi2_two_mul]
  have e : ∑ q ∈ (Icc 1 150000).filter Odd, mPhi2 q =
      ∑ t ∈ (oddPrimes 150000).powerset.filter (fun t => ∏ p ∈ t, p ≤ 150000),
        ∏ p ∈ t, 1 / ((p : ℝ) - 1) ^ 2 := by
    rw [← sum_odd_sqfree_eq]; exact sum_congr rfl fun q _ => mPhi2_eq q
  rw [e]
  have h1 : ∑ t ∈ (oddPrimes 150000).powerset.filter (fun t => ∏ p ∈ t, p ≤ 150000),
      ∏ p ∈ t, 1 / ((p : ℝ) - 1) ^ 2 ≤ ∏ p ∈ oddPrimes 150000, (1 + 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [prod_one_add]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ =>
      prod_nonneg fun p _ => by positivity
  have hB := prod_upper_bound (R := 150000) (by norm_num)
  have hE := exp_inv199_le
  have : 1.4122 * Real.exp (1 / 199) ≤ 1.4122 * 1.006 := by gcongr
  linarith

end TernaryGoldbach.MajorArcs
