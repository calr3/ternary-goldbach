import TernaryGoldbach.Prelim.MoebiusLog

/-!
# Liouville identities (Ramaré, Acta Arith. 165 (2014), Lemmas 2.3, 2.5, 3.2)

`λ = sq ∗ μ`, `μ = μ_sq ∗ λ` (`μ_sq(u²) = μ(u)`), and `λ·χ_q = d_q ∗ λ` (`d_q(d) = μ²(d)[d ∣ q]`), all by
multiplicativity; then the partial-sum forms with weights `1/n`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.omega

namespace TernaryGoldbach.Prelim

/-! ### Squares and coprimality -/

theorem isSquare_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  refine ⟨fun hmn => ?_, fun ⟨a, b⟩ => a.mul b⟩
  rw [Nat.isSquare_iff_even_factorization] at hmn ⊢
  rw [Nat.isSquare_iff_even_factorization]
  have key : ∀ p, p.Prime → m.factorization p = 0 ∨ n.factorization p = 0 := by
    intro p hp
    by_contra! hc
    have h1 : p ∣ m := Nat.dvd_of_factorization_pos hc.1
    have h2 : p ∣ n := Nat.dvd_of_factorization_pos hc.2
    have := Nat.dvd_gcd h1 h2
    rw [h] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  constructor
  · intro p hp
    have e := hmn p hp
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply] at e
    rcases key p hp with h0 | h0
    · rw [h0]; exact ⟨0, rfl⟩
    · rw [h0, add_zero] at e; exact e
  · intro p hp
    have e := hmn p hp
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply] at e
    rcases key p hp with h0 | h0
    · rw [h0, zero_add] at e; exact e
    · rw [h0]; exact ⟨0, rfl⟩

theorem isSquare_prime_pow_iff {p k : ℕ} (hp : p.Prime) : IsSquare (p ^ k) ↔ Even k := by
  rw [Nat.isSquare_iff_even_factorization, hp.factorization_pow]
  constructor
  · intro h; simpa using h p hp
  · intro h r _
    by_cases hr : r = p
    · subst hr; simpa using h
    · rw [Finsupp.single_eq_of_ne hr]; exact ⟨0, rfl⟩

/-! ### The arithmetic functions -/

/-- `λ` as a real arithmetic function. -/
noncomputable def lam : ArithmeticFunction ℝ := ((liouville : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

theorem lam_mult : lam.IsMultiplicative := isMultiplicative_liouville.intCast

theorem lam_pp {p : ℕ} (hp : p.Prime) (k : ℕ) : lam (p ^ k) = (-1) ^ k := by
  rw [lam, intCoe_apply, liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]
  push_cast; ring

/-- Indicator of the nonzero squares. -/
noncomputable def sqI : ArithmeticFunction ℝ :=
  ⟨fun n => by classical exact if n ≠ 0 ∧ IsSquare n then 1 else 0, by simp⟩

theorem sqI_apply (n : ℕ) : sqI n = if n ≠ 0 ∧ IsSquare n then 1 else 0 := by
  simp only [sqI, coe_mk]

theorem sqI_mult : sqI.IsMultiplicative := by
  refine ⟨by simp [sqI_apply], fun {m n} hmn => ?_⟩
  by_cases hm : m = 0
  · simp [sqI_apply, hm]
  by_cases hn : n = 0
  · simp [sqI_apply, hn]
  simp only [sqI_apply, ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
    isSquare_mul_of_coprime hmn hm hn]
  split_ifs <;> simp_all

theorem sqI_pp {p : ℕ} (hp : p.Prime) (k : ℕ) : sqI (p ^ k) = if Even k then 1 else 0 := by
  have h0 : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [sqI_apply, ne_eq, h0, not_false_eq_true, true_and, isSquare_prime_pow_iff hp]

/-- `μ_sq(u²) = μ(u)`, zero off the squares. -/
noncomputable def msq : ArithmeticFunction ℝ :=
  ⟨fun n => by classical exact if n ≠ 0 ∧ IsSquare n then (μ (Nat.sqrt n) : ℝ) else 0, by simp⟩

theorem msq_apply (n : ℕ) : msq n = if n ≠ 0 ∧ IsSquare n then (μ (Nat.sqrt n) : ℝ) else 0 := by
  simp only [msq, coe_mk]

theorem msq_sq (u : ℕ) (hu : u ≠ 0) : msq (u * u) = μ u := by
  rw [msq_apply, if_pos ⟨mul_ne_zero hu hu, ⟨u, rfl⟩⟩, Nat.sqrt_eq]

theorem msq_mult : msq.IsMultiplicative := by
  refine ⟨by rw [show (1 : ℕ) = 1 * 1 from rfl, msq_sq 1 one_ne_zero]; simp, fun {m n} hmn => ?_⟩
  by_cases hm : m = 0
  · simp [msq_apply, hm]
  by_cases hn : n = 0
  · simp [msq_apply, hn]
  by_cases hs : IsSquare m ∧ IsSquare n
  · obtain ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩ := hs
    have hs0 : s ≠ 0 := by rintro rfl; simp at hm
    have ht0 : t ≠ 0 := by rintro rfl; simp at hn
    have hst : Nat.Coprime s t :=
      Nat.Coprime.coprime_mul_left (Nat.Coprime.coprime_mul_left_right hmn)
    rw [show s * s * (t * t) = (s * t) * (s * t) by ring, msq_sq _ (mul_ne_zero hs0 ht0),
      msq_sq _ hs0, msq_sq _ ht0, isMultiplicative_moebius.map_mul_of_coprime hst]
    push_cast; ring
  · have hmn' : ¬ IsSquare (m * n) := by rwa [isSquare_mul_of_coprime hmn hm hn]
    rw [msq_apply, if_neg (fun h => hmn' h.2)]
    simp only [not_and_or] at hs
    rcases hs with h | h
    · rw [msq_apply m, if_neg (fun h' => h h'.2), zero_mul]
    · rw [msq_apply n, if_neg (fun h' => h h'.2), mul_zero]

theorem msq_pp_zero {p : ℕ} (hp : p.Prime) : msq (p ^ 0) = 1 := by
  rw [pow_zero, show (1 : ℕ) = 1 * 1 from rfl, msq_sq 1 one_ne_zero]; simp

theorem msq_pp_one {p : ℕ} (hp : p.Prime) : msq (p ^ 1) = 0 := by
  rw [msq_apply, if_neg]; rintro ⟨-, h⟩
  have := (isSquare_prime_pow_iff hp).1 h
  exact Nat.not_even_one this

theorem msq_pp_two {p : ℕ} (hp : p.Prime) : msq (p ^ 2) = -1 := by
  rw [sq, msq_sq p hp.ne_zero, moebius_apply_prime hp]; simp

theorem msq_pp_ge3 {p : ℕ} (hp : p.Prime) (i : ℕ) : msq (p ^ (i + 3)) = 0 := by
  rw [msq_apply]
  by_cases he : Even (i + 3)
  · obtain ⟨r, hr⟩ := he
    have hpr : p ^ (i + 3) = p ^ r * p ^ r := by rw [hr, pow_add]
    rw [if_pos ⟨pow_ne_zero _ hp.ne_zero, (isSquare_prime_pow_iff hp).2 ⟨r, hr⟩⟩, hpr, Nat.sqrt_eq,
      moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  · rw [if_neg]; rintro ⟨-, h⟩; exact he ((isSquare_prime_pow_iff hp).1 h)

/-- `d_q(d) = μ²(d)` for `d ∣ q`, else `0`. -/
noncomputable def dq (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => by classical exact if d ≠ 0 ∧ d ∣ q then ((μ d : ℝ)) ^ 2 else 0, by simp⟩

theorem dq_apply (q d : ℕ) : dq q d = if d ≠ 0 ∧ d ∣ q then ((μ d : ℝ)) ^ 2 else 0 := by
  simp only [dq, coe_mk]

theorem dq_mult (q : ℕ) : (dq q).IsMultiplicative := by
  refine ⟨by simp [dq_apply], fun {m n} hmn => ?_⟩
  by_cases hm : m = 0
  · simp [dq_apply, hm]
  by_cases hn : n = 0
  · simp [dq_apply, hn]
  have hiff : m * n ∣ q ↔ m ∣ q ∧ n ∣ q :=
    ⟨fun h => ⟨(Dvd.intro n rfl).trans h, (Dvd.intro_left m rfl).trans h⟩,
      fun ⟨a, b⟩ => hmn.mul_dvd_of_dvd_of_dvd a b⟩
  simp only [dq_apply, ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and, hiff,
    isMultiplicative_moebius.map_mul_of_coprime hmn]
  split_ifs <;> simp_all <;> push_cast <;> ring

/-! ### Convolutions at prime powers -/

theorem conv_pp (F G : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (F * G) (p ^ k) = ∑ i ∈ range (k + 1), F (p ^ i) * G (p ^ (k - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => F a * G b), Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (by have := mem_range.1 hi; omega) hp.pos]

theorem sum_neg_one_pow (k : ℕ) : ∑ i ∈ range (k + 1), (-1 : ℝ) ^ i = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    by_cases hk : Even k
    · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.2 hk
      rw [if_pos hk, if_neg this, pow_succ, hk.neg_one_pow]; ring
    · have : Even (k + 1) := by rw [Nat.even_add_one]; exact hk
      rw [if_neg hk, if_pos this, pow_succ, (Nat.not_even_iff_odd.1 hk).neg_one_pow]; ring

/-- `λ ∗ 1 = sq`. -/
theorem lam_mul_zeta : lam * (ζ : ArithmeticFunction ℝ) = sqI := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (lam_mult.mul isMultiplicative_zeta.natCast) _ sqI_mult]
  intro p k hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sqI_pp hp]
  simp only [lam_pp hp]
  exact sum_neg_one_pow k

/-- `λ = sq ∗ μ`. -/
theorem lam_eq_sqI_mul_moebius : lam = sqI * (μ : ArithmeticFunction ℝ) := by
  rw [← lam_mul_zeta, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

/-- `μ = μ_sq ∗ λ`. -/
theorem moebius_eq_msq_mul_lam : (μ : ArithmeticFunction ℝ) = msq * lam := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ isMultiplicative_moebius.intCast _
    (msq_mult.mul lam_mult)]
  intro p k hp
  rw [conv_pp _ _ hp, intCoe_apply]
  have hl1 : lam p = -1 := by simpa using lam_pp hp 1
  rcases k with _ | _ | k
  · simp [msq_mult.map_one, lam_mult.map_one]
  · rw [sum_range_succ, sum_range_succ, sum_range_zero, msq_pp_one hp, msq_pp_zero hp,
      moebius_apply_prime_pow hp (by norm_num)]
    simp [hl1, lam_mult.map_one]
  · rw [sum_range_succ', sum_range_succ', sum_range_succ']
    rw [sum_eq_zero fun i _ => by rw [msq_pp_ge3 hp, zero_mul]]
    rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    rw [msq_pp_zero hp, msq_pp_one hp, msq_pp_two hp]
    simp only [lam_pp hp]
    have e1 : k + 1 + 1 - (0 + 1 + 1) = k := by omega
    have e2 : k + 1 + 1 - 0 = k + 2 := by omega
    rw [e1, e2, pow_add]; push_cast; ring

/-- `λ·χ_q = d_q ∗ λ`. -/
theorem lam_chiq_eq (q : ℕ) : pmul lam (chiq q) = dq q * lam := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (lam_mult.pmul (chiq_mult q)) _
    ((dq_mult q).mul lam_mult)]
  intro p k hp
  rw [conv_pp _ _ hp, pmul_apply, chiq_apply, lam_pp hp]
  rcases k with _ | k
  · simp [(dq_mult q).map_one, lam_mult.map_one, chiq_apply]
  · rw [sum_range_succ', sum_range_succ']
    have h0 : ∀ i ∈ range k, dq q (p ^ (i + 1 + 1)) * lam (p ^ (k + 1 - (i + 1 + 1))) = 0 := by
      intro i _
      have hm : (μ (p ^ (i + 1 + 1)) : ℝ) = 0 := by
        rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]; simp
      rw [dq_apply]; split_ifs <;> simp [hm]
    rw [sum_eq_zero h0, zero_add]
    have hc : Nat.Coprime (p ^ (k + 1)) q ↔ ¬ p ∣ q := by
      rw [Nat.coprime_pow_left_iff (by omega), hp.coprime_iff_not_dvd]
    have hd1 : dq q (p ^ (0 + 1)) = if p ∣ q then 1 else 0 := by
      rw [zero_add, pow_one, dq_apply, moebius_apply_prime hp]; simp [hp.ne_zero]
    have hd0 : dq q (p ^ 0) = 1 := by rw [pow_zero]; exact (dq_mult q).map_one
    have hp0 : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
    have e1 : k + 1 - (0 + 1) = k := by omega
    have e2 : k + 1 - 0 = k + 1 := by omega
    rw [hd1, hd0, lam_pp hp, lam_pp hp, e1, e2]
    simp only [ne_eq, hp0, not_false_eq_true, true_and, hc]
    by_cases hd : p ∣ q
    · rw [if_pos hd, if_neg (not_not.2 hd), pow_succ]; ring
    · rw [if_neg hd, if_pos hd, pow_succ]; ring

/-! ### Coprimality and partial sums -/

theorem chiq_mul (q a b : ℕ) : chiq q (a * b) = chiq q a * chiq q b := by
  by_cases ha : a = 0
  · simp [chiq_apply, ha]
  by_cases hb : b = 0
  · simp [chiq_apply, hb]
  simp only [chiq_apply, ne_eq, mul_eq_zero, ha, hb, or_self, not_false_eq_true, true_and,
    Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

theorem chiq_sq (q u : ℕ) : chiq q (u * u) = chiq q u := by
  rw [chiq_mul, chiq_apply]; split_ifs <;> simp

theorem chiq_le_one (q n : ℕ) : chiq q n ≤ 1 := by rw [chiq_apply]; split_ifs <;> norm_num

theorem chiq_nonneg (q n : ℕ) : 0 ≤ chiq q n := by rw [chiq_apply]; split_ifs <;> norm_num

/-- `(F χ_q) ∗ (G χ_q) = (F ∗ G) χ_q` (`χ_q` is completely multiplicative). -/
theorem pmul_chiq_mul (F G : ArithmeticFunction ℝ) (q : ℕ) :
    pmul F (chiq q) * pmul G (chiq q) = pmul (F * G) (chiq q) := by
  ext n
  simp only [pmul_apply, mul_apply, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.1 hx).1, chiq_mul]; ring

/-- `Σ_{n ≤ x} (F ∗ G)(n)/n = Σ_{a ≤ x} F(a)/a · Σ_{d ≤ x/a} G(d)/d`. -/
theorem sum_conv_div (F G : ArithmeticFunction ℝ) (x : ℝ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (F * G) n / n =
      ∑ a ∈ Icc 1 ⌊x⌋₊, F a / a * ∑ d ∈ Icc 1 ⌊x / a⌋₊, G d / d := by
  let f : ArithmeticFunction ℝ := ⟨fun n => F n / n, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => G n / n, by simp⟩
  have hfg : ∀ n, 0 < n → (f * g) n = (F * G) n / n := by
    intro n hn
    rw [mul_apply, mul_apply, sum_div]
    refine sum_congr rfl fun y hy => ?_
    have hy' := Nat.mem_divisorsAntidiagonal.1 hy
    have h1 : (y.1 : ℝ) ≠ 0 := by
      have : y.1 ≠ 0 := fun h => by rw [h, zero_mul] at hy'; omega
      exact_mod_cast this
    have h2 : (y.2 : ℝ) ≠ 0 := by
      have : y.2 ≠ 0 := fun h => by rw [h, mul_zero] at hy'; omega
      exact_mod_cast this
    have hn' : (n : ℝ) = y.1 * y.2 := by exact_mod_cast hy'.1.symm
    show F y.1 / y.1 * (G y.2 / y.2) = F y.1 * G y.2 / n
    rw [hn']; field_simp
  have h := sum_Ioc_mul_eq_sum_sum f g ⌊x⌋₊
  rw [show Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ from rfl]
  rw [← sum_congr rfl fun n hn => hfg n (mem_Ioc.1 hn).1, h]
  refine sum_congr rfl fun a _ => ?_
  rw [Nat.floor_div_natCast]; rfl

/-- Reindexing a sum over squares. -/
theorem sum_sq_reindex (f : ℕ → ℝ) (N : ℕ) :
    ∑ a ∈ Icc 1 N, (if a ≠ 0 ∧ IsSquare a then f a else 0) =
      ∑ u ∈ Icc 1 (Nat.sqrt N), f (u * u) := by
  rw [← sum_filter]
  have himg : (Icc 1 N).filter (fun a => a ≠ 0 ∧ IsSquare a) =
      (Icc 1 (Nat.sqrt N)).image (fun u => u * u) := by
    ext a
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h0, ⟨r, rfl⟩⟩
      refine ⟨r, ⟨?_, Nat.le_sqrt.2 h2⟩, rfl⟩
      rcases Nat.eq_zero_or_pos r with hr | hr
      · simp [hr] at h0
      · exact hr
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (by omega)), Nat.le_sqrt.1 h2⟩,
        mul_ne_zero (by omega) (by omega), ⟨u, rfl⟩⟩
  rw [himg, sum_image]
  intro u _ v _ h
  exact Nat.mul_self_inj.1 h

/-! ### The partial sums -/

/-- `m_q(x) = Σ_{n ≤ x, (n,q)=1} μ(n)/n`. -/
noncomputable def mqs (q : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, muq q n / n

/-- `ℓ_q(x) = Σ_{n ≤ x, (n,q)=1} λ(n)/n`. -/
noncomputable def lqs (q : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, pmul lam (chiq q) n / n

/-- `ℓ(x) = Σ_{n ≤ x} λ(n)/n`. -/
noncomputable def ls (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, lam n / n

/-- **Ramaré's Lemma 2.3**: `ℓ_q(x) = Σ_{u² ≤ x, (u,q)=1} m_q(x/u²)/u²`. -/
theorem lqs_eq (q : ℕ) (x : ℝ) :
    lqs q x = ∑ u ∈ Icc 1 (Nat.sqrt ⌊x⌋₊), chiq q u / (u * u : ℕ) * mqs q (x / (u * u : ℕ)) := by
  have e : pmul lam (chiq q) = pmul sqI (chiq q) * muq q := by
    rw [muq, pmul_chiq_mul, ← lam_eq_sqI_mul_moebius]
  rw [lqs, e, sum_conv_div]
  have e2 : ∀ a ∈ Icc 1 ⌊x⌋₊, pmul sqI (chiq q) a / a * ∑ d ∈ Icc 1 ⌊x / a⌋₊, muq q d / d =
      if a ≠ 0 ∧ IsSquare a then chiq q a / a * mqs q (x / a) else 0 := by
    intro a _
    rw [pmul_apply, sqI_apply, mqs]
    split_ifs <;> simp
  rw [sum_congr rfl e2, sum_sq_reindex (fun a => chiq q a / a * mqs q (x / a))]
  refine sum_congr rfl fun u _ => ?_
  rw [chiq_sq]

/-- **Ramaré's Lemma 3.2**: `m_q(x) = Σ_{u² ≤ x, (u,q)=1} μ(u)/u² ℓ_q(x/u²)`. -/
theorem mqs_eq (q : ℕ) (x : ℝ) :
    mqs q x = ∑ u ∈ Icc 1 (Nat.sqrt ⌊x⌋₊),
      (μ u : ℝ) * chiq q u / (u * u : ℕ) * lqs q (x / (u * u : ℕ)) := by
  have e : muq q = pmul msq (chiq q) * pmul lam (chiq q) := by
    rw [muq, pmul_chiq_mul, ← moebius_eq_msq_mul_lam]
  rw [mqs, e, sum_conv_div]
  have e2 : ∀ a ∈ Icc 1 ⌊x⌋₊, pmul msq (chiq q) a / a *
      ∑ d ∈ Icc 1 ⌊x / a⌋₊, pmul lam (chiq q) d / d =
      if a ≠ 0 ∧ IsSquare a then msq a * chiq q a / a * lqs q (x / a) else 0 := by
    intro a _
    rw [pmul_apply, msq_apply, lqs]
    split_ifs with h <;> simp [msq_apply, h]
  rw [sum_congr rfl e2, sum_sq_reindex (fun a => msq a * chiq q a / a * lqs q (x / a))]
  refine sum_congr rfl fun u hu => ?_
  rw [chiq_sq, msq_sq u (by have := (mem_Icc.1 hu).1; omega)]

/-- **Ramaré's Lemma 2.5**: `ℓ_q(x) = Σ_{d ∣ q} μ²(d)/d · ℓ(x/d)`. -/
theorem lqs_eq_dq (q : ℕ) (x : ℝ) :
    lqs q x = ∑ d ∈ Icc 1 ⌊x⌋₊, dq q d / d * ls (x / d) := by
  rw [lqs, lam_chiq_eq, sum_conv_div]; rfl

/-- `ℓ = ℓ_1`, `m = m_1`. -/
theorem lqs_one (x : ℝ) : lqs 1 x = ls x := by
  rw [lqs, ls]; refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.1 hn).1; omega
  rw [pmul_apply, chiq_apply, if_pos ⟨hn0, Nat.coprime_one_right n⟩, mul_one]

theorem mqs_one (x : ℝ) : mqs 1 x = ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n := by
  rw [mqs]; refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.1 hn).1; omega
  rw [muq, pmul_apply, chiq_apply, if_pos ⟨hn0, Nat.coprime_one_right n⟩, mul_one, intCoe_apply]

end TernaryGoldbach.Prelim
