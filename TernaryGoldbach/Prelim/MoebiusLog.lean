import TernaryGoldbach.Prelim.MertensProduct

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# [H, (2.23)], elementary form: `|∑_{n≤x, (n,q)=1} μ(n)/n · log(x/n)| ≤ q/φ(q) + 2.67`

`∑_{n ≤ N, (n,q)=1} (μ(n)/n) H(N/n) = ∑_{k ≤ N} c_q(k)/k` with `c_q(k) = ∑_{d | k, (d,q)=1} μ(d)`
multiplicative, `c_q(p^e) = [p | q]`, so the sum is over `k ≤ N` with all prime factors dividing
`q` and lies in `[0, q/φ(q)]` (Euler product over `q`-factored numbers).  With
`H(M) = log y + γ + O*(1/M)` for `y ∈ [M, M+1)`, `|∑ μ(n)/n| ≤ 1` ((2.20)) and `n⌊x/n⌋ ≥ x/2`, the
bound follows.  ([H] quotes `1.00303 q/φ(q)` from Ramaré; the weaker constant suffices here.)
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim

/-- `χ_q(n) = [n ≠ 0, gcd(n, q) = 1]`. -/
noncomputable def chiq (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ Nat.Coprime n q then 1 else 0, by simp⟩

theorem chiq_apply (q n : ℕ) : chiq q n = if n ≠ 0 ∧ Nat.Coprime n q then 1 else 0 := rfl

theorem chiq_mult (q : ℕ) : (chiq q).IsMultiplicative := by
  refine ⟨by simp [chiq_apply], fun {m n} hmn => ?_⟩
  simp only [chiq_apply]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [ne_eq, hmn0, hm, hn, not_false_eq_true, true_and, Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

/-- `μ_q = μ · χ_q`. -/
noncomputable def muq (q : ℕ) : ArithmeticFunction ℝ := pmul (μ : ArithmeticFunction ℝ) (chiq q)

theorem muq_mult (q : ℕ) : (muq q).IsMultiplicative :=
  isMultiplicative_moebius.intCast.pmul (chiq_mult q)

/-- `c_q = μ_q * ζ`, i.e. `c_q(k) = ∑_{d ∣ k, (d,q)=1} μ(d)`. -/
noncomputable def cq (q : ℕ) : ArithmeticFunction ℝ := muq q * (ζ : ArithmeticFunction ℝ)

theorem cq_mult (q : ℕ) : (cq q).IsMultiplicative :=
  (muq_mult q).mul isMultiplicative_zeta.natCast

theorem cq_prime_pow {q p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    cq q (p ^ e) = if p ∣ q then 1 else 0 := by
  rw [cq, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [sum_range_succ', sum_range_succ']
  have h0 : ∀ j ∈ range e', muq q (p ^ (j + 1 + 1)) = 0 := by
    intro j _
    simp only [muq, pmul_apply, intCoe_apply]
    rw [moebius_apply_prime_pow hp (by omega)]
    simp
  rw [sum_eq_zero h0]
  have hp0 : p ≠ 0 := hp.ne_zero
  simp only [muq, pmul_apply, intCoe_apply, zero_add, pow_zero, pow_one, moebius_apply_one,
    moebius_apply_prime hp, chiq_apply, Nat.Prime.coprime_iff_not_dvd hp]
  by_cases hd : p ∣ q <;> simp [hd, hp0]

theorem cq_cases {q k : ℕ} (hq : q ≠ 0) (hk : k ≠ 0) :
    (cq q k = 1 ∧ k ∈ Nat.factoredNumbers q.primeFactors) ∨ cq q k = 0 := by
  rw [(cq_mult q).multiplicative_factorization (cq q) hk, Finsupp.prod]
  by_cases h : ∀ p ∈ k.factorization.support, p ∣ q
  · left
    constructor
    · refine prod_eq_one fun p hp => ?_
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
      rw [cq_prime_pow hpp (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp)), if_pos (h p hp)]
    · rw [Nat.mem_factoredNumbers']
      intro p hp hpk
      have hs : p ∈ k.factorization.support := by
        rw [Nat.support_factorization]; exact Nat.mem_primeFactors.2 ⟨hp, hpk, hk⟩
      exact Nat.mem_primeFactors.2 ⟨hp, h p hs, hq⟩
  · right
    simp only [not_forall] at h
    obtain ⟨p, hp, hpq⟩ := h
    refine prod_eq_zero hp ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    rw [cq_prime_pow hpp (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp)), if_neg hpq]

/-- `n ↦ 1/n` as a monoid hom. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_inv]

/-- `∑_{k ≤ N, k q-factored} 1/k ≤ q/φ(q)`. -/
theorem sum_factored_le {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    ∑ k ∈ (Ioc 0 N).filter (· ∈ Nat.factoredNumbers q.primeFactors), (k : ℝ)⁻¹ ≤
      (q : ℝ) / Nat.totient q := by
  have hHas := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := invHom) (fun {p} hp => by
      simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, Real.norm_natCast]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) q.primeFactors).2
  have hprod : ∏ p ∈ q.primeFactors with p.Prime, (1 - invHom p)⁻¹ = (q : ℝ) / Nat.totient q := by
    rw [div_totient_eq_prod hq, filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    refine prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]
    field_simp
  rw [hprod] at hHas
  have hsub : ∑ k ∈ (Ioc 0 N).filter (· ∈ Nat.factoredNumbers q.primeFactors), (k : ℝ)⁻¹ =
      ∑ x ∈ (Ioc 0 N).subtype (· ∈ Nat.factoredNumbers q.primeFactors), invHom x := by
    rw [sum_subtype_eq_sum_filter]; rfl
  rw [hsub]
  exact sum_le_hasSum (f := fun m : Nat.factoredNumbers q.primeFactors => invHom m) _
    (fun x _ => by simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]; positivity) hHas

/-- `∑_{n ≤ N} (μ_q(n)/n) H(N/n) = ∑_{k ≤ N} c_q(k)/k ∈ [0, q/φ(q)]`. -/
theorem P_bounds {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    0 ≤ ∑ n ∈ Ioc 0 N, muq q n / n * (harmonic (N / n) : ℝ) ∧
    ∑ n ∈ Ioc 0 N, muq q n / n * (harmonic (N / n) : ℝ) ≤ q / Nat.totient q := by
  let a : ArithmeticFunction ℝ := ⟨fun n => muq q n / n, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩
  have hsum := sum_Ioc_mul_eq_sum_sum a g N
  have hR : ∑ n ∈ Ioc 0 N, a n * ∑ m ∈ Ioc 0 (N / n), g m =
      ∑ n ∈ Ioc 0 N, muq q n / n * (harmonic (N / n) : ℝ) := by
    refine sum_congr rfl fun n _ => ?_
    congr 1
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have hL : ∀ k ∈ Ioc 0 N, (a * g) k = cq q k / k := by
    intro k hk
    have hk0 : k ≠ 0 := by have := (mem_Ioc.1 hk).1; omega
    rw [mul_apply, cq, coe_mul_zeta_apply, sum_div]
    rw [← Nat.sum_divisorsAntidiagonal (fun d _ => muq q d / k)]
    refine sum_congr rfl fun x hx => ?_
    have hx' := Nat.mem_divisorsAntidiagonal.1 hx
    have h1 : (x.1 : ℝ) ≠ 0 := by
      have : x.1 ≠ 0 := fun h => hk0 (by rw [← hx'.1, h, zero_mul])
      exact_mod_cast this
    have h2 : (x.2 : ℝ) ≠ 0 := by
      have : x.2 ≠ 0 := fun h => hk0 (by rw [← hx'.1, h, mul_zero])
      exact_mod_cast this
    have hk : (k : ℝ) = x.1 * x.2 := by exact_mod_cast hx'.1.symm
    show muq q x.1 / x.1 * (x.2 : ℝ)⁻¹ = muq q x.1 / k
    rw [hk]; field_simp
  rw [← hR, ← hsum, sum_congr rfl hL]
  have hq0 : q ≠ 0 := by omega
  constructor
  · refine sum_nonneg fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (mem_Ioc.1 hk).1; omega
    rcases cq_cases hq0 hk0 with ⟨h, _⟩ | h <;> rw [h] <;> positivity
  · refine le_trans ?_ (sum_factored_le hq N)
    rw [sum_filter]
    refine sum_le_sum fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (mem_Ioc.1 hk).1; omega
    rcases cq_cases hq0 hk0 with ⟨h, hm⟩ | h
    · rw [h, if_pos hm, one_div]
    · rw [h, zero_div]; split_ifs <;> positivity

/-- `|H(M) − log y − γ| ≤ 1/M` for `M ≥ 1`, `M ≤ y < M + 1`. -/
theorem harmonic_err {M : ℕ} (hM : 1 ≤ M) {y : ℝ} (h1 : (M : ℝ) ≤ y) (h2 : y < M + 1) :
    |(harmonic M : ℝ) - Real.log y - Real.eulerMascheroniConstant| ≤ 1 / M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant M
  have hhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' M
  rw [Real.eulerMascheroniSeq] at hlo
  rw [Real.eulerMascheroniSeq', if_neg (by omega)] at hhi
  have hl1 : Real.log M ≤ Real.log y := Real.log_le_log hM0 h1
  have hl2 : Real.log y ≤ Real.log (M + 1) := Real.log_le_log (by linarith) h2.le
  have hd : Real.log ((M : ℝ) + 1) - Real.log M ≤ 1 / M := by
    have := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 1) / M) (by positivity)
    rw [Real.log_div (by positivity) hM0.ne'] at this
    have e : ((M : ℝ) + 1) / M - 1 = 1 / M := by field_simp; ring
    linarith
  rw [abs_le]; constructor <;> linarith

/-- **[H, (2.23)], elementary form**: `|∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n)| ≤ q/φ(q) + 2.67`. -/
theorem abs_sum_moebius_div_log_coprime_le {x : ℝ} (hx : 0 < x) {q : ℕ} (hq : 1 ≤ q) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0)| ≤
      q / Nat.totient q + 2.67 := by
  set N := ⌊x⌋₊ with hN
  have hφ : (0 : ℝ) ≤ (q : ℝ) / Nat.totient q := by positivity
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · rw [hN0]; simp; linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx.le
  -- `a(n) = [coprime] μ(n)/n` on `n ≥ 1`
  have ha : ∀ n ∈ Icc 1 N, (muq q n : ℝ) / n = if Nat.Coprime n q then (μ n : ℝ) / n else 0 := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.1 hn).1; omega
    simp only [muq, pmul_apply, intCoe_apply, chiq_apply, ne_eq, hn0, not_false_eq_true, true_and]
    split_ifs <;> simp
  -- `M_n = ⌊x/n⌋ = N/n`
  have hMn : ∀ n ∈ Icc 1 N, 1 ≤ N / n ∧ ((N / n : ℕ) : ℝ) ≤ x / n ∧ x / n < (N / n : ℕ) + 1 := by
    intro n hn
    have hn1 := (mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hfl : ⌊x / n⌋₊ = N / n := Nat.floor_div_natCast x n
    refine ⟨Nat.div_pos (mem_Icc.1 hn).2 hn1, ?_, ?_⟩
    · rw [← hfl]; exact Nat.floor_le (by positivity)
    · rw [← hfl]; exact Nat.lt_floor_add_one _
  -- decomposition
  set E : ℕ → ℝ := fun n => (harmonic (N / n) : ℝ) - Real.log (x / n) -
    Real.eulerMascheroniConstant with hE
  have hdec : ∑ n ∈ Icc 1 N, (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0) =
      ∑ n ∈ Icc 1 N, muq q n / n * (harmonic (N / n) : ℝ) -
        Real.eulerMascheroniConstant * ∑ n ∈ Icc 1 N, (if Nat.Coprime n q then (μ n : ℝ) / n else 0) -
        ∑ n ∈ Icc 1 N, muq q n / n * E n := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [← ha n hn]
    simp only [hE]
    have : (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0) =
        muq q n / n * Real.log (x / n) := by
      rw [ha n hn]; split_ifs <;> simp
    rw [this]; ring
  rw [hdec]
  have hP := P_bounds hq N
  rw [show Icc 1 N = Ioc 0 N from rfl]
  have hm := abs_sum_moebius_div_coprime_le_one x hq
  rw [← hN, show Icc 1 N = Ioc 0 N from rfl] at hm
  -- the error sum
  have hErr : |∑ n ∈ Ioc 0 N, muq q n / n * E n| ≤ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ n ∈ Ioc 0 N, |muq q n / n * E n| ≤ 2 / x := by
      intro n hn
      have hn' : n ∈ Icc 1 N := hn
      obtain ⟨hM1, hMl, hMu⟩ := hMn n hn'
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn').1
      have hM0 : (0 : ℝ) < ((N / n : ℕ) : ℝ) := by exact_mod_cast hM1
      have hEb := harmonic_err hM1 hMl hMu
      have hmu : |muq q n / n| ≤ 1 / n := by
        rw [ha n hn']
        split_ifs
        · rw [abs_div, abs_of_pos hn0]
          refine div_le_div_of_nonneg_right ?_ hn0.le
          have := abs_moebius_le_one (n := n)
          exact_mod_cast this
        · simp
      -- `n ⌊x/n⌋ ≥ x/2`
      have hnM : x / 2 ≤ n * ((N / n : ℕ) : ℝ) := by
        have h1 : n * ((N / n : ℕ) : ℝ) ≥ n := by nlinarith [show (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) by exact_mod_cast hM1]
        have h2 : n * ((N / n : ℕ) : ℝ) > x - n := by
          have := mul_lt_mul_of_pos_left hMu hn0
          rw [mul_div_cancel₀ _ hn0.ne'] at this; linarith
        linarith
      rw [abs_mul]
      calc |muq q n / n| * |E n| ≤ 1 / n * (1 / ((N / n : ℕ) : ℝ)) :=
            mul_le_mul hmu hEb (abs_nonneg _) (by positivity)
        _ = 1 / (n * ((N / n : ℕ) : ℝ)) := by field_simp
        _ ≤ 1 / (x / 2) := one_div_le_one_div_of_le (by positivity) hnM
        _ = 2 / x := by field_simp
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]
    rw [mul_div_assoc', div_le_iff₀ hx]; linarith
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    have := Real.one_half_lt_eulerMascheroniConstant; linarith
  have hγm : |Real.eulerMascheroniConstant * ∑ n ∈ Ioc 0 N,
      (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤ 2 / 3 := by
    rw [abs_mul, abs_of_nonneg hγ0]
    calc _ ≤ Real.eulerMascheroniConstant * 1 := mul_le_mul_of_nonneg_left hm hγ0
      _ ≤ 2 / 3 := by linarith
  rw [abs_le] at hErr hγm ⊢
  constructor <;> linarith [hP.1, hP.2, hErr.1, hErr.2, hγm.1, hγm.2]

end TernaryGoldbach.Prelim
