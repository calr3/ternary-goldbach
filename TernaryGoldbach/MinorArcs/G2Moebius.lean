import TernaryGoldbach.MinorArcs.T2Defs
import TernaryGoldbach.Prelim.Liouville

/-!
# `g₂` via Möbius inversion of the coprimality condition ([H, (5.20)])

With `f(r) = μ(r)/σ(r)` for odd `r` (`0` for even `r`) and `S_d(M) = ∑_{r ≤ M, (r, d) = 1} f(r)`:

`g₂(x) = ∑_{d ≤ x} μ(d) f(d)² S_d(⌊x⌋/d)²` (`g2_eq_sum_moebius`).
-/

open Real Finset
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs

/-- `f(r) = μ(r)/σ(r)` for odd `r`, `0` for even `r`. -/
noncomputable def fo (r : ℕ) : ℝ := if Odd r then (μ r : ℝ) / (σ 1 r : ℝ) else 0

/-- `S_d(M) = ∑_{r ≤ M, (r, d) = 1} f(r)`. -/
noncomputable def Sd (d M : ℕ) : ℝ := ∑ r ∈ Icc 1 M, if Nat.Coprime r d then fo r else 0

theorem g2_sum_moebius_divisors (n : ℕ) : ∑ d ∈ n.divisors, (μ d : ℝ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have : ((∑ d ∈ n.divisors, μ d : ℤ) : ℝ) = ((if n = 1 then 1 else 0 : ℤ) : ℝ) := by rw [h]
  push_cast at this; rw [this]

/-- The summand of `g₂` in terms of `f`. -/
theorem g2_term_eq (r₁ r₂ : ℕ) :
    (if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0) =
      if Nat.Coprime r₁ r₂ then fo r₁ * fo r₂ else 0 := by
  unfold fo
  by_cases hc : Nat.Coprime r₁ r₂
  · by_cases h₁ : Odd r₁ <;> by_cases h₂ : Odd r₂ <;>
      simp [hc, h₁, h₂, Nat.odd_mul, div_mul_div_comm]
  · simp [hc]

/-- **`g₂(x) = ∑_{d ≤ N} μ(d) (∑_{r ≤ N, d ∣ r} f(r))²`**, `N = ⌊x⌋`. -/
theorem g2_eq_sum_dvd (x : ℝ) :
    g2 x = ∑ d ∈ Icc 1 ⌊x⌋₊, (μ d : ℝ) * (∑ r ∈ (Icc 1 ⌊x⌋₊).filter (d ∣ ·), fo r) ^ 2 := by
  set N := ⌊x⌋₊
  unfold g2
  simp_rw [g2_term_eq]
  -- `[coprime] = ∑_{d ∣ gcd} μ(d)`
  have hcop : ∀ r₁ r₂ : ℕ, (if Nat.Coprime r₁ r₂ then fo r₁ * fo r₂ else 0) =
      ∑ d ∈ (Nat.gcd r₁ r₂).divisors, (μ d : ℝ) * (fo r₁ * fo r₂) := by
    intro r₁ r₂
    rw [← sum_mul, g2_sum_moebius_divisors]
    simp only [Nat.Coprime]; split_ifs <;> simp
  simp_rw [hcop]
  -- swap: `∑_{r₁, r₂} ∑_{d ∣ (r₁, r₂)} = ∑_d ∑_{d ∣ r₁} ∑_{d ∣ r₂}`
  have hswap : ∀ r₁ ∈ Icc 1 N, ∀ r₂ ∈ Icc 1 N,
      ∑ d ∈ (Nat.gcd r₁ r₂).divisors, (μ d : ℝ) * (fo r₁ * fo r₂) =
        ∑ d ∈ Icc 1 N, if d ∣ r₁ ∧ d ∣ r₂ then (μ d : ℝ) * (fo r₁ * fo r₂) else 0 := by
    intro r₁ hr₁ r₂ hr₂
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc, Nat.dvd_gcd_iff]
    have h1 := (mem_Icc.1 hr₁).1; have h2 := (mem_Icc.1 hr₁).2
    constructor
    · rintro ⟨⟨hd1, hd2⟩, hg⟩
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd1 (by omega)
      exact ⟨⟨hpos, (Nat.le_of_dvd (by omega) hd1).trans h2⟩, hd1, hd2⟩
    · rintro ⟨-, hd1, hd2⟩
      exact ⟨⟨hd1, hd2⟩, (Nat.gcd_pos_of_pos_left _ (by omega)).ne'⟩
  rw [sum_congr rfl fun r₁ hr₁ => sum_congr rfl fun r₂ hr₂ => hswap r₁ hr₁ r₂ hr₂]
  have hin : ∀ r₁ ∈ Icc 1 N, (∑ r₂ ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
      if d ∣ r₁ ∧ d ∣ r₂ then (μ d : ℝ) * (fo r₁ * fo r₂) else 0) =
      ∑ d ∈ Icc 1 N, ∑ r₂ ∈ Icc 1 N, if d ∣ r₁ ∧ d ∣ r₂ then (μ d : ℝ) * (fo r₁ * fo r₂) else 0 :=
    fun _ _ => sum_comm
  rw [sum_congr rfl hin, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_filter, sq, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun r₁ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun r₂ _ => ?_
  by_cases h1 : d ∣ r₁ <;> by_cases h2 : d ∣ r₂ <;> simp [h1, h2]

theorem fo_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) : fo (a * b) = fo a * fo b := by
  unfold fo
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h]
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [ha, hb, Nat.odd_mul]
  push_cast; rw [div_mul_div_comm]

theorem fo_mul_eq_zero {d r : ℕ} (h : ¬Nat.Coprime d r) : fo (d * r) = 0 := by
  unfold fo
  have : μ (d * r) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs =>
    h (Nat.squarefree_mul_iff.1 hs).1
  simp [this]

/-- `∑_{r ≤ N, d ∣ r} f(r) = f(d) S_d(N/d)` for squarefree `d`. -/
theorem sum_dvd_fo {d N : ℕ} (hd0 : 1 ≤ d) :
    ∑ r ∈ (Icc 1 N).filter (d ∣ ·), fo r = fo d * Sd d (N / d) := by
  have himg : (Icc 1 N).filter (d ∣ ·) = (Icc 1 (N / d)).image (d * ·) := by
    ext r
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp at h1
        · exact hk
      · rw [Nat.le_div_iff_mul_le hd0]; rw [mul_comm]; exact h2
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩, dvd_mul_right d k⟩
      rw [Nat.le_div_iff_mul_le hd0] at hk2; rw [mul_comm]; exact hk2
  rw [himg, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h), Sd, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  by_cases hc : Nat.Coprime r d
  · rw [if_pos hc, fo_mul_of_coprime hc.symm]
  · rw [if_neg hc, mul_zero, fo_mul_eq_zero (fun h => hc h.symm)]

/-- **[H, (5.20)]**: `g₂(x) = ∑_{d ≤ N} μ(d) f(d)² S_d(N/d)²`, `N = ⌊x⌋`. -/
theorem g2_eq_sum_moebius (x : ℝ) :
    g2 x = ∑ d ∈ Icc 1 ⌊x⌋₊, (μ d : ℝ) * fo d ^ 2 * Sd d (⌊x⌋₊ / d) ^ 2 := by
  rw [g2_eq_sum_dvd]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_dvd_fo (mem_Icc.1 hd).1]; ring

/-- `|g₂(x)| ≤ ∑_{d ≤ N} f(d)² S_d(N/d)²`. -/
theorem abs_g2_le_sum (x : ℝ) :
    |g2 x| ≤ ∑ d ∈ Icc 1 ⌊x⌋₊, fo d ^ 2 * Sd d (⌊x⌋₊ / d) ^ 2 := by
  rw [g2_eq_sum_moebius]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (fo d)),
    abs_of_nonneg (sq_nonneg (Sd d (⌊x⌋₊ / d))), mul_assoc]
  have : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc |(μ d : ℝ)| * (fo d ^ 2 * Sd d (⌊x⌋₊ / d) ^ 2) ≤ 1 * (fo d ^ 2 * Sd d (⌊x⌋₊ / d) ^ 2) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := one_mul _

/-! ### `f·1_{(·,d)=1} = H_d ∗ (μ/id)` with `H_d = f·1_{(·,d)=1} ∗ (1/id) ≥ 0` -/

section Conv
open ArithmeticFunction

/-- `F_d(n) = f(n)` for `(n, d) = 1`, `0` otherwise. -/
noncomputable def Fd (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n d then fo n else 0, by simp [fo]⟩

/-- `n ↦ 1/n`. -/
noncomputable def Rc : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩

/-- `n ↦ μ(n)/n`. -/
noncomputable def Mu : ArithmeticFunction ℝ := ⟨fun n => (μ n : ℝ) / n, by simp⟩

/-- `H_d = F_d ∗ (1/id)`. -/
noncomputable def Hd (d : ℕ) : ArithmeticFunction ℝ := Fd d * Rc

theorem Fd_apply (d n : ℕ) : Fd d n = if Nat.Coprime n d then fo n else 0 := rfl
theorem Rc_apply (n : ℕ) : Rc n = (n : ℝ)⁻¹ := rfl
theorem Mu_apply (n : ℕ) : Mu n = (μ n : ℝ) / n := rfl

theorem Rc_mul_Mu : Rc * Mu = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [mul_apply, one_apply]
  have h1 : ∀ x ∈ n.divisorsAntidiagonal, Rc x.1 * Mu x.2 = (μ x.2 : ℝ) / n := by
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.1 hx
    have h1 : (x.1 : ℝ) ≠ 0 := by
      have := hx'.1; intro h; apply hx'.2; rw [← this]; simp [Nat.cast_eq_zero.1 h]
    have h2 : (x.2 : ℝ) ≠ 0 := by
      have := hx'.1; intro h; apply hx'.2; rw [← this]; simp [Nat.cast_eq_zero.1 h]
    rw [Rc_apply, Mu_apply, ← hx'.1]; push_cast; field_simp
  rw [sum_congr rfl h1, ← sum_div]
  have h2 := Nat.sum_divisorsAntidiagonal' (fun _ b => (μ b : ℝ)) (n := n)
  rw [h2, g2_sum_moebius_divisors]
  split_ifs with h
  · subst h; simp
  · simp

theorem Hd_mul_Mu (d : ℕ) : Hd d * Mu = Fd d := by
  rw [Hd, mul_assoc, Rc_mul_Mu, mul_one]

/-- **`S_d(M) = ∑_{a ≤ M} H_d(a) m(M/a)`**, `m(K) = ∑_{b ≤ K} μ(b)/b`. -/
theorem Sd_eq (d M : ℕ) :
    Sd d M = ∑ a ∈ Icc 1 M, Hd d a * ∑ b ∈ Icc 1 (M / a), (μ b : ℝ) / b := by
  have h := sum_Ioc_mul_eq_sum_sum (Hd d) Mu M
  rw [Hd_mul_Mu] at h
  exact h

theorem fo_one : fo 1 = 1 := by simp [fo]

theorem fo_prime {p : ℕ} (hp : p.Prime) : fo p = if p = 2 then 0 else -1 / ((p : ℝ) + 1) := by
  unfold fo
  rcases hp.eq_two_or_odd' with rfl | hodd
  · simp
  · have h2 : p ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
    have hs : (σ 1 p : ℝ) = p + 1 := by
      have := sigma_one_apply_prime_pow (i := 1) hp
      simp only [pow_one] at this; rw [this]; simp [sum_range_succ]; ring
    rw [if_pos hodd, if_neg h2, moebius_apply_prime hp, hs]; push_cast; ring

theorem fo_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : fo (p ^ k) = 0 := by
  unfold fo
  simp [moebius_apply_prime_pow hp (by omega : k ≠ 0), show k ≠ 1 by omega]

theorem isMultiplicative_Fd (d : ℕ) : IsMultiplicative (Fd d) := by
  refine ⟨by simp [Fd_apply, fo_one], fun {m n} hmn => ?_⟩
  simp only [Fd_apply, Nat.coprime_mul_iff_left]
  by_cases hm : Nat.Coprime m d
  · by_cases hn : Nat.Coprime n d
    · rw [if_pos ⟨hm, hn⟩, if_pos hm, if_pos hn, fo_mul_of_coprime hmn]
    · rw [if_neg fun h => hn h.2, if_neg hn, mul_zero]
  · rw [if_neg fun h => hm h.1, if_neg hm, zero_mul]

theorem isMultiplicative_Rc : IsMultiplicative Rc :=
  ⟨by simp [Rc_apply], fun {m n} _ => by simp only [Rc_apply, Nat.cast_mul, mul_inv]⟩

theorem isMultiplicative_Hd (d : ℕ) : IsMultiplicative (Hd d) :=
  (isMultiplicative_Fd d).mul isMultiplicative_Rc

/-- `κ_p = 1/(p+1)` for odd `p ∤ d`, `1` otherwise. -/
noncomputable def kapH (d p : ℕ) : ℝ := if p ≠ 2 ∧ ¬ p ∣ d then 1 / (p + 1) else 1

theorem kapH_nonneg (d p : ℕ) : 0 ≤ kapH d p := by unfold kapH; split_ifs <;> positivity

theorem kapH_le_one (d p : ℕ) : kapH d p ≤ 1 := by
  unfold kapH; split_ifs
  · rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  · exact le_rfl

theorem Hd_prime_pow {d p : ℕ} (hp : p.Prime) (k : ℕ) :
    Hd d (p ^ (k + 1)) = kapH d p * ((p : ℝ)⁻¹) ^ (k + 1) := by
  rw [Hd, TernaryGoldbach.Prelim.conv_pp _ _ hp, sum_range_succ', sum_range_succ']
  have h0 : ∑ i ∈ range k, Fd d (p ^ (i + 1 + 1)) * Rc (p ^ (k + 1 - (i + 1 + 1))) = 0 := by
    refine sum_eq_zero fun i _ => ?_
    rw [Fd_apply, fo_prime_pow hp (by omega)]; simp
  rw [h0, zero_add, pow_zero, (isMultiplicative_Fd d).map_one, one_mul, pow_one,
    show k + 1 - (0 + 1) = k by omega, show k + 1 - 0 = k + 1 by omega, Rc_apply, Rc_apply, Fd_apply]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcop : Nat.Coprime p d ↔ ¬ p ∣ d := hp.coprime_iff_not_dvd
  unfold kapH
  by_cases h2 : p = 2
  · subst h2
    simp [fo_prime hp]
  · rw [fo_prime hp, if_neg h2]
    by_cases hd : p ∣ d
    · simp [hcop, hd, h2]
    · rw [if_pos (hcop.2 hd), if_pos ⟨h2, hd⟩, inv_pow]
      have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem Hd_nonneg (d n : ℕ) : 0 ≤ Hd d n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [IsMultiplicative.multiplicative_factorization (Hd d) (isMultiplicative_Hd d) hn]
  unfold Finsupp.prod
  refine prod_nonneg fun p hp => ?_
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hp)
  show 0 ≤ Hd d (p ^ n.factorization p)
  rw [hk, Hd_prime_pow hp']
  exact mul_nonneg (kapH_nonneg d p) (by positivity)

end Conv

/-! ### Euler products -/

/-- `∑_{n ≤ A} f(n) ≤ ∏_{p ≤ A} ∑_e f(p^e)` for nonnegative multiplicative `f`. -/
theorem sum_le_euler {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (h1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖f (p ^ e)‖)) (A : ℕ) :
    ∑ n ∈ Icc 1 A, f n ≤ ∏ p ∈ Nat.primesBelow (A + 1), ∑' e, f (p ^ e) := by
  obtain ⟨-, hHas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum h1 hmul hsum (A + 1)
  have hsub : ∑ n ∈ Icc 1 A, f n = ∑ x ∈ (Icc 1 A).subtype (· ∈ (A + 1).smoothNumbers), f x := by
    rw [sum_subtype_eq_sum_filter, filter_true_of_mem]
    intro n hn
    rw [Nat.mem_smoothNumbers]
    refine ⟨by have := (mem_Icc.1 hn).1; omega, fun p hp => ?_⟩
    have := Nat.le_of_mem_primeFactorsList hp; have := (mem_Icc.1 hn).2; omega
  rw [hsub]
  exact sum_le_hasSum (f := fun m : (A + 1).smoothNumbers => f m) _ (fun x _ => hf0 x) hHas

end TernaryGoldbach.MinorArcs
