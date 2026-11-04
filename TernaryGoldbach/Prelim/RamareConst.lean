import TernaryGoldbach.Prelim.RamareLog

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# The constant `c_E = γ + ∑_p log p/(p(p−1))`: identities

* `∑ Λ(n)/n² = (∑ log n/n²)/ζ(2)`, `ζ(2) = π²/6` (`tsum_vonMangoldt_sq`, from Mathlib's
  `L(Λ, s) = −ζ'(s)/ζ(s)` and `L(1, s) = ζ(s)`);
* `∑ Λ(n)/n² = ∑_p log p/(p² − 1)` (`tsum_vonMangoldt_eq`);
* `∑_p log p/(p(p−1)) = ∑_p log p/(p² − 1) + ∑_p log p/(p³ − p)` (`sumP_eq`).
-/

open Finset Real ArithmeticFunction Function Complex

namespace TernaryGoldbach.Prelim.RamPf

theorem term_real (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) 2 n = ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [LSeries.term, hf]
  · rw [LSeries.term, if_neg h.ne']
    push_cast
    congr 1
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]

theorem LSeries_real (f : ℕ → ℝ) (hf : f 0 = 0) :
    LSeries (fun n => (f n : ℂ)) 2 = ((∑' n, f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => term_real f hf n

/-- **`∑ Λ(n)/n² = (∑ log n/n²)/(π²/6)`.** -/
theorem tsum_vonMangoldt_sq :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 = (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) / (π ^ 2 / 6) := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have h2 : deriv riemannZeta 2 = deriv (LSeries 1) 2 := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
      fun z hz => (LSeries_one_eq_riemannZeta hz).symm⟩
  have h3 : deriv (LSeries 1) 2 = -LSeries (LSeries.logMul 1) 2 :=
    LSeries_deriv (by
      rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast (show (1 : ℝ) < (2 : ℂ).re by norm_num))
  have h4 : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := riemannZeta_two
  rw [h2, h3, h4, neg_neg] at h1
  have hΛ : LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) 2 =
      ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) :=
    LSeries_real (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (by simp)
  have hlog : LSeries (LSeries.logMul 1) 2 = ((∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    have e : LSeries.logMul (1 : ℕ → ℂ) = fun (n : ℕ) => ((Real.log (n : ℝ) : ℝ) : ℂ) := by
      funext n
      simp only [LSeries.logMul, Pi.one_apply, mul_one]
      rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; rfl, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [e]; exact LSeries_real (fun (n : ℕ) => Real.log (n : ℝ)) (by simp)
  rw [hΛ, hlog] at h1
  have h5 : ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) =
      (((∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) / (π ^ 2 / 6) : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h5

/-! ### `∑ Λ(n)/n² = ∑_p log p/(p² − 1)` -/

/-- The prime-power terms. -/
noncomputable def ppTerm (qk : ℕ × ℕ) : ℝ :=
  if qk.1.Prime then Real.log qk.1 * ((1 : ℝ) / (qk.1 : ℝ) ^ 2) ^ (qk.2 + 1) else 0

theorem hasSum_vonMangoldt_pp {s : ℝ} (h : HasSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2) s) :
    HasSum ppTerm s := by
  refine (hasSum_iff_hasSum_of_ne_zero_bij (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2) (g := ppTerm)
    (fun x => x.1.1 ^ (x.1.2 + 1)) ?_ ?_ ?_).1 h
  · rintro ⟨⟨q, k⟩, hx⟩ ⟨⟨q', k'⟩, hy⟩ hxy
    simp only [mem_support, ppTerm] at hx hy hxy
    have hq : q.Prime := by by_contra h'; simp [ppTerm, h'] at hx
    have hq' : q'.Prime := by by_contra h'; simp [ppTerm, h'] at hy
    have := Nat.Prime.pow_inj hq hq' hxy
    obtain ⟨rfl, hk⟩ := this
    have : k = k' := by omega
    subst this; rfl
  · intro n hn
    simp only [mem_support] at hn
    have hΛ : Λ n ≠ 0 := by intro h0; apply hn; simp [h0]
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    refine ⟨⟨(q, k - 1), ?_⟩, ?_⟩
    · simp only [mem_support, ppTerm, if_pos hq, ne_eq, mul_eq_zero, not_or]
      refine ⟨(Real.log_pos (by exact_mod_cast hq.one_lt)).ne', ?_⟩
      have : (0 : ℝ) < q := by exact_mod_cast hq.pos
      exact pow_ne_zero _ (by positivity)
    · simp only; rw [Nat.sub_add_cancel hk]
  · rintro ⟨⟨q, k⟩, hx⟩
    simp only [ppTerm] at hx ⊢
    have hq : q.Prime := by by_contra h'; simp [ppTerm, h'] at hx
    rw [if_pos hq, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hq]
    push_cast
    rw [div_pow, one_pow, ← pow_mul, one_div, ← inv_pow, div_eq_mul_inv]
    congr 1; ring

theorem summable_vonMangoldt_sq : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 := by
  have hs : Summable fun n : ℕ => 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h
  have hr := Real.rpow_pos_of_pos hn0 ((1 : ℝ) / 2)
  have hlog : Real.log n ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have := Real.log_le_sub_one_of_pos hr
    rw [Real.log_rpow hn0] at this; linarith
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n := vonMangoldt_le_log
  have e : 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) = 2 * (n : ℝ) ^ ((1 : ℝ) / 2) / (n : ℝ) ^ 2 := by
    rw [show (-(3 / 2 : ℝ)) = (1 / 2) - 2 by norm_num, Real.rpow_sub hn0, Real.rpow_two]; ring
  rw [e]
  exact div_le_div_of_nonneg_right (hΛ.trans hlog) (by positivity)

theorem hasSum_vonMangoldt_primes :
    HasSum (fun q : ℕ => if q.Prime then Real.log q / ((q : ℝ) ^ 2 - 1) else 0)
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2) := by
  refine (hasSum_vonMangoldt_pp summable_vonMangoldt_sq.hasSum).prod_fiberwise fun q => ?_
  by_cases hq : q.Prime
  · have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
    set r : ℝ := (1 : ℝ) / (q : ℝ) ^ 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; nlinarith
    have hg := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.log q * r))
    convert hg using 1
    · funext k; simp only [ppTerm, if_pos hq]; rw [pow_succ]; ring
    · rw [if_pos hq, hr]
      have : (q : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      have : (q : ℝ) ^ 2 ≠ 0 := by positivity
      field_simp
  · simp only [ppTerm, if_neg hq]
    exact hasSum_zero

/-- **`∑ Λ(n)/n² = ∑_p log p/(p² − 1)`.** -/
theorem tsum_vonMangoldt_eq :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 =
      ∑' q : ℕ, if q.Prime then Real.log q / ((q : ℝ) ^ 2 - 1) else 0 :=
  hasSum_vonMangoldt_primes.tsum_eq.symm

/-- **`∑_p log p/(p(p−1)) = ∑_p log p/(p² − 1) + ∑_p log p/(p³ − p)`.** -/
theorem sumP_eq :
    sumP = (∑' q : ℕ, if q.Prime then Real.log q / ((q : ℝ) ^ 2 - 1) else 0) +
      ∑' q : ℕ, if q.Prime then Real.log q / ((q : ℝ) ^ 3 - q) else 0 := by
  have hs2 : Summable fun q : ℕ => if q.Prime then Real.log q / ((q : ℝ) ^ 2 - 1) else 0 :=
    hasSum_vonMangoldt_primes.summable
  have hs3 : Summable fun q : ℕ => if q.Prime then Real.log q / ((q : ℝ) ^ 3 - q) else 0 := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) summable_sumP
    · split_ifs with hq
      · have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
        have : 0 < (q : ℝ) ^ 3 - q := by
          have := mul_pos (by linarith : (0 : ℝ) < q) (by nlinarith : (0 : ℝ) < (q : ℝ) ^ 2 - 1)
          nlinarith
        exact div_nonneg (Real.log_natCast_nonneg q) this.le
      · exact le_rfl
    · split_ifs with hq
      · have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
        have h1 : 0 < (q : ℝ) * ((q : ℝ) - 1) := by nlinarith
        have h2 : (q : ℝ) * ((q : ℝ) - 1) ≤ (q : ℝ) ^ 3 - q := by
          have := mul_nonneg (by nlinarith : (0 : ℝ) ≤ (q : ℝ) ^ 2) (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)
          nlinarith
        exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg q) h1 h2
      · exact le_rfl
  rw [sumP, ← Summable.tsum_add hs2 hs3]
  refine tsum_congr fun q => ?_
  split_ifs with hq
  · have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
    have h1 : (q : ℝ) * ((q : ℝ) - 1) ≠ 0 := by nlinarith
    have h2 : (q : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h3 : (q : ℝ) ^ 3 - q ≠ 0 := by
      have := mul_pos (by linarith : (0 : ℝ) < q) (by nlinarith : (0 : ℝ) < (q : ℝ) ^ 2 - 1)
      nlinarith
    field_simp
    ring
  · ring

end TernaryGoldbach.Prelim.RamPf
