import TernaryGoldbach.MinorArcs.G2Euler
import TernaryGoldbach.Prelim.MVLemma7

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# Numerical values of the Euler products for `g₂`

* `c_{1/22}(2) ≤ 2.067`, `c_{1/2}(2) ≤ 3.4148`;
* `∏_{2 < p < M} ℓ_{1/22}(p) ≤ 1.389`, `∏_{2 < p < M} (1 + b_{1/22}(p)) ≤ 1.443`,
  `∏_{2 < p < M} ℓ_{1/2}(p) ≤ 3.364` for every `M`.

The primes below `12` (resp. `30`) are evaluated with rational upper bounds for `p^{1/22}`
(resp. `√p`); the rest is bounded by `exp(∑_{n ≥ P₀} C n^{−α}) ≤ 1/(1 − C(P₀−1)^{1−α}/(α−1))`.
-/

open Real Finset

namespace TernaryGoldbach.MinorArcs

/-! ### Elementary bounds -/

theorem rpow_le_of_pow_le {x r e : ℝ} {k : ℕ} (he : e * k = 1) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (h : x ≤ r ^ k) : x ^ e ≤ r := by
  have he0 : 0 ≤ e := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at he
    · have : (0 : ℝ) < k := by exact_mod_cast hk
      nlinarith
  calc x ^ e ≤ (r ^ k) ^ e := Real.rpow_le_rpow hx h he0
    _ = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
      rw [show (k : ℝ) * e = 1 by linarith, Real.rpow_one]

theorem le_rpow_frac {x r : ℝ} {a b : ℕ} (hb : 0 < b) (hx : 0 ≤ x) (hr : 0 ≤ r) (h : r ^ b ≤ x ^ a) :
    r ≤ x ^ ((a : ℝ) / b) := by
  calc r = (r ^ b) ^ ((1 : ℝ) / b) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr, mul_one_div_cancel (by exact_mod_cast hb.ne'),
          Real.rpow_one]
    _ ≤ (x ^ a) ^ ((1 : ℝ) / b) := Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = x ^ ((a : ℝ) / b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; ring

theorem ell_le_of {s r : ℝ} {p : ℕ} (hX : (p : ℝ) ^ s ≤ r) (hr : r < p) :
    ell s p ≤ 1 + r / ((p + 1) * (p - r)) := by
  unfold ell
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hX0 : 0 ≤ (p : ℝ) ^ s := by positivity
  have h1 : (0 : ℝ) < (p + 1) * (p - r) := mul_pos (by linarith) (by linarith)
  have := div_le_div₀ (by linarith) hX h1
    (mul_le_mul_of_nonneg_left (show (p : ℝ) - r ≤ p - (p : ℝ) ^ s by linarith)
      (by linarith : (0 : ℝ) ≤ p + 1))
  linarith

theorem bterm_le_of {s r : ℝ} {p : ℕ} (hX : (p : ℝ) ^ s ≤ r) (hr : r < p + 1) :
    bterm s p ≤ (r / (p + 1 - r)) ^ 2 := by
  unfold bterm
  have hX0 : 0 ≤ (p : ℝ) ^ s := by positivity
  exact pow_le_pow_left₀ (div_nonneg hX0 (by linarith))
    (div_le_div₀ (by linarith) hX (by linarith) (by linarith)) 2

theorem cfac_le_of {s r : ℝ} {p : ℕ} (hX : (p : ℝ) ^ s ≤ r) (hr : r < p) :
    cfac s p ≤ p / (p - r) := by
  unfold cfac
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  exact div_le_div_of_nonneg_left hp0 (by linarith) (by linarith)

/-- For `n ≥ P₀`, `n^s/n ≤ P₀^s/P₀`. -/
theorem rpow_div_anti {s : ℝ} (hs1 : s < 1) {n P0 : ℕ} (hP0 : 1 ≤ P0) (hn : P0 ≤ n) :
    (n : ℝ) ^ s / n ≤ (P0 : ℝ) ^ s / P0 := by
  have hP : (0 : ℝ) < P0 := by exact_mod_cast hP0
  have hn' : (P0 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.rpow_sub_one (by linarith), ← Real.rpow_sub_one hP.ne']
  exact Real.rpow_le_rpow_of_nonpos hP hn' (by linarith)

/-- Tail of `ℓ_s`: `ℓ_s(n) − 1 ≤ n^{−(2−s)}/(1 − ρ₀)` for `n ≥ P₀`, `P₀^s/P₀ ≤ ρ₀ < 1`. -/
theorem ell_sub_one_le {s : ℝ} (hs1 : s < 1) {n P0 : ℕ} (hP0 : 1 ≤ P0) (hn : P0 ≤ n) {ρ0 : ℝ}
    (hρ : (P0 : ℝ) ^ s / P0 ≤ ρ0) (hρ1 : ρ0 < 1) :
    ell s n - 1 ≤ (n : ℝ) ^ (-(2 - s)) / (1 - ρ0) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr := (rpow_div_anti hs1 hP0 hn).trans hρ
  set X := (n : ℝ) ^ s with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXn : X ≤ ρ0 * n := by rw [div_le_iff₀ hn0] at hr; linarith
  have e : (n : ℝ) ^ (-(2 - s)) = X / n ^ 2 := by
    rw [show -(2 - s) = s - 2 by ring, Real.rpow_sub hn0, Real.rpow_two]
  rw [e]
  unfold ell
  rw [← hXdef]
  have h1 : 0 < (n : ℝ) - X := by nlinarith
  have h2 : (0 : ℝ) < 1 - ρ0 := by linarith
  rw [add_sub_cancel_left, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hX0 (sq_nonneg (n : ℝ)), mul_nonneg hX0 hn0.le,
    mul_nonneg (mul_nonneg hX0 hn0.le) h1.le]

/-- Tail of `b_s`: `b_s(n) ≤ n^{−(2−2s)}/(1 − ρ₀)²` for `n ≥ P₀`, `P₀^s/P₀ ≤ ρ₀ < 1`. -/
theorem bterm_le_tail {s : ℝ} (hs1 : s < 1) {n P0 : ℕ} (hP0 : 1 ≤ P0) (hn : P0 ≤ n) {ρ0 : ℝ}
    (hρ : (P0 : ℝ) ^ s / P0 ≤ ρ0) (hρ1 : ρ0 < 1) :
    bterm s n ≤ (n : ℝ) ^ (-(2 - 2 * s)) / (1 - ρ0) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr := (rpow_div_anti hs1 hP0 hn).trans hρ
  set X := (n : ℝ) ^ s with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXn : X ≤ ρ0 * n := by rw [div_le_iff₀ hn0] at hr; linarith
  have e : (n : ℝ) ^ (-(2 - 2 * s)) = (X / n) ^ 2 := by
    rw [show -(2 - 2 * s) = (s - 1) * 2 by ring, Real.rpow_mul hn0.le, Real.rpow_sub_one hn0.ne',
      ← hXdef, Real.rpow_two]
  rw [e]
  unfold bterm
  rw [← hXdef, ← div_pow]
  have h2 : (0 : ℝ) < 1 - ρ0 := by linarith
  have h1 : 0 < (n : ℝ) - X := by nlinarith
  refine pow_le_pow_left₀ (div_nonneg hX0 (by linarith)) ?_ 2
  rw [div_div, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [mul_nonneg hX0 hn0.le]

/-- `∏ (1 + a_p) ≤ exp(∑ a_p)`. -/
theorem prod_one_add_le_exp {S : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ p ∈ S, 0 ≤ a p) :
    ∏ p ∈ S, (1 + a p) ≤ Real.exp (∑ p ∈ S, a p) := by
  rw [Real.exp_sum]
  exact prod_le_prod₀ (fun p hp => by linarith [ha p hp]) fun p _ => by
    linarith [Real.add_one_le_exp (a p)]

/-- Odd primes `< P₀` lie in a given finite set. -/
theorem odd_primes_sub {M P0 : ℕ} {T : Finset ℕ}
    (hT : ∀ p < P0, p.Prime → p ≠ 2 → p ∈ T) :
    ((Nat.primesBelow M).filter (· ≠ 2)).filter (· < P0) ⊆ T := by
  intro p hp
  simp only [mem_filter, Nat.mem_primesBelow] at hp
  exact hT p hp.2 hp.1.1.2 hp.1.2

/-- The splitting argument: finite part times tail. -/
theorem prod_split_le {f : ℕ → ℝ} {M P0 : ℕ} {T : Finset ℕ} {A τ : ℝ}
    (hT : ∀ p < P0, p.Prime → p ≠ 2 → p ∈ T) (hf1 : ∀ p, 2 ≤ p → 1 ≤ f p)
    (hT2 : ∀ p ∈ T, 2 ≤ p) (hA : ∏ p ∈ T, f p ≤ A)
    (htail : ∑ n ∈ Ico P0 M, (f n - 1) ≤ τ) (hτ : τ < 1) (hP0 : 2 ≤ P0) :
    ∏ p ∈ (Nat.primesBelow M).filter (· ≠ 2), f p ≤ A / (1 - τ) := by
  set P := (Nat.primesBelow M).filter (· ≠ 2)
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp =>
    (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le
  rw [← prod_filter_mul_prod_filter_not P (· < P0)]
  have h1 : ∏ p ∈ P.filter (· < P0), f p ≤ A :=
    le_trans (prod_le_prod_of_subset_of_one_le₀ (odd_primes_sub hT)
      (fun p hp => by linarith [hf1 p (hP2 p (mem_filter.1 hp).1)])
      fun p hp _ => hf1 p (hT2 p hp)) hA
  have h2 : ∏ p ∈ P.filter (fun p => ¬ p < P0), f p ≤ 1 / (1 - τ) := by
    have e : ∏ p ∈ P.filter (fun p => ¬ p < P0), f p =
        ∏ p ∈ P.filter (fun p => ¬ p < P0), (1 + (f p - 1)) :=
      prod_congr rfl fun _ _ => by ring
    rw [e]
    refine (prod_one_add_le_exp fun p hp => ?_).trans ?_
    · linarith [hf1 p (hP2 p (mem_filter.1 hp).1)]
    · have hs : ∑ p ∈ P.filter (fun p => ¬ p < P0), (f p - 1) ≤ τ := by
        refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ ?_) htail
        · intro p hp
          simp only [P, mem_filter, Nat.mem_primesBelow, not_lt] at hp
          exact mem_Ico.2 ⟨hp.2, hp.1.1.1⟩
        · intro n hn _
          linarith [hf1 n (by have := (mem_Ico.1 hn).1; omega)]
      have hτ0 : 0 ≤ τ := le_trans (sum_nonneg fun p hp => by
        linarith [hf1 p (hP2 p (mem_filter.1 hp).1)]) hs
      exact (Real.exp_le_exp.2 hs).trans (Real.exp_bound_div_one_sub_of_interval hτ0 hτ)
  have hA0 : 0 ≤ ∏ p ∈ P.filter (· < P0), f p :=
    prod_nonneg fun p hp => by linarith [hf1 p (hP2 p (mem_filter.1 hp).1)]
  have hB0 : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ p < P0), f p :=
    prod_nonneg fun p hp => by linarith [hf1 p (hP2 p (mem_filter.1 hp).1)]
  calc (∏ p ∈ P.filter (· < P0), f p) * ∏ p ∈ P.filter (fun p => ¬ p < P0), f p
      ≤ A * (1 / (1 - τ)) := mul_le_mul h1 h2 hB0 (hA0.trans h1)
    _ = A / (1 - τ) := by ring

/-! ### `s = 1/22` -/

theorem two_rpow22 : (2 : ℝ) ^ ((1 : ℝ) / 22) ≤ 1.0321 :=
  rpow_le_of_pow_le (k := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cfac22_two : cfac (1 / 22) 2 ≤ 2.067 := by
  have := cfac_le_of (p := 2) (by exact_mod_cast two_rpow22) (by norm_num)
  refine this.trans ?_; norm_num

theorem rpow22_12 : (12 : ℝ) ^ ((1 : ℝ) / 22) / 12 ≤ 0.0934 := by
  have : (12 : ℝ) ^ ((1 : ℝ) / 22) ≤ 1.1197 :=
    rpow_le_of_pow_le (k := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [div_le_iff₀ (by norm_num)]; linarith

theorem odd_primes_lt_12 : ∀ p < 12, p.Prime → p ≠ 2 → p ∈ ({3, 5, 7, 11} : Finset ℕ) := by
  intro p hp hpp h2
  interval_cases p
  all_goals first
    | exact absurd rfl h2
    | (exfalso; revert hpp; decide)
    | simp

theorem odd_primes_lt_30 :
    ∀ p < 30, p.Prime → p ≠ 2 → p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
  intro p hp hpp h2
  interval_cases p
  all_goals first
    | exact absurd rfl h2
    | (exfalso; revert hpp; decide)
    | simp

/-- `∑_{12 ≤ n < M} n^{−(2 − 1/22)} ≤ 0.10626`. -/
theorem tail22_a (M : ℕ) : ∑ n ∈ Ico 12 M, (n : ℝ) ^ (-(2 - (1 : ℝ) / 22)) ≤ 0.10626 := by
  have h := TernaryGoldbach.Prelim.MV.sum_rpow_neg_le (s := 2 - 1 / 22) (by norm_num)
    (P0 := 12) (by norm_num) M
  have e : ((12 : ℕ) : ℝ) - 1 = 11 := by norm_num
  rw [e] at h
  have hb : (9.86 : ℝ) ≤ (11 : ℝ) ^ ((21 : ℕ) / (22 : ℕ) : ℝ) :=
    le_rpow_frac (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : (11 : ℝ) ^ (1 - (2 - (1 : ℝ) / 22)) = ((11 : ℝ) ^ ((21 : ℕ) / (22 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; congr 1; push_cast; ring
  rw [e2] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num)]
  have : ((11 : ℝ) ^ ((21 : ℕ) / (22 : ℕ) : ℝ))⁻¹ ≤ 1 / 9.86 := by
    rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hb
  linarith

/-- `∑_{12 ≤ n < M} n^{−(2 − 2/22)} ≤ 0.125`. -/
theorem tail22_b (M : ℕ) : ∑ n ∈ Ico 12 M, (n : ℝ) ^ (-(2 - 2 * ((1 : ℝ) / 22))) ≤ 0.125 := by
  have h := TernaryGoldbach.Prelim.MV.sum_rpow_neg_le (s := 2 - 2 * (1 / 22)) (by norm_num)
    (P0 := 12) (by norm_num) M
  have e : ((12 : ℕ) : ℝ) - 1 = 11 := by norm_num
  rw [e] at h
  have hb : (8.8 : ℝ) ≤ (11 : ℝ) ^ ((10 : ℕ) / (11 : ℕ) : ℝ) :=
    le_rpow_frac (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : (11 : ℝ) ^ (1 - (2 - 2 * ((1 : ℝ) / 22))) = ((11 : ℝ) ^ ((10 : ℕ) / (11 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; congr 1; push_cast; ring
  rw [e2] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num)]
  have : ((11 : ℝ) ^ ((10 : ℕ) / (11 : ℕ) : ℝ))⁻¹ ≤ 1 / 8.8 := by
    rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hb
  linarith

/-- Upper bounds for `p^{1/22}`, `p ∈ {3, 5, 7, 11}`. -/
noncomputable def U22 (p : ℕ) : ℝ :=
  if p = 3 then 1.0513 else if p = 5 then 1.076 else if p = 7 then 1.0926 else 1.1153

theorem rpow22_le_U {p : ℕ} (hp : p ∈ ({3, 5, 7, 11} : Finset ℕ)) :
    (p : ℝ) ^ ((1 : ℝ) / 22) ≤ U22 p ∧ U22 p < p := by
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    exact ⟨rpow_le_of_pow_le (k := 22) (by norm_num) (by norm_num) (by norm_num [U22])
      (by norm_num [U22]), by norm_num [U22]⟩

/-- **`∏_{2 < p < M} ℓ_{1/22}(p) ≤ 1.389`**. -/
theorem prod_ell22_le (M : ℕ) :
    ∏ p ∈ (Nat.primesBelow M).filter (· ≠ 2), ell (1 / 22) p ≤ 1.389 := by
  have hT2 : ∀ p ∈ ({3, 5, 7, 11} : Finset ℕ), 2 ≤ p := by decide
  have hA : ∏ p ∈ ({3, 5, 7, 11} : Finset ℕ), ell (1 / 22) p ≤ 1.2256 := by
    refine (prod_le_prod₀ (g := fun p => 1 + U22 p / ((p + 1) * (p - U22 p)))
      (fun p hp => by linarith [one_le_ell (s := 1 / 22) (by norm_num) (hT2 p hp)])
      fun p hp => ell_le_of (rpow22_le_U hp).1 (rpow22_le_U hp).2).trans ?_
    simp only [prod_insert (show (3 : ℕ) ∉ ({5, 7, 11} : Finset ℕ) by decide),
      prod_insert (show (5 : ℕ) ∉ ({7, 11} : Finset ℕ) by decide),
      prod_insert (show (7 : ℕ) ∉ ({11} : Finset ℕ) by decide), prod_singleton]
    norm_num [U22]
  have h := prod_split_le (f := ell (1 / 22)) (M := M) (P0 := 12) (A := 1.2256) (τ := 0.1173)
    odd_primes_lt_12 (fun p hp => one_le_ell (by norm_num) hp) hT2 hA ?_ (by norm_num)
    (by norm_num)
  · exact h.trans (by norm_num)
  · have hb : ∀ n ∈ Ico 12 M, ell (1 / 22) n - 1 ≤
        (n : ℝ) ^ (-(2 - (1 : ℝ) / 22)) / (1 - 0.0934) := fun n hn =>
      ell_sub_one_le (by norm_num) (P0 := 12) (by norm_num) (mem_Ico.1 hn).1
        (by exact_mod_cast rpow22_12) (by norm_num)
    refine (sum_le_sum hb).trans ?_
    rw [← sum_div, div_le_iff₀ (by norm_num)]
    have := tail22_a M
    linarith

/-- **`∏_{2 < p < M} (1 + b_{1/22}(p)) ≤ 1.443`**. -/
theorem prod_bterm22_le (M : ℕ) :
    ∏ p ∈ (Nat.primesBelow M).filter (· ≠ 2), (1 + bterm (1 / 22) p) ≤ 1.443 := by
  have hT2 : ∀ p ∈ ({3, 5, 7, 11} : Finset ℕ), 2 ≤ p := by decide
  have hb0 : ∀ p, 0 ≤ bterm (1 / 22) p := fun p => by unfold bterm; positivity
  have hA : ∏ p ∈ ({3, 5, 7, 11} : Finset ℕ), (1 + bterm (1 / 22) p) ≤ 1.2232 := by
    refine (prod_le_prod₀ (g := fun p => 1 + (U22 p / (p + 1 - U22 p)) ^ 2)
      (fun p _ => by linarith [hb0 p])
      fun p hp => by
        have := bterm_le_of (rpow22_le_U hp).1 (by linarith [(rpow22_le_U hp).2])
        linarith).trans ?_
    simp only [prod_insert (show (3 : ℕ) ∉ ({5, 7, 11} : Finset ℕ) by decide),
      prod_insert (show (5 : ℕ) ∉ ({7, 11} : Finset ℕ) by decide),
      prod_insert (show (7 : ℕ) ∉ ({11} : Finset ℕ) by decide), prod_singleton]
    norm_num [U22]
  have h := prod_split_le (f := fun p => 1 + bterm (1 / 22) p) (M := M) (P0 := 12) (A := 1.2232)
    (τ := 0.1521) odd_primes_lt_12 (fun p _ => by linarith [hb0 p]) hT2 hA ?_ (by norm_num)
    (by norm_num)
  · exact h.trans (by norm_num)
  · have hb : ∀ n ∈ Ico 12 M, (1 + bterm (1 / 22) n) - 1 ≤
        (n : ℝ) ^ (-(2 - 2 * ((1 : ℝ) / 22))) / (1 - 0.0934) ^ 2 := fun n hn => by
      rw [add_sub_cancel_left]
      exact bterm_le_tail (by norm_num) (P0 := 12) (by norm_num) (mem_Ico.1 hn).1
        (by exact_mod_cast rpow22_12) (by norm_num)
    refine (sum_le_sum hb).trans ?_
    rw [← sum_div, div_le_iff₀ (by norm_num)]
    have := tail22_b M
    linarith

/-! ### `s = 1/2` -/

theorem cfac2_two : cfac (1 / 2) 2 ≤ 3.4148 := by
  have h : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 1.4143 :=
    rpow_le_of_pow_le (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := cfac_le_of (p := 2) (by exact_mod_cast h) (by norm_num)
  refine this.trans ?_; norm_num

/-- Upper bounds for `√p`, odd `p < 30`. -/
noncomputable def Uh (p : ℕ) : ℝ :=
  if p = 3 then 1.7321 else if p = 5 then 2.2361 else if p = 7 then 2.6458 else
  if p = 11 then 3.3167 else if p = 13 then 3.6056 else if p = 17 then 4.1232 else
  if p = 19 then 4.359 else if p = 23 then 4.7959 else 5.3852

theorem sqrt_le_Uh {p : ℕ} (hp : p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ)) :
    (p : ℝ) ^ ((1 : ℝ) / 2) ≤ Uh p ∧ Uh p < p := by
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rpow_le_of_pow_le (k := 2) (by norm_num) (by norm_num) (by norm_num [Uh])
      (by norm_num [Uh]), by norm_num [Uh]⟩

/-- `∑_{30 ≤ n < M} n^{−3/2} ≤ 0.3715`. -/
theorem tailh (M : ℕ) : ∑ n ∈ Ico 30 M, (n : ℝ) ^ (-(2 - (1 : ℝ) / 2)) ≤ 0.3715 := by
  have h := TernaryGoldbach.Prelim.MV.sum_rpow_neg_le (s := 2 - 1 / 2) (by norm_num)
    (P0 := 30) (by norm_num) M
  have e : ((30 : ℕ) : ℝ) - 1 = 29 := by norm_num
  rw [e] at h
  have hb : (5.385 : ℝ) ≤ (29 : ℝ) ^ ((1 : ℕ) / (2 : ℕ) : ℝ) :=
    le_rpow_frac (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : (29 : ℝ) ^ (1 - (2 - (1 : ℝ) / 2)) = ((29 : ℝ) ^ ((1 : ℕ) / (2 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; congr 1; push_cast; ring
  rw [e2] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num)]
  have : ((29 : ℝ) ^ ((1 : ℕ) / (2 : ℕ) : ℝ))⁻¹ ≤ 1 / 5.385 := by
    rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hb
  linarith

/-- **`∏_{2 < p < M} ℓ_{1/2}(p) ≤ 3.364`**. -/
theorem prod_ellh_le (M : ℕ) :
    ∏ p ∈ (Nat.primesBelow M).filter (· ≠ 2), ell (1 / 2) p ≤ 3.364 := by
  have hT2 : ∀ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), 2 ≤ p := by decide
  have hA : ∏ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), ell (1 / 2) p ≤ 1.8346 := by
    refine (prod_le_prod₀ (g := fun p => 1 + Uh p / ((p + 1) * (p - Uh p)))
      (fun p hp => by linarith [one_le_ell (s := 1 / 2) (by norm_num) (hT2 p hp)])
      fun p hp => ell_le_of (sqrt_le_Uh hp).1 (sqrt_le_Uh hp).2).trans ?_
    rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_singleton]
    norm_num [Uh]
  have hρ : (30 : ℝ) ^ ((1 : ℝ) / 2) / 30 ≤ 0.1826 := by
    have : (30 : ℝ) ^ ((1 : ℝ) / 2) ≤ 5.478 :=
      rpow_le_of_pow_le (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [div_le_iff₀ (by norm_num)]; linarith
  have h := prod_split_le (f := ell (1 / 2)) (M := M) (P0 := 30) (A := 1.8346) (τ := 0.4545)
    odd_primes_lt_30 (fun p hp => one_le_ell (by norm_num) hp) hT2 hA ?_ (by norm_num)
    (by norm_num)
  · exact h.trans (by norm_num)
  · have hb : ∀ n ∈ Ico 30 M, ell (1 / 2) n - 1 ≤
        (n : ℝ) ^ (-(2 - (1 : ℝ) / 2)) / (1 - 0.1826) := fun n hn =>
      ell_sub_one_le (by norm_num) (P0 := 30) (by norm_num) (mem_Ico.1 hn).1
        (by exact_mod_cast hρ) (by norm_num)
    refine (sum_le_sum hb).trans ?_
    rw [← sum_div, div_le_iff₀ (by norm_num)]
    have := tailh M
    linarith

/-! ### `s = 1/9` -/

theorem two_rpow9 : (2 : ℝ) ^ ((1 : ℝ) / 9) ≤ 1.0801 :=
  rpow_le_of_pow_le (k := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cfac9_two : cfac (1 / 9) 2 ≤ 2.175 := by
  have := cfac_le_of (p := 2) (by exact_mod_cast two_rpow9) (by norm_num)
  refine this.trans ?_; norm_num

theorem rpow9_30 : (30 : ℝ) ^ ((1 : ℝ) / 9) / 30 ≤ 0.0487 := by
  have : (30 : ℝ) ^ ((1 : ℝ) / 9) ≤ 1.4593 :=
    rpow_le_of_pow_le (k := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [div_le_iff₀ (by norm_num)]; linarith

/-- `∑_{30 ≤ n < M} n^{−(2 − 1/9)} ≤ 0.0566`. -/
theorem tail9_a (M : ℕ) : ∑ n ∈ Ico 30 M, (n : ℝ) ^ (-(2 - (1 : ℝ) / 9)) ≤ 0.0566 := by
  have h := TernaryGoldbach.Prelim.MV.sum_rpow_neg_le (s := 2 - 1 / 9) (by norm_num)
    (P0 := 30) (by norm_num) M
  have e : ((30 : ℕ) : ℝ) - 1 = 29 := by norm_num
  rw [e] at h
  have hb : (19.88 : ℝ) ≤ (29 : ℝ) ^ ((8 : ℕ) / (9 : ℕ) : ℝ) :=
    le_rpow_frac (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : (29 : ℝ) ^ (1 - (2 - (1 : ℝ) / 9)) = ((29 : ℝ) ^ ((8 : ℕ) / (9 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; congr 1; push_cast; ring
  rw [e2] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num)]
  have : ((29 : ℝ) ^ ((8 : ℕ) / (9 : ℕ) : ℝ))⁻¹ ≤ 1 / 19.88 := by
    rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hb
  linarith

/-- `∑_{30 ≤ n < M} n^{−(2 − 2/9)} ≤ 0.0939`. -/
theorem tail9_b (M : ℕ) : ∑ n ∈ Ico 30 M, (n : ℝ) ^ (-(2 - 2 * ((1 : ℝ) / 9))) ≤ 0.0939 := by
  have h := TernaryGoldbach.Prelim.MV.sum_rpow_neg_le (s := 2 - 2 * (1 / 9)) (by norm_num)
    (P0 := 30) (by norm_num) M
  have e : ((30 : ℕ) : ℝ) - 1 = 29 := by norm_num
  rw [e] at h
  have hb : (13.70 : ℝ) ≤ (29 : ℝ) ^ ((7 : ℕ) / (9 : ℕ) : ℝ) :=
    le_rpow_frac (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : (29 : ℝ) ^ (1 - (2 - 2 * ((1 : ℝ) / 9))) = ((29 : ℝ) ^ ((7 : ℕ) / (9 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; congr 1; push_cast; ring
  rw [e2] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num)]
  have : ((29 : ℝ) ^ ((7 : ℕ) / (9 : ℕ) : ℝ))⁻¹ ≤ 1 / 13.70 := by
    rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hb
  linarith

/-- Upper bounds for `p^{1/9}`, odd `p < 30`. -/
noncomputable def U9 (p : ℕ) : ℝ :=
  if p = 3 then 1.1299 else if p = 5 then 1.1959 else if p = 7 then 1.2414 else
  if p = 11 then 1.3053 else if p = 13 then 1.3298 else if p = 17 then 1.37 else
  if p = 19 then 1.3871 else if p = 23 then 1.4168 else 1.4538

theorem rpow9_le_U {p : ℕ} (hp : p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ)) :
    (p : ℝ) ^ ((1 : ℝ) / 9) ≤ U9 p ∧ U9 p < p := by
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rpow_le_of_pow_le (k := 9) (by norm_num) (by norm_num) (by norm_num [U9])
      (by norm_num [U9]), by norm_num [U9]⟩

/-- **`∏_{2 < p < M} ℓ_{1/9}(p) ≤ 1.367`**. -/
theorem prod_ell9_le (M : ℕ) :
    ∏ p ∈ (Nat.primesBelow M).filter (· ≠ 2), ell (1 / 9) p ≤ 1.367 := by
  have hT2 : ∀ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), 2 ≤ p := by decide
  have hA : ∏ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), ell (1 / 9) p ≤ 1.2852 := by
    refine (prod_le_prod₀ (g := fun p => 1 + U9 p / ((p + 1) * (p - U9 p)))
      (fun p hp => by linarith [one_le_ell (s := 1 / 9) (by norm_num) (hT2 p hp)])
      fun p hp => ell_le_of (rpow9_le_U hp).1 (rpow9_le_U hp).2).trans ?_
    rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_singleton]
    norm_num [U9]
  have h := prod_split_le (f := ell (1 / 9)) (M := M) (P0 := 30) (A := 1.2852) (τ := 0.0596)
    odd_primes_lt_30 (fun p hp => one_le_ell (by norm_num) hp) hT2 hA ?_ (by norm_num)
    (by norm_num)
  · exact h.trans (by norm_num)
  · have hb : ∀ n ∈ Ico 30 M, ell (1 / 9) n - 1 ≤
        (n : ℝ) ^ (-(2 - (1 : ℝ) / 9)) / (1 - 0.0487) := fun n hn =>
      ell_sub_one_le (by norm_num) (P0 := 30) (by norm_num) (mem_Ico.1 hn).1
        (by exact_mod_cast rpow9_30) (by norm_num)
    refine (sum_le_sum hb).trans ?_
    rw [← sum_div, div_le_iff₀ (by norm_num)]
    have := tail9_a M
    linarith

/-- **`∏_{2 < p < M} (1 + b_{1/9}(p)) ≤ 1.48`**. -/
theorem prod_bterm9_le (M : ℕ) :
    ∏ p ∈ (Nat.primesBelow M).filter (· ≠ 2), (1 + bterm (1 / 9) p) ≤ 1.48 := by
  have hT2 : ∀ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), 2 ≤ p := by decide
  have hb0 : ∀ p, 0 ≤ bterm (1 / 9) p := fun p => by unfold bterm; positivity
  have hA : ∏ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), (1 + bterm (1 / 9) p) ≤ 1.3258 := by
    refine (prod_le_prod₀ (g := fun p => 1 + (U9 p / (p + 1 - U9 p)) ^ 2)
      (fun p _ => by linarith [hb0 p])
      fun p hp => by
        have := bterm_le_of (rpow9_le_U hp).1 (by linarith [(rpow9_le_U hp).2])
        linarith).trans ?_
    rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_singleton]
    norm_num [U9]
  have h := prod_split_le (f := fun p => 1 + bterm (1 / 9) p) (M := M) (P0 := 30) (A := 1.3258)
    (τ := 0.1038) odd_primes_lt_30 (fun p _ => by linarith [hb0 p]) hT2 hA ?_ (by norm_num)
    (by norm_num)
  · exact h.trans (by norm_num)
  · have hb : ∀ n ∈ Ico 30 M, (1 + bterm (1 / 9) n) - 1 ≤
        (n : ℝ) ^ (-(2 - 2 * ((1 : ℝ) / 9))) / (1 - 0.0487) ^ 2 := fun n hn => by
      rw [add_sub_cancel_left]
      exact bterm_le_tail (by norm_num) (P0 := 30) (by norm_num) (mem_Ico.1 hn).1
        (by exact_mod_cast rpow9_30) (by norm_num)
    refine (sum_le_sum hb).trans ?_
    rw [← sum_div, div_le_iff₀ (by norm_num)]
    have := tail9_b M
    linarith

end TernaryGoldbach.MinorArcs
