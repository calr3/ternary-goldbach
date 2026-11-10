import TernaryGoldbach.MinorArcs.G2Numerics
import TernaryGoldbach.Prelim.LiouvilleBound

variable [Fact TernaryGoldbach.PlattGRH]

/-!
# [H, Lemma 5.1.2] for `v = 2` from a bound on `∑ μ(n)/n`

`|g₂(x)| ≤ 0.513/(log x)² + 528 (1 + log x)²/x` for `x > 1` (`abs_g2_le_large`).

Proof (a version of [H]'s, with cruder constants):
* `g₂(x) = ∑_{d ≤ x} μ(d) f(d)² S_d(x/d)²` ([H, (5.20)], `g2_eq_sum_moebius`);
* `S_d(M) = ∑_{a ≤ M} H_d(a) m(M/a)` with `H_d ≥ 0` multiplicative (`Sd_eq`);
* `|m(x/u)| ≤ 0.14 u^{1/9}/log x + √(2u/x)` (`abs_m_le`): `|m(y)| ≤ 0.14/log y`
  for `y ≥ 11815` (`abs_m_le_014`, `Prelim/MoebiusProfile.lean`) with Rankin's
  `log x/log(x/u) ≤ u^{1/9}` for `x/u ≥ 11815`, and the kernel-checked `|m(y)| ≤ √(2/y)`
  (`Prelim/SmallMoebius.lean`) for `y < 11815`;
* the Euler products of `G2Euler.lean`, evaluated in `G2Numerics.lean`.
-/

open Real Finset
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs

omit [Fact TernaryGoldbach.PlattGRH] in
theorem log_11815_ge9 : 9 ≤ Real.log 11815 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have e : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc Real.exp 1 ^ 9 ≤ (2.7182818286 : ℝ) ^ 9 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 9
    _ ≤ 11815 := by norm_num

/-- **`|m(x/u)| ≤ 0.14 u^{1/9}/log x + √2 √u/√x`** for `1 ≤ u ≤ x`, `x > 1`. -/
theorem abs_m_le {x : ℝ} (hx : 1 < x) {u : ℕ} (hu : 1 ≤ u) (hux : (u : ℝ) ≤ x) :
    |∑ n ∈ Icc 1 ⌊x / u⌋₊, (μ n : ℝ) / n| ≤
      0.14 * (u : ℝ) ^ ((1 : ℝ) / 9) / Real.log x + √2 * √(u : ℝ) / √x := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hy1 : 1 ≤ x / u := by rw [le_div_iff₀ hu0]; linarith
  have hA0 : 0 ≤ 0.14 * (u : ℝ) ^ ((1 : ℝ) / 9) / Real.log x := by positivity
  have hB0 : 0 ≤ √2 * √(u : ℝ) / √x := by positivity
  by_cases h : 11815 ≤ x / u
  · have hR := TernaryGoldbach.Prelim.abs_m_le_014 h
    have hw : 9 ≤ Real.log (x / u) := le_trans log_11815_ge9 (Real.log_le_log (by norm_num) h)
    have hv : 0 ≤ Real.log u := Real.log_natCast_nonneg u
    have hsplit : Real.log x = Real.log u + Real.log (x / u) := by
      rw [Real.log_div hx0.ne' hu0.ne']; ring
    have hexp : 1 + Real.log u / 9 ≤ (u : ℝ) ^ ((1 : ℝ) / 9) := by
      rw [Real.rpow_def_of_pos hu0]
      have := Real.add_one_le_exp (Real.log u * (1 / 9))
      linarith
    have key : Real.log x ≤ (u : ℝ) ^ ((1 : ℝ) / 9) * Real.log (x / u) := by
      rw [hsplit]
      have : (1 + Real.log u / 9) * Real.log (x / u) ≤
          (u : ℝ) ^ ((1 : ℝ) / 9) * Real.log (x / u) :=
        mul_le_mul_of_nonneg_right hexp (by linarith)
      nlinarith [mul_nonneg hv (by linarith : (0 : ℝ) ≤ Real.log (x / u) - 9)]
    have hw0 : 0 < Real.log (x / u) := by linarith
    calc _ ≤ 0.14 / Real.log (x / u) := hR
      _ ≤ 0.14 * (u : ℝ) ^ ((1 : ℝ) / 9) / Real.log x := by
        rw [div_le_div_iff₀ hw0 hlx]
        have := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 0.14)
        linarith
      _ ≤ _ := le_add_of_nonneg_right hB0
  · push Not at h
    have hm := TernaryGoldbach.Prelim.m_sqrt hy1 h
    calc _ ≤ √2 / √(x / u) := hm
      _ = √2 * √(u : ℝ) / √x := by
        rw [Real.sqrt_div hx0.le, div_div_eq_mul_div]
      _ ≤ _ := le_add_of_nonneg_left hA0

/-- `P_s(d, A) = ∑_{a ≤ A} H_d(a) a^s`. -/
noncomputable def PS (s : ℝ) (d A : ℕ) : ℝ := ∑ a ∈ Icc 1 A, Hd d a * (a : ℝ) ^ s

/-- **`|S_d(N/d)| ≤ 0.14 d^{1/9} P_{1/9}(d)/log x + √2 √d P_{1/2}(d)/√x`**. -/
theorem abs_Sd_le {x : ℝ} (hx : 1 < x) {d : ℕ} (hd1 : 1 ≤ d) :
    |Sd d (⌊x⌋₊ / d)| ≤ 0.14 * (d : ℝ) ^ ((1 : ℝ) / 9) / Real.log x * PS (1 / 9) d (⌊x⌋₊ / d) +
      √2 * √(d : ℝ) / √x * PS (1 / 2) d (⌊x⌋₊ / d) := by
  have hx0 : 0 < x := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  rw [Sd_eq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ a ∈ Icc 1 (⌊x⌋₊ / d),
      |Hd d a * ∑ b ∈ Icc 1 (⌊x⌋₊ / d / a), (μ b : ℝ) / b| ≤
        0.14 * (d : ℝ) ^ ((1 : ℝ) / 9) / Real.log x * (Hd d a * (a : ℝ) ^ ((1 : ℝ) / 9)) +
        √2 * √(d : ℝ) / √x * (Hd d a * (a : ℝ) ^ ((1 : ℝ) / 2)) := by
    intro a ha
    have ha1 := (mem_Icc.1 ha).1
    have haN := (mem_Icc.1 ha).2
    have hda : d * a ≤ ⌊x⌋₊ := by
      rw [Nat.le_div_iff_mul_le hd1] at haN; rw [mul_comm]; exact haN
    have hu1 : 1 ≤ d * a := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have hux : ((d * a : ℕ) : ℝ) ≤ x :=
      (by exact_mod_cast hda : ((d * a : ℕ) : ℝ) ≤ ⌊x⌋₊).trans (Nat.floor_le hx0.le)
    have hfl : ⌊x⌋₊ / d / a = ⌊x / ((d * a : ℕ) : ℝ)⌋₊ := by
      rw [Nat.div_div_eq_div_mul, Nat.floor_div_natCast]
    have hm := abs_m_le hx hu1 hux
    rw [← hfl] at hm
    rw [abs_mul, abs_of_nonneg (Hd_nonneg d a)]
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have e1 : ((d * a : ℕ) : ℝ) ^ ((1 : ℝ) / 9) =
        (d : ℝ) ^ ((1 : ℝ) / 9) * (a : ℝ) ^ ((1 : ℝ) / 9) := by
      push_cast; exact Real.mul_rpow hd0.le ha0
    have e2 : √((d * a : ℕ) : ℝ) = √(d : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2) := by
      push_cast; rw [Real.sqrt_mul hd0.le, Real.sqrt_eq_rpow (a : ℝ)]
    rw [e1, e2] at hm
    calc Hd d a * |∑ b ∈ Icc 1 (⌊x⌋₊ / d / a), (μ b : ℝ) / b|
        ≤ Hd d a * (0.14 * ((d : ℝ) ^ ((1 : ℝ) / 9) * (a : ℝ) ^ ((1 : ℝ) / 9)) / Real.log x +
          √2 * (√(d : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2)) / √x) :=
          mul_le_mul_of_nonneg_left hm (Hd_nonneg d a)
      _ = _ := by ring
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  rfl

omit [Fact TernaryGoldbach.PlattGRH] in
theorem rho_prod_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) (d : ℕ) :
    0 ≤ ∏ p ∈ d.primeFactors, rho s p :=
  prod_nonneg fun p hp => by
    linarith [one_le_rho hs0 hs1 (Nat.prime_of_mem_primeFactors hp).two_le]

omit [Fact TernaryGoldbach.PlattGRH] in
theorem PS9_le {d : ℕ} (hd : Odd d) (A : ℕ) :
    PS (1 / 9) d A ≤ 2.9733 * ∏ p ∈ d.primeFactors, rho (1 / 9) p := by
  have h := sum_Hd_rpow_le hd (s := 1 / 9) (by norm_num) (by norm_num) A
  have hl0 : 0 ≤ ∏ p ∈ (Nat.primesBelow (A + 1)).filter (· ≠ 2), ell (1 / 9) p :=
    prod_nonneg fun p hp => by
      linarith [one_le_ell (s := 1 / 9) (by norm_num)
        (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le]
  have hr0 := rho_prod_nonneg (1 / 9) (by norm_num) (by norm_num) d
  calc PS (1 / 9) d A ≤ _ := h
    _ ≤ 2.175 * 1.367 * ∏ p ∈ d.primeFactors, rho (1 / 9) p :=
        mul_le_mul_of_nonneg_right (mul_le_mul cfac9_two (prod_ell9_le (A + 1)) hl0
          (by norm_num)) hr0
    _ ≤ 2.9733 * ∏ p ∈ d.primeFactors, rho (1 / 9) p :=
        mul_le_mul_of_nonneg_right (by norm_num) hr0

omit [Fact TernaryGoldbach.PlattGRH] in
theorem PSh_le {d : ℕ} (hd : Odd d) (A : ℕ) :
    PS (1 / 2) d A ≤ 11.4874 * ∏ p ∈ d.primeFactors, rho (1 / 2) p := by
  have h := sum_Hd_rpow_le hd (s := 1 / 2) (by norm_num) (by norm_num) A
  have hl0 : 0 ≤ ∏ p ∈ (Nat.primesBelow (A + 1)).filter (· ≠ 2), ell (1 / 2) p :=
    prod_nonneg fun p hp => by
      linarith [one_le_ell (s := 1 / 2) (by norm_num)
        (Nat.mem_primesBelow.1 (mem_filter.1 hp).1).2.two_le]
  have hr0 := rho_prod_nonneg (1 / 2) (by norm_num) (by norm_num) d
  calc PS (1 / 2) d A ≤ _ := h
    _ ≤ 3.4148 * 3.364 * ∏ p ∈ d.primeFactors, rho (1 / 2) p :=
        mul_le_mul_of_nonneg_right (mul_le_mul cfac2_two (prod_ellh_le (A + 1)) hl0
          (by norm_num)) hr0
    _ ≤ 11.4874 * ∏ p ∈ d.primeFactors, rho (1 / 2) p :=
        mul_le_mul_of_nonneg_right (by norm_num) hr0

/-- One term of `∑_d f(d)² S_d²`. -/
theorem fo_sq_Sd_sq_le {x : ℝ} (hx : 1 < x) {d : ℕ} (hd1 : 1 ≤ d) :
    fo d ^ 2 * Sd d (⌊x⌋₊ / d) ^ 2 ≤
      0.34655 / Real.log x ^ 2 * gmain (1 / 9) d + 527.85 / x * gsq d := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hg1 := gmain_nonneg (1 / 9) d
  have hg2 := gsq_nonneg d
  rcases Nat.even_or_odd d with he | ho
  · have : fo d = 0 := by simp [fo, Nat.not_odd_iff_even.2 he]
    rw [this]
    have : 0 ≤ 0.34655 / Real.log x ^ 2 * gmain (1 / 9) d + 527.85 / x * gsq d := by positivity
    simpa using this
  have hS := abs_Sd_le hx hd1
  set A := ⌊x⌋₊ / d
  have hP1 := PS9_le ho A
  have hP2 := PSh_le ho A
  set R1 := ∏ p ∈ d.primeFactors, rho (1 / 9) p
  set R2 := ∏ p ∈ d.primeFactors, rho (1 / 2) p
  set α := 0.14 * (d : ℝ) ^ ((1 : ℝ) / 9) / Real.log x * (2.9733 * R1) with hα
  set β := √2 * √(d : ℝ) / √x * (11.4874 * R2) with hβ
  have hab : |Sd d A| ≤ α + β :=
    hS.trans (add_le_add (mul_le_mul_of_nonneg_left hP1 (by positivity))
      (mul_le_mul_of_nonneg_left hP2 (by positivity)))
  have hsq : Sd d A ^ 2 ≤ 2 * α ^ 2 + 2 * β ^ 2 := by
    calc Sd d A ^ 2 = |Sd d A| ^ 2 := (sq_abs _).symm
      _ ≤ (α + β) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hab 2
      _ ≤ 2 * α ^ 2 + 2 * β ^ 2 := by nlinarith [sq_nonneg (α - β)]
  have hβ2 : β ^ 2 = 2 * d / x * (11.4874 * R2) ^ 2 := by
    rw [hβ, mul_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt hx0.le]
  calc fo d ^ 2 * Sd d A ^ 2 ≤ fo d ^ 2 * (2 * α ^ 2 + 2 * β ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = 2 * (0.14 * 2.9733) ^ 2 / Real.log x ^ 2 * gmain (1 / 9) d +
        2 * (2 * 11.4874 ^ 2) / x * gsq d := by
        rw [hβ2, hα, gmain, gsq_apply]
        field_simp
        ring
    _ ≤ 0.34655 / Real.log x ^ 2 * gmain (1 / 9) d + 527.85 / x * gsq d := by
        gcongr
        · norm_num
        · norm_num

/-- **[H, Lemma 5.1.2] (`v = 2`, our constants)**: `|g₂(x)| ≤ 0.513/(log x)² + 528 (1 + log x)²/x`
for `x > 1`. -/
theorem abs_g2_le_large {x : ℝ} (hx : 1 < x) :
    |g2 x| ≤ 0.513 / Real.log x ^ 2 + 528 * (1 + Real.log x) ^ 2 / x := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx.le)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hlogN0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlogN : Real.log N ≤ Real.log x := Real.log_le_log (by exact_mod_cast hN1) hNx
  refine (abs_g2_le_sum x).trans ?_
  refine (sum_le_sum fun d hd => fo_sq_Sd_sq_le hx (mem_Icc.1 hd).1).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have h1 : ∑ d ∈ Icc 1 N, gmain (1 / 9) d ≤ 1.48 :=
    (sum_d_main_le (by norm_num) N).trans (prod_bterm9_le (N + 1))
  have h2 : ∑ d ∈ Icc 1 N, gsq d ≤ (1 + Real.log x) ^ 2 :=
    (sum_d_sqrt_le N).trans (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  calc 0.34655 / Real.log x ^ 2 * ∑ d ∈ Icc 1 N, gmain (1 / 9) d +
        527.85 / x * ∑ d ∈ Icc 1 N, gsq d
      ≤ 0.34655 / Real.log x ^ 2 * 1.48 + 527.85 / x * (1 + Real.log x) ^ 2 := by
        gcongr
    _ ≤ 0.513 / Real.log x ^ 2 + 528 * (1 + Real.log x) ^ 2 / x := by
        have e1 : 0.34655 / Real.log x ^ 2 * 1.48 = 0.512894 / Real.log x ^ 2 := by ring
        have e2 : 527.85 / x * (1 + Real.log x) ^ 2 = 527.85 * (1 + Real.log x) ^ 2 / x := by ring
        rw [e1, e2]
        gcongr
        · norm_num
        · norm_num

end TernaryGoldbach.MinorArcs
