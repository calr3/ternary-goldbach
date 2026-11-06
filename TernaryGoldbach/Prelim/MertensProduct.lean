import TernaryGoldbach.Prelim.LambdaMu
import TernaryGoldbach.Prelim.PNTMertens
import TernaryGoldbach.Prelim.SmallMertensProd

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# [H, Lemma C.2.2]: `q/φ(q) < e^γ log log r + 2.50637/log log r`

Rosser–Schoenfeld's bound [RS62, Thm. 15], proved here from
* Mertens' second theorem in the form `∑_{d ≤ x} Λ(d)/(d log d) = log log x + γ + E₂Λ(x)` with
  `E₂Λ(x) = E₁Λ(x)/log x − ∫_x^∞ E₁Λ(t)/(t log² t) dt` (ported from PNT+, `Prelim/PNTMertens.lean`);
* `|E₂Λ(x)| ≤ 2D/log x` when `E₁Λ` stays within `D` of `E₁Λ(x)` on `[x, ∞)`, and `D = O(1/log² x)`
  by summation by parts from `theta_explicit` (`|θ(n) − n| < n/log³ n + ε_pl(n) n`, `Prelim/ThetaExplicit.lean`;
  the plateau adds `P(M) = 3.7·10⁻⁷` to `D` while `log M < 20000`);
* `log ∏_{p ≤ x} p/(p−1) ≤ ∑_{d ≤ x} Λ(d)/(d log d) + 3/⌊√x⌋` (the log series);
* hence `∏_{p ≤ x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)` for `x ≥ 10¹²` (`F_large`);
* for `10⁵ ≤ x < 10¹²` the same argument, with `E₂Λ` bounded by the variation of
  `∑ Λ(n)/(n log n) − log log n` (`E2_var`, `E2_le_bin`: summation by parts against `ψ(n) − n` with
  the envelope `cE`, i.e. the tables below `5·10⁷` and `psi_two_sided` above) and the
  θ bounds of `theta_small_two_sided`, `thetaN_sieve`, `thetaN_close_cB` (`F_mid`), and the
  sharper prime-power tail `7/(6⌊√x⌋)` (`logF_le'`); for primes `5 ≤ x ≤ 10⁵` the kernel
  (`Prelim/SmallMertensProd.lean`);
* the exchange argument: `q/φ(q) ≤ ∏_{p ≤ p_k} p/(p−1)` and `p_1 ⋯ p_k ≤ q` for `k = ω(q)`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens

/-- `|E₂Λ(x)| ≤ 2D/log x` if `E₁Λ` stays within `D` of a constant on `[x, ∞)`. -/
theorem E2_le_of {x c D : ℝ} (hx : 2 ≤ x) (h : ∀ t, x < t → |E₁Λ t - c| ≤ D)
    (h0 : |E₁Λ x - c| ≤ D) : |E₂Λ x| ≤ 2 * D / Real.log x := by
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  rw [E₂Λ.eq hx]
  have hup : ∫ t in Set.Ioi x, E₁Λ t / (t * Real.log t ^ 2) ≤ (c + D) / Real.log x := by
    rw [← integ_div_mul_log_sq (c + D) hx]
    apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
      (integrable_const_div_mul_log_sq (c + D) hx) measurableSet_Ioi
    intro t ht
    have ht' : x < t := ht
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have ht0 : 0 < t := by linarith
    have := (abs_le.1 (h t ht')).2
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hlo : (c - D) / Real.log x ≤ ∫ t in Set.Ioi x, E₁Λ t / (t * Real.log t ^ 2) := by
    rw [← integ_div_mul_log_sq (c - D) hx]
    apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (c - D) hx)
      (integrable_E₁Λ_div_mul_log_sq hx) measurableSet_Ioi
    intro t ht
    have ht' : x < t := ht
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have ht0 : 0 < t := by linarith
    have := (abs_le.1 (h t ht')).1
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h1 : E₁Λ x / Real.log x ≤ (c + D) / Real.log x :=
    div_le_div_of_nonneg_right (by linarith [(abs_le.1 h0).2]) hl.le
  have h2 : (c - D) / Real.log x ≤ E₁Λ x / Real.log x :=
    div_le_div_of_nonneg_right (by linarith [(abs_le.1 h0).1]) hl.le
  have e1 : (c + D) / Real.log x - (c - D) / Real.log x = 2 * D / Real.log x := by ring
  rw [abs_le]; constructor <;> linarith

/-- `|ψ(n) − n| ≤ n/log³ n + ε_pl(n) n + 7.04 √n` for `n ≥ 10¹²`. -/
theorem psi_err {n : ℕ} (hn : 1000000000000 ≤ n) :
    |psiN n - n| ≤ n / Real.log n ^ 3 + epl n * n + 7.04 * √(n : ℝ) := by
  have h1 := psi_upper_of hn (psi_bounds _).1
  have h2 := (abs_lt.1 (thetaN_large hn)).1
  have h3 := thetaN_le_psiN n
  have h4 := Real.sqrt_nonneg (n : ℝ)
  rw [abs_le]; constructor <;> linarith

/-- `∑_{a < n < b} 1/(n+1) ≤ log b − log(a+1)`. -/
theorem sum_inv_succ_le {a b : ℕ} (hab : a < b) :
    ∑ n ∈ Ioo a b, (1 : ℝ) / (n + 1) ≤ Real.log b - Real.log (a + 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h | h
    · rw [Ioo_succ_insert h, sum_insert (by simp)]
      have ih := ih h
      have hb : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
      have hl := Real.one_sub_inv_le_log_of_pos (x := ((b : ℝ) + 1) / b) (by positivity)
      rw [Real.log_div (by positivity) hb.ne'] at hl
      have e : 1 - (((b : ℝ) + 1) / b)⁻¹ = 1 / (b + 1) := by field_simp; ring
      rw [e] at hl
      push_cast
      linarith
    · have : a = b := by omega
      subst this
      rw [Ioo_self_succ]
      push_cast; simp

/-- The Abel summation term, centred: `|ψ(n)(1/n − 1/(n+1)) − 1/(n+1)| ≤ …`. -/
theorem abel_term_err {n : ℕ} (hn : 1000000000000 ≤ n) :
    |psiN n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) - 1 / ((n : ℝ) + 1)| ≤
      1 / ((n + 1) * Real.log n ^ 3) + 7.04 * (1 / (√(n : ℝ) * (n + 1))) + epl n / ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have e : psiN n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) - 1 / ((n : ℝ) + 1) =
      (psiN n - n) * (1 / (n * (n + 1))) := by
    push_cast; field_simp; ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n * (n + 1)))]
  have h := mul_le_mul_of_nonneg_right (psi_err hn) (by positivity : (0 : ℝ) ≤ 1 / (n * (n + 1)))
  have e2 : ((n : ℝ) / Real.log n ^ 3 + epl n * n + 7.04 * √(n : ℝ)) * (1 / (n * (n + 1))) =
      1 / ((n + 1) * Real.log n ^ 3) + 7.04 * (1 / (√(n : ℝ) * (n + 1))) + epl n / ((n : ℝ) + 1) := by
    have : √(n : ℝ) * (1 / (n * (n + 1))) = 1 / (√(n : ℝ) * (n + 1)) := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), ← mul_assoc, hss]; ring
    have e3 : epl n * n * (1 / (n * (n + 1))) = epl n / ((n : ℝ) + 1) := by field_simp
    rw [add_mul, add_mul, mul_assoc (7.04 : ℝ), this, e3]; field_simp; ring
  linarith

/-- `E₁Λ` varies by at most `D(M)` on `[M, ∞)`, `M ≥ 10¹²`. -/
theorem E1_diff {M : ℕ} (hM : 1000000000000 ≤ M) {t : ℝ} (ht : (M : ℝ) ≤ t) :
    |E₁Λ t - E₁Λ M| ≤ 3 / M + 2 * (1 / Real.log M ^ 3 + 7.04 / √(M : ℝ)) +
      (2 / Real.log M ^ 2 + 14.08 / √(M : ℝ)) + Pth M := by
  have hPth := Pth_nonneg (M : ℝ)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hLM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hsM : 0 < √(M : ℝ) := Real.sqrt_pos.2 hM0
  set N := ⌊t⌋₊ with hN
  have hMN : M ≤ N := Nat.le_floor ht
  have ht0 : 0 < t := lt_of_lt_of_le hM0 ht
  have hNt : (N : ℝ) ≤ t := Nat.floor_le ht0.le
  have htN : t < N + 1 := Nat.lt_floor_add_one t
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 (by exact_mod_cast hMN)
  have hlt1 : Real.log N ≤ Real.log t := Real.log_le_log hN0 hNt
  have hlt2 : Real.log t ≤ Real.log (N + 1) := Real.log_le_log ht0 htN.le
  have hdiff : E₁Λ t - E₁Λ M = ∑ n ∈ Ioc M N, (Λ n : ℝ) * (fun n : ℕ => 1 / (n : ℝ)) n -
      Real.log t + Real.log M := by
    simp only [E₁Λ, Nat.floor_natCast, mul_one_div]
    rw [← sum_Ioc_consecutive _ (Nat.zero_le M) hMN]; ring
  -- `log(M+1) − log M ≤ 1/M`, `log(M+2) − log M ≤ 2/M`
  have hl1 : Real.log (M + 1) - Real.log M ≤ 1 / M := by
    have := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 1) / M) (by positivity)
    rw [Real.log_div (by positivity) hM0.ne'] at this
    have e : ((M : ℝ) + 1) / M - 1 = 1 / M := by field_simp; ring
    linarith
  have hl2 : Real.log (M + 2) - Real.log M ≤ 2 / M := by
    have := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 2) / M) (by positivity)
    rw [Real.log_div (by positivity) hM0.ne'] at this
    have e : ((M : ℝ) + 2) / M - 1 = 2 / M := by field_simp; ring
    linarith
  have hlogMM : Real.log M ≤ Real.log (M + 1) := Real.log_le_log hM0 (by linarith)
  have hpos : 0 ≤ 1 / Real.log M ^ 3 + 7.04 / √(M : ℝ) := by positivity
  have hpos2 : 0 ≤ 2 / Real.log M ^ 2 + 14.08 / √(M : ℝ) := by positivity
  rcases eq_or_lt_of_le hMN with hEq | hlt
  · -- `N = M`
    rw [hdiff, ← hEq, Ioc_self, sum_empty]
    have : Real.log t ≤ Real.log (M + 1) := by rw [hEq]; exact hlt2
    have h3 : Real.log M ≤ Real.log t := by rw [hEq]; exact hlt1
    have h30 : 0 ≤ 3 / (M : ℝ) := by positivity
    rw [abs_le]; constructor
    · have : 1 / (M : ℝ) ≤ 3 / M := div_le_div_of_nonneg_right (by norm_num) hM0.le
      linarith
    · linarith
  -- `M < N`: summation by parts
  rw [hdiff, abel_Ioc _ M N hlt]
  -- interior
  set Se := ∑ n ∈ Ioo M N, epl n / ((n : ℝ) + 1) with hSe
  have hint : |∑ n ∈ Ioo M N, (psiN n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) - 1 / ((n : ℝ) + 1))| ≤
      2 / Real.log M ^ 2 + 14.08 / √(M : ℝ) + Se := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun n hn => abel_term_err (n := n)
      (by have := (mem_Ioo.1 hn).1; omega)).trans ?_
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← hSe]
    have h1 := sum_inv_log_cube_le (a := M) (by omega) hlt
    have h2 := sum_inv_sqrt_le hlt
    have h1' : 2 / Real.log ((M : ℝ) + 1) ^ 2 ≤ 2 / Real.log M ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ hLM.le hlogMM 2)
    have h2' : 2 / √((M : ℝ) + 1) ≤ 2 / √(M : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hsM (Real.sqrt_le_sqrt (by linarith))
    have h3 : 0 ≤ 2 / Real.log (N : ℝ) ^ 2 := by positivity
    have h4 : 0 ≤ 2 / √(N : ℝ) := by positivity
    have e : (14.08 : ℝ) / √(M : ℝ) = 7.04 * (2 / √(M : ℝ)) := by ring
    linarith
  rw [sum_sub_distrib] at hint
  have hH1 := sum_inv_succ_ge hlt
  have hH2 := sum_inv_succ_le hlt
  -- boundary terms
  have heN := psi_err (n := N) (by omega)
  have heM := psi_err (n := M) hM
  have hbN : |psiN N * (1 / (N : ℝ)) - 1| ≤ 1 / Real.log M ^ 3 + 7.04 / √(M : ℝ) + epl N := by
    have e : psiN N * (1 / (N : ℝ)) - 1 = (psiN N - N) * (1 / (N : ℝ)) := by field_simp
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN0
    have hssN : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN0.le
    have hLN : Real.log M ≤ Real.log N := Real.log_le_log hM0 (by exact_mod_cast hMN)
    calc |psiN N - N| * (1 / (N : ℝ)) ≤ (N / Real.log N ^ 3 + epl N * N + 7.04 * √(N : ℝ)) * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right heN (by positivity)
      _ = 1 / Real.log N ^ 3 + 7.04 / √(N : ℝ) + epl N := by
          have a : (N : ℝ) / Real.log N ^ 3 * (1 / N) = 1 / Real.log N ^ 3 := by field_simp
          have b : √(N : ℝ) * (1 / N) = 1 / √(N : ℝ) := by
            rw [mul_one_div, div_eq_div_iff hN0.ne' hsN.ne', one_mul, hssN]
          have c : epl N * N * (1 / (N : ℝ)) = epl N := by field_simp
          rw [add_mul, add_mul, a, mul_assoc (7.04 : ℝ), b, c]; ring
      _ ≤ 1 / Real.log M ^ 3 + 7.04 / √(M : ℝ) + epl N := by
          gcongr
  have hbM : |psiN M * (1 / ((M + 1 : ℕ) : ℝ)) - (1 - 1 / ((M : ℝ) + 1))| ≤
      1 / Real.log M ^ 3 + 7.04 / √(M : ℝ) + epl M := by
    have e : psiN M * (1 / ((M + 1 : ℕ) : ℝ)) - (1 - 1 / ((M : ℝ) + 1)) =
        (psiN M - M) * (1 / ((M : ℝ) + 1)) := by push_cast; field_simp; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1))]
    have hssM : √(M : ℝ) * √(M : ℝ) = M := Real.mul_self_sqrt hM0.le
    have hepM := mul_nonneg (epl_nonneg (M : ℝ)) hM0.le
    calc |psiN M - M| * (1 / ((M : ℝ) + 1)) ≤
          (M / Real.log M ^ 3 + epl M * M + 7.04 * √(M : ℝ)) * (1 / (M : ℝ)) := by
          apply mul_le_mul heM (div_le_div_of_nonneg_left (by norm_num) hM0 (by linarith))
            (by positivity) (by positivity)
      _ = 1 / Real.log M ^ 3 + 7.04 / √(M : ℝ) + epl M := by
          have a : (M : ℝ) / Real.log M ^ 3 * (1 / M) = 1 / Real.log M ^ 3 := by field_simp
          have b : √(M : ℝ) * (1 / M) = 1 / √(M : ℝ) := by
            rw [mul_one_div, div_eq_div_iff hM0.ne' hsM.ne', one_mul, hssM]
          have c : epl M * M * (1 / (M : ℝ)) = epl M := by field_simp
          rw [add_mul, add_mul, a, mul_assoc (7.04 : ℝ), b, c]; ring
  have hM1 : 1 / ((M : ℝ) + 1) ≤ 1 / M := div_le_div_of_nonneg_left (by norm_num) hM0 (by linarith)
  have hM1' : 0 ≤ 1 / ((M : ℝ) + 1) := by positivity
  have hlN : Real.log (N + 1) - Real.log t ≥ 0 := by linarith
  have hP := epl_total_le (M := M) (N := N) (by omega) hMN
  rw [← hSe] at hP
  rw [abs_le] at hint hbN hbM ⊢
  have e3 : (3 : ℝ) / M = 1 / M + 2 / M := by ring
  constructor <;> linarith [hint.1, hint.2, hbN.1, hbN.2, hbM.1, hbM.2]

/-- `∑_{a < n ≤ b} 1/(n(n−1)) ≤ 1/a − 1/b`. -/
theorem sum_inv_mul_pred_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, (1 : ℝ) / (n * (n - 1)) ≤ 1 / a - 1 / b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · have hab' : a ≤ b := by omega
      rw [sum_Ioc_succ_top hab']
      have := ih hab'
      have hb : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
      have e : (1 : ℝ) / (((b : ℝ) + 1) * ((b : ℝ) + 1 - 1)) = 1 / b - 1 / (b + 1) := by
        rw [show (b : ℝ) + 1 - 1 = b by ring]; field_simp; ring
      push_cast; rw [e]; linarith
    · have : a = b + 1 := by omega
      subst this; simp

/-- The tail of `−log(1 − 1/p)` beyond the prime powers `≤ x`. -/
theorem neg_log_le (p K : ℕ) (hp : 2 ≤ p) :
    -Real.log (1 - 1 / (p : ℝ)) ≤ ∑ i ∈ range K, (1 / (p : ℝ)) ^ (i + 1) / (i + 1) +
      (1 / (p : ℝ)) ^ (K + 1) / (1 - 1 / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hy : |1 / (p : ℝ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hp0]; exact_mod_cast (by omega : 1 < p)
  have h := Real.abs_log_sub_add_sum_range_le hy K
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / p)] at h
  have := (abs_le.1 h).1
  linarith

/-- `log ∏_{p ≤ x} p/(p−1) ≤ ∑_{d ≤ x} Λ(d)/(d log d) + 3/⌊√x⌋`. -/
theorem logF_le (x : ℕ) (hx : 4 ≤ x) :
    ∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log ((p : ℝ) / (p - 1)) ≤
      ∑ d ∈ Ioc 0 x, (Λ d : ℝ) / (d * Real.log d) + 3 / Nat.sqrt x := by
  set P := (Icc 1 x).filter Nat.Prime with hP
  set s := Nat.sqrt x with hs
  have hs1 : 2 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hss : s * s ≤ x := Nat.sqrt_le x
  have hss' : x < (s + 1) * (s + 1) := Nat.lt_succ_sqrt x
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  set K : ℕ → ℕ := fun p => Nat.log p x with hK
  -- pointwise
  have hpt : ∀ p ∈ P, Real.log ((p : ℝ) / (p - 1)) ≤
      ∑ i ∈ range (K p), (1 / (p : ℝ)) ^ (i + 1) / (i + 1) +
        (1 / (p : ℝ)) ^ (K p + 1) / (1 - 1 / p) := by
    intro p hp
    have hp2 := (mem_filter.1 hp).2.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have e : Real.log ((p : ℝ) / (p - 1)) = -Real.log (1 - 1 / (p : ℝ)) := by
      rw [← Real.log_inv]; congr 1; field_simp
    rw [e]; exact neg_log_le p (K p) hp2
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  -- main part: reindex by prime powers
  have hmain : ∑ p ∈ P, ∑ i ∈ range (K p), (1 / (p : ℝ)) ^ (i + 1) / (i + 1) ≤
      ∑ d ∈ Ioc 0 x, (Λ d : ℝ) / (d * Real.log d) := by
    rw [sum_sigma']
    set S := P.sigma (fun p => range (K p)) with hS
    set f : ℕ → ℝ := fun d => (Λ d : ℝ) / (d * Real.log d) with hf
    set g : (Σ _ : ℕ, ℕ) → ℕ := fun σ => σ.1 ^ (σ.2 + 1) with hg
    have hinj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b := by
      rintro ⟨p, i⟩ h1 ⟨q, j⟩ h2 he
      have hp := (mem_filter.1 (mem_sigma.1 h1).1).2
      have hq := (mem_filter.1 (mem_sigma.1 h2).1).2
      obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj hp hq he
      rfl
    have hval : ∀ σ ∈ S, (1 / (σ.1 : ℝ)) ^ (σ.2 + 1) / (σ.2 + 1) = f (g σ) := by
      rintro ⟨p, i⟩ hσ
      have hp := (mem_filter.1 (mem_sigma.1 hσ).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      simp only [hf, hg]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      push_cast
      rw [Real.log_pow, one_div_pow]
      push_cast
      field_simp
    rw [sum_congr rfl hval, ← sum_image hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨⟨p, i⟩, hσ, rfl⟩ := mem_image.1 hd
      have hp := (mem_filter.1 (mem_sigma.1 hσ).1).2
      have hi := mem_range.1 (mem_sigma.1 hσ).2
      rw [mem_Ioc]
      refine ⟨pow_pos hp.pos _, ?_⟩
      calc p ^ (i + 1) ≤ p ^ (K p) := Nat.pow_le_pow_right hp.pos hi
        _ ≤ x := Nat.pow_log_le_self p (by omega)
    · intro d _ _
      have : 0 ≤ Real.log d := Real.log_natCast_nonneg d
      have : (0 : ℝ) ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      simp only [hf]
      positivity
  -- tail
  have htail : ∑ p ∈ P, (1 / (p : ℝ)) ^ (K p + 1) / (1 - 1 / p) ≤ 3 / s := by
    have hT : ∀ p ∈ P, (1 / (p : ℝ)) ^ (K p + 1) / (1 - 1 / p) ≤
        (if p ≤ s then (2 : ℝ) / x else 1 / ((p : ℝ) * (p - 1))) := by
      intro p hp
      have hpp := (mem_filter.1 hp).2
      have hp2 := hpp.two_le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
      have e : (1 / (p : ℝ)) ^ (K p + 1) / (1 - 1 / p) =
          1 / (p : ℝ) ^ (K p + 1) * (p / (p - 1)) := by
        rw [one_div_pow]
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
      rw [e]
      split_ifs with h
      · -- `p^{K+1} > x`
        have hlt : x < p ^ (K p + 1) := Nat.lt_pow_succ_log_self hpp.one_lt x
        have hlt' : (x : ℝ) < (p : ℝ) ^ (K p + 1) := by exact_mod_cast hlt
        have h2 : (p : ℝ) / (p - 1) ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]; have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
          linarith
        calc 1 / (p : ℝ) ^ (K p + 1) * (p / (p - 1)) ≤ 1 / x * 2 :=
              mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hx0 hlt'.le) h2
                (by positivity) (by positivity)
          _ = 2 / x := by ring
      · have hK1 : 1 ≤ K p := by
          rw [hK]; exact Nat.le_log_of_pow_le hpp.one_lt (by
            have := (mem_Icc.1 (mem_filter.1 hp).1).2; simpa using this)
        have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (K p + 1) := pow_le_pow_right₀ hp1.le (by omega)
        calc 1 / (p : ℝ) ^ (K p + 1) * (p / (p - 1)) ≤ 1 / (p : ℝ) ^ 2 * (p / (p - 1)) :=
              mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow)
                (by have : (0 : ℝ) < p - 1 := by linarith
                    positivity)
          _ = 1 / (p * (p - 1)) := by
              have : (p : ℝ) - 1 ≠ 0 := by linarith
              field_simp
    refine (sum_le_sum hT).trans ?_
    rw [sum_ite]
    have hA : ∑ p ∈ P.filter (fun p => p ≤ s), (2 : ℝ) / x ≤ s * (2 / x) := by
      rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (P.filter (fun p => p ≤ s)).card ≤ (Icc 1 s).card := by
        apply card_le_card
        intro p hp
        have h1 := mem_filter.1 hp
        have h2 := mem_filter.1 h1.1
        exact mem_Icc.2 ⟨(mem_Icc.1 h2.1).1, h1.2⟩
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : (P.filter (fun p => p ≤ s)).card ≤ s)
    have hB : ∑ p ∈ P.filter (fun p => ¬ p ≤ s), (1 : ℝ) / (p * (p - 1)) ≤ 1 / s - 1 / x := by
      refine le_trans ?_ (sum_inv_mul_pred_le (a := s) (b := x) (by omega) (by nlinarith))
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have h1 := mem_filter.1 hp
        have h2 := mem_filter.1 h1.1
        exact mem_Ioc.2 ⟨by omega, (mem_Icc.1 h2.1).2⟩
      · intro n hn _
        have : (1 : ℝ) ≤ n := by exact_mod_cast (by have := (mem_Ioc.1 hn).1; omega)
        have : (0 : ℝ) ≤ n - 1 := by linarith
        positivity
    have hsx : (s : ℝ) * (2 / x) ≤ 2 / s := by
      have : ((s * s : ℕ) : ℝ) ≤ x := by exact_mod_cast hss
      push_cast at this
      rw [mul_div_assoc', div_le_div_iff₀ hx0 hs0]; nlinarith
    have : (0 : ℝ) ≤ 1 / x := by positivity
    have e3 : (3 : ℝ) / s = 2 / s + 1 / s := by ring
    linarith
  linarith

/-- `e^γ < 1.95`. -/
theorem exp_gamma_lt : Real.exp Real.eulerMascheroniConstant < 1.95 := by
  have h1 : Real.exp Real.eulerMascheroniConstant < Real.exp (2 / 3) :=
    Real.exp_lt_exp.2 Real.eulerMascheroniConstant_lt_two_thirds
  have h2 : Real.exp (2 / 3) ^ 3 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h3 := Real.exp_one_lt_d9
  have h4 : 0 < Real.exp (2 / 3) := Real.exp_pos _
  have h5 : Real.exp (2 / 3) < 1.95 := by
    by_contra! h
    have : (1.95 : ℝ) ^ 3 ≤ Real.exp (2 / 3) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    have : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 := pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (by norm_num)
    nlinarith
  linarith

/-- `log x ≤ 19` at `x = 10⁸`, hence `log² x ≤ 0.0361 √x` for `x ≥ 10⁸`. -/
theorem log_sq_le_sqrt {x : ℝ} (hx : 10 ^ 8 ≤ x) : Real.log x ^ 2 ≤ 0.0361 * √x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have he4 : Real.exp ((1 / 4 : ℝ)⁻¹) ≤ 10 ^ 8 := by
    rw [show ((1 / 4 : ℝ)⁻¹) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    have := Real.exp_one_lt_d9
    calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 4
      _ ≤ 10 ^ 8 := by norm_num
  have hanti := Real.log_div_self_rpow_antitoneOn (a := 1 / 4) (by norm_num)
    (Set.mem_Ici.2 he4) (Set.mem_Ici.2 (he4.trans hx)) hx
  simp only at hanti
  have h100 : ((10 : ℝ) ^ 8) ^ (1 / 4 : ℝ) = 100 := by
    rw [show (10 : ℝ) ^ 8 = 100 ^ 4 by norm_num, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
  have hl19 : Real.log (10 ^ 8) ≤ 19 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (10 : ℝ) ^ 8 ≤ 2.7182818283 ^ 19 := by norm_num
      _ ≤ Real.exp 1 ^ 19 := pow_le_pow_left₀ (by norm_num) this.le 19
      _ = Real.exp 19 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h100] at hanti
  have hq : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hq2 : (x ^ (1 / 4 : ℝ)) ^ 2 = √x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]; norm_num
  have hL : Real.log x ≤ 0.19 * x ^ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hq] at hanti
    have h19 : Real.log (10 ^ 8) / 100 ≤ 0.19 := by
      generalize Real.log (10 ^ 8) = c at hl19 ⊢
      linarith
    have : Real.log (10 ^ 8) / 100 * x ^ (1 / 4 : ℝ) ≤ 0.19 * x ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right h19 hq.le
    linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  calc Real.log x ^ 2 ≤ (0.19 * x ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hL0 hL 2
    _ = 0.0361 * √x := by rw [mul_pow, hq2]; norm_num

/-- **[H, Lemma C.2.2]** for `x ≥ 10¹²`: `∏_{p ≤ x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)`. -/
theorem F_large {x : ℕ} (hx : 10 ^ 12 ≤ x) :
    ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) <
      Real.exp Real.eulerMascheroniConstant * Real.log (thetaN x) + 2.50637 / Real.log (thetaN x) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hxr : (10 : ℝ) ^ 8 ≤ x := by exact_mod_cast (le_trans (by norm_num) hx : 10 ^ 8 ≤ x)
  set L := Real.log x with hLdef
  have hL18 : (18 : ℝ) ≤ L := by
    have := nat_le_log (N := (x : ℝ)) (k := 18) (le_trans (by norm_num) hxr)
    exact_mod_cast this
  have hL0 : 0 < L := by linarith
  set sx := √(x : ℝ) with hsx
  have hsx0 : 0 < sx := Real.sqrt_pos.2 hx0
  have hsx2 : sx * sx = x := Real.mul_self_sqrt hx0.le
  have hsx4 : (10000 : ℝ) ≤ sx := Real.le_sqrt_of_sq_le (by linarith)
  have hL2 : L ^ 2 ≤ 0.0361 * sx := log_sq_le_sqrt hxr
  -- the product as an exponential
  have hFpos : ∀ p ∈ (Icc 1 x).filter Nat.Prime, (0 : ℝ) < (p : ℝ) / (p - 1) := by
    intro p hp
    have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.1 hp).2.one_lt
    exact div_pos (by linarith) (by linarith)
  have hlogF : Real.log (∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1))) =
      ∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log ((p : ℝ) / (p - 1)) :=
    Real.log_prod (fun p hp => (hFpos p hp).ne')
  -- `log F ≤ log L + γ + η`
  set s := Nat.sqrt x with hs
  have hs0 : (0 : ℝ) < s := by
    have : 1 ≤ s := by rw [hs, Nat.le_sqrt]; omega
    exact_mod_cast this
  have hss : sx < s + 1 := by
    have : x < (s + 1) * (s + 1) := Nat.lt_succ_sqrt x
    have : (x : ℝ) < ((s : ℝ) + 1) * (s + 1) := by exact_mod_cast this
    nlinarith
  set D := 3 / (x : ℝ) + 2 * (1 / L ^ 3 + 7.04 / sx) + (2 / L ^ 2 + 14.08 / sx) + Pth x with hD
  have hD0 : 0 ≤ D := by
    have : 0 ≤ 3 / (x : ℝ) + 2 * (1 / L ^ 3 + 7.04 / sx) + (2 / L ^ 2 + 14.08 / sx) := by positivity
    have := Pth_nonneg (x : ℝ)
    rw [hD]; linarith
  have hE2 : |E₂Λ (x : ℝ)| ≤ 2 * D / L := by
    refine E2_le_of (c := E₁Λ (x : ℝ)) (by linarith) (fun t ht => E1_diff (by omega) ht.le) ?_
    rw [sub_self, abs_zero]; exact hD0
  have hmert := sum_mangoldt_div_log_eq (x : ℝ)
  rw [Nat.floor_natCast] at hmert
  have hlF := logF_le x (by omega)
  set η := 2 * D / L + 3 / s with hη
  have hlogle : Real.log (∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1))) ≤
      Real.log L + Real.eulerMascheroniConstant + η := by
    rw [hlogF]; linarith [(abs_le.1 hE2).2]
  have hη0 : 0 ≤ η := by
    rw [hη]; exact add_nonneg (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hD0) hL0.le) (by positivity)
  -- bounds on the pieces of `η L²`
  have hLsx : L ≤ 0.0021 * sx := by nlinarith only [hL2, hL18, hL0]
  have hLL : (324 : ℝ) ≤ L ^ 2 := by nlinarith only [hL18]
  have k1 : 6 / (x : ℝ) * L ≤ 0.001 := by
    rw [← hsx2, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith only [hLsx, hsx4, hsx0]
  have k2 : 4 / L ^ 3 * L ≤ 0.0124 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : L ^ 3 = L * L ^ 2 := by ring
    rw [this]; nlinarith only [hLL, hL0]
  have k3 : 4 / L ^ 2 * L ≤ 0.2223 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith only [hL18, hL0]
  have k4 : 56.32 / sx * L ≤ 0.1183 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hsx0]; linarith only [hLsx, hsx0]
  have k5 : 3 / (s : ℝ) * L ^ 2 ≤ 0.1084 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hs0]; linarith only [hL2, hss, hsx4, hs0]
  have k6 : 1 / L ^ 3 * L ≤ 0.0031 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : L ^ 3 = L * L ^ 2 := by ring
    rw [this]; nlinarith only [hLL, hL0]
  -- `4/L + 2 P(x) L`: for `L ≤ 780`, `P(x) L ≤ 0.0275`; above, `4/L ≤ 0.0052` and `P(x) L ≤ 0.1831`
  have k37 : 4 / L ^ 2 * L + 2 * (Pth x * L) ≤ 0.3773 := by
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
    rcases le_or_gt L 780 with h | h
    · have := Pth_mul_log_le_small hx1 h
      linarith only [k3, this]
    · have := Pth_mul_log_le hx1
      have h4 : 4 / L ^ 2 * L ≤ 0.0052 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith only [h]
      linarith only [h4, this]
  have hηL : η * L ^ 2 ≤ 0.0124 + 0.1183 + 0.001 + 0.1084 + 0.3773 := by
    have e : η * L ^ 2 = 6 / (x : ℝ) * L + 4 / L ^ 3 * L + 4 / L ^ 2 * L + 56.32 / sx * L +
        3 / (s : ℝ) * L ^ 2 + 2 * (Pth x * L) := by
      rw [hη, hD]; field_simp; ring
    rw [e]; linarith only [k1, k2, k37, k4, k5]
  have hη1 : η ≤ 1 / 2 := by
    have : η * L ^ 2 ≤ 1 / 2 * L ^ 2 := by linarith only [hηL, hLL]
    exact le_of_mul_le_mul_right this (by positivity)
  -- `exp η ≤ 1 + 2η`
  have hexp : Real.exp η ≤ 1 + 2 * η := by
    have h1 : 1 - η ≤ Real.exp (-η) := by linarith [Real.add_one_le_exp (-η)]
    have h2 : Real.exp η * Real.exp (-η) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < 1 - η := by linarith
    have h4 : Real.exp η * (1 - η) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos η).le; linarith
    by_contra! hc
    have : (1 + 2 * η) * (1 - η) < Real.exp η * (1 - η) := mul_lt_mul_of_pos_right hc h3
    nlinarith only [this, h4, hη0, hη1]
  set G := Real.exp Real.eulerMascheroniConstant with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hG1 := exp_gamma_lt
  have hF : ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) ≤ G * L + 2 * (G * η * L) := by
    have hpos : 0 < ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) := prod_pos hFpos
    rw [← Real.exp_log hpos]
    calc Real.exp (Real.log (∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)))) ≤
          Real.exp (Real.log L + Real.eulerMascheroniConstant + η) := Real.exp_le_exp.2 hlogle
      _ = L * G * Real.exp η := by rw [Real.exp_add, Real.exp_add, Real.exp_log hL0]
      _ ≤ L * G * (1 + 2 * η) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = G * L + 2 * (G * η * L) := by ring
  -- `θ(x)` bounds
  have hθ := abs_lt.1 (thetaN_large (n := x) (by omega))
  set u := 1 / L ^ 3 + epl x with hu
  have hepl0 := epl_nonneg (x : ℝ)
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 5800 := by
    have h1 : 1 / L ^ 3 ≤ 1 / 5832 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := pow_le_pow_left₀ (by norm_num) hL18 3
      linarith
    have := epl_le (x : ℝ)
    rw [hu]; linarith
  have hθx : (x : ℝ) / L ^ 3 + epl x * x = x * u := by rw [hu]; ring
  rw [hθx] at hθ
  have hθ0 : 0 < thetaN x := by nlinarith only [hθ.1, hx0, hu1, hu0]
  have hlθ1 : L - 2 * u ≤ Real.log (thetaN x) := by
    have h1 : (x : ℝ) * (1 - u) ≤ thetaN x := by linarith
    have h2 : Real.log ((x : ℝ) * (1 - u)) ≤ Real.log (thetaN x) :=
      Real.log_le_log (by nlinarith only [hx0, hu1, hu0]) h1
    rw [Real.log_mul hx0.ne' (by linarith)] at h2
    have h3 := Real.one_sub_inv_le_log_of_pos (x := 1 - u) (by linarith)
    have h4 : 1 - (1 - u)⁻¹ ≥ -2 * u := by
      have hu' : (1 : ℝ) - u ≠ 0 := by linarith
      rw [ge_iff_le, show 1 - (1 - u)⁻¹ = -(u / (1 - u)) by field_simp; ring]
      have : u / (1 - u) ≤ 2 * u := by
        rw [div_le_iff₀ (by linarith)]; nlinarith only [hu0, hu1]
      linarith
    linarith
  have hlθ2 : Real.log (thetaN x) ≤ L + u := by
    have h1 : thetaN x ≤ (x : ℝ) * (1 + u) := by linarith
    have h2 := Real.log_le_log hθ0 h1
    rw [Real.log_mul hx0.ne' (by linarith)] at h2
    have h3 := Real.log_le_sub_one_of_pos (x := 1 + u) (by linarith)
    linarith
  have hlθ0 : 0 < Real.log (thetaN x) := by linarith
  have hc : 2.5 / L ≤ 2.50637 / Real.log (thetaN x) := by
    rw [div_le_div_iff₀ hL0 hlθ0]; linarith only [hlθ2, hu1, hL18]
  -- final comparison
  have hGL : G * L - 2 * (G * u) ≤ G * Real.log (thetaN x) := by
    have := mul_le_mul_of_nonneg_left hlθ1 hG0.le
    have e : G * (L - 2 * u) = G * L - 2 * (G * u) := by ring
    linarith
  have key : 2 * (G * η * L) + 2 * (G * u) < 2.5 / L := by
    rw [lt_div_iff₀ hL0]
    have hk : (2 * (G * η * L) + 2 * (G * u)) * L = 2 * (G * (η * L ^ 2)) + 2 * (G * (u * L)) := by
      ring
    have huL : u * L ≤ 0.0032 := by
      have := epl_mul_log_le (x : ℝ)
      have e : u * L = 1 / L ^ 3 * L + epl x * L := by rw [hu]; ring
      rw [e]; linarith [k6]
    have a1 : G * (η * L ^ 2) ≤ 1.95 * 0.6174 :=
      mul_le_mul hG1.le (by linarith only [hηL]) (by positivity) (by norm_num)
    have a2 : G * (u * L) ≤ 1.95 * 0.0032 :=
      mul_le_mul hG1.le huL (by positivity) (by norm_num)
    rw [hk]; linarith only [a1, a2]
  linarith only [hF, hGL, hc, key]

/-- `D(10¹⁷) ≤ 0.0014` in `E1_diff`. -/
theorem D19_le {M : ℝ} (hM : 10 ^ 17 ≤ M) :
    3 / M + 2 * (1 / Real.log M ^ 3 + 7.04 / √M) + (2 / Real.log M ^ 2 + 14.08 / √M) + Pth M ≤
      0.0014 := by
  have hM0 : 0 < M := by linarith
  have hL : (39 : ℝ) ≤ Real.log M := by
    have := nat_le_log (N := M) (k := 39) (le_trans (by norm_num) hM)
    exact_mod_cast this
  have hs : (3 * 10 ^ 8 : ℝ) ≤ √M := Real.le_sqrt_of_sq_le (by nlinarith)
  have hP := Pth_le M
  have h1 : 3 / M ≤ 3 / 10 ^ 17 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hM
  have h2 : 1 / Real.log M ^ 3 ≤ 1 / 39 ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 3)
  have h3 : 2 / Real.log M ^ 2 ≤ 2 / 39 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 2)
  have h4 : 7.04 / √M ≤ 7.04 / (3 * 10 ^ 8) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have h5 : 14.08 / √M ≤ 14.08 / (3 * 10 ^ 8) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have : (3 : ℝ) / 10 ^ 17 + 2 * (1 / 39 ^ 3 + 7.04 / (3 * 10 ^ 8)) + (2 / 39 ^ 2 + 14.08 / (3 * 10 ^ 8)) +
      3.52e-5 ≤ 0.0014 := by norm_num
  linarith

/-! ### `10⁵ ≤ x < 10¹²`: the variation of `∑ Λ(n)/(n log n) − log log n` (route D)

`E₂Λ(M) − E₂Λ(N) = −(∑_{M<n≤N} Λ(n) w(n) − (log log N − log log M))`, `w(n) = 1/(n log n)`; by
summation by parts against `ψ(n) − n` (`E2_var`) the `ψ`-errors at `n` enter with weight
`w(n) − w(n+1) ≈ 1/(n² log n)`. With `|ψ(n) − n| ≤ c(n)√n` (`c = 1` below `10⁶`, `5` up to `5·10⁷`
(`thetaN_sieve`), `cB` up to `10¹⁷`) this gives `|E₂Λ(M)| ≲ 0.0026` already at `M = 10⁵`
(`E2_le_bin`). -/

/-- `w(n) = 1/(n log n)`. -/
noncomputable def wl (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.log n)

theorem wl_nonneg (n : ℕ) : 0 ≤ wl n := by
  unfold wl; have := Real.log_natCast_nonneg n; positivity

theorem wl_diff {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ wl n - wl (n + 1) ∧
      wl n - wl (n + 1) ≤ 1 / (n * ((n : ℝ) + 1)) * (1 / Real.log n + 1 / Real.log n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hab : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  have hb : 0 < Real.log ((n : ℝ) + 1) := lt_of_lt_of_le ha hab
  have hba : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    have := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at this
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have e : wl n - wl (n + 1) = ((n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) + Real.log ((n : ℝ) + 1)) /
      (n * ((n : ℝ) + 1) * Real.log n * Real.log ((n : ℝ) + 1)) := by
    unfold wl; push_cast; field_simp; ring
  rw [e]
  have hnum : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) + Real.log ((n : ℝ) + 1) ≤
      1 + Real.log ((n : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hba hn0.le
    rw [mul_one_div_cancel hn0.ne'] at this; linarith
  constructor
  · apply div_nonneg _ (by positivity)
    have : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n := by linarith
    positivity
  · rw [div_le_iff₀ (by positivity)]
    have e2 : 1 / (n * ((n : ℝ) + 1)) * (1 / Real.log n + 1 / Real.log n ^ 2) *
        (n * ((n : ℝ) + 1) * Real.log n * Real.log ((n : ℝ) + 1)) =
        Real.log ((n : ℝ) + 1) + Real.log ((n : ℝ) + 1) / Real.log n := by
      field_simp; try ring
    rw [e2]
    have : 1 ≤ Real.log ((n : ℝ) + 1) / Real.log n := by rw [le_div_iff₀ ha]; linarith
    linarith

/-- Summation by parts for the counting function `⌊t⌋`. -/
theorem abel_id (w : ℕ → ℝ) (M N : ℕ) (hMN : M < N) :
    ∑ n ∈ Ioc M N, w n = N * w N - M * w (M + 1) + ∑ n ∈ Ioo M N, (n : ℝ) * (w n - w (n + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_or_ge M N with h | h
    · rw [Finset.sum_Ioc_succ_top (by omega), ih h,
        show Ioo M (N + 1) = insert N (Ioo M N) by ext x; simp; omega, sum_insert (by simp)]
      push_cast; ring
    · have hN : N = M := by omega
      subst hN
      rw [show Ioc N (N + 1) = {N + 1} by ext x; simp only [mem_Ioc, mem_singleton]; omega,
        show Ioo N (N + 1) = ∅ by ext x; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega,
        sum_singleton, sum_empty]
      push_cast; ring

theorem wl_le_llog {n : ℕ} (hn : 3 ≤ n) :
    wl n ≤ Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by rw [hcast]; linarith
  have hlm : 0 < Real.log ((n - 1 : ℕ) : ℝ) := Real.log_pos (by rw [hcast]; linarith)
  have hln : 0 < Real.log n := Real.log_pos (by linarith)
  have h1 : 1 / (n : ℝ) ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (n : ℝ) / ((n - 1 : ℕ) : ℝ)) (by positivity)
    rw [Real.log_div hn0.ne' hm0.ne', inv_div] at this
    have e : 1 - ((n - 1 : ℕ) : ℝ) / n = 1 / n := by rw [hcast]; field_simp; ring
    linarith
  have h2 : (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log n ≤
      Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) := by
    have := Real.one_sub_inv_le_log_of_pos (x := Real.log n / Real.log ((n - 1 : ℕ) : ℝ)) (by positivity)
    rw [Real.log_div hln.ne' hlm.ne', inv_div] at this
    have e : 1 - Real.log ((n - 1 : ℕ) : ℝ) / Real.log n =
        (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log n := by field_simp
    linarith
  have h3 : wl n = (1 / (n : ℝ)) / Real.log n := by unfold wl; field_simp
  rw [h3]
  exact (div_le_div_of_nonneg_right h1 hln.le).trans h2

theorem llog_le_wl {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n) ≤ wl n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hln1 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_le_log hn0 (by push_cast; linarith)
  have hln1' : 0 < Real.log ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le hln hln1
  have h1 : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ 1 / n := by
    have := Real.log_le_sub_one_of_pos (x := ((n + 1 : ℕ) : ℝ) / n) (by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at this
    have e : ((n + 1 : ℕ) : ℝ) / n - 1 = 1 / n := by push_cast; field_simp; ring
    linarith
  have h2 : Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n) ≤
      (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log n := by
    have := Real.log_le_sub_one_of_pos (x := Real.log ((n + 1 : ℕ) : ℝ) / Real.log n) (by positivity)
    rw [Real.log_div hln1'.ne' hln.ne'] at this
    have e : Real.log ((n + 1 : ℕ) : ℝ) / Real.log n - 1 =
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log n := by field_simp
    linarith
  have h3 : wl n = (1 / (n : ℝ)) / Real.log n := by unfold wl; field_simp
  rw [h3]
  exact h2.trans (div_le_div_of_nonneg_right h1 hln.le)

theorem sum_wl_le {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    ∑ n ∈ Ioc M N, wl n ≤ Real.log (Real.log N) - Real.log (Real.log M) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_or_ge N M with h | h
    · have : N + 1 = M := by omega
      subst this; simp
    · rw [Finset.sum_Ioc_succ_top (by omega)]
      have h1 := ih h
      have h2 := wl_le_llog (n := N + 1) (by omega)
      rw [show N + 1 - 1 = N by omega] at h2
      linarith

theorem sum_wl_ge {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    Real.log (Real.log N) - Real.log (Real.log M) - wl M ≤ ∑ n ∈ Ioc M N, wl n := by
  have key : ∀ k : ℕ, Real.log (Real.log ((M + k + 1 : ℕ) : ℝ)) - Real.log (Real.log ((M + 1 : ℕ) : ℝ)) ≤
      ∑ n ∈ Ioc M (M + k), wl n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show M + (k + 1) = M + k + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
      have := llog_le_wl (n := M + k + 1) (by omega)
      linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMN
  have h1 := key k
  have h2 := llog_le_wl (n := M) hM
  have hpos : (0 : ℝ) < ((M + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + k)
  have hl1 : 0 < Real.log ((M + k : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M + k))
  have h3 : Real.log (Real.log ((M + k : ℕ) : ℝ)) ≤ Real.log (Real.log ((M + k + 1 : ℕ) : ℝ)) :=
    Real.log_le_log hl1 (Real.log_le_log hpos (by push_cast; linarith))
  linarith

/-- **The variation lemma**: `|E₂Λ(M) − E₂Λ(N)| ≤ |e(N)| w(N) + |e(M)| w(M+1) + ∑ |e(n)| (w(n) − w(n+1)) + w(M)`,
`e(n) = ψ(n) − n`. -/
theorem E2_var {M N : ℕ} (hM : 3 ≤ M) (hMN : M < N) :
    |E₂Λ (M : ℝ) - E₂Λ (N : ℝ)| ≤ |psiN N - N| * wl N + |psiN M - M| * wl (M + 1) +
      ∑ n ∈ Ioo M N, |psiN n - n| * (wl n - wl (n + 1)) + wl M := by
  have hE : E₂Λ (M : ℝ) - E₂Λ (N : ℝ) = -(∑ n ∈ Ioc M N, (Λ n : ℝ) * wl n -
      (Real.log (Real.log N) - Real.log (Real.log M))) := by
    simp only [E₂Λ, Nat.floor_natCast]
    rw [← sum_Ioc_consecutive _ (Nat.zero_le M) hMN.le]
    have : ∀ n ∈ Ioc M N, (Λ n : ℝ) / (n * Real.log n) = (Λ n : ℝ) * wl n := fun n _ => by
      unfold wl; ring
    rw [sum_congr rfl this]; ring
  have hA := abel_Ioc wl M N hMN
  have hI := abel_id wl M N hMN
  have hl := sum_wl_le (by omega : 2 ≤ M) hMN.le
  have hg := sum_wl_ge (by omega : 2 ≤ M) hMN.le
  have hS : |∑ n ∈ Ioo M N, (psiN n - n) * (wl n - wl (n + 1))| ≤
      ∑ n ∈ Ioo M N, |psiN n - n| * (wl n - wl (n + 1)) := by
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun n hn => ?_))
    rw [abs_mul, abs_of_nonneg (wl_diff (by have := (mem_Ioo.1 hn).1; omega)).1]
  have hsplit : ∑ n ∈ Ioo M N, psiN n * (wl n - wl (n + 1)) -
      ∑ n ∈ Ioo M N, (n : ℝ) * (wl n - wl (n + 1)) =
      ∑ n ∈ Ioo M N, (psiN n - n) * (wl n - wl (n + 1)) := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring
  have hX := abs_le.1 (le_of_eq (show |(psiN N - N) * wl N| = |psiN N - N| * wl N by
    rw [abs_mul, abs_of_nonneg (wl_nonneg N)]))
  have hY := abs_le.1 (le_of_eq (show |(psiN M - M) * wl (M + 1)| = |psiN M - M| * wl (M + 1) by
    rw [abs_mul, abs_of_nonneg (wl_nonneg (M + 1))]))
  have hZ := abs_le.1 hS
  rw [hE, abs_neg]
  have key : ∑ n ∈ Ioc M N, (Λ n : ℝ) * wl n - (Real.log (Real.log N) - Real.log (Real.log M)) =
      ((psiN N - N) * wl N - (psiN M - M) * wl (M + 1) +
        ∑ n ∈ Ioo M N, (psiN n - n) * (wl n - wl (n + 1))) +
      (∑ n ∈ Ioc M N, wl n - (Real.log (Real.log N) - Real.log (Real.log M))) := by
    rw [hA, ← hsplit, hI]; ring
  rw [key, abs_le]
  constructor <;> linarith [hX.1, hX.2, hY.1, hY.2, hZ.1, hZ.2]

/-- `D(10¹⁸) ≤ 0.0014`, so `|E₂Λ(10¹⁸)| ≤ 2·0.0014/41`. -/
theorem E2_1e18 : |E₂Λ ((10 ^ 18 : ℕ) : ℝ)| ≤ 0.0000683 := by
  have hN : (2 : ℝ) ≤ ((10 ^ 18 : ℕ) : ℝ) := by norm_num
  have h := E2_le_of (c := E₁Λ ((10 ^ 18 : ℕ) : ℝ)) hN
    (fun t ht => E1_diff (M := 10 ^ 18) (by norm_num) ht.le) (by
      rw [sub_self, abs_zero]
      have := Pth_nonneg (((10 ^ 18 : ℕ) : ℝ)); positivity)
  have hD := D19_le (M := ((10 ^ 18 : ℕ) : ℝ)) (by norm_num)
  have hL : (41 : ℝ) ≤ Real.log ((10 ^ 18 : ℕ) : ℝ) := by
    exact_mod_cast nat_le_log (N := ((10 ^ 18 : ℕ) : ℝ)) (k := 41) (by norm_num)
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  generalize 3 / ((10 ^ 18 : ℕ) : ℝ) + 2 * (1 / Real.log ((10 ^ 18 : ℕ) : ℝ) ^ 3 + 7.04 / √((10 ^ 18 : ℕ) : ℝ)) +
      (2 / Real.log ((10 ^ 18 : ℕ) : ℝ) ^ 2 + 14.08 / √((10 ^ 18 : ℕ) : ℝ)) + Pth ((10 ^ 18 : ℕ) : ℝ) = X at hD ⊢
  generalize Real.log ((10 ^ 18 : ℕ) : ℝ) = L at hL ⊢
  nlinarith

/-- The tail `n > 10¹⁷` of the error sum (`psi_err`, `big_sum_le`). -/
theorem tail_sum_le (M N : ℕ) :
    ∑ n ∈ Ioo M N, (if 10 ^ 17 < n then |psiN n - n| * (wl n - wl (n + 1)) else 0) ≤ 0.0000358 := by
  have hterm : ∀ n ∈ Ioo M N, (if 10 ^ 17 < n then |psiN n - n| * (wl n - wl (n + 1)) else 0) ≤
      (1 / 39 + 1 / 39 ^ 2) * ((if 10 ^ 17 < n then 1 / ((n + 1) * Real.log n ^ 3) + epl n / ((n : ℝ) + 1)
        else 0) + 7.04 * (if 10 ^ 17 < n then 1 / (√(n : ℝ) * (n + 1)) else 0)) := by
    intro n _
    split_ifs with h
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
      have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
      have hL : (39 : ℝ) ≤ Real.log n := by
        have h' : (100000000000000000 : ℝ) < n := by exact_mod_cast h
        exact_mod_cast nat_le_log (N := (n : ℝ)) (k := 39)
          (le_trans (by norm_num : (2.7182818286 : ℝ) ^ 39 ≤ 100000000000000000) h'.le)
      have hw := wl_diff (n := n) (by omega)
      have he := psi_err (n := n) (by omega)
      have hk : 1 / Real.log n + 1 / Real.log n ^ 2 ≤ 1 / 39 + 1 / 39 ^ 2 := by
        gcongr
      have hd := hw.2.trans (mul_le_mul_of_nonneg_left hk (by positivity))
      have h1 := mul_le_mul he hd hw.1 (by have := epl_nonneg (n : ℝ); positivity)
      refine h1.trans (le_of_eq ?_)
      have a : (n : ℝ) / Real.log n ^ 3 * (1 / (n * ((n : ℝ) + 1))) = 1 / ((n + 1) * Real.log n ^ 3) := by
        field_simp
      have b : epl n * n * (1 / (n * ((n : ℝ) + 1))) = epl n / ((n : ℝ) + 1) := by field_simp
      have c : √(n : ℝ) * (1 / (n * ((n : ℝ) + 1))) = 1 / (√(n : ℝ) * (n + 1)) := by
        rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), ← mul_assoc, hss]; ring
      calc ((n : ℝ) / Real.log n ^ 3 + epl n * n + 7.04 * √(n : ℝ)) *
            (1 / (n * ((n : ℝ) + 1)) * (1 / 39 + 1 / 39 ^ 2))
          = (1 / 39 + 1 / 39 ^ 2) * ((n : ℝ) / Real.log n ^ 3 * (1 / (n * ((n : ℝ) + 1))) +
              epl n * n * (1 / (n * ((n : ℝ) + 1))) +
              7.04 * (√(n : ℝ) * (1 / (n * ((n : ℝ) + 1))))) := by ring
        _ = _ := by rw [a, b, c]
    · simp
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum, sum_add_distrib, ← mul_sum]
  have h1 := big_sum_le M N
  have h2 := (sum_Ioo_ite_le (fun n => 1 / (√(n : ℝ) * (n + 1))) (fun n => by positivity) (10 ^ 17) M N).trans
    (sum_Ioo_inv_sqrt_le (10 ^ 17) N)
  have h3 : 2 / √(((10 ^ 17 : ℕ) : ℝ) + 1) ≤ 0.000000007 := by
    have : (300000000 : ℝ) ≤ √(((10 ^ 17 : ℕ) : ℝ) + 1) := Real.le_sqrt_of_sq_le (by norm_num)
    calc 2 / √(((10 ^ 17 : ℕ) : ℝ) + 1) ≤ 2 / 300000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
      _ ≤ 0.000000007 := by norm_num
  have h4 : 0 ≤ ∑ n ∈ Ioo M N, (if 10 ^ 17 < n then 1 / (√(n : ℝ) * (n + 1)) else 0) :=
    sum_nonneg fun n _ => by split_ifs <;> positivity
  have h5 : 0 ≤ ∑ n ∈ Ioo M N, (if 10 ^ 17 < n then 1 / (((n : ℝ) + 1) * Real.log n ^ 3) +
      epl n / ((n : ℝ) + 1) else 0) := sum_nonneg fun n _ => by
    split_ifs
    · have := epl_nonneg (n : ℝ); have := Real.log_natCast_nonneg n; positivity
    · exact le_rfl
  nlinarith

/-- **`|E₂Λ(M)|` for `10⁵ ≤ M < 10¹⁷`**, given `|ψ(n) − n| ≤ c(n)√n` on `[M, 10¹⁷]` with
`c(n) = c₀ + d₁[n ≥ 10⁶] + d₂[n ≥ 5·10⁷] + d₃[n > 10⁸] + d₄[n > 3.2·10¹⁰]`, `L₀ ≤ log M`, `s₀ ≤ √M`. -/
theorem E2_le_bin {M : ℕ} (hM : 100000 ≤ M) (hM17 : M < 10 ^ 17) {c₀ d₁ d₂ d₃ d₄ L₀ s₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃) (hd₄ : 0 ≤ d₄)
    (hc : ∀ n : ℕ, M < n → n ≤ 10 ^ 17 → |psiN n - n| ≤ (c₀ + d₁ * (if 999999 < n then 1 else 0) +
      d₂ * (if 49999999 < n then 1 else 0) + d₃ * (if 10 ^ 8 < n then 1 else 0) +
      d₄ * (if 32000000000 < n then 1 else 0)) * √(n : ℝ))
    (hcM : |psiN M - M| ≤ c₀ * √(M : ℝ))
    (hL₀ : L₀ ≤ Real.log M) (hL₀0 : 0 < L₀) (hs₀ : s₀ ≤ √(M : ℝ)) (hs₀0 : 0 < s₀) :
    |E₂Λ (M : ℝ)| ≤ (1 / L₀ + 1 / L₀ ^ 2) * (c₀ * (2 / s₀) + d₁ * 0.002 + d₂ * 0.00028285 +
      d₃ * 0.0002 + d₄ * 0.0000111804) + c₀ / (s₀ * L₀) + 0.00011 := by
  set N₁ : ℕ := 10 ^ 18 with hN₁
  have hMN : M < N₁ := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hLM : 0 < Real.log M := lt_of_lt_of_le hL₀0 hL₀
  have hvar := E2_var (M := M) (N := N₁) (by omega) hMN
  have hE1 := E2_1e18
  -- boundary at `N₁`
  have hbN : |psiN N₁ - N₁| * wl N₁ ≤ 0.00000036 := by
    have he := psi_err (n := N₁) (by norm_num)
    have hN0 : (0 : ℝ) < N₁ := by norm_num
    have hL : (41 : ℝ) ≤ Real.log N₁ := by
      exact_mod_cast nat_le_log (N := ((10 ^ 18 : ℕ) : ℝ)) (k := 41) (by norm_num)
    have hs : (1000000000 : ℝ) ≤ √(N₁ : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
    have hss : √(N₁ : ℝ) * √(N₁ : ℝ) = N₁ := Real.mul_self_sqrt hN0.le
    have hw : wl N₁ = 1 / ((N₁ : ℝ) * Real.log N₁) := rfl
    have hep := epl_le (N₁ : ℝ)
    have hep0 := epl_nonneg (N₁ : ℝ)
    have hL0 : 0 < Real.log N₁ := by linarith
    have hs0 : 0 < √(N₁ : ℝ) := by linarith
    have t1 : (N₁ : ℝ) / Real.log N₁ ^ 3 * (1 / ((N₁ : ℝ) * Real.log N₁)) = 1 / Real.log N₁ ^ 4 := by
      field_simp
    have t2 : epl N₁ * N₁ * (1 / ((N₁ : ℝ) * Real.log N₁)) = epl N₁ / Real.log N₁ := by field_simp
    have t3 : 7.04 * √(N₁ : ℝ) * (1 / ((N₁ : ℝ) * Real.log N₁)) = 7.04 / (√(N₁ : ℝ) * Real.log N₁) := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination 7.04 * Real.log N₁ * hss
    have h1 := mul_le_mul_of_nonneg_right he (wl_nonneg N₁)
    rw [hw, add_mul, add_mul, t1, t2, t3] at h1
    have a : 1 / Real.log N₁ ^ 4 ≤ 1 / 41 ^ 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 4)
    have b : epl N₁ / Real.log N₁ ≤ 1.83e-9 / 41 :=
      div_le_div₀ (by norm_num) hep (by norm_num) hL
    have c : 7.04 / (√(N₁ : ℝ) * Real.log N₁) ≤ 7.04 / (1000000000 * 41) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hs hL (by norm_num) hs0.le)
    have : (1 : ℝ) / 41 ^ 4 + 1.83e-9 / 41 + 7.04 / (1000000000 * 41) ≤ 0.00000036 := by norm_num
    rw [hw]; linarith
  -- boundary at `M`
  have hbM : |psiN M - M| * wl (M + 1) ≤ c₀ / (s₀ * L₀) := by
    have hw : wl (M + 1) ≤ 1 / ((M : ℝ) * Real.log M) := by
      unfold wl
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast
      exact mul_le_mul (by linarith) (Real.log_le_log hM0 (by linarith)) hLM.le (by positivity)
    have hss : √(M : ℝ) * √(M : ℝ) = M := Real.mul_self_sqrt hM0.le
    have hsM : 0 < √(M : ℝ) := Real.sqrt_pos.2 hM0
    calc |psiN M - M| * wl (M + 1) ≤ c₀ * √(M : ℝ) * (1 / ((M : ℝ) * Real.log M)) :=
          mul_le_mul hcM hw (wl_nonneg _) (by positivity)
      _ = c₀ / (√(M : ℝ) * Real.log M) := by
          rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
          linear_combination c₀ * Real.log M * hss
      _ ≤ c₀ / (s₀ * L₀) := div_le_div_of_nonneg_left hc₀ (by positivity)
          (mul_le_mul hs₀ hL₀ hL₀0.le (Real.sqrt_nonneg _))
  -- `w(M)`
  have hwM : wl M ≤ 0.00000091 := by
    have hL11 : (11 : ℝ) ≤ Real.log M := by
      exact_mod_cast nat_le_log (N := (M : ℝ)) (k := 11) (by
        have : (100000 : ℝ) ≤ M := by exact_mod_cast hM
        norm_num; linarith)
    unfold wl
    rw [div_le_iff₀ (by positivity)]
    have : (100000 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  -- the interior: split at `10¹⁷`
  have hsplit : ∑ n ∈ Ioo M N₁, |psiN n - n| * (wl n - wl (n + 1)) =
      ∑ n ∈ Ioo M N₁, (if n ≤ 10 ^ 17 then |psiN n - n| * (wl n - wl (n + 1)) else 0) +
      ∑ n ∈ Ioo M N₁, (if 10 ^ 17 < n then |psiN n - n| * (wl n - wl (n + 1)) else 0) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    by_cases h : n ≤ 10 ^ 17
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have htail := tail_sum_le M N₁
  set κ := 1 / L₀ + 1 / L₀ ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set g : ℕ → ℝ := fun n => 1 / (√(n : ℝ) * (n + 1)) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; positivity
  have hmain : ∀ n ∈ Ioo M N₁, (if n ≤ 10 ^ 17 then |psiN n - n| * (wl n - wl (n + 1)) else 0) ≤
      κ * (c₀ * g n + d₁ * (if 999999 < n then g n else 0) + d₂ * (if 49999999 < n then g n else 0) +
        d₃ * (if 10 ^ 8 < n then g n else 0) + d₄ * (if 32000000000 < n then g n else 0)) := by
    intro n hn
    have hn1 := (mem_Ioo.1 hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
    have hLn : L₀ ≤ Real.log n := hL₀.trans (Real.log_le_log hM0 (by exact_mod_cast hn1.le))
    have hk : 1 / Real.log n + 1 / Real.log n ^ 2 ≤ κ := by
      rw [hκ]; gcongr
    have hw := wl_diff (n := n) (by omega)
    have hd := hw.2.trans (mul_le_mul_of_nonneg_left hk (by positivity))
    have hgn : √(n : ℝ) * (1 / (n * ((n : ℝ) + 1))) = g n := by
      simp only [hg]
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), ← mul_assoc, hss]; ring
    by_cases h17 : n ≤ 10 ^ 17
    · rw [if_pos h17]
      have he := hc n hn1 h17
      have hcpos : 0 ≤ c₀ + d₁ * (if 999999 < n then 1 else 0) + d₂ * (if 49999999 < n then 1 else 0) +
          d₃ * (if 10 ^ 8 < n then 1 else 0) + d₄ * (if 32000000000 < n then 1 else 0) := by
        split_ifs <;> positivity
      have h1 := mul_le_mul he hd hw.1 (by positivity)
      refine h1.trans (le_of_eq ?_)
      have e : (c₀ + d₁ * (if 999999 < n then 1 else 0) + d₂ * (if 49999999 < n then 1 else 0) +
          d₃ * (if 10 ^ 8 < n then 1 else 0) + d₄ * (if 32000000000 < n then 1 else 0)) * √(n : ℝ) *
          (1 / (n * ((n : ℝ) + 1)) * κ) =
          κ * ((c₀ + d₁ * (if 999999 < n then 1 else 0) + d₂ * (if 49999999 < n then 1 else 0) +
          d₃ * (if 10 ^ 8 < n then 1 else 0) + d₄ * (if 32000000000 < n then 1 else 0)) *
            (√(n : ℝ) * (1 / (n * ((n : ℝ) + 1))))) := by ring
      rw [e, hgn]
      congr 1
      split_ifs <;> ring
    · rw [if_neg h17]
      have := hg0 n
      have : 0 ≤ c₀ * g n + d₁ * (if 999999 < n then g n else 0) + d₂ * (if 49999999 < n then g n else 0) +
          d₃ * (if 10 ^ 8 < n then g n else 0) + d₄ * (if 32000000000 < n then g n else 0) := by
        split_ifs <;> positivity
      positivity
  have hsum := sum_le_sum hmain
  rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    ← mul_sum, ← mul_sum, ← mul_sum] at hsum
  have hA : ∑ n ∈ Ioo M N₁, g n ≤ 2 / s₀ := by
    refine (sum_Ioo_inv_sqrt_le M N₁).trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) hs₀0
    exact hs₀.trans (Real.sqrt_le_sqrt (by linarith))
  have hB := (sum_Ioo_ite_le g hg0 999999 M N₁).trans (sum_Ioo_inv_sqrt_le 999999 N₁)
  have hC := (sum_Ioo_ite_le g hg0 49999999 M N₁).trans (sum_Ioo_inv_sqrt_le 49999999 N₁)
  have hD := (sum_Ioo_ite_le g hg0 (10 ^ 8) M N₁).trans (sum_Ioo_inv_sqrt_le (10 ^ 8) N₁)
  have hE := (sum_Ioo_ite_le g hg0 32000000000 M N₁).trans (sum_Ioo_inv_sqrt_le 32000000000 N₁)
  have hB' : 2 / √(((999999 : ℕ) : ℝ) + 1) ≤ 0.002 := by
    have : (1000 : ℝ) ≤ √(((999999 : ℕ) : ℝ) + 1) := Real.le_sqrt_of_sq_le (by norm_num)
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) this).trans (by norm_num)
  have hC' : 2 / √(((49999999 : ℕ) : ℝ) + 1) ≤ 0.00028285 := by
    have : (7071 : ℝ) ≤ √(((49999999 : ℕ) : ℝ) + 1) := Real.le_sqrt_of_sq_le (by norm_num)
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) this).trans (by norm_num)
  have hD' : 2 / √(((10 ^ 8 : ℕ) : ℝ) + 1) ≤ 0.0002 := by
    have : (10000 : ℝ) ≤ √(((10 ^ 8 : ℕ) : ℝ) + 1) := Real.le_sqrt_of_sq_le (by norm_num)
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) this).trans (by norm_num)
  have hE' : 2 / √(((32000000000 : ℕ) : ℝ) + 1) ≤ 0.0000111804 := by
    have : (178885.4 : ℝ) ≤ √(((32000000000 : ℕ) : ℝ) + 1) := Real.le_sqrt_of_sq_le (by norm_num)
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) this).trans (by norm_num)
  have hint : ∑ n ∈ Ioo M N₁, (if n ≤ 10 ^ 17 then |psiN n - n| * (wl n - wl (n + 1)) else 0) ≤
      κ * (c₀ * (2 / s₀) + d₁ * 0.002 + d₂ * 0.00028285 + d₃ * 0.0002 + d₄ * 0.0000111804) := by
    refine hsum.trans (mul_le_mul_of_nonneg_left ?_ hκ0)
    have := mul_le_mul_of_nonneg_left hA hc₀
    have := mul_le_mul_of_nonneg_left (hB.trans hB') hd₁
    have := mul_le_mul_of_nonneg_left (hC.trans hC') hd₂
    have := mul_le_mul_of_nonneg_left (hD.trans hD') hd₃
    have := mul_le_mul_of_nonneg_left (hE.trans hE') hd₄
    linarith
  have htri : |E₂Λ (M : ℝ)| ≤ |E₂Λ (M : ℝ) - E₂Λ (N₁ : ℝ)| + |E₂Λ (N₁ : ℝ)| := by
    have := abs_add_le (E₂Λ (M : ℝ) - E₂Λ (N₁ : ℝ)) (E₂Λ (N₁ : ℝ))
    rwa [sub_add_cancel] at this
  rw [hsplit] at hvar
  have : ((10 ^ 18 : ℕ) : ℝ) = (N₁ : ℝ) := rfl
  rw [this] at hE1
  calc |E₂Λ (M : ℝ)| ≤ |E₂Λ (M : ℝ) - E₂Λ (N₁ : ℝ)| + |E₂Λ (N₁ : ℝ)| := htri
    _ ≤ (|psiN N₁ - N₁| * wl N₁ + |psiN M - M| * wl (M + 1) +
          ((∑ n ∈ Ioo M N₁, (if n ≤ 10 ^ 17 then |psiN n - n| * (wl n - wl (n + 1)) else 0)) +
            ∑ n ∈ Ioo M N₁, (if 10 ^ 17 < n then |psiN n - n| * (wl n - wl (n + 1)) else 0)) + wl M) +
          0.0000683 := add_le_add hvar hE1
    _ ≤ (0.00000036 + c₀ / (s₀ * L₀) + (κ * (c₀ * (2 / s₀) + d₁ * 0.002 + d₂ * 0.00028285 +
          d₃ * 0.0002 + d₄ * 0.0000111804) + 0.0000358) + 0.00000091) + 0.0000683 := by
        gcongr
    _ ≤ _ := by rw [hκ]; linarith

/-- `−log(1 − y) ≤ ∑_{i<K} y^{i+1}/(i+1) + y^{K+1}/((K+1)(1 − y))` for `y = 1/p`. -/
theorem neg_log_le' (p K : ℕ) (hp : 2 ≤ p) :
    -Real.log (1 - 1 / (p : ℝ)) ≤ ∑ i ∈ range K, (1 / (p : ℝ)) ^ (i + 1) / (i + 1) +
      (1 / (p : ℝ)) ^ (K + 1) / ((K + 1) * (1 - 1 / p)) := by
  set y : ℝ := 1 / (p : ℝ) with hy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one hp0]; exact_mod_cast (by omega : 1 < p)
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (show |y| < 1 by rwa [abs_of_nonneg hy0])
  rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add K]
  gcongr
  have hg := (hasSum_geometric_of_lt_one hy0 hy1).mul_left (y ^ (K + 1) / (K + 1))
  have ht := (summable_nat_add_iff K).2 hs.summable
  refine (Summable.tsum_le_tsum (fun i => ?_) ht hg.summable).trans (le_of_eq ?_)
  · have hK : (0 : ℝ) < K + 1 := by positivity
    have hi : (K : ℝ) + 1 ≤ ((i + K : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    rw [show i + K + 1 = (K + 1) + i by ring, pow_add]
    calc y ^ (K + 1) * y ^ i / (((i + K : ℕ) : ℝ) + 1) ≤ y ^ (K + 1) * y ^ i / (K + 1) :=
          div_le_div_of_nonneg_left (by positivity) hK hi
      _ = y ^ (K + 1) / (K + 1) * y ^ i := by ring
  · rw [hg.tsum_eq]; field_simp

/-- **`log ∏_{p ≤ x} p/(p−1) ≤ ∑_{d ≤ x} Λ(d)/(d log d) + 7/(6⌊√x⌋)`**. -/
theorem logF_le' (x : ℕ) (hx : 4 ≤ x) :
    ∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log ((p : ℝ) / (p - 1)) ≤
      ∑ d ∈ Ioc 0 x, (Λ d : ℝ) / (d * Real.log d) + 7 / (6 * Nat.sqrt x) := by
  set P := (Icc 1 x).filter Nat.Prime with hP
  set s := Nat.sqrt x with hs
  have hs1 : 2 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hss : s * s ≤ x := Nat.sqrt_le x
  have hss' : x < (s + 1) * (s + 1) := Nat.lt_succ_sqrt x
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  set K : ℕ → ℕ := fun p => Nat.log p x with hK
  have hpt : ∀ p ∈ P, Real.log ((p : ℝ) / (p - 1)) ≤
      ∑ i ∈ range (K p), (1 / (p : ℝ)) ^ (i + 1) / (i + 1) +
        (1 / (p : ℝ)) ^ (K p + 1) / ((K p + 1) * (1 - 1 / p)) := by
    intro p hp
    have hp2 := (mem_filter.1 hp).2.two_le
    have e : Real.log ((p : ℝ) / (p - 1)) = -Real.log (1 - 1 / (p : ℝ)) := by
      rw [← Real.log_inv]; congr 1; field_simp
    rw [e]; exact neg_log_le' p (K p) hp2
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  -- main part: reindex by prime powers
  have hmain : ∑ p ∈ P, ∑ i ∈ range (K p), (1 / (p : ℝ)) ^ (i + 1) / (i + 1) ≤
      ∑ d ∈ Ioc 0 x, (Λ d : ℝ) / (d * Real.log d) := by
    rw [sum_sigma']
    set S := P.sigma (fun p => range (K p)) with hS
    set f : ℕ → ℝ := fun d => (Λ d : ℝ) / (d * Real.log d) with hf
    set g : (Σ _ : ℕ, ℕ) → ℕ := fun σ => σ.1 ^ (σ.2 + 1) with hg
    have hinj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b := by
      rintro ⟨p, i⟩ h1 ⟨q, j⟩ h2 he
      have hp := (mem_filter.1 (mem_sigma.1 h1).1).2
      have hq := (mem_filter.1 (mem_sigma.1 h2).1).2
      obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj hp hq he
      rfl
    have hval : ∀ σ ∈ S, (1 / (σ.1 : ℝ)) ^ (σ.2 + 1) / (σ.2 + 1) = f (g σ) := by
      rintro ⟨p, i⟩ hσ
      have hp := (mem_filter.1 (mem_sigma.1 hσ).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      simp only [hf, hg]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      push_cast
      rw [Real.log_pow, one_div_pow]
      push_cast
      field_simp
    rw [sum_congr rfl hval, ← sum_image hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨⟨p, i⟩, hσ, rfl⟩ := mem_image.1 hd
      have hp := (mem_filter.1 (mem_sigma.1 hσ).1).2
      have hi := mem_range.1 (mem_sigma.1 hσ).2
      rw [mem_Ioc]
      refine ⟨pow_pos hp.pos _, ?_⟩
      calc p ^ (i + 1) ≤ p ^ (K p) := Nat.pow_le_pow_right hp.pos hi
        _ ≤ x := Nat.pow_log_le_self p (by omega)
    · intro d _ _
      have : 0 ≤ Real.log d := Real.log_natCast_nonneg d
      have : (0 : ℝ) ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      simp only [hf]
      positivity
  have htail : ∑ p ∈ P, (1 / (p : ℝ)) ^ (K p + 1) / ((K p + 1) * (1 - 1 / p)) ≤ 7 / (6 * s) := by
    have hT : ∀ p ∈ P, (1 / (p : ℝ)) ^ (K p + 1) / ((K p + 1) * (1 - 1 / p)) ≤
        (if p ≤ s then (2 / 3 : ℝ) / x else 1 / (2 * ((p : ℝ) * (p - 1)))) := by
      intro p hp
      have hpp := (mem_filter.1 hp).2
      have hp2 := hpp.two_le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
      have hpx : p ≤ x := (mem_Icc.1 (mem_filter.1 hp).1).2
      have e : (1 / (p : ℝ)) ^ (K p + 1) / ((K p + 1) * (1 - 1 / p)) =
          1 / (p : ℝ) ^ (K p + 1) * (p / (p - 1)) / (K p + 1) := by
        rw [one_div_pow]
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
      rw [e]
      have hq0 : (0 : ℝ) ≤ p / (p - 1) := div_nonneg hp0.le (by linarith)
      split_ifs with h
      · have hK2 : 2 ≤ K p := by
          rw [hK]; exact Nat.le_log_of_pow_le hpp.one_lt (by nlinarith)
        have hlt : x < p ^ (K p + 1) := Nat.lt_pow_succ_log_self hpp.one_lt x
        have hlt' : (x : ℝ) < (p : ℝ) ^ (K p + 1) := by exact_mod_cast hlt
        have h2 : (p : ℝ) / (p - 1) ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]; have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
          linarith
        have hK3 : (3 : ℝ) ≤ K p + 1 := by exact_mod_cast (by omega : 3 ≤ K p + 1)
        calc 1 / (p : ℝ) ^ (K p + 1) * (p / (p - 1)) / (K p + 1) ≤ 1 / x * 2 / 3 := by
              apply div_le_div₀ (by positivity) _ (by norm_num) hK3
              exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hx0 hlt'.le) h2
                hq0 (by positivity)
          _ = (2 / 3 : ℝ) / x := by ring
      · have hK1 : 1 ≤ K p := by
          rw [hK]; exact Nat.le_log_of_pow_le hpp.one_lt (by simpa using hpx)
        have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (K p + 1) := pow_le_pow_right₀ hp1.le (by omega)
        have hK2 : (2 : ℝ) ≤ K p + 1 := by exact_mod_cast (by omega : 2 ≤ K p + 1)
        calc 1 / (p : ℝ) ^ (K p + 1) * (p / (p - 1)) / (K p + 1) ≤ 1 / (p : ℝ) ^ 2 * (p / (p - 1)) / 2 := by
              apply div_le_div₀ (by positivity) _ (by norm_num) hK2
              exact mul_le_mul_of_nonneg_right
                (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow) hq0
          _ = 1 / (2 * ((p : ℝ) * (p - 1))) := by
              have : (p : ℝ) - 1 ≠ 0 := by linarith
              field_simp
    refine (sum_le_sum hT).trans ?_
    rw [sum_ite]
    have hA : ∑ p ∈ P.filter (fun p => p ≤ s), (2 / 3 : ℝ) / x ≤ s * ((2 / 3) / x) := by
      rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (P.filter (fun p => p ≤ s)).card ≤ (Icc 1 s).card := by
        apply card_le_card
        intro p hp
        have h1 := mem_filter.1 hp
        have h2 := mem_filter.1 h1.1
        exact mem_Icc.2 ⟨(mem_Icc.1 h2.1).1, h1.2⟩
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : (P.filter (fun p => p ≤ s)).card ≤ s)
    have hB : ∑ p ∈ P.filter (fun p => ¬ p ≤ s), (1 : ℝ) / (2 * ((p : ℝ) * (p - 1))) ≤
        (1 / s - 1 / x) / 2 := by
      have h := sum_inv_mul_pred_le (a := s) (b := x) (by omega) (by nlinarith)
      have e : ∑ p ∈ P.filter (fun p => ¬ p ≤ s), (1 : ℝ) / (2 * ((p : ℝ) * (p - 1))) =
          (∑ p ∈ P.filter (fun p => ¬ p ≤ s), (1 : ℝ) / ((p : ℝ) * (p - 1))) / 2 := by
        rw [sum_div]; exact sum_congr rfl fun p _ => by rw [div_div, mul_comm (2 : ℝ)]
      rw [e]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      refine le_trans ?_ h
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have h1 := mem_filter.1 hp
        have h2 := mem_filter.1 h1.1
        exact mem_Ioc.2 ⟨by omega, (mem_Icc.1 h2.1).2⟩
      · intro n hn _
        have : (1 : ℝ) ≤ n := by exact_mod_cast (by have := (mem_Ioc.1 hn).1; omega)
        have : (0 : ℝ) ≤ n - 1 := by linarith
        positivity
    have hsx : (s : ℝ) * ((2 / 3) / x) ≤ (2 / 3) / s := by
      have : ((s * s : ℕ) : ℝ) ≤ x := by exact_mod_cast hss
      push_cast at this
      rw [mul_div_assoc', div_le_div_iff₀ hx0 hs0]; nlinarith
    have : (0 : ℝ) ≤ 1 / x := by positivity
    have e3 : (7 : ℝ) / (6 * s) = (2 / 3) / s + 1 / s / 2 := by field_simp; ring
    linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **[RS62, Thm 15] for `x ≥ 10⁵`**, given `|E₂Λ(x)| ≤ E`, `|θ(x) − x| ≤ c_θ √x` and numerical
conditions on `S₀ ≤ ⌊√x⌋` and `L_m ≥ log x`. -/
theorem F_mid_gen {x : ℕ} (hx1 : 100000 ≤ x) {S0 : ℕ} {Lm E cθ : ℝ}
    (hS0 : 316 ≤ S0) (hS : S0 ≤ Nat.sqrt x) (hLm : Real.log x ≤ Lm)
    (hE : |E₂Λ (x : ℝ)| ≤ E) (hθc : |thetaN x - x| ≤ cθ * √(x : ℝ)) (hcθ : 0 ≤ cθ)
    (hc1 : E + 7 / (6 * S0) ≤ 0.0196) (hcu : cθ / S0 ≤ 2.37 / 316)
    (hc2 : 1.95 * (1.02 * ((E + 7 / (6 * S0)) * Lm ^ 2) + 2 * (cθ / S0 * Lm)) < 2.5) :
    ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) <
      Real.exp Real.eulerMascheroniConstant * Real.log (thetaN x) + 2.50637 / Real.log (thetaN x) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  set L := Real.log x with hLdef
  have hL11 : (11 : ℝ) ≤ L := by
    have := nat_le_log (N := (x : ℝ)) (k := 11) (by
      have : (100000 : ℝ) ≤ x := by exact_mod_cast hx1
      linarith [show (2.7182818286 : ℝ) ^ 11 ≤ 100000 by norm_num])
    exact_mod_cast this
  have hL0 : 0 < L := by linarith
  set s := Nat.sqrt x with hs
  have hss : s * s ≤ x := Nat.sqrt_le x
  have hS0r : (316 : ℝ) ≤ S0 := by exact_mod_cast hS0
  have hSs : (S0 : ℝ) ≤ s := by exact_mod_cast hS
  have hs0 : (0 : ℝ) < s := by linarith
  set sx := √(x : ℝ) with hsx
  have hsx0 : 0 < sx := Real.sqrt_pos.2 hx0
  have hssx : (s : ℝ) ≤ sx := by
    rw [hsx]; apply Real.le_sqrt_of_sq_le
    have : ((s * s : ℕ) : ℝ) ≤ x := by exact_mod_cast hss
    push_cast at this; nlinarith
  have hxS : (S0 : ℝ) ^ 2 ≤ x := by
    have : ((s * s : ℕ) : ℝ) ≤ x := by exact_mod_cast hss
    push_cast at this; nlinarith
  -- the product as an exponential
  have hFpos : ∀ p ∈ (Icc 1 x).filter Nat.Prime, (0 : ℝ) < (p : ℝ) / (p - 1) := by
    intro p hp
    have : (1 : ℝ) < p := by exact_mod_cast (mem_filter.1 hp).2.one_lt
    exact div_pos (by linarith) (by linarith)
  have hlogF : Real.log (∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1))) =
      ∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log ((p : ℝ) / (p - 1)) :=
    Real.log_prod (fun p hp => (hFpos p hp).ne')
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hmert := sum_mangoldt_div_log_eq (x : ℝ)
  rw [Nat.floor_natCast] at hmert
  have hlF := logF_le' x (by omega)
  set δ := 7 / (6 * (s : ℝ)) with hδ
  set η := E + δ with hη
  have hlogle : Real.log (∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1))) ≤
      Real.log L + Real.eulerMascheroniConstant + η := by
    rw [hlogF]; linarith [(abs_le.1 hE).2]
  have hδ0 : 0 ≤ δ := by positivity
  have hδS : δ ≤ 7 / (6 * S0) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hη0 : 0 ≤ η := by positivity
  have hη1 : η ≤ 0.0196 := by linarith
  -- `η L² ≤ (E + 7/(6 S₀)) L_m²`
  have hLLm : L ≤ Lm := hLm
  have hηL : η * L ^ 2 ≤ (E + 7 / (6 * S0)) * Lm ^ 2 := by
    have : L ^ 2 ≤ Lm ^ 2 := pow_le_pow_left₀ hL0.le hLLm 2
    exact mul_le_mul (by linarith) this (by positivity) (by positivity)
  -- `exp η ≤ 1 + 1.02 η`
  have hexp : Real.exp η ≤ 1 + 1.02 * η := by
    have h1 : 1 - η ≤ Real.exp (-η) := by linarith [Real.add_one_le_exp (-η)]
    have h2 : Real.exp η * Real.exp (-η) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < 1 - η := by linarith
    have h4 : Real.exp η * (1 - η) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos η).le; linarith
    by_contra! hc
    have : (1 + 1.02 * η) * (1 - η) < Real.exp η * (1 - η) := mul_lt_mul_of_pos_right hc h3
    nlinarith only [this, h4, hη0, hη1]
  set G := Real.exp Real.eulerMascheroniConstant with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hG1 := exp_gamma_lt
  have hF : ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) ≤ G * L + 1.02 * (G * η * L) := by
    have hpos : 0 < ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) := prod_pos hFpos
    rw [← Real.exp_log hpos]
    calc Real.exp (Real.log (∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)))) ≤
          Real.exp (Real.log L + Real.eulerMascheroniConstant + η) := Real.exp_le_exp.2 hlogle
      _ = L * G * Real.exp η := by rw [Real.exp_add, Real.exp_add, Real.exp_log hL0]
      _ ≤ L * G * (1 + 1.02 * η) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = G * L + 1.02 * (G * η * L) := by ring
  -- `θ(x)` bounds
  have hθ := abs_le.1 hθc
  set u := cθ / sx with hu
  have hu0 : 0 ≤ u := by positivity
  have hsxS : (S0 : ℝ) ≤ sx := hSs.trans hssx
  have hu1 : u ≤ 2.37 / 316 :=
    (div_le_div_of_nonneg_left hcθ (by positivity) hsxS).trans hcu
  have hθx : cθ * sx = x * u := by
    have hss2 : sx * sx = x := Real.mul_self_sqrt hx0.le
    rw [hu, mul_div_assoc', eq_div_iff hsx0.ne']
    linear_combination cθ * hss2
  rw [hθx] at hθ
  have hθ0 : 0 < thetaN x := by nlinarith only [hθ.1, hx0, hu1, hu0]
  have hlθ1 : L - 2 * u ≤ Real.log (thetaN x) := by
    have h1 : (x : ℝ) * (1 - u) ≤ thetaN x := by linarith
    have h2 : Real.log ((x : ℝ) * (1 - u)) ≤ Real.log (thetaN x) :=
      Real.log_le_log (by nlinarith only [hx0, hu1, hu0]) h1
    rw [Real.log_mul hx0.ne' (by linarith)] at h2
    have h3 := Real.one_sub_inv_le_log_of_pos (x := 1 - u) (by linarith)
    have h4 : 1 - (1 - u)⁻¹ ≥ -2 * u := by
      have hu' : (1 : ℝ) - u ≠ 0 := by linarith
      rw [ge_iff_le, show 1 - (1 - u)⁻¹ = -(u / (1 - u)) by field_simp; ring]
      have : u / (1 - u) ≤ 2 * u := by
        rw [div_le_iff₀ (by linarith)]; nlinarith only [hu0, hu1]
      linarith
    linarith
  have hlθ2 : Real.log (thetaN x) ≤ L + u := by
    have h1 : thetaN x ≤ (x : ℝ) * (1 + u) := by linarith
    have h2 := Real.log_le_log hθ0 h1
    rw [Real.log_mul hx0.ne' (by linarith)] at h2
    have h3 := Real.log_le_sub_one_of_pos (x := 1 + u) (by linarith)
    linarith
  have hlθ0 : 0 < Real.log (thetaN x) := by linarith
  have hc : 2.5 / L ≤ 2.50637 / Real.log (thetaN x) := by
    rw [div_le_div_iff₀ hL0 hlθ0]; nlinarith only [hlθ2, hu1, hL11]
  have hGL : G * L - 2 * (G * u) ≤ G * Real.log (thetaN x) := by
    have := mul_le_mul_of_nonneg_left hlθ1 hG0.le
    have e : G * (L - 2 * u) = G * L - 2 * (G * u) := by ring
    linarith
  have huL : u * L ≤ cθ / S0 * Lm := by
    have h1 : u ≤ cθ / S0 := div_le_div_of_nonneg_left hcθ (by positivity) hsxS
    exact mul_le_mul h1 hLLm hL0.le (by positivity)
  have key : 1.02 * (G * η * L) + 2 * (G * u) < 2.5 / L := by
    rw [lt_div_iff₀ hL0]
    have hk : (1.02 * (G * η * L) + 2 * (G * u)) * L = G * (1.02 * (η * L ^ 2) + 2 * (u * L)) := by ring
    rw [hk]
    have hb : 1.02 * (η * L ^ 2) + 2 * (u * L) ≤
        1.02 * ((E + 7 / (6 * S0)) * Lm ^ 2) + 2 * (cθ / S0 * Lm) := by
      linarith
    have hb0 : 0 ≤ 1.02 * (η * L ^ 2) + 2 * (u * L) := by positivity
    calc G * (1.02 * (η * L ^ 2) + 2 * (u * L)) ≤
          1.95 * (1.02 * ((E + 7 / (6 * S0)) * Lm ^ 2) + 2 * (cθ / S0 * Lm)) :=
          mul_le_mul hG1.le hb hb0 (by norm_num)
      _ < 2.5 := hc2
  linarith only [hF, hGL, hc, key]

theorem log_le_of_exp {x : ℝ} {k : ℕ} (hx : 0 < x) (h : x ≤ 2.7182818283 ^ k) : Real.log x ≤ k := by
  rw [Real.log_le_iff_le_exp hx]
  calc x ≤ 2.7182818283 ^ k := h
    _ ≤ Real.exp 1 ^ k := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k
    _ = Real.exp k := by rw [← Real.exp_nat_mul, mul_one]

theorem log_3e5_le : Real.log 300000 ≤ 12.62 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 12 (u := 0.62) (by norm_num) 8
  have e : ((12 : ℕ) : ℝ) + 0.62 = 12.62 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_1e6_le : Real.log 1000000 ≤ 13.82 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 13 (u := 0.82) (by norm_num) 8
  have e : ((13 : ℕ) : ℝ) + 0.82 = 13.82 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_5e6_le : Real.log 5000000 ≤ 15.43 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 15 (u := 0.43) (by norm_num) 8
  have e : ((15 : ℕ) : ℝ) + 0.43 = 15.43 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_5e7_le : Real.log 50000000 ≤ 17.73 := by
  refine TernaryGoldbach.Explicit.log_le_of_le_exp'' (by norm_num) ?_
  have h := TernaryGoldbach.Explicit.exp_split_ge' 17 (u := 0.73) (by norm_num) 8
  have e : ((17 : ℕ) : ℝ) + 0.73 = 17.73 := by norm_num
  rw [e] at h; refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The envelope `c(n)` of `|ψ(n) − n|/√n` on `[12, 10¹⁷]`: `1` below `10⁶` (`small_table`), `5` up to
`5·10⁷` (`thetaN_sieve`, `nonprime_small`), then `31.5`, `35.5`, `72` (`cB`). -/
noncomputable def cE (n : ℕ) : ℝ :=
  1 + 4 * (if 999999 < n then 1 else 0) + 26.5 * (if 49999999 < n then 1 else 0) +
    4 * (if 10 ^ 8 < n then 1 else 0) + 36.5 * (if 32000000000 < n then 1 else 0)

theorem psi_cE {n : ℕ} (h12 : 12 ≤ n) (h17 : n ≤ 10 ^ 17) : |psiN n - n| ≤ cE n * √(n : ℝ) := by
  have hs := Real.sqrt_nonneg (n : ℝ)
  rcases lt_or_ge n 1000000 with h6 | h6
  · have hb := psi_two_sided h12 h17
    rw [cB_small h6] at hb
    have : cE n = 1 := by unfold cE; simp only [if_neg (show ¬ 999999 < n by omega),
      if_neg (show ¬ 49999999 < n by omega), if_neg (show ¬ 10 ^ 8 < n by omega),
      if_neg (show ¬ 32000000000 < n by omega)]; norm_num
    rw [this]; exact hb
  rcases lt_or_ge n 50000000 with h7 | h7
  · obtain ⟨hu, hl⟩ := thetaN_sieve h6 h7
    have hθψ := thetaN_le_psiN n
    have hnp := nonprime_small n (by omega) (by omega)
    have he := psiN_eq n
    have : cE n = 5 := by unfold cE; simp only [if_pos (show 999999 < n by omega),
      if_neg (show ¬ 49999999 < n by omega), if_neg (show ¬ 10 ^ 8 < n by omega),
      if_neg (show ¬ 32000000000 < n by omega)]; norm_num
    rw [this, abs_le]; constructor <;> linarith
  have hb := psi_two_sided h12 h17
  rcases le_or_gt n (10 ^ 8) with h8 | h8
  · have hc := cB_le_315 (n := n) (by omega) h8
    have : cE n = 31.5 := by unfold cE; simp only [if_pos (show 999999 < n by omega),
      if_pos (show 49999999 < n by omega), if_neg (show ¬ 10 ^ 8 < n by omega),
      if_neg (show ¬ 32000000000 < n by omega)]; norm_num
    rw [this]; exact hb.trans (mul_le_mul_of_nonneg_right hc hs)
  rcases le_or_gt n 32000000000 with h10 | h10
  · have hc := cB_le_355 (n := n) h10
    have : cE n = 35.5 := by unfold cE; simp only [if_pos (show 999999 < n by omega),
      if_pos (show 49999999 < n by omega), if_pos (show 10 ^ 8 < n by omega),
      if_neg (show ¬ 32000000000 < n by omega)]; norm_num
    rw [this]; exact hb.trans (mul_le_mul_of_nonneg_right hc hs)
  · have hc := cB_le_72 n
    have : cE n = 72 := by unfold cE; simp only [if_pos (show 999999 < n by omega),
      if_pos (show 49999999 < n by omega), if_pos (show 10 ^ 8 < n by omega),
      if_pos (show 32000000000 < n by omega)]; norm_num
    rw [this]; exact hb.trans (mul_le_mul_of_nonneg_right hc hs)

/-- `cE` written with the coefficients of a bin: `c₀` absorbs the thresholds below `M`. -/
theorem cE_eq {n : ℕ} {c₀ d₁ d₂ d₃ d₄ : ℝ}
    (h : cE n = c₀ + d₁ * (if 999999 < n then 1 else 0) + d₂ * (if 49999999 < n then 1 else 0) +
      d₃ * (if 10 ^ 8 < n then 1 else 0) + d₄ * (if 32000000000 < n then 1 else 0)) :
    |psiN n - n| ≤ cE n * √(n : ℝ) → |psiN n - n| ≤ (c₀ + d₁ * (if 999999 < n then 1 else 0) +
      d₂ * (if 49999999 < n then 1 else 0) + d₃ * (if 10 ^ 8 < n then 1 else 0) +
      d₄ * (if 32000000000 < n then 1 else 0)) * √(n : ℝ) := by
  rw [h]; exact id

theorem lnat (N : ℝ) (k : ℕ) (h : (2.7182818286 : ℝ) ^ k ≤ N) : (k : ℝ) ≤ Real.log N := nat_le_log h

set_option maxHeartbeats 4000000 in
/-- **[RS62, Thm 15] for `10⁵ ≤ x < 10¹²`**: seven bins, each with `E2_le_bin` and `F_mid_gen`. -/
theorem F_mid {x : ℕ} (hx1 : 100000 ≤ x) (hx2 : x < 10 ^ 12) :
    ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) <
      Real.exp Real.eulerMascheroniConstant * Real.log (thetaN x) + 2.50637 / Real.log (thetaN x) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hxr : (100000 : ℝ) ≤ x := by exact_mod_cast hx1
  have hlogmono : ∀ y : ℝ, (x : ℝ) ≤ y → Real.log x ≤ Real.log y := fun y hy => Real.log_le_log hx0 hy
  have hcM : ∀ c₀ : ℝ, cE x = c₀ → |psiN x - x| ≤ c₀ * √(x : ℝ) := fun c₀ h => by
    rw [← h]; exact psi_cE (by omega) (by omega)
  have hθlo : x < 1000000 → |thetaN x - x| ≤ 2.3662 * √(x : ℝ) := fun h => by
    obtain ⟨h1, h2⟩ := theta_small_two_sided (n := x) (by omega) h
    rw [abs_le]; constructor <;> (unfold thetaN; linarith)
  have hθsv : 1000000 ≤ x → x < 50000000 → |thetaN x - x| ≤ 5 * √(x : ℝ) := fun h1 h2 => by
    obtain ⟨a, b⟩ := thetaN_sieve h1 h2
    have := Real.sqrt_nonneg (x : ℝ)
    rw [abs_le]; constructor <;> linarith
  have hθcB : ∀ c : ℝ, cB x ≤ c → |thetaN x - x| ≤ (c + 1.4262) * √(x : ℝ) := fun c hc =>
    (thetaN_close_cB (by omega) hx2).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  rcases lt_or_ge x 300000 with h1 | h1
  · -- `[10⁵, 3·10⁵)`
    have hE := E2_le_bin (M := x) hx1 (by omega) (c₀ := 1) (d₁ := 4) (d₂ := 26.5) (d₃ := 4) (d₄ := 36.5)
      (L₀ := 11) (s₀ := 316) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun n hn h17 => cE_eq (by unfold cE; ring) (psi_cE (by omega) h17))
      (hcM 1 (by unfold cE; simp only [if_neg (show ¬ 999999 < x by omega),
        if_neg (show ¬ 49999999 < x by omega), if_neg (show ¬ 10 ^ 8 < x by omega),
        if_neg (show ¬ 32000000000 < x by omega)]; norm_num))
      (by exact_mod_cast lnat x 11 (by norm_num; linarith)) (by norm_num)
      (Real.le_sqrt_of_sq_le (by linarith)) (by norm_num)
    refine F_mid_gen (S0 := 316) (Lm := 12.62) (cθ := 2.3662) hx1 le_rfl (by rw [Nat.le_sqrt]; omega)
      ((hlogmono 300000 (by exact_mod_cast h1.le)).trans log_3e5_le) hE (hθlo (by omega)) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  rcases lt_or_ge x 1000000 with h2 | h2
  · -- `[3·10⁵, 10⁶)`
    have hE := E2_le_bin (M := x) hx1 (by omega) (c₀ := 1) (d₁ := 4) (d₂ := 26.5) (d₃ := 4) (d₄ := 36.5)
      (L₀ := 12) (s₀ := 547) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun n hn h17 => cE_eq (by unfold cE; ring) (psi_cE (by omega) h17))
      (hcM 1 (by unfold cE; simp only [if_neg (show ¬ 999999 < x by omega),
        if_neg (show ¬ 49999999 < x by omega), if_neg (show ¬ 10 ^ 8 < x by omega),
        if_neg (show ¬ 32000000000 < x by omega)]; norm_num))
      (by exact_mod_cast lnat x 12 (by norm_num; have : (300000 : ℝ) ≤ x := by exact_mod_cast h1
                                       linarith)) (by norm_num)
      (Real.le_sqrt_of_sq_le (by have : (300000 : ℝ) ≤ x := by exact_mod_cast h1
                                 linarith)) (by norm_num)
    refine F_mid_gen (S0 := 547) (Lm := 13.82) (cθ := 2.3662) hx1 (by norm_num) (by rw [Nat.le_sqrt]; omega)
      ((hlogmono 1000000 (by exact_mod_cast h2.le)).trans log_1e6_le) hE (hθlo h2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hc5 : ∀ n : ℕ, x < n → n ≤ 10 ^ 17 → |psiN n - n| ≤ (5 + 0 * (if 999999 < n then 1 else 0) +
      26.5 * (if 49999999 < n then 1 else 0) + 4 * (if 10 ^ 8 < n then 1 else 0) +
      36.5 * (if 32000000000 < n then 1 else 0)) * √(n : ℝ) := fun n hn h17 =>
    cE_eq (by unfold cE; rw [if_pos (show 999999 < n by omega)]; ring) (psi_cE (by omega) h17)
  have hcM5 : x < 50000000 → |psiN x - x| ≤ 5 * √(x : ℝ) := fun h => hcM 5 (by
    unfold cE; simp only [if_pos (show 999999 < x by omega),
      if_neg (show ¬ 49999999 < x by omega), if_neg (show ¬ 10 ^ 8 < x by omega),
      if_neg (show ¬ 32000000000 < x by omega)]; norm_num)
  rcases lt_or_ge x 5000000 with h3 | h3
  · -- `[10⁶, 5·10⁶)`
    have hE := E2_le_bin (M := x) hx1 (by omega) (c₀ := 5) (d₁ := 0) (d₂ := 26.5) (d₃ := 4) (d₄ := 36.5)
      (L₀ := 13) (s₀ := 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hc5 (hcM5 (by omega))
      (by exact_mod_cast lnat x 13 (by norm_num; have : (1000000 : ℝ) ≤ x := by exact_mod_cast h2
                                       linarith)) (by norm_num)
      (Real.le_sqrt_of_sq_le (by have : (1000000 : ℝ) ≤ x := by exact_mod_cast h2
                                 linarith)) (by norm_num)
    refine F_mid_gen (S0 := 1000) (Lm := 15.43) (cθ := 5) hx1 (by norm_num) (by rw [Nat.le_sqrt]; omega)
      ((hlogmono 5000000 (by exact_mod_cast h3.le)).trans log_5e6_le) hE (hθsv h2 (by omega)) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  rcases lt_or_ge x 50000000 with h4 | h4
  · -- `[5·10⁶, 5·10⁷)`
    have hE := E2_le_bin (M := x) hx1 (by omega) (c₀ := 5) (d₁ := 0) (d₂ := 26.5) (d₃ := 4) (d₄ := 36.5)
      (L₀ := 15) (s₀ := 2236) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hc5 (hcM5 h4)
      (by exact_mod_cast lnat x 15 (by norm_num; have : (5000000 : ℝ) ≤ x := by exact_mod_cast h3
                                       linarith)) (by norm_num)
      (Real.le_sqrt_of_sq_le (by have : (5000000 : ℝ) ≤ x := by exact_mod_cast h3
                                 linarith)) (by norm_num)
    refine F_mid_gen (S0 := 2236) (Lm := 17.73) (cθ := 5) hx1 (by norm_num) (by rw [Nat.le_sqrt]; omega)
      ((hlogmono 50000000 (by exact_mod_cast h4.le)).trans log_5e7_le) hE (hθsv (by omega) h4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt x (10 ^ 8) with h5 | h5
  · -- `[5·10⁷, 10⁸]`
    have hE := E2_le_bin (M := x) hx1 (by omega) (c₀ := 31.5) (d₁ := 0) (d₂ := 0) (d₃ := 4) (d₄ := 36.5)
      (L₀ := 17) (s₀ := 7071) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun n hn h17 => cE_eq (by unfold cE; rw [if_pos (show 999999 < n by omega),
        if_pos (show 49999999 < n by omega)]; ring) (psi_cE (by omega) h17))
      (hcM 31.5 (by unfold cE; simp only [if_pos (show 999999 < x by omega),
        if_pos (show 49999999 < x by omega), if_neg (show ¬ 10 ^ 8 < x by omega),
        if_neg (show ¬ 32000000000 < x by omega)]; norm_num))
      (by exact_mod_cast lnat x 17 (by norm_num; have : (50000000 : ℝ) ≤ x := by exact_mod_cast h4
                                       linarith)) (by norm_num)
      (Real.le_sqrt_of_sq_le (by have : (50000000 : ℝ) ≤ x := by exact_mod_cast h4
                                 linarith)) (by norm_num)
    refine F_mid_gen (S0 := 7071) (Lm := 18.421) (cθ := 31.5 + 1.4262) hx1 (by norm_num)
      (by rw [Nat.le_sqrt]; omega)
      ((hlogmono 100000000 (by exact_mod_cast h5)).trans log_1e8_le) hE
      (hθcB 31.5 (cB_le_315 (by omega) h5)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt x 32000000000 with h6 | h6
  · -- `(10⁸, 3.2·10¹⁰]`
    have hE := E2_le_bin (M := x) hx1 (by omega) (c₀ := 35.5) (d₁ := 0) (d₂ := 0) (d₃ := 0) (d₄ := 36.5)
      (L₀ := 18) (s₀ := 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun n hn h17 => cE_eq (by unfold cE; rw [if_pos (show 999999 < n by omega),
        if_pos (show 49999999 < n by omega), if_pos (show 10 ^ 8 < n by omega)]; ring)
        (psi_cE (by omega) h17))
      (hcM 35.5 (by unfold cE; simp only [if_pos (show 999999 < x by omega),
        if_pos (show 49999999 < x by omega), if_pos (show 10 ^ 8 < x by omega),
        if_neg (show ¬ 32000000000 < x by omega)]; norm_num))
      (by exact_mod_cast lnat x 18 (by norm_num; have : (100000000 : ℝ) < x := by exact_mod_cast h5
                                       linarith)) (by norm_num)
      (Real.le_sqrt_of_sq_le (by have : (100000000 : ℝ) < x := by exact_mod_cast h5
                                 linarith)) (by norm_num)
    refine F_mid_gen (S0 := 10000) (Lm := 24.19) (cθ := 35.5 + 1.4262) hx1 (by norm_num)
      (by rw [Nat.le_sqrt]; omega)
      ((hlogmono 32000000000 (by exact_mod_cast h6)).trans log_32e9_le) hE
      (hθcB 35.5 (cB_le_355 h6)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- `(3.2·10¹⁰, 10¹²)`
    have hE := E2_le_bin (M := x) hx1 (by omega) (c₀ := 72) (d₁ := 0) (d₂ := 0) (d₃ := 0) (d₄ := 0)
      (L₀ := 24) (s₀ := 178885) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun n hn h17 => cE_eq (by unfold cE; rw [if_pos (show 999999 < n by omega),
        if_pos (show 49999999 < n by omega), if_pos (show 10 ^ 8 < n by omega),
        if_pos (show 32000000000 < n by omega)]; ring) (psi_cE (by omega) h17))
      (hcM 72 (by unfold cE; simp only [if_pos (show 999999 < x by omega),
        if_pos (show 49999999 < x by omega), if_pos (show 10 ^ 8 < x by omega),
        if_pos (show 32000000000 < x by omega)]; norm_num))
      (by exact_mod_cast lnat x 24 (by norm_num; have : (32000000000 : ℝ) < x := by exact_mod_cast h6
                                       linarith)) (by norm_num)
      (Real.le_sqrt_of_sq_le (by have : (32000000000 : ℝ) < x := by exact_mod_cast h6
                                 linarith)) (by norm_num)
    refine F_mid_gen (S0 := 178885) (Lm := 27.632) (cθ := 72 + 1.4262) hx1 (by norm_num)
      (by rw [Nat.le_sqrt]; omega)
      ((hlogmono 1e12 (by have : (x : ℝ) < 1000000000000 := by exact_mod_cast hx2
                          norm_num; linarith)).trans log_1e12_le) hE
      (hθcB 72 (cB_le_72 x)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `q/φ(q) = ∏_{p ∣ q} p/(p−1)`. -/
theorem div_totient_eq_prod {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) / Nat.totient q = ∏ p ∈ q.primeFactors, ((p : ℝ) / (p - 1)) := by
  have h := Nat.totient_mul_prod_primeFactors q
  have h' : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
      q * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]; congr 1
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hP : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    refine prod_pos fun p hp => ?_
    have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  rw [prod_div_distrib, div_eq_div_iff hφ.ne' hP.ne']
  linarith

/-- The `p/(p−1)` factors decrease. -/
theorem frac_anti {a b : ℕ} (hb : 2 ≤ b) (hab : b ≤ a) :
    (a : ℝ) / (a - 1) ≤ (b : ℝ) / (b - 1) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hab' : (b : ℝ) ≤ a := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

/-- Exchange: a set of `k` primes has `∏ p/(p−1)` at most, and product at least, those of the first
`k` primes. -/
theorem exch (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, ((p : ℝ) / (p - 1)) ≤
        ∏ i ∈ range P.card, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) ∧
      ∏ i ∈ range P.card, Nat.nth Nat.Prime i ≤ ∏ p ∈ P, p := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a.Prime := hP a (mem_insert_self a s)
    have ih := ih (fun p hp => hP p (mem_insert_of_mem hp))
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    -- `a ≥ nth (card s)`
    have hcount : s.card < Nat.count Nat.Prime (a + 1) := by
      rw [Nat.count_eq_card_filter_range]
      have : insert a s ⊆ (range (a + 1)).filter (fun x => Nat.Prime x) := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨mem_range.2 (by omega), ha⟩
        · exact mem_filter.2 ⟨mem_range.2 (by have := hlt x hx; omega),
            hP x (mem_insert_of_mem hx)⟩
      have := card_le_card this
      rw [card_insert_of_notMem has] at this
      omega
    have hnth : Nat.nth Nat.Prime s.card ≤ a := by
      have := Nat.nth_lt_of_lt_count hcount; omega
    have hn2 : 2 ≤ Nat.nth Nat.Prime s.card := (Nat.prime_nth_prime _).two_le
    rw [card_insert_of_notMem has, prod_insert has, prod_insert has, prod_range_succ, prod_range_succ]
    constructor
    · have h1 := frac_anti hn2 hnth
      have h0 : (0 : ℝ) ≤ (a : ℝ) / (a - 1) := by
        have : (1 : ℝ) < a := by exact_mod_cast ha.one_lt
        exact div_nonneg (by linarith) (by linarith)
      have h0' : (0 : ℝ) ≤ ∏ p ∈ s, ((p : ℝ) / (p - 1)) := by
        refine prod_nonneg fun p hp => ?_
        have : (1 : ℝ) < p := by exact_mod_cast (hP p (mem_insert_of_mem hp)).one_lt
        exact div_nonneg (by linarith) (by linarith)
      calc (a : ℝ) / (a - 1) * ∏ p ∈ s, ((p : ℝ) / (p - 1)) ≤
            (Nat.nth Nat.Prime s.card : ℝ) / (Nat.nth Nat.Prime s.card - 1) *
              ∏ i ∈ range s.card, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) :=
            mul_le_mul h1 ih.1 h0' (by
              have : (2 : ℝ) ≤ Nat.nth Nat.Prime s.card := by exact_mod_cast hn2
              exact div_nonneg (by linarith) (by linarith))
        _ = _ := by ring
    · calc (∏ i ∈ range s.card, Nat.nth Nat.Prime i) * Nat.nth Nat.Prime s.card ≤
            (∏ p ∈ s, p) * a := Nat.mul_le_mul ih.2 hnth
        _ = a * ∏ p ∈ s, p := by ring

/-- The first `k` primes are the primes up to the `k`-th one. -/
theorem image_nth (k : ℕ) (hk : 1 ≤ k) :
    (range k).image (Nat.nth Nat.Prime) = (Icc 1 (Nat.nth Nat.Prime (k - 1))).filter Nat.Prime := by
  ext p
  simp only [mem_image, mem_range, mem_filter, mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨(Nat.prime_nth_prime i).one_lt.le,
      Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)⟩, Nat.prime_nth_prime i⟩
  · rintro ⟨⟨_, hp⟩, hpp⟩
    refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hpp⟩
    have h1 := Nat.count_monotone Nat.Prime hp
    rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at h1
    have h2 : Nat.count Nat.Prime p < Nat.count Nat.Prime (p + 1) := by
      rw [Nat.count_succ]; simp [hpp]
    omega

theorem F_all {x : ℕ} (hx : x.Prime) (h5 : 5 ≤ x) :
    ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) <
      Real.exp Real.eulerMascheroniConstant * Real.log (thetaN x) +
        2.50637 / Real.log (thetaN x) := by
  rcases le_or_gt x (10 ^ 5) with h | h
  · exact MertProd.mertens_product_kernel x hx h5 h
  rcases lt_or_ge x (10 ^ 12) with h' | h'
  · exact F_mid (by omega) h'
  · exact F_large h'

theorem exp_gamma_ge : 1.625 ≤ Real.exp Real.eulerMascheroniConstant := by
  have h1 := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
  have h2 : Real.exp (1 / 2) ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.exp_le_exp.2 Real.one_half_lt_eulerMascheroniConstant.le
  norm_num at h1; linarith

theorem bigF_gt {r : ℝ} (hr : 3 ≤ r) :
    3.75 < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) := by
  have hl1 : 1 < Real.log r := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    exact Real.exp_one_lt_d9.trans_le (by linarith)
  set t := Real.log (Real.log r)
  have ht : 0 < t := Real.log_pos hl1
  have hG := exp_gamma_ge
  have h1 : 1.625 * t ≤ Real.exp Real.eulerMascheroniConstant * t :=
    mul_le_mul_of_nonneg_right hG ht.le
  have h2 : 3.75 < 1.625 * t + 2.50637 / t := by
    rw [← sub_pos]
    have e : 1.625 * t + 2.50637 / t - 3.75 = (1.625 * t ^ 2 - 3.75 * t + 2.50637) / t := by
      field_simp; ring
    rw [e]; apply div_pos _ ht
    nlinarith [sq_nonneg (t - 1.15385)]
  linarith

/-- **[H, Lemma C.2.2]** ([RS62, Thm. 15]): `q/φ(q) < e^γ log log r + 2.50637/log log r` for `q ≥ 1`,
`r ≥ max(3, q)`. -/
theorem div_totient_lt {q : ℕ} (hq : 1 ≤ q) {r : ℝ} (hr : 3 ≤ r) (hqr : (q : ℝ) ≤ r) :
    (q : ℝ) / Nat.totient q < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) := by
  set P := q.primeFactors with hP
  set k := P.card with hk
  set G := Real.exp Real.eulerMascheroniConstant with hGdef
  have hex := exch P (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [div_totient_eq_prod hq]
  have hF3 := bigF_gt hr
  have hgpos : ∀ i, (0 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1) := by
    intro i
    have : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
    exact div_nonneg (by linarith) (by linarith)
  have hg1 : ∀ i, (1 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1) := by
    intro i
    have : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
    rw [le_div_iff₀ (by linarith)]; linarith
  rcases le_or_gt k 3 with hk3 | hk3
  · have h1 : ∏ i ∈ range k, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) ≤
        ∏ i ∈ range 3, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) :=
      prod_le_prod_of_subset_of_one_le₀ (range_subset_range.2 hk3) (fun i _ => hgpos i)
        (fun i _ _ => hg1 i)
    have h2 : ∏ i ∈ range 3, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) = 3.75 := by
      simp only [prod_range_succ, prod_range_zero, Nat.nth_prime_zero_eq_two,
        Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
      norm_num
    linarith [hex.1]
  -- `k ≥ 4`: compare with the primes up to `x = p_k`
  set x := Nat.nth Nat.Prime (k - 1) with hx
  have himg := image_nth k (by omega)
  have hinj : Set.InjOn (Nat.nth Nat.Prime) (range k : Set ℕ) :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective.injOn
  have hprodF : ∏ i ∈ range k, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) =
      ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) := by
    rw [← himg, prod_image (fun a ha b hb h => hinj ha hb h)]
  have hθ : thetaN x = Real.log (∏ i ∈ range k, (Nat.nth Nat.Prime i : ℝ)) := by
    rw [thetaN, ← himg, sum_image (fun a ha b hb h => hinj ha hb h), Real.log_prod]
    intro i _
    exact_mod_cast (Nat.prime_nth_prime i).pos.ne'
  have hx7 : 7 ≤ x := by
    rw [hx, ← Nat.nth_prime_three_eq_seven]
    exact Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)
  have hF := F_all (Nat.prime_nth_prime (k - 1)) (le_trans (by norm_num : 5 ≤ 7) hx7)
  rw [← hx] at hF
  -- `θ(x) ≤ log r`
  have hprodpos : (0 : ℝ) < ∏ i ∈ range k, (Nat.nth Nat.Prime i : ℝ) :=
    prod_pos fun i _ => by exact_mod_cast (Nat.prime_nth_prime i).pos
  have hθr : thetaN x ≤ Real.log r := by
    rw [hθ]
    apply Real.log_le_log hprodpos
    have h1 : ∏ i ∈ range k, Nat.nth Nat.Prime i ≤ q :=
      hex.2.trans (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q))
    have h2 : ((∏ i ∈ range k, Nat.nth Nat.Prime i : ℕ) : ℝ) ≤ q := by exact_mod_cast h1
    push_cast at h2
    linarith
  -- `θ(x) ≥ log 210 ≥ 4`
  have hθ4 : 4 ≤ thetaN x := by
    rw [hθ]
    have h1 : ∏ i ∈ range 4, Nat.nth Nat.Prime i ≤ ∏ i ∈ range k, Nat.nth Nat.Prime i :=
      prod_le_prod_of_subset_of_one_le (range_subset_range.2 (by omega))
        (fun i _ _ => (Nat.prime_nth_prime i).one_lt.le)
    have h2 : ∏ i ∈ range 4, Nat.nth Nat.Prime i = 210 := by
      simp only [prod_range_succ, prod_range_zero, Nat.nth_prime_zero_eq_two,
        Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
      norm_num
    rw [h2] at h1
    have h3 : (210 : ℝ) ≤ ∏ i ∈ range k, (Nat.nth Nat.Prime i : ℝ) := by exact_mod_cast h1
    rw [Real.le_log_iff_exp_le hprodpos]
    have := Real.exp_one_lt_d9
    calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 4
      _ ≤ 210 := by norm_num
      _ ≤ _ := h3
  -- monotonicity of `t ↦ G t + c/t`
  set t₁ := Real.log (thetaN x) with ht₁
  set t₂ := Real.log (Real.log r) with ht₂
  have ht₁0 : 1.386 ≤ t₁ := by
    have : Real.log 4 ≤ t₁ := Real.log_le_log (by norm_num) hθ4
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have ht₁₂ : t₁ ≤ t₂ := Real.log_le_log (by linarith) hθr
  have hG := exp_gamma_ge
  have hmono : G * t₁ + 2.50637 / t₁ ≤ G * t₂ + 2.50637 / t₂ := by
    have ht0 : 0 < t₁ := by linarith
    have ht0' : 0 < t₂ := by linarith
    have e : G * t₂ + 2.50637 / t₂ - (G * t₁ + 2.50637 / t₁) =
        (t₂ - t₁) * (G - 2.50637 / (t₁ * t₂)) := by field_simp; ring
    have h1 : 2.50637 / (t₁ * t₂) ≤ 1.625 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have : 0 ≤ (t₂ - t₁) * (G - 2.50637 / (t₁ * t₂)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  linarith [hex.1]

end TernaryGoldbach.Prelim
