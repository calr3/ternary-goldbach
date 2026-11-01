import TernaryGoldbach.Prelim.MoebiusDecay

/-!
# `|∑_{n≤x} μ(n)/n| ≤ 0.55/(log x − 0.7521)` for `x ≥ 10¹⁰`

The `q = 1` input for [B, (2.22)] (Ramaré's route, hal-02572851).  From `MoebiusDecay.mlog_identity`
with `c = E(x)`, `m(x)(log x + E(x)) = −∑_{n≤x} μ(n)/n (E(x/n) − E(x))`, where `E(y) = ∑_{n≤y} Λ(n)/n − log y`,
so it suffices to bound `K(x) = ∑_{n≤x} |E(x/n) − E(x)|/n ≤ 0.55` (`K_bound`).  Splitting by `y = x/n`:

* **A** (`y < 1000`, `K_partA`): `[k, k+1)` cut into `⌈400/k⌉` pieces; on each piece `|E(y) − E(10⁹)|` is at
  most its value at an endpoint (`E_piece_le`), and the piecewise sum is the numerical axiom `K_pieces`
  (`≤ 0.4035`); `|E(x) − E(10⁹)| ≤ 0.00231` (`E1_diff'`, from `theta_explicit`); `≤ 0.4259` in total.
* **B** (`1000 ≤ y < 10⁹`, `K_partB`): dyadic blocks with the block maxima of the numerical axiom `K_blocks`;
  `≤ 0.0755`.
* **C** (`y ≥ 10⁹`, `K_partC`): `|E(y) − E(x)| ≤ 1/⌊y⌋ + D'(⌊y⌋)` (`E1_diff'`) on dyadic blocks, summed by
  telescoping (`tele_part`) and geometric series; the plateau term `P(M)` of `theta_explicit` (`3.7·10⁻⁷`
  for `log M < 20000`) adds `≤ 0.0074` (`partC_pth`); `≤ 0.0452`.

Each block uses `∑_{a ≤ x/n < b} 1/n ≤ log(b/a) + b/x` (`harm_piece`).  Finally
`log x + E(x) ≥ log x − log(3/√2)` ((2.13)) gives `abs_sum_moebius_div_le`.

Numerical axioms: `K_pieces`, `K_blocks` (`scripts/moebius_K_check.py`, a segmented sieve to `10⁹`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

set_option linter.constructorNameAsVariable false

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens

/-- `1/((b+1) log³ b) ≤ 0.51 (1/log² b − 1/log²(b+1))` for `b ≥ 100`. -/
theorem inv_log_cube_tele' {b : ℝ} (hb : 100 ≤ b) :
    1 / ((b + 1) * Real.log b ^ 3) ≤ 0.51 / Real.log b ^ 2 - 0.51 / Real.log (b + 1) ^ 2 := by
  have hb0 : 0 < b := by linarith
  set L := Real.log b with hL
  set M := Real.log (b + 1) with hM
  have hL1 : 4 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hb0]
    have := Real.exp_one_lt_d9
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 4
      _ ≤ 100 := by norm_num
      _ ≤ b := hb
  have hLM : L ≤ M := Real.log_le_log hb0 (by linarith)
  have hd : 1 / (b + 1) ≤ M - L := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (b + 1) / b) (by positivity)
    rw [Real.log_div (by linarith) hb0.ne'] at h
    have e : 1 - ((b + 1) / b)⁻¹ = 1 / (b + 1) := by field_simp; ring
    rw [e] at h; exact h
  have hd2 : M - L ≤ 0.01 := by
    have h := Real.log_le_sub_one_of_pos (x := (b + 1) / b) (by positivity)
    rw [Real.log_div (by linarith) hb0.ne'] at h
    have e : (b + 1) / b - 1 = 1 / b := by field_simp; ring
    have : 1 / b ≤ 0.01 := by rw [div_le_iff₀ hb0]; linarith
    linarith
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have hb1 : 0 < b + 1 := by linarith
  have h1 : 0.51 / L ^ 2 - 0.51 / M ^ 2 = 0.51 * (M - L) * (M + L) / (L ^ 2 * M ^ 2) := by
    field_simp; ring
  have h2 : 0.51 * (1 / (b + 1)) * (M + L) / (L ^ 2 * M ^ 2) ≤
      0.51 * (M - L) * (M + L) / (L ^ 2 * M ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_right hd (by linarith : (0 : ℝ) ≤ 0.51 * (M + L))
    nlinarith
  have h3 : 1 / ((b + 1) * L ^ 3) ≤ 0.51 * (1 / (b + 1)) * (M + L) / (L ^ 2 * M ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : M ^ 2 ≤ 0.51 * L * (M + L) := by nlinarith
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ L ^ 2 * (b + 1))]
  linarith

/-- `∑_{a < n < b} 1/((n+1) log³ n) ≤ 0.51/log²(a+1) − 0.51/log² b` for `a ≥ 100`. -/
theorem sum_inv_log_cube_le' {a b : ℕ} (ha : 100 ≤ a) (hab : a < b) :
    ∑ n ∈ Ioo a b, (1 : ℝ) / ((n + 1) * Real.log n ^ 3) ≤
      0.51 / Real.log ((a : ℝ) + 1) ^ 2 - 0.51 / Real.log (b : ℝ) ^ 2 := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h | h
    · rw [Ioo_succ_insert h, sum_insert (by simp)]
      have := inv_log_cube_tele' (b := (b : ℝ)) (by exact_mod_cast (by omega : 100 ≤ b))
      have := ih h
      push_cast; linarith
    · have : a = b := by omega
      subst this
      rw [Ioo_self_succ]
      push_cast; simp

/-- `E₁Λ` varies by at most `D(M)` on `[M, ∞)` (sharpened tail constant `0.51`). -/
theorem E1_diff' {M : ℕ} (hM : 200000000 ≤ M) {t : ℝ} (ht : (M : ℝ) ≤ t) :
    |E₁Λ t - E₁Λ M| ≤ 3 / M + 2 * (1 / Real.log M ^ 3 + 7.04 / √(M : ℝ)) +
      (0.51 / Real.log M ^ 2 + 14.08 / √(M : ℝ)) + Pth M := by
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
  have hpos2 : 0 ≤ 0.51 / Real.log M ^ 2 + 14.08 / √(M : ℝ) := by positivity
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
      0.51 / Real.log M ^ 2 + 14.08 / √(M : ℝ) + Se := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun n hn => abel_term_err (n := n)
      (by have := (mem_Ioo.1 hn).1; omega)).trans ?_
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← hSe]
    have h1 := sum_inv_log_cube_le' (a := M) (by omega) hlt
    have h2 := sum_inv_sqrt_le hlt
    have h1' : 0.51 / Real.log ((M : ℝ) + 1) ^ 2 ≤ 0.51 / Real.log M ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ hLM.le hlogMM 2)
    have h2' : 2 / √((M : ℝ) + 1) ≤ 2 / √(M : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hsM (Real.sqrt_le_sqrt (by linarith))
    have h3 : 0 ≤ 0.51 / Real.log (N : ℝ) ^ 2 := by positivity
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


/-- `∑_{n ≤ x, a ≤ x/n < b} 1/n ≤ log(b/a) + b/x`. -/
theorem harm_piece {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) :
    ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => a ≤ x / n ∧ x / n < b), (1 : ℝ) / n ≤
      Real.log (b / a) + b / x := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set α := ⌊x / b⌋₊ with hα
  set β := ⌊x / a⌋₊ with hβ
  have hsub : (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => a ≤ x / n ∧ x / n < b) ⊆ Ioc α β := by
    intro n hn
    obtain ⟨hn1, h1, h2⟩ := by simpa only [mem_filter, mem_Icc] using hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    refine mem_Ioc.2 ⟨?_, ?_⟩
    · have : x / b < n := by rw [div_lt_iff₀ hb]; rw [div_lt_iff₀ hn0] at h2; linarith
      exact (Nat.floor_lt (by positivity)).2 this
    · apply Nat.le_floor
      rw [le_div_iff₀ ha]; rw [le_div_iff₀ hn0] at h1; linarith
  refine (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity).trans ?_
  have hlog0 : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  rcases le_or_gt β α with hle | hlt
  · rw [Ioc_eq_empty (by omega), sum_empty]; positivity
  have hα1 : (x / b) < (α : ℝ) + 1 := Nat.lt_floor_add_one _
  have hα0 : (0 : ℝ) < (α : ℝ) + 1 := by positivity
  have hfirst : Ioc α β = insert (α + 1) (Ioc (α + 1) β) := by
    ext n; simp only [mem_Ioc, mem_insert]; omega
  rw [hfirst, sum_insert (by simp)]
  have h1 : (1 : ℝ) / ((α + 1 : ℕ) : ℝ) ≤ b / x := by
    push_cast
    rw [div_le_div_iff₀ hα0 hx]
    rw [div_lt_iff₀ hb] at hα1; linarith
  have h2 : ∑ n ∈ Ioc (α + 1) β, (1 : ℝ) / n ≤ Real.log β - Real.log ((α + 1 : ℕ) : ℝ) :=
    sum_inv_le_log (by omega) (by omega)
  have h3 : Real.log β ≤ Real.log (x / a) := by
    rcases Nat.eq_zero_or_pos β with h0 | hpos
    · omega
    exact Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le (by positivity))
  have h4 : Real.log (x / b) ≤ Real.log ((α + 1 : ℕ) : ℝ) := by
    push_cast; exact Real.log_le_log (by positivity) hα1.le
  have e : Real.log (b / a) = Real.log (x / a) - Real.log (x / b) := by
    rw [Real.log_div hb.ne' ha.ne', Real.log_div hx.ne' ha.ne', Real.log_div hx.ne' hb.ne']; ring
  linarith

/-- `Ψ(k) = ∑_{n ≤ k} Λ(n)/n`. -/
noncomputable def PsiT (k : ℕ) : ℝ := ∑ n ∈ Icc 1 k, (Λ n : ℝ) / n

theorem E1_eq (y : ℝ) : E₁Λ y = PsiT ⌊y⌋₊ - Real.log y := rfl

/-- The anchor `E(10⁹)`. -/
noncomputable def EZ : ℝ := E₁Λ (10 ^ 9 : ℝ)

/-- Number of pieces of `[k, k+1)`: `⌈400/k⌉`. -/
def mk (k : ℕ) : ℕ := (400 + k - 1) / k

noncomputable def pa (k i : ℕ) : ℝ := k + i / (mk k : ℝ)
noncomputable def pb (k i : ℕ) : ℝ := k + (i + 1) / (mk k : ℝ)
noncomputable def pg (k i : ℕ) : ℝ :=
  max |PsiT k - Real.log (pa k i) - EZ| |PsiT k - Real.log (pb k i) - EZ|

/-- **Numerical axiom** (`scripts/moebius_K_check.py`; value `0.40342`): the piecewise integral of
`|E(y) − E(10⁹)| dy/y` over `[1, 1000)`, with `[k, k+1)` cut into `⌈400/k⌉` pieces and the maximum
taken on each piece. -/
axiom K_pieces :
    ∑ k ∈ Ico 1 1000, ∑ i ∈ range (mk k), pg k i * Real.log (pb k i / pa k i) ≤ 0.4035

/-- Block maxima of `|E(y) − E(10⁹)|` on `[1000·2ʲ, 1000·2ʲ⁺¹)` (rounded up). -/
noncomputable def hblk : ℕ → ℝ
  | 0 => 0.02012
  | 1 => 0.01191
  | 2 => 0.007334
  | 3 => 0.006359
  | 4 => 0.005002
  | 5 => 0.003464
  | 6 => 0.002257
  | 7 => 0.001477
  | 8 => 0.001299
  | 9 => 0.0007304
  | 10 => 0.0006189
  | 11 => 0.0003705
  | 12 => 0.0002869
  | 13 => 0.0001922
  | 14 => 0.0001315
  | 15 => 0.000125
  | 16 => 0.00007399
  | 17 => 0.00005302
  | 18 => 0.00003196
  | 19 => 0.00002567
  | _ => 1

theorem hblk_nonneg (j : ℕ) : 0 ≤ hblk j := by
  unfold hblk; split <;> norm_num

/-- **Numerical axiom** (`scripts/moebius_K_check.py`): for `1000 ≤ k < 10⁹`,
`|Ψ(k) − log t − E(10⁹)| ≤ hblk(⌊log₂(k/1000)⌋)` at `t = k` and `t = k + 1`. -/
axiom K_blocks (k : ℕ) (h1 : 1000 ≤ k) (h2 : k < 10 ^ 9) :
    max |PsiT k - Real.log k - EZ| |PsiT k - Real.log (k + 1) - EZ| ≤ hblk (Nat.log 2 (k / 1000))

/-- On `[a, b) ⊆ [k, k+1)`, `|E(y) − c| ≤ max(|Ψ(k) − log a − c|, |Ψ(k) − log b − c|)`. -/
theorem E_piece_le {k : ℕ} {y a b c : ℝ} (hk : ⌊y⌋₊ = k) (ha0 : 0 < a) (ha : a ≤ y) (hb : y ≤ b) :
    |E₁Λ y - c| ≤ max |PsiT k - Real.log a - c| |PsiT k - Real.log b - c| := by
  rw [E1_eq, hk]
  have h1 : Real.log a ≤ Real.log y := Real.log_le_log ha0 ha
  have h2 : Real.log y ≤ Real.log b := Real.log_le_log (by linarith) hb
  rw [abs_le]
  constructor
  · have := le_max_right |PsiT k - Real.log a - c| |PsiT k - Real.log b - c|
    have := neg_abs_le (PsiT k - Real.log b - c)
    linarith
  · have := le_max_left |PsiT k - Real.log a - c| |PsiT k - Real.log b - c|
    have := le_abs_self (PsiT k - Real.log a - c)
    linarith

/-- `D'(M)` from `E1_diff'`. -/
noncomputable def Dp (M : ℝ) : ℝ :=
  3 / M + 2 * (1 / Real.log M ^ 3 + 7.04 / √M) + (0.51 / Real.log M ^ 2 + 14.08 / √M) + Pth M

theorem Dp_anti {M M' : ℝ} (hM : 3 ≤ M) (h : M ≤ M') : Dp M' ≤ Dp M := by
  have hM0 : 0 < M := by linarith
  have hL : 1 ≤ Real.log M := by
    rw [Real.le_log_iff_exp_le hM0]; exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hM
  have hL' : Real.log M ≤ Real.log M' := Real.log_le_log hM0 h
  have hs : √M ≤ √M' := Real.sqrt_le_sqrt h
  have hs0 : 0 < √M := Real.sqrt_pos.2 hM0
  unfold Dp
  have a1 : 3 / M' ≤ 3 / M := div_le_div_of_nonneg_left (by norm_num) hM0 h
  have a2 : 1 / Real.log M' ^ 3 ≤ 1 / Real.log M ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by linarith) hL' 3)
  have a3 : 7.04 / √M' ≤ 7.04 / √M := div_le_div_of_nonneg_left (by norm_num) hs0 hs
  have a4 : 0.51 / Real.log M' ^ 2 ≤ 0.51 / Real.log M ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by linarith) hL' 2)
  have a5 : 14.08 / √M' ≤ 14.08 / √M := div_le_div_of_nonneg_left (by norm_num) hs0 hs
  have a6 : Pth M' ≤ Pth M := by
    unfold Pth; split_ifs with h1 h2 h2 <;> try norm_num
    exact h2 (lt_of_le_of_lt hL' h1)
  linarith

/-- `|E(y) − E(x)| ≤ 1/⌊y⌋ + D'(⌊y⌋)` for `2·10⁸ ≤ y ≤ x`. -/
theorem E_far {x y : ℝ} (hy : 200000000 ≤ y) (hyx : y ≤ x) :
    |E₁Λ y - E₁Λ x| ≤ 1 / ⌊y⌋₊ + Dp ⌊y⌋₊ := by
  set M := ⌊y⌋₊ with hM
  have hM1 : 200000000 ≤ M := Nat.le_floor (by exact_mod_cast hy)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMy : (M : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyM : y < M + 1 := Nat.lt_floor_add_one y
  have h1 := E1_diff' hM1 (hMy.trans hyx)
  have h2 : |E₁Λ y - E₁Λ (M : ℝ)| ≤ 1 / M := by
    rw [E1_eq, E1_eq, Nat.floor_natCast, ← hM]
    have : Real.log y - Real.log M ≤ 1 / M := by
      have := Real.log_le_sub_one_of_pos (x := y / M) (by positivity)
      rw [Real.log_div (by linarith) hM0.ne'] at this
      have e : y / M - 1 ≤ 1 / M := by rw [div_sub_one hM0.ne', div_le_div_iff_of_pos_right hM0]; linarith
      linarith
    have : Real.log M ≤ Real.log y := Real.log_le_log hM0 hMy
    rw [abs_le]; constructor <;> linarith
  unfold Dp
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem log_1e9_ge : (20.7 : ℝ) ≤ Real.log (10 ^ 9) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 20.7 = Real.exp 1 ^ 20 * Real.exp 0.7 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h3 : Real.exp 0.7 ≤ 2.02 := by
    have := Real.exp_bound' (x := 0.7) (by norm_num) (by norm_num) (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
  rw [h2]
  calc Real.exp 1 ^ 20 * Real.exp 0.7 ≤ (2.7182818286 : ℝ) ^ 20 * 2.02 :=
        mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 20) h3 (by positivity) (by positivity)
    _ ≤ 10 ^ 9 := by norm_num

theorem Dp_1e9_le : Dp (10 ^ 9) ≤ 0.00231 := by
  have hL := log_1e9_ge
  have hs : (31622 : ℝ) ≤ √(10 ^ 9) := Real.le_sqrt_of_sq_le (by norm_num)
  unfold Dp
  have a1 : 1 / Real.log (10 ^ 9) ^ 3 ≤ 1 / 20.7 ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 3)
  have a2 : 7.04 / √(10 ^ 9 : ℝ) ≤ 7.04 / 31622 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have a3 : 0.51 / Real.log (10 ^ 9) ^ 2 ≤ 0.51 / 20.7 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 2)
  have a4 : 14.08 / √(10 ^ 9 : ℝ) ≤ 14.08 / 31622 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have a5 := Pth_le (10 ^ 9 : ℝ)
  norm_num at a1 a2 a3 a4 a5 ⊢
  linarith

theorem log_1000_le : Real.log 1000 ≤ 6.932 := by
  have h : Real.log 1000 ≤ Real.log (2 ^ 10) := Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  have := Real.log_two_lt_d9
  push_cast at h; linarith

theorem sum_inv_Ico_le : ∑ k ∈ Ico (1 : ℕ) 1000, (1 : ℝ) / (k : ℝ) ≤ 7.932 := by
  have hs : Ico (1 : ℕ) 1000 = insert 1 (Ioc 1 999) := by ext n; simp only [mem_Ico, mem_insert, mem_Ioc]; omega
  rw [hs, sum_insert (by simp)]
  have h := sum_inv_le_log (a := 1) (b := 999) (by norm_num) (by norm_num)
  have h2 : Real.log 999 ≤ Real.log 1000 := Real.log_le_log (by norm_num) (by norm_num)
  have := log_1000_le
  push_cast at h ⊢; simp only [Real.log_one, sub_zero] at h
  linarith

theorem mk_pos {k : ℕ} (hk : 1 ≤ k) : 0 < mk k := by
  unfold mk; exact Nat.div_pos (by omega) (by omega)

theorem mk_le {k : ℕ} (hk : 1 ≤ k) : (mk k : ℝ) ≤ 400 / k + 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h : mk k * k ≤ 400 + k - 1 := Nat.div_mul_le_self _ _
  have h' : (mk k : ℝ) * k ≤ 400 + k := by
    have : ((mk k * k : ℕ) : ℝ) ≤ ((400 + k - 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    have : ((400 + k - 1 : ℕ) : ℝ) ≤ 400 + k := by
      rw [Nat.cast_sub (by omega)]; push_cast; linarith
    push_cast at this; linarith
  rw [div_add_one hk0.ne', le_div_iff₀ hk0]; linarith

/-- The number of pieces: `∑_{k<1000} ⌈400/k⌉ ≤ 4175`. -/
theorem card_pieces : ∑ k ∈ Ico (1 : ℕ) 1000, (mk k : ℝ) ≤ 4175 := by
  calc ∑ k ∈ Ico (1 : ℕ) 1000, (mk k : ℝ) ≤ ∑ k ∈ Ico (1 : ℕ) 1000, (400 * ((1 : ℝ) / (k : ℝ)) + 1) :=
        sum_le_sum fun k hk => by
          have := mk_le (k := k) (mem_Ico.1 hk).1; rw [mul_one_div]; exact this
    _ = 400 * ∑ k ∈ Ico (1 : ℕ) 1000, (1 : ℝ) / (k : ℝ) + 999 := by
        rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico]; norm_num
    _ ≤ 400 * 7.932 + 999 := by have := sum_inv_Ico_le; linarith
    _ ≤ 4175 := by norm_num

/-- `|E(10⁹)| ≤ 1`. -/
theorem abs_EZ_le : |EZ| ≤ 1 := by
  have h1 := sum_vonMangoldt_div_le_log (x := (10 ^ 9 : ℝ)) (by norm_num)
  have h2 := log_sub_le_sum_vonMangoldt_div (x := (10 ^ 9 : ℝ)) (by norm_num)
  have h3 : Real.log (3 / √2) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have : (3 : ℝ) / √2 ≤ 2.2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (1.4 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    have := Real.exp_one_gt_d9
    linarith
  unfold EZ
  rw [E1_eq, PsiT]
  have e : ∑ n ∈ Icc 1 ⌊(10 ^ 9 : ℝ)⌋₊, (Λ n : ℝ) / n = ∑ n ∈ Icc 1 ⌊(10 ^ 9 : ℝ)⌋₊, (Λ n : ℝ) / n := rfl
  rw [abs_le]; constructor <;> linarith

theorem E_x_EZ {x : ℝ} (hx : 1e10 ≤ x) : |E₁Λ x - EZ| ≤ 0.00231 := by
  have h := E1_diff' (M := 10 ^ 9) (by norm_num) (t := x) (by push_cast; linarith)
  have e : (((10 ^ 9 : ℕ)) : ℝ) = (10 ^ 9 : ℝ) := by push_cast; ring
  rw [e] at h
  have := Dp_1e9_le
  unfold Dp at this
  unfold EZ
  linarith

theorem pg_le {k i : ℕ} (hk : k ∈ Ico 1 1000) (hi : i < mk k) : pg k i ≤ 15 := by
  have hk1 : 1 ≤ k := (mem_Ico.1 hk).1
  have hk2 : k < 1000 := (mem_Ico.1 hk).2
  have hm : (0 : ℝ) < mk k := by exact_mod_cast mk_pos hk1
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkr2 : (k : ℝ) + 1 ≤ 1000 := by exact_mod_cast hk2
  have hpa1 : 1 ≤ pa k i := by
    unfold pa
    have : (0 : ℝ) ≤ i / mk k := by positivity
    linarith
  have hpb : pb k i ≤ 1000 := by
    unfold pb
    have : ((i : ℝ) + 1) / mk k ≤ 1 := by
      rw [div_le_one hm]; exact_mod_cast hi
    linarith
  have hpab : pa k i ≤ pb k i := by
    unfold pa pb; gcongr; linarith
  have hPsi0 : 0 ≤ PsiT k := sum_nonneg fun n _ => by
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity
  have hPsi : PsiT k ≤ Real.log k := by
    have := sum_vonMangoldt_div_le_log (x := (k : ℝ)) hkr
    rwa [Nat.floor_natCast] at this
  have hlk : Real.log k ≤ 6.932 := (Real.log_le_log (by linarith) (by linarith)).trans log_1000_le
  have hEZ := abs_EZ_le
  have hla : 0 ≤ Real.log (pa k i) := Real.log_nonneg hpa1
  have hlb : Real.log (pb k i) ≤ 6.932 := (Real.log_le_log (by linarith) hpb).trans log_1000_le
  have hla' : Real.log (pa k i) ≤ 6.932 := (Real.log_le_log (by linarith) (hpab.trans hpb)).trans log_1000_le
  have hlb' : 0 ≤ Real.log (pb k i) := Real.log_nonneg (hpa1.trans hpab)
  unfold pg
  rw [abs_le] at hEZ
  apply max_le <;> rw [abs_le] <;> constructor <;> linarith

theorem log_pb_pa_le {k i : ℕ} (hk : 1 ≤ k) :
    Real.log (pb k i / pa k i) ≤ 1 / ((mk k : ℝ) * k) := by
  have hm : (0 : ℝ) < mk k := by exact_mod_cast mk_pos hk
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpa : (k : ℝ) ≤ pa k i := by
    unfold pa
    have : (0 : ℝ) ≤ i / mk k := by positivity
    linarith
  have hpa0 : 0 < pa k i := by linarith
  have h := Real.log_le_sub_one_of_pos (x := pb k i / pa k i) (by
    have : 0 < pb k i := by unfold pb; positivity
    positivity)
  have e : pb k i / pa k i - 1 = (1 / mk k) / pa k i := by
    unfold pb pa; field_simp; ring
  rw [e] at h
  refine h.trans ?_
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity)
  have := mul_le_mul_of_nonneg_left hpa hm.le
  linarith [mul_comm (pa k i) (mk k : ℝ)]

/-- The pieces `(k, i)`, `1 ≤ k < 1000`, `i < ⌈400/k⌉`. -/
def pieceSet : Finset (Σ _ : ℕ, ℕ) := (Ico 1 1000).sigma (fun k => range (mk k))

theorem pieceSet_def : pieceSet = (Ico 1 1000).sigma (fun k => range (mk k)) := rfl

attribute [irreducible] pieceSet

/-- The piece containing `y`. -/
noncomputable def gP (y : ℝ) : Σ _ : ℕ, ℕ := ⟨⌊y⌋₊, ⌊(y - ⌊y⌋₊) * mk ⌊y⌋₊⌋₊⟩

theorem gP_mem {y : ℝ} (h1 : 1 ≤ y) (h2 : y < 1000) : gP y ∈ pieceSet := by
  have hk1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hk2 : ⌊y⌋₊ < 1000 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast h2)
  rw [pieceSet_def, gP, mem_sigma, mem_Ico, mem_range]
  refine ⟨⟨hk1, hk2⟩, ?_⟩
  have hm : (0 : ℝ) < mk ⌊y⌋₊ := by exact_mod_cast mk_pos hk1
  have hfl := Nat.floor_le (show 0 ≤ y by linarith)
  have h0 : (0 : ℝ) ≤ y - ⌊y⌋₊ := by linarith
  have h1' : y - ⌊y⌋₊ < 1 := by have := Nat.lt_floor_add_one y; linarith
  apply (Nat.floor_lt (by positivity)).2
  calc (y - ⌊y⌋₊) * mk ⌊y⌋₊ < 1 * mk ⌊y⌋₊ := mul_lt_mul_of_pos_right h1' hm
    _ = ((mk ⌊y⌋₊ : ℕ) : ℝ) := one_mul _

theorem gP_piece {y : ℝ} {k i : ℕ} (hy : 1 ≤ y) (hg : gP y = ⟨k, i⟩) :
    ⌊y⌋₊ = k ∧ pa k i ≤ y ∧ y < pb k i := by
  rw [gP, Sigma.mk.inj_iff] at hg
  obtain ⟨hkk, hii⟩ := hg
  have hii' : ⌊(y - ⌊y⌋₊) * mk ⌊y⌋₊⌋₊ = i := eq_of_heq hii
  rw [hkk] at hii'
  have hk1 : 1 ≤ k := by rw [← hkk]; exact Nat.le_floor (by exact_mod_cast hy)
  have hm : (0 : ℝ) < mk k := by exact_mod_cast mk_pos hk1
  have hfl0 := Nat.floor_le (show 0 ≤ y by linarith)
  rw [hkk] at hfl0
  have h0 : (0 : ℝ) ≤ (y - k) * mk k := by
    have : (0 : ℝ) ≤ y - k := by linarith
    positivity
  have hfl := Nat.floor_le h0
  have hlt := Nat.lt_floor_add_one ((y - k) * mk k)
  rw [hii'] at hfl hlt
  refine ⟨hkk, ?_, ?_⟩
  · unfold pa
    have : (i : ℝ) / mk k ≤ y - k := by rw [div_le_iff₀ hm]; linarith
    linarith
  · unfold pb
    have : y - k < ((i : ℝ) + 1) / mk k := by rw [lt_div_iff₀ hm]; linarith
    linarith

theorem card_pieceSet_le : (pieceSet.card : ℝ) ≤ 4175 := by
  have h : pieceSet.card = ∑ k ∈ Ico 1 1000, mk k := by
    rw [pieceSet_def, card_sigma]; simp only [card_range]
  rw [h]; push_cast; exact card_pieces

/-- One piece: `∑_{gP(x/n) = (k,i)} |E(x/n) − E(x)|/n ≤ (pg + D)(log(pb/pa) + pb/x)`. -/
theorem K_fiber {x : ℝ} (hx : 1e10 ≤ x) {k i : ℕ} (hp : (⟨k, i⟩ : Σ _ : ℕ, ℕ) ∈ pieceSet) :
    ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => x / n < 1000)).filter (fun n : ℕ => gP (x / n) = ⟨k, i⟩),
      |E₁Λ (x / n) - E₁Λ x| / n ≤
      (pg k i + 0.00231) * (Real.log (pb k i / pa k i) + pb k i / x) := by
  have hx0 : 0 < x := by linarith
  have hD := E_x_EZ hx
  rw [pieceSet_def, mem_sigma] at hp
  obtain ⟨hk, hi⟩ := hp
  have hk1 : 1 ≤ k := (mem_Ico.1 hk).1
  have hm : (0 : ℝ) < mk k := by exact_mod_cast mk_pos hk1
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpa0 : 0 < pa k i := by unfold pa; positivity
  have hpab : pa k i ≤ pb k i := by unfold pa pb; gcongr; linarith
  have hy1 : ∀ n ∈ Icc 1 ⌊x⌋₊, (1 : ℝ) ≤ x / n ∧ (0 : ℝ) < n := by
    intro n hn
    obtain ⟨hn1, hnx⟩ := mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnx' : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnx) (Nat.floor_le hx0.le)
    exact ⟨by rw [le_div_iff₀ hn0]; linarith, hn0⟩
  have hsub : ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => x / n < 1000)).filter
      (fun n : ℕ => gP (x / n) = ⟨k, i⟩) ⊆
      (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => pa k i ≤ x / n ∧ x / n < pb k i) := by
    intro n hn
    obtain ⟨hnA, hg⟩ := mem_filter.1 hn
    have hnI := (mem_filter.1 hnA).1
    obtain ⟨-, ha, hb⟩ := gP_piece (hy1 n hnI).1 hg
    exact mem_filter.2 ⟨hnI, ha, hb⟩
  have hpt : ∀ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => x / n < 1000)).filter
      (fun n : ℕ => gP (x / n) = ⟨k, i⟩), |E₁Λ (x / n) - E₁Λ x| / n ≤ (pg k i + 0.00231) * (1 / n) := by
    intro n hn
    obtain ⟨hnA, hg⟩ := mem_filter.1 hn
    have hnI := (mem_filter.1 hnA).1
    obtain ⟨hkk, ha, hb⟩ := gP_piece (hy1 n hnI).1 hg
    have h1 := E_piece_le (c := EZ) hkk hpa0 ha hb.le
    have h2 : |E₁Λ (x / n) - E₁Λ x| ≤ pg k i + 0.00231 := by
      have := abs_sub_le (E₁Λ (x / n)) EZ (E₁Λ x)
      rw [abs_sub_comm EZ] at this
      unfold pg; linarith
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right h2 (by have := (hy1 n hnI).2; positivity)
  have hpgD : 0 ≤ pg k i + 0.00231 := by unfold pg; positivity
  calc _ ≤ ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => x / n < 1000)).filter
          (fun n : ℕ => gP (x / n) = ⟨k, i⟩), (pg k i + 0.00231) * (1 / (n : ℝ)) := sum_le_sum hpt
    _ ≤ ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => pa k i ≤ x / n ∧ x / n < pb k i),
          (pg k i + 0.00231) * (1 / (n : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ = (pg k i + 0.00231) * ∑ n ∈ (Icc 1 ⌊x⌋₊).filter
          (fun n : ℕ => pa k i ≤ x / n ∧ x / n < pb k i), (1 / (n : ℝ)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harm_piece hx0 hpa0 hpab) hpgD

theorem pa_pos {k i : ℕ} (hk : 1 ≤ k) : 0 < pa k i := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold pa; positivity

theorem pb_eq {k i : ℕ} : pb k i = pa k (i + 1) := by
  unfold pb pa; push_cast; ring

theorem sum_log_piece {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ range (mk k), Real.log (pb k i / pa k i) = Real.log (k + 1) - Real.log k := by
  have hm : (0 : ℝ) < mk k := by exact_mod_cast mk_pos hk
  have e : ∀ i ∈ range (mk k), Real.log (pb k i / pa k i) =
      Real.log (pa k (i + 1)) - Real.log (pa k i) := by
    intro i _
    rw [Real.log_div (by rw [pb_eq]; exact (pa_pos hk).ne') (pa_pos hk).ne', pb_eq]
  rw [sum_congr rfl e, sum_range_sub (fun i => Real.log (pa k i))]
  have h1 : pa k (mk k) = k + 1 := by unfold pa; rw [div_self hm.ne']
  have h0 : pa k 0 = k := by unfold pa; simp
  rw [h1, h0]

theorem sum_pieces_log : ∑ p ∈ pieceSet, Real.log (pb p.1 p.2 / pa p.1 p.2) = Real.log 1000 := by
  rw [pieceSet_def, sum_sigma]
  rw [sum_congr rfl fun k hk => sum_log_piece (mem_Ico.1 hk).1]
  rw [sum_Ico_eq_sum_range]
  have e : ∀ j ∈ range (1000 - 1), Real.log (((1 + j : ℕ) : ℝ) + 1) - Real.log ((1 + j : ℕ) : ℝ) =
      Real.log (((j + 1 : ℕ) : ℝ) + 1) - Real.log (((j : ℕ) : ℝ) + 1) := by
    intro j _; push_cast; ring_nf
  rw [sum_congr rfl e, sum_range_sub (fun j : ℕ => Real.log ((j : ℝ) + 1))]
  norm_num

theorem sum_pieces_err {x : ℝ} (hx : 1e10 ≤ x) :
    ∑ p ∈ pieceSet, (pg p.1 p.2 + 0.00231) * (pb p.1 p.2 / x) ≤ 0.0063 := by
  have hx0 : 0 < x := by linarith
  have hbound : ∀ p ∈ pieceSet, (pg p.1 p.2 + 0.00231) * (pb p.1 p.2 / x) ≤ 15.01 * (1000 / x) := by
    rintro ⟨k, i⟩ hp
    rw [pieceSet_def, mem_sigma] at hp
    obtain ⟨hk, hi⟩ := hp
    have hi' := mem_range.1 hi
    have hk1 : 1 ≤ k := (mem_Ico.1 hk).1
    have hm : (0 : ℝ) < mk k := by exact_mod_cast mk_pos hk1
    have hpb : pb k i ≤ 1000 := by
      unfold pb
      have : ((i : ℝ) + 1) / mk k ≤ 1 := by rw [div_le_one hm]; exact_mod_cast hi'
      have : (k : ℝ) + 1 ≤ 1000 := by exact_mod_cast (mem_Ico.1 hk).2
      linarith
    have hpb0 : 0 ≤ pb k i := by rw [pb_eq]; exact (pa_pos hk1).le
    have hpg := pg_le hk hi'
    have hpg0 : 0 ≤ pg k i := by unfold pg; positivity
    dsimp only
    exact mul_le_mul (by linarith) (div_le_div_of_nonneg_right hpb hx0.le) (by positivity)
      (by norm_num)
  refine (sum_le_sum hbound).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have : (1000 : ℝ) / x ≤ 1e-7 := by rw [div_le_iff₀ hx0]; linarith
  calc (pieceSet.card : ℝ) * (15.01 * (1000 / x)) ≤ 4175 * (15.01 * 1e-7) :=
        mul_le_mul card_pieceSet_le (by linarith) (by positivity) (by norm_num)
    _ ≤ 0.0063 := by norm_num

theorem sum_pieces_main : ∑ p ∈ pieceSet, pg p.1 p.2 * Real.log (pb p.1 p.2 / pa p.1 p.2) ≤ 0.4035 := by
  rw [pieceSet_def, sum_sigma]; exact K_pieces

/-- **Part A** of the `K` bound (`x/n < 1000`): `≤ 0.4035 + 0.00231 log 1000 + 0.0063 ≤ 0.4259`. -/
theorem K_partA {x : ℝ} (hx : 1e10 ≤ x) :
    ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => x / n < 1000), |E₁Λ (x / n) - E₁Λ x| / n ≤ 0.4259 := by
  have hx0 : 0 < x := by linarith
  have hmaps : ∀ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => x / n < 1000), gP (x / n) ∈ pieceSet := by
    intro n hn
    obtain ⟨hnI, hlt⟩ := mem_filter.1 hn
    obtain ⟨hn1, hnx⟩ := mem_Icc.1 hnI
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnx' : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnx) (Nat.floor_le hx0.le)
    exact gP_mem (by rw [le_div_iff₀ hn0]; linarith) hlt
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ p ∈ pieceSet, ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => x / n < 1000)).filter
      (fun n : ℕ => gP (x / n) = p), |E₁Λ (x / n) - E₁Λ x| / n ≤
      (pg p.1 p.2 + 0.00231) * (Real.log (pb p.1 p.2 / pa p.1 p.2) + pb p.1 p.2 / x) := by
    rintro ⟨k, i⟩ hp
    exact K_fiber hx hp
  refine (sum_le_sum hfib).trans ?_
  have hsplit : ∑ p ∈ pieceSet, (pg p.1 p.2 + 0.00231) *
        (Real.log (pb p.1 p.2 / pa p.1 p.2) + pb p.1 p.2 / x) =
      ∑ p ∈ pieceSet, pg p.1 p.2 * Real.log (pb p.1 p.2 / pa p.1 p.2) +
        0.00231 * ∑ p ∈ pieceSet, Real.log (pb p.1 p.2 / pa p.1 p.2) +
        ∑ p ∈ pieceSet, (pg p.1 p.2 + 0.00231) * (pb p.1 p.2 / x) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun p _ => by ring
  rw [hsplit, sum_pieces_log]
  have := sum_pieces_main
  have := sum_pieces_err hx
  have := log_1000_le
  linarith

/-- Block index of `y ∈ [1000, 10⁹)`. -/
noncomputable def gB (y : ℝ) : ℕ := Nat.log 2 (⌊y⌋₊ / 1000)

theorem gB_block {y : ℝ} (h1 : 1000 ≤ y) (h2 : y < 10 ^ 9) :
    gB y < 20 ∧ 1000 * 2 ^ gB y ≤ y ∧ y < 1000 * 2 ^ (gB y + 1) := by
  have hk1 : 1000 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hk2 : ⌊y⌋₊ < 10 ^ 9 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast h2)
  have hd : ⌊y⌋₊ / 1000 ≠ 0 := by omega
  have hlo : 2 ^ gB y ≤ ⌊y⌋₊ / 1000 := Nat.pow_log_le_self 2 hd
  have hhi : ⌊y⌋₊ / 1000 < 2 ^ (gB y + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlo' : 2 ^ gB y * 1000 ≤ ⌊y⌋₊ := (Nat.le_div_iff_mul_le (by norm_num)).1 hlo
  have hhi' : ⌊y⌋₊ < 2 ^ (gB y + 1) * 1000 := (Nat.div_lt_iff_lt_mul (by norm_num)).1 hhi
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.log_lt_of_lt_pow hd
    calc ⌊y⌋₊ / 1000 < 10 ^ 6 := by omega
      _ ≤ 2 ^ 20 := by norm_num
  · have hfl := Nat.floor_le (by linarith : 0 ≤ y)
    have : ((2 ^ gB y * 1000 : ℕ) : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hlo'
    push_cast at this; linarith
  · have hlt := Nat.lt_floor_add_one y
    have : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (gB y + 1) * 1000 : ℕ) : ℝ) := by exact_mod_cast hhi'
    push_cast at this; linarith

theorem E_blockB {x y : ℝ} (hx : 1e10 ≤ x) (h1 : 1000 ≤ y) (h2 : y < 10 ^ 9) :
    |E₁Λ y - E₁Λ x| ≤ hblk (gB y) + 0.00231 := by
  have hk1 : 1000 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hk2 : ⌊y⌋₊ < 10 ^ 9 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast h2)
  have hk0 : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast (by omega : 0 < ⌊y⌋₊)
  have hky : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyk : y ≤ ⌊y⌋₊ + 1 := (Nat.lt_floor_add_one y).le
  have h := E_piece_le (c := EZ) (k := ⌊y⌋₊) rfl hk0 hky hyk
  have hb := K_blocks ⌊y⌋₊ hk1 hk2
  have hD := E_x_EZ hx
  have := abs_sub_le (E₁Λ y) EZ (E₁Λ x)
  rw [abs_sub_comm EZ] at this
  unfold gB; linarith

/-- **Part B** of the `K` bound (`1000 ≤ x/n < 10⁹`). -/
theorem K_partB {x : ℝ} (hx : 1e10 ≤ x) :
    ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 1000 ≤ x / n ∧ x / n < 10 ^ 9),
      |E₁Λ (x / n) - E₁Λ x| / n ≤ 0.0755 := by
  have hx0 : 0 < x := by linarith
  have hn0 : ∀ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 1000 ≤ x / n ∧ x / n < 10 ^ 9), (0 : ℝ) < n :=
    fun n hn => by exact_mod_cast (mem_Icc.1 (mem_filter.1 hn).1).1
  have hmaps : ∀ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 1000 ≤ x / n ∧ x / n < 10 ^ 9),
      gB (x / n) ∈ range 20 := fun n hn => by
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hn
    exact mem_range.2 (gB_block h1 h2).1
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ range 20, ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter
      (fun n : ℕ => 1000 ≤ x / n ∧ x / n < 10 ^ 9)).filter (fun n : ℕ => gB (x / n) = j),
      |E₁Λ (x / n) - E₁Λ x| / n ≤ (hblk j + 0.00231) * (Real.log 2 + 1000 * 2 ^ (j + 1) / x) := by
    intro j _
    have h0 : 0 ≤ hblk j + 0.00231 := by have := hblk_nonneg j; linarith
    have hsub : ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 1000 ≤ x / n ∧ x / n < 10 ^ 9)).filter
        (fun n : ℕ => gB (x / n) = j) ⊆ (Icc 1 ⌊x⌋₊).filter
        (fun n : ℕ => 1000 * 2 ^ j ≤ x / n ∧ x / n < 1000 * 2 ^ (j + 1)) := by
      intro n hn
      obtain ⟨hnA, hg⟩ := mem_filter.1 hn
      obtain ⟨hnI, h1, h2⟩ := mem_filter.1 hnA
      obtain ⟨-, hlo, hhi⟩ := gB_block h1 h2
      rw [hg] at hlo hhi
      exact mem_filter.2 ⟨hnI, hlo, hhi⟩
    have hpt : ∀ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 1000 ≤ x / n ∧ x / n < 10 ^ 9)).filter
        (fun n : ℕ => gB (x / n) = j), |E₁Λ (x / n) - E₁Λ x| / n ≤ (hblk j + 0.00231) * (1 / n) := by
      intro n hn
      obtain ⟨hnA, hg⟩ := mem_filter.1 hn
      obtain ⟨-, h1, h2⟩ := mem_filter.1 hnA
      have := E_blockB hx h1 h2
      rw [hg] at this
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right this (by have := hn0 n hnA; positivity)
    have hlog : Real.log (1000 * 2 ^ (j + 1) / (1000 * 2 ^ j)) = Real.log 2 := by
      congr 1; rw [pow_succ]; field_simp
    calc _ ≤ ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 1000 ≤ x / n ∧ x / n < 10 ^ 9)).filter
          (fun n : ℕ => gB (x / n) = j), (hblk j + 0.00231) * (1 / (n : ℝ)) := sum_le_sum hpt
      _ ≤ ∑ n ∈ (Icc 1 ⌊x⌋₊).filter
          (fun n : ℕ => 1000 * 2 ^ j ≤ x / n ∧ x / n < 1000 * 2 ^ (j + 1)),
          (hblk j + 0.00231) * (1 / (n : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => by
          have : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 (mem_filter.1 hn).1).1
          positivity
      _ = (hblk j + 0.00231) * ∑ n ∈ (Icc 1 ⌊x⌋₊).filter
          (fun n : ℕ => 1000 * 2 ^ j ≤ x / n ∧ x / n < 1000 * 2 ^ (j + 1)), (1 / (n : ℝ)) := by
        rw [mul_sum]
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ h0
        have := harm_piece hx0 (a := 1000 * 2 ^ j) (b := 1000 * 2 ^ (j + 1)) (by positivity)
          (by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j])
        rwa [hlog] at this
  refine (sum_le_sum hfib).trans ?_
  have hl2 : Real.log 2 ≤ 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hxj : ∀ j : ℕ, 1000 * 2 ^ (j + 1) / x ≤ 2 ^ (j + 1) * 1e-7 := fun j => by
    rw [div_le_iff₀ hx0]
    have : (0 : ℝ) < 2 ^ (j + 1) := by positivity
    nlinarith
  refine (sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (add_le_add hl2 (hxj j))
    (by have := hblk_nonneg j; linarith)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hblk]
  norm_num

/-! ### Part C: `x/n ≥ 10⁹` -/

/-- `M_j = 10⁹·2ʲ`. -/
noncomputable def Mj (j : ℕ) : ℝ := 10 ^ 9 * 2 ^ j

theorem Mj_pos (j : ℕ) : 0 < Mj j := by unfold Mj; positivity

theorem Mj_ge (j : ℕ) : (10 : ℝ) ^ 9 ≤ Mj j := by
  unfold Mj; have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num); nlinarith

theorem log_Mj (j : ℕ) : Real.log (Mj j) = Real.log (10 ^ 9) + j * Real.log 2 := by
  unfold Mj; rw [Real.log_mul (by positivity) (by positivity), Real.log_pow 2 j]

theorem sqrt_two_pow' (j : ℕ) : √((2 : ℝ) ^ j) = √2 ^ j := by
  rw [show (2 : ℝ) ^ j = (√2 ^ j) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (by positivity)

theorem sqrt_Mj (j : ℕ) : √(Mj j) = √(10 ^ 9) * √2 ^ j := by
  unfold Mj; rw [Real.sqrt_mul (by positivity), sqrt_two_pow']

theorem sqrt2_bounds : (1.414213 : ℝ) ≤ √2 ∧ √2 ≤ 1.414214 := by
  refine ⟨Real.le_sqrt_of_sq_le (by norm_num), ?_⟩
  calc √2 ≤ √(1.414214 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 1.414214 := Real.sqrt_sq (by norm_num)

theorem sqrt_1e9_ge : (31622 : ℝ) ≤ √(10 ^ 9) := Real.le_sqrt_of_sq_le (by norm_num)

/-- The `C`-block term, split. -/
theorem termC_eq {M x : ℝ} (hM : 0 < M) (hx : 0 < x) :
    (1 / M + Dp M) * (Real.log 2 + 2 * M / x) =
      Real.log 2 * (4 / M + 28.16 / √M) +
        Real.log 2 * (0.51 / Real.log M ^ 2 + 2 / Real.log M ^ 3) +
        2 * M / x * (2 / Real.log M ^ 3 + 0.51 / Real.log M ^ 2) + (8 / x + 56.32 * √M / x) +
        Pth M * (Real.log 2 + 2 * M / x) := by
  unfold Dp
  have hs : 0 < √M := Real.sqrt_pos.2 hM
  have key : 2 * M / x * (28.16 / √M) = 56.32 * √M / x := by
    have hM' : M = √M ^ 2 := (Real.sq_sqrt hM.le).symm
    rw [hM']
    rw [Real.sqrt_sq hs.le]
    field_simp
    ring
  have key2 : 2 * M / x * (1 / M) = 2 / x := by field_simp
  have key3 : 2 * M / x * (3 / M) = 6 / x := by field_simp; norm_num
  linear_combination key + key2 + key3

theorem tele_sq {t d : ℝ} (hd : 0 ≤ d) (htd : 0 < t - d) : d / t ^ 2 ≤ 1 / (t - d) - 1 / t := by
  have ht : 0 < t := by linarith
  have e : 1 / (t - d) - 1 / t = d / (t * (t - d)) := by
    field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_left hd (by positivity)
  rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) ht.le

theorem tele_cube {t d : ℝ} (hd : 0 ≤ d) (htd : 0 < t - d) :
    2 * d / t ^ 3 ≤ 1 / (t - d) ^ 2 - 1 / t ^ 2 := by
  have ht : 0 < t := by linarith
  have e : 1 / (t - d) ^ 2 - 1 / t ^ 2 = d * (2 * t - d) / (t ^ 2 * (t - d) ^ 2) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : d * (2 * t - d) * t ^ 3 - 2 * d * (t ^ 2 * (t - d) ^ 2) = d ^ 2 * t ^ 2 * (3 * t - 2 * d) := by
    ring
  have : 0 ≤ d ^ 2 * t ^ 2 * (3 * t - 2 * d) := mul_nonneg (by positivity) (by linarith)
  linarith

/-- Telescoping: `∑_{j<J} d (0.51/L_j² + 2/L_j³) ≤ 0.028` for `L_j = L₀ + j d`, `L₀ ≥ 20.7`, `d ≤ 0.7`. -/
theorem tele_part {L0 d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 0.7) (hL : 20.7 ≤ L0) (J : ℕ) :
    ∑ j ∈ range J, d * (0.51 / (L0 + j * d) ^ 2 + 2 / (L0 + j * d) ^ 3) ≤ 0.028 := by
  set G : ℝ → ℝ := fun t => 0.51 / t + 1 / t ^ 2 with hG
  set f : ℕ → ℝ := fun j => G (L0 + j * d - d) with hf
  have hterm : ∀ j ∈ range J, d * (0.51 / (L0 + j * d) ^ 2 + 2 / (L0 + j * d) ^ 3) ≤ f j - f (j + 1) := by
    intro j _
    have hj : (0 : ℝ) ≤ j * d := by positivity
    have htd : 0 < L0 + j * d - d := by linarith
    have e : L0 + ((j + 1 : ℕ) : ℝ) * d - d = L0 + j * d := by push_cast; ring
    simp only [hf, hG, e]
    have h1 := tele_sq hd0.le htd
    have h2 := tele_cube hd0.le htd
    have e1 : d * (0.51 / (L0 + j * d) ^ 2) = 0.51 * (d / (L0 + j * d) ^ 2) := by ring
    have e2 : d * (2 / (L0 + j * d) ^ 3) = 2 * d / (L0 + j * d) ^ 3 := by ring
    rw [mul_add, e1, e2]
    have : 0.51 * (d / (L0 + j * d) ^ 2) ≤ 0.51 * (1 / (L0 + j * d - d) - 1 / (L0 + j * d)) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have e3 : 0.51 / (L0 + j * d - d) + 1 / (L0 + j * d - d) ^ 2 -
        (0.51 / (L0 + j * d) + 1 / (L0 + j * d) ^ 2) =
        0.51 * (1 / (L0 + j * d - d) - 1 / (L0 + j * d)) +
          (1 / (L0 + j * d - d) ^ 2 - 1 / (L0 + j * d) ^ 2) := by ring
    rw [e3]; linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_range_sub']
  have hfJ : 0 ≤ f J := by
    simp only [hf, hG]
    have : 0 < L0 + J * d - d := by have : (0 : ℝ) ≤ J * d := by positivity
                                    linarith
    positivity
  have hf0 : f 0 ≤ 0.028 := by
    simp only [hf, hG, Nat.cast_zero, zero_mul, add_zero]
    have h20 : 20 ≤ L0 - d := by linarith
    have a1 : 0.51 / (L0 - d) ≤ 0.51 / 20 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h20
    have a2 : 1 / (L0 - d) ^ 2 ≤ 1 / 20 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) h20 2)
    norm_num at a1 a2 ⊢; linarith
  linarith

theorem log2_bounds : (0.6931 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 0.6932 := by
  have h1 := Real.log_two_gt_d9; have h2 := Real.log_two_lt_d9
  constructor <;> linarith

theorem geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (J : ℕ) : ∑ j ∈ range J, r ^ j ≤ 1 / (1 - r) := by
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) h0 h1
  rwa [← range_eq_Ico, pow_zero] at this

/-- Part C sum, first two groups (the `log 2` main terms). -/
theorem partC_main (J : ℕ) :
    ∑ j ∈ range J, (Real.log 2 * (4 / Mj j + 28.16 / √(Mj j)) +
      Real.log 2 * (0.51 / Real.log (Mj j) ^ 2 + 2 / Real.log (Mj j) ^ 3)) ≤ 0.03012 := by
  obtain ⟨hl1, hl2⟩ := log2_bounds
  obtain ⟨hs1, hs2⟩ := sqrt2_bounds
  have hs9 := sqrt_1e9_ge
  rw [sum_add_distrib]
  -- telescoping part
  have ht : ∑ j ∈ range J, Real.log 2 * (0.51 / Real.log (Mj j) ^ 2 + 2 / Real.log (Mj j) ^ 3) ≤ 0.028 := by
    have := tele_part (L0 := Real.log (10 ^ 9)) (d := Real.log 2) (by linarith) (by linarith)
      log_1e9_ge J
    refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) this
    rw [log_Mj]
  -- geometric part
  have hg : ∑ j ∈ range J, (4 / Mj j + 28.16 / √(Mj j)) ≤ 0.0030407 := by
    have e : ∀ j ∈ range J, 4 / Mj j + 28.16 / √(Mj j) =
        4 / 10 ^ 9 * (1 / 2) ^ j + 28.16 / √(10 ^ 9) * (1 / √2) ^ j := by
      intro j _
      rw [sqrt_Mj]; unfold Mj
      rw [one_div_pow, one_div_pow, div_mul_div_comm, div_mul_div_comm, mul_one, mul_one]
    rw [sum_congr rfl e, sum_add_distrib, ← mul_sum, ← mul_sum]
    have g1 := geom_le (r := 1 / 2) (by norm_num) (by norm_num) J
    have hr0 : (0 : ℝ) ≤ 1 / √2 := by positivity
    have hr1 : 1 / √2 ≤ 0.70711 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    have g2 := geom_le (r := 1 / √2) hr0 (by linarith) J
    have g2' : 1 / (1 - 1 / √2) ≤ 3.41427 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have c1 : 28.16 / √(10 ^ 9 : ℝ) ≤ 28.16 / 31622 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs9
    have p1 : 4 / 10 ^ 9 * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j ≤ 4 / 10 ^ 9 * 2 := by
      have : 1 / (1 - (1 / 2 : ℝ)) = 2 := by norm_num
      rw [this] at g1
      exact mul_le_mul_of_nonneg_left g1 (by norm_num)
    have p2 : 28.16 / √(10 ^ 9 : ℝ) * ∑ j ∈ range J, (1 / √2) ^ j ≤ 28.16 / 31622 * 3.41427 :=
      mul_le_mul c1 (g2.trans g2') (sum_nonneg fun j _ => by positivity) (by norm_num)
    norm_num at p1 p2 ⊢
    linarith
  have := mul_le_mul_of_nonneg_left hg (by linarith : (0 : ℝ) ≤ Real.log 2)
  rw [← mul_sum]
  linarith

theorem sum_Mj_le (J : ℕ) : ∑ j ∈ range J, Mj j ≤ 10 ^ 9 * 2 ^ J := by
  unfold Mj
  rw [← mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  norm_num

theorem sum_sqrt_Mj_le (J : ℕ) : ∑ j ∈ range J, √(Mj j) ≤ (√2 + 1) * √(10 ^ 9 * 2 ^ J) := by
  obtain ⟨hs1, hs2⟩ := sqrt2_bounds
  have hne : √2 ≠ 1 := by intro h; rw [h] at hs1; norm_num at hs1
  rw [sum_congr rfl fun j _ => sqrt_Mj j, ← mul_sum, geom_sum_eq hne,
    Real.sqrt_mul (by positivity), sqrt_two_pow']
  have e : (√2 ^ J - 1) / (√2 - 1) = (√2 ^ J - 1) * (√2 + 1) := by
    rw [div_eq_iff (by linarith)]
    have : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    linear_combination (-(√2 ^ J - 1)) * this
  rw [e]
  have h9 : 0 ≤ √(10 ^ 9 : ℝ) := Real.sqrt_nonneg _
  have hp : 0 ≤ √2 ^ J := by positivity
  have : (√2 ^ J - 1) * (√2 + 1) ≤ √2 ^ J * (√2 + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  calc √(10 ^ 9) * ((√2 ^ J - 1) * (√2 + 1)) ≤ √(10 ^ 9) * (√2 ^ J * (√2 + 1)) :=
        mul_le_mul_of_nonneg_left this h9
    _ = (√2 + 1) * (√(10 ^ 9) * √2 ^ J) := by ring

theorem log_Mj_ge (j : ℕ) : 20.7 ≤ Real.log (Mj j) := by
  rw [log_Mj]
  have := log_1e9_ge
  have : (0 : ℝ) ≤ j * Real.log 2 := mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  linarith

/-- Part C sum, last two groups (the `b/x` errors). -/
theorem partC_err {x : ℝ} (hx : 1e10 ≤ x) (J : ℕ) (hJ : (10 : ℝ) ^ 9 * 2 ^ J ≤ 2 * x) :
    ∑ j ∈ range J, (2 * Mj j / x * (2 / Real.log (Mj j) ^ 3 + 0.51 / Real.log (Mj j) ^ 2) +
      (8 / x + 56.32 * √(Mj j) / x)) ≤ 0.00759 := by
  have hx0 : 0 < x := by linarith
  rw [sum_add_distrib]
  have hc : ∑ j ∈ range J, 2 * Mj j / x * (2 / Real.log (Mj j) ^ 3 + 0.51 / Real.log (Mj j) ^ 2) ≤
      0.0056633 := by
    have hb : ∀ j, 2 / Real.log (Mj j) ^ 3 + 0.51 / Real.log (Mj j) ^ 2 ≤ 0.0014158 := by
      intro j
      have hL := log_Mj_ge j
      have a1 : 2 / Real.log (Mj j) ^ 3 ≤ 2 / 20.7 ^ 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 3)
      have a2 : 0.51 / Real.log (Mj j) ^ 2 ≤ 0.51 / 20.7 ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 2)
      norm_num at a1 a2 ⊢; linarith
    calc _ ≤ ∑ j ∈ range J, 2 * Mj j / x * 0.0014158 :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb j) (by have := Mj_pos j; positivity)
      _ = 0.0014158 * (2 / x) * ∑ j ∈ range J, Mj j := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      _ ≤ 0.0014158 * (2 / x) * (2 * x) :=
          mul_le_mul_of_nonneg_left ((sum_Mj_le J).trans hJ) (by positivity)
      _ = 0.0056632 := by field_simp; norm_num
      _ ≤ 0.0056633 := by norm_num
  have hd : ∑ j ∈ range J, (8 / x + 56.32 * √(Mj j) / x) ≤ 0.001923 := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    have hJ' : (J : ℝ) ≤ 2 ^ J := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h1 : (J : ℝ) * (8 / x) ≤ 1.6e-8 := by
      have : (J : ℝ) ≤ 2 * x / 10 ^ 9 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
      calc (J : ℝ) * (8 / x) ≤ 2 * x / 10 ^ 9 * (8 / x) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 1.6e-8 := by field_simp; norm_num
    obtain ⟨hs1, hs2⟩ := sqrt2_bounds
    have hs : (1e5 : ℝ) ≤ √x := Real.le_sqrt_of_sq_le (by norm_num; linarith)
    have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
    have hS2 : √((10 : ℝ) ^ 9 * 2 ^ J) ≤ √2 * √x := by
      rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt hJ
    have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsum : ∑ j ∈ range J, √(Mj j) ≤ (2 + √2) * √x := by
      calc ∑ j ∈ range J, √(Mj j) ≤ (√2 + 1) * √(10 ^ 9 * 2 ^ J) := sum_sqrt_Mj_le J
        _ ≤ (√2 + 1) * (√2 * √x) := mul_le_mul_of_nonneg_left hS2 (by positivity)
        _ = (2 + √2) * √x := by linear_combination (√x) * h22
    have hsx0 : 0 < √x := by linarith
    have h2 : ∑ j ∈ range J, 56.32 * √(Mj j) / x ≤ 0.001922886 := by
      rw [← sum_div, ← mul_sum]
      calc (56.32 * ∑ j ∈ range J, √(Mj j)) / x ≤ 56.32 * ((2 + √2) * √x) / x :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hx0.le
        _ = 56.32 * (2 + √2) / √x := by
            rw [div_eq_div_iff hx0.ne' hsx0.ne']; linear_combination (56.32 * (2 + √2)) * hss
        _ ≤ 56.32 * (2 + √2) / 1e5 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hs
        _ ≤ 56.32 * 3.414214 / 1e5 := div_le_div_of_nonneg_right (by nlinarith) (by norm_num)
        _ ≤ 0.001922886 := by norm_num
    linarith
  linarith

/-- Part C sum, the plateau term of `theta_explicit`: only the blocks with `log M_j < 20000` count. -/
theorem partC_pth {x : ℝ} (hx : 1e10 ≤ x) (J : ℕ) (hJ : (10 : ℝ) ^ 9 * 2 ^ J ≤ 2 * x) :
    ∑ j ∈ range J, Pth (Mj j) * (Real.log 2 + 2 * Mj j / x) ≤ 0.0074 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hl1, hl2⟩ := log2_bounds
  have hpt : ∀ j, Pth (Mj j) ≤ if j < 28827 then 3.7e-7 else 0 := by
    intro j
    split_ifs with hj
    · exact Pth_le _
    · unfold Pth
      rw [if_neg]
      push Not at hj ⊢
      have hj' : (28827 : ℝ) ≤ j := by exact_mod_cast hj
      have hm : (28827 : ℝ) * 0.6931 ≤ j * Real.log 2 := mul_le_mul hj' hl1 (by norm_num) (by positivity)
      have h9 := log_1e9_ge
      rw [log_Mj]; norm_num at hm h9 ⊢; linarith
  simp_rw [mul_add]
  rw [sum_add_distrib]
  have h1 : ∑ j ∈ range J, Pth (Mj j) * Real.log 2 ≤ 3.7e-7 * 28827 * 0.6932 := by
    calc ∑ j ∈ range J, Pth (Mj j) * Real.log 2
          ≤ ∑ j ∈ range J, (if j < 28827 then (3.7e-7 : ℝ) else 0) * 0.6932 :=
          sum_le_sum fun j _ => mul_le_mul (hpt j) hl2 (by linarith)
            (by split_ifs <;> norm_num)
      _ = (∑ j ∈ range J, if j < 28827 then (3.7e-7 : ℝ) else 0) * 0.6932 := by rw [sum_mul]
      _ ≤ (3.7e-7 * 28827) * 0.6932 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          have : ((range J).filter (fun j => j < 28827)).card ≤ 28827 := by
            calc _ ≤ (range 28827).card :=
                  card_le_card fun j hj => mem_range.2 (mem_filter.1 hj).2
              _ = 28827 := card_range _
          exact_mod_cast this
  have h2 : ∑ j ∈ range J, Pth (Mj j) * (2 * Mj j / x) ≤ 1.48e-6 := by
    calc ∑ j ∈ range J, Pth (Mj j) * (2 * Mj j / x) ≤ ∑ j ∈ range J, 3.7e-7 * (2 * Mj j / x) :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (Pth_le _)
            (by have := Mj_pos j; positivity)
      _ = 3.7e-7 * (2 / x) * ∑ j ∈ range J, Mj j := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      _ ≤ 3.7e-7 * (2 / x) * (2 * x) :=
          mul_le_mul_of_nonneg_left ((sum_Mj_le J).trans hJ) (by positivity)
      _ = 1.48e-6 := by field_simp; norm_num
  norm_num at h1
  linarith

/-- Block index of `y ≥ 10⁹`. -/
noncomputable def gC (y : ℝ) : ℕ := Nat.log 2 (⌊y⌋₊ / 10 ^ 9)

theorem gC_block {y : ℝ} (h1 : 10 ^ 9 ≤ y) : Mj (gC y) ≤ ⌊y⌋₊ ∧ y < Mj (gC y + 1) := by
  have hk1 : 10 ^ 9 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hd : ⌊y⌋₊ / 10 ^ 9 ≠ 0 := by omega
  have hlo : 2 ^ gC y ≤ ⌊y⌋₊ / 10 ^ 9 := Nat.pow_log_le_self 2 hd
  have hhi : ⌊y⌋₊ / 10 ^ 9 < 2 ^ (gC y + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlo' : 2 ^ gC y * 10 ^ 9 ≤ ⌊y⌋₊ := (Nat.le_div_iff_mul_le (by norm_num)).1 hlo
  have hhi' : ⌊y⌋₊ < 2 ^ (gC y + 1) * 10 ^ 9 := (Nat.div_lt_iff_lt_mul (by norm_num)).1 hhi
  unfold Mj
  refine ⟨?_, ?_⟩
  · have : ((2 ^ gC y * 10 ^ 9 : ℕ) : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hlo'
    push_cast at this; linarith
  · have hlt := Nat.lt_floor_add_one y
    have : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (gC y + 1) * 10 ^ 9 : ℕ) : ℝ) := by exact_mod_cast hhi'
    push_cast at this; linarith

theorem gC_le {x y : ℝ} (hyx : y ≤ x) : gC y ≤ Nat.log 2 (⌊x⌋₊ / 10 ^ 9) :=
  Nat.log_mono_right (Nat.div_le_div_right (Nat.floor_mono hyx))

theorem E_blockC {x y : ℝ} (h1 : 10 ^ 9 ≤ y) (hyx : y ≤ x) :
    |E₁Λ y - E₁Λ x| ≤ 1 / Mj (gC y) + Dp (Mj (gC y)) := by
  have h := E_far (by linarith) hyx
  obtain ⟨hM, -⟩ := gC_block h1
  have hM0 := Mj_pos (gC y)
  have hM3 : (3 : ℝ) ≤ Mj (gC y) := by have := Mj_ge (gC y); linarith
  have a1 : 1 / (⌊y⌋₊ : ℝ) ≤ 1 / Mj (gC y) := one_div_le_one_div_of_le hM0 hM
  have a2 := Dp_anti hM3 hM
  linarith

/-- **Part C** of the `K` bound (`x/n ≥ 10⁹`). -/
theorem K_partC {x : ℝ} (hx : 1e10 ≤ x) :
    ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 10 ^ 9 ≤ x / n), |E₁Λ (x / n) - E₁Λ x| / n ≤ 0.0452 := by
  have hx0 : 0 < x := by linarith
  set J := Nat.log 2 (⌊x⌋₊ / 10 ^ 9) + 1 with hJdef
  have hJ : (10 : ℝ) ^ 9 * 2 ^ J ≤ 2 * x := by
    have hk : 10 ^ 10 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
    have hd : ⌊x⌋₊ / 10 ^ 9 ≠ 0 := by omega
    have hlo : 2 ^ Nat.log 2 (⌊x⌋₊ / 10 ^ 9) * 10 ^ 9 ≤ ⌊x⌋₊ :=
      (Nat.le_div_iff_mul_le (by norm_num)).1 (Nat.pow_log_le_self 2 hd)
    have : ((2 ^ Nat.log 2 (⌊x⌋₊ / 10 ^ 9) * 10 ^ 9 : ℕ) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hlo
    have hfl := Nat.floor_le hx0.le
    rw [hJdef, pow_succ (2 : ℝ)]
    push_cast at this
    generalize (2 : ℝ) ^ Nat.log 2 (⌊x⌋₊ / 10 ^ 9) = P at this ⊢
    norm_num at this ⊢; linarith
  have hyx : ∀ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 10 ^ 9 ≤ x / n), x / n ≤ x ∧ (0 : ℝ) < n := by
    intro n hn
    have hn1 := (mem_Icc.1 (mem_filter.1 hn).1).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    refine ⟨div_le_self hx0.le (by exact_mod_cast hn1), hn0⟩
  have hmaps : ∀ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 10 ^ 9 ≤ x / n), gC (x / n) ∈ range J := by
    intro n hn
    exact mem_range.2 (Nat.lt_succ_of_le (gC_le (hyx n hn).1))
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ range J, ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 10 ^ 9 ≤ x / n)).filter
      (fun n : ℕ => gC (x / n) = j), |E₁Λ (x / n) - E₁Λ x| / n ≤
      (1 / Mj j + Dp (Mj j)) * (Real.log 2 + 2 * Mj j / x) := by
    intro j _
    have hM0 := Mj_pos j
    have h0 : 0 ≤ 1 / Mj j + Dp (Mj j) := by
      have : 0 < Real.log (Mj j) := by have := log_Mj_ge j; linarith
      have := Pth_nonneg (Mj j)
      have : 0 ≤ 3 / Mj j + 2 * (1 / Real.log (Mj j) ^ 3 + 7.04 / √(Mj j)) +
          (0.51 / Real.log (Mj j) ^ 2 + 14.08 / √(Mj j)) := by positivity
      have : 0 ≤ 1 / Mj j := by positivity
      unfold Dp; linarith
    have hsub : ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 10 ^ 9 ≤ x / n)).filter
        (fun n : ℕ => gC (x / n) = j) ⊆ (Icc 1 ⌊x⌋₊).filter
        (fun n : ℕ => Mj j ≤ x / n ∧ x / n < Mj (j + 1)) := by
      intro n hn
      obtain ⟨hnA, hg⟩ := mem_filter.1 hn
      obtain ⟨hnI, h1⟩ := mem_filter.1 hnA
      obtain ⟨hlo, hhi⟩ := gC_block h1
      rw [hg] at hlo hhi
      have : (⌊x / n⌋₊ : ℝ) ≤ x / n := Nat.floor_le (by linarith)
      exact mem_filter.2 ⟨hnI, hlo.trans this, hhi⟩
    have hpt : ∀ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 10 ^ 9 ≤ x / n)).filter
        (fun n : ℕ => gC (x / n) = j), |E₁Λ (x / n) - E₁Λ x| / n ≤
        (1 / Mj j + Dp (Mj j)) * (1 / n) := by
      intro n hn
      obtain ⟨hnA, hg⟩ := mem_filter.1 hn
      obtain ⟨-, h1⟩ := mem_filter.1 hnA
      have := E_blockC h1 (hyx n hnA).1
      rw [hg] at this
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right this (by have := (hyx n hnA).2; positivity)
    have hMs : Mj (j + 1) = 2 * Mj j := by unfold Mj; rw [pow_succ]; ring
    have hlog : Real.log (Mj (j + 1) / Mj j) = Real.log 2 := by
      rw [hMs]; congr 1; field_simp
    calc _ ≤ ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 10 ^ 9 ≤ x / n)).filter
          (fun n : ℕ => gC (x / n) = j), (1 / Mj j + Dp (Mj j)) * (1 / (n : ℝ)) := sum_le_sum hpt
      _ ≤ ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => Mj j ≤ x / n ∧ x / n < Mj (j + 1)),
          (1 / Mj j + Dp (Mj j)) * (1 / (n : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => by
          have : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 (mem_filter.1 hn).1).1
          positivity
      _ = (1 / Mj j + Dp (Mj j)) * ∑ n ∈ (Icc 1 ⌊x⌋₊).filter
          (fun n : ℕ => Mj j ≤ x / n ∧ x / n < Mj (j + 1)), (1 / (n : ℝ)) := by rw [mul_sum]
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ h0
        have := harm_piece hx0 (a := Mj j) (b := Mj (j + 1)) hM0 (by rw [hMs]; linarith)
        rwa [hlog, show Mj (j + 1) / x = 2 * Mj j / x by rw [hMs]] at this
  refine (sum_le_sum hfib).trans ?_
  rw [sum_congr rfl fun j _ => termC_eq (Mj_pos j) hx0]
  have e : ∀ j ∈ range J,
      Real.log 2 * (4 / Mj j + 28.16 / √(Mj j)) +
        Real.log 2 * (0.51 / Real.log (Mj j) ^ 2 + 2 / Real.log (Mj j) ^ 3) +
        2 * Mj j / x * (2 / Real.log (Mj j) ^ 3 + 0.51 / Real.log (Mj j) ^ 2) +
        (8 / x + 56.32 * √(Mj j) / x) + Pth (Mj j) * (Real.log 2 + 2 * Mj j / x) =
      ((Real.log 2 * (4 / Mj j + 28.16 / √(Mj j)) +
        Real.log 2 * (0.51 / Real.log (Mj j) ^ 2 + 2 / Real.log (Mj j) ^ 3)) +
      (2 * Mj j / x * (2 / Real.log (Mj j) ^ 3 + 0.51 / Real.log (Mj j) ^ 2) +
        (8 / x + 56.32 * √(Mj j) / x))) + Pth (Mj j) * (Real.log 2 + 2 * Mj j / x) :=
    fun j _ => by ring
  rw [sum_congr rfl e, sum_add_distrib, sum_add_distrib]
  have := partC_main J
  have := partC_err hx J hJ
  have := partC_pth hx J hJ
  linarith

/-- **The `K` bound**: `∑_{n ≤ x} |E(x/n) − E(x)|/n ≤ 0.55` for `x ≥ 10¹⁰`. -/
theorem K_bound {x : ℝ} (hx : 1e10 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, |E₁Λ (x / n) - E₁Λ x| / n ≤ 0.55 := by
  rw [← sum_filter_add_sum_filter_not _ (fun n : ℕ => x / n < 1000)]
  rw [← sum_filter_add_sum_filter_not ((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => ¬ x / n < 1000))
    (fun n : ℕ => x / n < 10 ^ 9), filter_filter, filter_filter]
  have hA := K_partA hx
  have hB := K_partB hx
  have hC := K_partC hx
  have eB : (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => ¬ x / n < 1000 ∧ x / n < 10 ^ 9) =
      (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 1000 ≤ x / n ∧ x / n < 10 ^ 9) :=
    filter_congr fun n _ => by rw [not_lt]
  have eC : (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => ¬ x / n < 1000 ∧ ¬ x / n < 10 ^ 9) =
      (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 10 ^ 9 ≤ x / n) :=
    filter_congr fun n _ => by
      constructor
      · rintro ⟨-, h⟩; exact not_lt.1 h
      · intro h; exact ⟨by norm_num at h ⊢; linarith, not_lt.2 h⟩
  rw [eB, eC]
  linarith

theorem log_three_div_sqrt_two_le : Real.log (3 / √2) ≤ 0.7521 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h := Real.sum_le_exp_of_nonneg (x := 0.7521) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hs : (1.414213 : ℝ) ≤ √2 := sqrt2_bounds.1
  have : (3 : ℝ) / √2 ≤ 2.12133 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- `E(x) ≥ −log(3/√2)` (from (2.13)). -/
theorem E1_ge {x : ℝ} (hx : 1 ≤ x) : -0.7521 ≤ E₁Λ x := by
  have h := log_sub_le_sum_vonMangoldt_div hx
  have := log_three_div_sqrt_two_le
  rw [E1_eq, PsiT]; linarith

/-- **Uniform Möbius bound** (Ramaré's route, `q = 1`): `|∑_{n ≤ x} μ(n)/n| ≤ 0.55/(log x − 0.7521)`
for `x ≥ 10¹⁰`. -/
theorem abs_sum_moebius_div_le {x : ℝ} (hx : 1e10 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 0.55 / (Real.log x - 0.7521) := by
  have hx1 : 1 ≤ x := by linarith
  have hid := mlog_identity hx1 (E₁Λ x)
  have hE := E1_ge hx1
  have hlx : 23 ≤ Real.log x := by
    have : (23 : ℝ) ≤ Real.log (1e10) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h1 := Real.exp_one_lt_d9
      have : Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 23 ≤ (2.7182818286 : ℝ) ^ 23 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 23
        _ ≤ 1e10 := by norm_num
    exact this.trans (Real.log_le_log (by norm_num) hx)
  have hpos : 0 < Real.log x - 0.7521 := by linarith
  have hR : |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n * (E₁Λ (x / n) - E₁Λ x)| ≤ 0.55 := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun n hn => ?_).trans (K_bound hx))
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
    have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_mul, abs_div, abs_of_pos hn0, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hn0.le
    calc |(μ n : ℝ)| * |E₁Λ (x / n) - E₁Λ x| ≤ 1 * |E₁Λ (x / n) - E₁Λ x| :=
          mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
      _ = |E₁Λ (x / n) - E₁Λ x| := one_mul _
  have hL : Real.log x - 0.7521 ≤ Real.log x + E₁Λ x := by linarith
  rw [le_div_iff₀ hpos]
  calc |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| * (Real.log x - 0.7521)
      ≤ |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| * (Real.log x + E₁Λ x) :=
        mul_le_mul_of_nonneg_left hL (abs_nonneg _)
    _ = |(∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) * (Real.log x + E₁Λ x)| := by
        rw [abs_mul, abs_of_pos (by linarith : 0 < Real.log x + E₁Λ x)]
    _ = |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n * (E₁Λ (x / n) - E₁Λ x)| := by rw [hid, abs_neg]
    _ ≤ 0.55 := hR

end TernaryGoldbach.Prelim
