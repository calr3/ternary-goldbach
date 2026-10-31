import Mathlib
import TernaryGoldbach.Prelim.MoebiusCoprime

/-!
# Explicit bounds on sums of `Λ` and `μ` [B, §2.5]

[B] quotes these from the literature (with some supplementary computations).  They are recorded
here as **trusted facts** (`sorry`), each with its source. (2.15), (5.5) and (2.12) are **proved**
from (2.14) together with finite computer checks (numerical axioms, `scripts/psi_checks.py`).  Only the bounds needed so far are listed; [B, §2.5] has more
((2.13), (2.14), (2.17)–(2.19), (2.21)–(2.24)).

Two remarks.
* (2.16) is only claimed for `y > 663` (it fails, e.g., at `y = 3`), so results that use it need
  that hypothesis.
* (2.20) is **proved** (elementarily) in `Prelim/MoebiusCoprime.lean`.
-/

open Finset
open ArithmeticFunction (vonMangoldt moebius)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- **[B, (2.13)]** ([RS62, (3.21)] for `x > 1000` plus prime powers `≤ 1000`, and a computation
for `x ≤ 1000`): `∑_{n ≤ x} Λ(n)/n ≥ log x - log(3/√2)` for `x ≥ 1`. -/
theorem log_sub_le_sum_vonMangoldt_div {x : ℝ} (hx : 1 ≤ x) :
    Real.log x - Real.log (3 / √2) ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℝ) / n := by
  sorry

/-- **[B, (2.14)]** ([RR96, p. 423, second table] and a computation for `2·10⁶ ≤ y ≤ 4·10⁶`):
`∑_{n ≤ y} Λ(n) ≤ 1.0004 y` for `y ≥ 2·10⁶`. -/
theorem sum_vonMangoldt_le_10004 {y : ℝ} (hy : 2e6 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y := by
  sorry

/-! ### Consequences of (2.14), via finite checks

(2.15), (5.5) and (2.12) follow from (2.14) and three finite computer checks
(`scripts/psi_checks.py`), stated as numerical axioms. -/

/-- **Numerical axiom** (`scripts/psi_checks.py`; maximum `1.0388206` at `n = 113`):
`ψ(n) < 1.03883 n` for `1 ≤ n < 2·10⁶`. -/
axiom psi_small (n : ℕ) (h1 : 1 ≤ n) (h : n < 2000000) : ∑ m ∈ Icc 1 n, (Λ m : ℝ) < 1.03883 * n

/-- **Numerical axiom** (`scripts/psi_checks.py`; maximum `1.4261933` at `n = 361`):
`ψ(n) − θ(n) < 1.4262 √n` for `1 ≤ n ≤ 10¹²` (checked at every prime power `p^k`, `k ≥ 2`). -/
axiom nonprime_small (n : ℕ) (h1 : 1 ≤ n) (h : n ≤ 10 ^ 12) :
    ∑ m ∈ Icc 1 n, (if m.Prime then 0 else (Λ m : ℝ)) < 1.4262 * √n

/-- **Numerical axiom** (`scripts/psi_checks.py`): `∑_{m ≤ n} Λ(m)/m ≤ log n` for `1 ≤ n ≤ 100`. -/
axiom mertens_small (n : ℕ) (h1 : 1 ≤ n) (h : n ≤ 100) :
    ∑ m ∈ Icc 1 n, (Λ m : ℝ) / m ≤ Real.log n

/-- **[B, (2.15)]** ([RS62, Thm. 12]): `ψ(y) = ∑_{n ≤ y} Λ(n) < 1.03883 y` for `y > 0`.
Proved from (2.14) and the finite check `psi_small`. -/
theorem sum_vonMangoldt_lt {y : ℝ} (hy : 0 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) < 1.03883 * y := by
  rcases le_or_gt 2e6 y with h | h
  · have := sum_vonMangoldt_le_10004 h; linarith
  · set n := ⌊y⌋₊ with hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp; positivity
    · have hn2 : n < 2000000 :=
        Nat.floor_lt hy.le |>.2 (show y < ((2000000 : ℕ) : ℝ) by norm_num; linarith)
      have h1 := psi_small n hpos hn2
      have h2 : (n : ℝ) ≤ y := Nat.floor_le hy.le
      linarith

/-- `log N! ≤ N log N − N + 1 + log N`. -/
theorem sum_log_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Icc 1 N, Real.log m ≤ N * Real.log N - N + 1 + Real.log N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    have ih := ih hpos
    rw [sum_Icc_succ_top (by omega)]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    push_cast
    -- `(N+1) log(1 + 1/N) ≥ 1`
    have hl := Real.one_sub_inv_le_log_of_pos (x := ((N : ℝ) + 1) / N) (by positivity)
    rw [Real.log_div (by positivity) hN0.ne'] at hl
    have e : 1 - (((N : ℝ) + 1) / N)⁻¹ = 1 / (N + 1) := by field_simp; ring
    rw [e] at hl
    have : 1 ≤ ((N : ℝ) + 1) * (Real.log (N + 1) - Real.log N) := by
      have h := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ N + 1)
      rwa [show ((N : ℝ) + 1) * (1 / (N + 1)) = 1 by field_simp] at h
    nlinarith

/-- `ψ(n)` for natural `n`. -/
noncomputable def psiN (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, (Λ m : ℝ)

theorem psiN_succ (n : ℕ) : psiN (n + 1) = psiN n + Λ (n + 1) := by
  rw [psiN, sum_Icc_succ_top (by omega), psiN]

theorem psiN_le (n : ℕ) : psiN n ≤ 1.03883 * n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [psiN]
  have := sum_vonMangoldt_lt (y := n) (by exact_mod_cast h)
  rw [Nat.floor_natCast] at this; exact this.le

/-- Summation by parts on `(M, N]`. -/
theorem abel_Ioc (w : ℕ → ℝ) (M N : ℕ) (hMN : M < N) :
    ∑ n ∈ Ioc M N, (Λ n : ℝ) * w n = psiN N * w N - psiN M * w (M + 1) +
      ∑ n ∈ Ioo M N, psiN n * (w n - w (n + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_or_ge M N with h | h
    · rw [Finset.sum_Ioc_succ_top (by omega), ih h, psiN_succ,
        show Ioo M (N + 1) = insert N (Ioo M N) by ext x; simp; omega,
        sum_insert (by simp)]
      ring
    · have hN : N = M := by omega
      subst hN
      rw [show Ioc N (N + 1) = {N + 1} by ext x; simp only [mem_Ioc, mem_singleton]; omega,
        show Ioo N (N + 1) = ∅ by ext x; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega,
        sum_singleton, sum_empty, psiN_succ]
      ring

/-- `∑_{a < j ≤ b} 1/j ≤ log(b/a)`. -/
theorem sum_inv_le_log {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Ioc a b, (1 : ℝ) / j ≤ Real.log b - Real.log a := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · have hab' : a ≤ b := by omega
      rw [Finset.sum_Ioc_succ_top hab']
      have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
      have hl := Real.one_sub_inv_le_log_of_pos (x := ((b : ℝ) + 1) / b) (by positivity)
      rw [Real.log_div (by positivity) hb0.ne'] at hl
      have e : 1 - (((b : ℝ) + 1) / b)⁻¹ = 1 / (b + 1) := by field_simp; ring
      rw [e] at hl
      have := ih hab'
      push_cast; linarith
    · have : a = b + 1 := by omega
      subst this; simp

/-- **[B, (2.12)]** for integer `N ≥ 30`. -/
theorem sum_vonMangoldt_div_le_log_large {N : ℕ} (hN : 30 ≤ N) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) / n ≤ Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hfl : ∑ n ∈ Icc 1 N, (Λ n : ℝ) * ((N / n : ℕ) : ℝ) = ∑ m ∈ Icc 1 N, Real.log m := by
    have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (Λ : ArithmeticFunction ℝ) N
    rw [ArithmeticFunction.vonMangoldt_mul_zeta] at h
    simpa [show Icc 1 N = Ioc 0 N from rfl] using h.symm
  set R := ∑ n ∈ Icc 1 N, (Λ n : ℝ) * ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) with hR
  have hmain : (N : ℝ) * ∑ n ∈ Icc 1 N, (Λ n : ℝ) / n = ∑ m ∈ Icc 1 N, Real.log m + R := by
    rw [← hfl, hR, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by have := (mem_Icc.1 hn).1; omega)
    field_simp; ring
  -- bound `R`
  set M := N / 2 with hM
  have hMN : M < N := by omega
  have hM1 : 1 ≤ M := by omega
  have hsplit : Icc 1 N = Icc 1 M ∪ Ioc M N := by ext x; simp; omega
  have hdisj : Disjoint (Icc 1 M) (Ioc M N) := by
    rw [disjoint_left]; intro x h1 h2; simp at h1 h2; omega
  rw [hsplit, sum_union hdisj] at hR
  have hR1 : ∑ n ∈ Icc 1 M, (Λ n : ℝ) * ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) ≤ psiN M := by
    refine sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hfr : (N : ℝ) / n - ((N / n : ℕ) : ℝ) ≤ 1 := by
      have := Nat.lt_div_mul_add (a := N) (b := n) (by omega)
      rw [sub_le_iff_le_add, div_le_iff₀ hn0]
      have : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast this
      linarith
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    nlinarith
  have hR2 : ∑ n ∈ Ioc M N, (Λ n : ℝ) * ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) =
      ∑ n ∈ Ioc M N, (Λ n : ℝ) * ((N : ℝ) / n - 1) := by
    refine sum_congr rfl fun n hn => ?_
    have h := mem_Ioc.1 hn
    have : N / n = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [this]; simp
  rw [hR2] at hR
  have habel := abel_Ioc (fun n => (N : ℝ) / n - 1) M N hMN
  -- the boundary term at `N` vanishes, the interior terms are bounded via `ψ(n) ≤ 1.03883 n`
  have hint : ∑ n ∈ Ioo M N, psiN n * (((N : ℝ) / n - 1) - ((N : ℝ) / ((n + 1 : ℕ) : ℝ) - 1)) ≤
      1.03883 * N * (Real.log N - Real.log (M + 1 : ℕ)) := by
    have hpt : ∀ n ∈ Ioo M N, psiN n * (((N : ℝ) / n - 1) - ((N : ℝ) / ((n + 1 : ℕ) : ℝ) - 1)) ≤
        1.03883 * N * (1 / ((n + 1 : ℕ) : ℝ)) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := (mem_Ioo.1 hn).1; omega)
      have e : ((N : ℝ) / n - 1) - ((N : ℝ) / ((n + 1 : ℕ) : ℝ) - 1) = N / (n * (n + 1)) := by
        push_cast; field_simp; ring
      rw [e]
      have hd : 0 ≤ (N : ℝ) / (n * (n + 1)) := by positivity
      calc psiN n * (N / (n * (n + 1))) ≤ (1.03883 * n) * (N / (n * (n + 1))) :=
            mul_le_mul_of_nonneg_right (psiN_le n) hd
        _ = 1.03883 * N * (1 / ((n + 1 : ℕ) : ℝ)) := by push_cast; field_simp
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hre : ∑ n ∈ Ioo M N, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) = ∑ j ∈ Ioc (M + 1) N, (1 : ℝ) / j := by
      rw [show Ioc (M + 1) N = (Ioo M N).map ⟨(· + 1), add_left_injective 1⟩ by
        ext x; simp; constructor
        · rintro ⟨h1, h2⟩; exact ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
        · rintro ⟨a, ⟨h1, h2⟩, rfl⟩; omega, sum_map]
      rfl
    rw [hre]
    exact sum_inv_le_log (by omega) (by omega)
  have hlog2 : Real.log N - Real.log (M + 1 : ℕ) ≤ Real.log 2 := by
    rw [← Real.log_div hN0.ne' (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ (by positivity)]
    have : (N : ℝ) ≤ 2 * M + 1 := by exact_mod_cast (show N ≤ 2 * M + 1 by omega)
    push_cast; linarith
  have hl2 := Real.log_two_lt_d9
  have hpsiM := psiN_le M
  have hpsiM0 : 0 ≤ psiN M := sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  have hw : (N : ℝ) / ((M + 1 : ℕ) : ℝ) - 1 ≥ 1 - 2 / ((M + 1 : ℕ) : ℝ) := by
    have : (2 * M : ℝ) ≤ N := by exact_mod_cast (show 2 * M ≤ N by omega)
    have hM0 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    rw [ge_iff_le, ← sub_nonneg]
    have e : (N : ℝ) / ((M + 1 : ℕ) : ℝ) - 1 - (1 - 2 / ((M + 1 : ℕ) : ℝ)) =
        ((N : ℝ) - 2 * M) / ((M + 1 : ℕ) : ℝ) := by push_cast; field_simp; ring
    rw [e]; exact div_nonneg (by linarith) hM0.le
  have hψw : psiN M * (2 / ((M + 1 : ℕ) : ℝ)) ≤ 2.08 := by
    have hM0 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    rw [mul_div_assoc', div_le_iff₀ hM0]
    push_cast; nlinarith
  have hwN : (N : ℝ) / N - 1 = 0 := by rw [div_self hN0.ne']; ring
  simp only [hwN, mul_zero, zero_sub] at habel
  -- assemble
  have hR' : R ≤ psiN M + (-(psiN M * ((N : ℝ) / ((M + 1 : ℕ) : ℝ) - 1)) +
      1.03883 * N * (Real.log N - Real.log (M + 1 : ℕ))) := by
    rw [hR]; push_cast at habel hint ⊢; linarith
  have hlogfac := sum_log_le N (by omega)
  have hlogN : Real.log N ≤ N / 16 + 4 * Real.log 2 := by
    have := Real.log_le_sub_one_of_pos (x := (N : ℝ) / 16) (by positivity)
    rw [Real.log_div hN0.ne' (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  have h30 : (30 : ℝ) ≤ N := by exact_mod_cast hN
  have hw' : psiN M * ((N : ℝ) / ((M + 1 : ℕ) : ℝ) - 1) ≥ psiN M * (1 - 2 / ((M + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hw hpsiM0
  have e2 : psiN M * (1 - 2 / ((M + 1 : ℕ) : ℝ)) = psiN M - psiN M * (2 / ((M + 1 : ℕ) : ℝ)) := by ring
  have hfin : ∑ m ∈ Icc 1 N, Real.log m + R ≤ N * Real.log N := by
    have h3 : 1.03883 * (N : ℝ) * (Real.log N - Real.log (M + 1 : ℕ)) ≤ 1.03883 * N * 0.6931472 := by
      have := mul_le_mul_of_nonneg_left (hlog2.trans hl2.le) (by positivity : (0 : ℝ) ≤ 1.03883 * N)
      linarith
    linarith only [hR', hlogfac, hlogN, hl2, h30, hw', e2, hψw, h3]
  rw [← hmain] at hfin
  exact le_of_mul_le_mul_left (by linarith) hN0

/-- Pointwise domination of the non-prime prime powers. -/
theorem nonprime_term_le (N m : ℕ) (hm : m ∈ Icc 1 N) :
    (if m.Prime then 0 else (Λ m : ℝ)) ≤
      ∑ p ∈ (Icc 1 (Nat.sqrt N)).filter Nat.Prime, ∑ k ∈ Icc 2 (Nat.log p N),
        (if m = p ^ k then Real.log p else 0) := by
  have hnonneg : ∀ p ∈ (Icc 1 (Nat.sqrt N)).filter Nat.Prime, ∀ k ∈ Icc 2 (Nat.log p N),
      0 ≤ (if m = p ^ k then Real.log p else 0) := by
    intro p hp k _
    split_ifs
    · exact Real.log_nonneg (by exact_mod_cast (mem_filter.1 hp).2.one_lt.le)
    · exact le_rfl
  split_ifs with hprime
  · exact sum_nonneg fun p hp => sum_nonneg fun k hk => hnonneg p hp k hk
  by_cases hpp : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hk2 : 2 ≤ k := by
      by_contra h; have : k = 1 := by omega
      subst this; exact hprime (by simpa using hp)
    have hmN := (mem_Icc.1 hm).2
    have hpsq : p ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt]
      calc p * p = p ^ 2 := by ring
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
        _ ≤ N := hmN
    have hkL : k ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hmN
    have hΛ : (Λ (p ^ k) : ℝ) = Real.log p := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp]
    rw [hΛ]
    have hpmem : p ∈ (Icc 1 (Nat.sqrt N)).filter Nat.Prime :=
      mem_filter.2 ⟨mem_Icc.2 ⟨hp.one_lt.le, hpsq⟩, hp⟩
    refine le_trans ?_ (single_le_sum (fun p hp => sum_nonneg fun k hk => hnonneg p hp k hk) hpmem)
    refine le_trans ?_ (single_le_sum (fun k hk => hnonneg p hpmem k hk) (mem_Icc.2 ⟨hk2, hkL⟩))
    simp
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]
    exact sum_nonneg fun p hp => sum_nonneg fun k hk => hnonneg p hp k hk

/-- `ψ(N) − θ(N) ≤ ψ(√N) + N^{1/3} log N`. -/
theorem nonprime_sum_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Icc 1 N, (if m.Prime then 0 else (Λ m : ℝ)) ≤
      psiN (Nat.sqrt N) + (N : ℝ) ^ ((1 / 3) : ℝ) * Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set P := (Icc 1 (Nat.sqrt N)).filter Nat.Prime with hP
  refine (sum_le_sum fun m hm => nonprime_term_le N m hm).trans ?_
  rw [sum_comm]
  -- swap and count
  have hcount : ∀ p ∈ P, ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 2 (Nat.log p N),
      (if m = p ^ k then Real.log p else 0) ≤
      Real.log p + (if p ^ 3 ≤ N then Real.log N else 0) := by
    intro p hp
    have hpp := (mem_filter.1 hp).2
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [sum_comm]
    have h1 : ∑ k ∈ Icc 2 (Nat.log p N), ∑ m ∈ Icc 1 N, (if m = p ^ k then Real.log p else 0) ≤
        ∑ k ∈ Icc 2 (Nat.log p N), Real.log p := by
      refine sum_le_sum fun k _ => ?_
      rw [sum_ite_eq']; split_ifs <;> [exact le_rfl; exact hlp]
    refine h1.trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    set L := Nat.log p N
    have hpL : p ^ L ≤ N := Nat.pow_log_le_self p (by omega)
    have hLlog : (L : ℝ) * Real.log p ≤ Real.log N := by
      have hp0 : (0 : ℝ) < (p : ℝ) ^ L := pow_pos (by exact_mod_cast hpp.pos) L
      rw [← Real.log_pow]; exact Real.log_le_log hp0 (by exact_mod_cast hpL)
    split_ifs with h3
    · rcases le_or_gt L 1 with hL | hL
      · rw [show L + 1 - 2 = 0 by omega, Nat.cast_zero, zero_mul]
        have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
        linarith
      · rw [Nat.cast_sub (by omega)]; push_cast
        nlinarith
    · have hL : L ≤ 2 := by
        by_contra h; push Not at h
        exact h3 (le_trans (Nat.pow_le_pow_right hpp.pos h) hpL)
      have : ((L + 1 - 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : L + 1 - 2 ≤ 1)
      nlinarith
  refine (sum_le_sum hcount).trans ?_
  rw [sum_add_distrib]
  apply add_le_add
  · -- primes up to `√N`
    simp only [hP, psiN]
    rw [sum_filter]
    refine sum_le_sum fun p hp => ?_
    split_ifs with h
    · rw [ArithmeticFunction.vonMangoldt_apply_prime h]
    · exact ArithmeticFunction.vonMangoldt_nonneg
  · -- primes with `p³ ≤ N`: at most `N^{1/3}` of them
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by exact_mod_cast hN))
    have hsub : P.filter (fun p => p ^ 3 ≤ N) ⊆ Icc 1 ⌊(N : ℝ) ^ ((1 / 3) : ℝ)⌋₊ := by
      intro p hp
      simp only [hP, mem_filter, mem_Icc] at hp ⊢
      refine ⟨hp.1.1.1, Nat.le_floor ?_⟩
      have h3 : ((p : ℝ) ^ (3 : ℕ)) ≤ N := by exact_mod_cast hp.2
      calc (p : ℝ) = ((p : ℝ) ^ (3 : ℕ)) ^ ((1 / 3) : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (N : ℝ) ^ ((1 / 3) : ℝ) := Real.rpow_le_rpow (by positivity) h3 (by norm_num)
    calc ((P.filter (fun p => p ^ 3 ≤ N)).card : ℝ) ≤ (Icc 1 ⌊(N : ℝ) ^ ((1 / 3) : ℝ)⌋₊).card := by
          exact_mod_cast card_le_card hsub
      _ = ⌊(N : ℝ) ^ ((1 / 3) : ℝ)⌋₊ := by simp
      _ ≤ (N : ℝ) ^ ((1 / 3) : ℝ) := Nat.floor_le (by positivity)

/-- The final inequality for `N ≥ 10¹²`: `1.03883 √N + N^{1/3} log N < 1.4262 √N`. -/
theorem nonprime_final {N : ℝ} (hN : 1e12 ≤ N) :
    1.03883 * √N + N ^ ((1 / 3) : ℝ) * Real.log N < 1.4262 * √N := by
  have hN0 : 0 < N := by linarith
  set u := N ^ ((1 / 6) : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have hu100 : 100 ≤ u := by
    have : (100 : ℝ) = ((1e12 : ℝ)) ^ ((1 / 6) : ℝ) := by
      rw [show (1e12 : ℝ) = 100 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]; exact Real.rpow_le_rpow (by norm_num) hN (by norm_num)
  have hsq : √N = u ^ (3 : ℕ) := by
    rw [Real.sqrt_eq_rpow, hu, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hcube : N ^ ((1 / 3) : ℝ) = u ^ (2 : ℕ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hlog : Real.log N = 6 * Real.log u := by
    rw [hu, Real.log_rpow hN0]; ring
  -- `log u ≤ u/54.5 + 3`
  have he4 : 54.5 ≤ Real.exp 4 := by
    have := Real.exp_one_gt_d9
    have h : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have e2 : 7.389 ≤ Real.exp 1 ^ 2 := by nlinarith
    rw [h, show Real.exp 1 ^ 4 = (Real.exp 1 ^ 2) ^ 2 by ring]; nlinarith
  have hlogu : Real.log u ≤ u / 54.5 + 3 := by
    have := Real.log_le_sub_one_of_pos (x := u / Real.exp 4) (by positivity)
    rw [Real.log_div hu0.ne' (Real.exp_pos 4).ne', Real.log_exp] at this
    have : u / Real.exp 4 ≤ u / 54.5 := div_le_div_of_nonneg_left hu0.le (by norm_num) he4
    linarith
  rw [hsq, hcube, hlog]
  have hu2 : 0 < u ^ 2 := by positivity
  have h1 : u ^ 2 * (6 * Real.log u) ≤ 6 / 54.5 * u ^ 3 + 18 * u ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlogu (by positivity : (0 : ℝ) ≤ 6 * u ^ 2)
    have e1 : u ^ 2 * (6 * Real.log u) = 6 * u ^ 2 * Real.log u := by ring
    have e2 : 6 * u ^ 2 * (u / 54.5 + 3) = 6 / 54.5 * u ^ 3 + 18 * u ^ 2 := by ring
    linarith
  have h2 : 18 * u ^ 2 ≤ 0.18 * u ^ 3 := by
    have := mul_le_mul_of_nonneg_left hu100 hu2.le
    nlinarith
  have hu3 : 0 < u ^ 3 := by positivity
  linarith

/-- **[B, (2.12)]** ([RS62, (3.23)]): `∑_{n ≤ x} Λ(n)/n ≤ log x` for `x ≥ 1`.
Proved from (2.15) (Chebyshev's identity `∑ Λ(n)⌊N/n⌋ = log N!` and summation by parts) and the
finite check `mertens_small`. -/
theorem sum_vonMangoldt_div_le_log {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℝ) / n ≤ Real.log x := by
  set N := ⌊x⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : Real.log N ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le (by linarith))
  rcases le_or_gt 30 N with h | h
  · exact (sum_vonMangoldt_div_le_log_large h).trans hNx
  · exact (mertens_small N hN (by omega)).trans hNx

/-- **[B, (5.5)]** ([RS62, Thm. 13]): `ψ(y) − θ(y) = ∑_{n ≤ y, n not prime} Λ(n) < 1.4262 √y`
for `y > 0`. Proved from (2.15) (`ψ − θ ≤ ψ(√y) + y^{1/3} log y`) and the finite check
`nonprime_small`. -/
theorem sum_vonMangoldt_nonprime_lt {y : ℝ} (hy : 0 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y := by
  set n := ⌊y⌋₊ with hn
  have hny : (n : ℝ) ≤ y := Nat.floor_le hy.le
  have hsq : √(n : ℝ) ≤ √y := Real.sqrt_le_sqrt hny
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0]; simp; positivity
  rcases le_or_gt n (10 ^ 12) with h | h
  · have := nonprime_small n hpos h; linarith
  · have hN := nonprime_sum_le n hpos
    have hpsi : psiN (Nat.sqrt n) ≤ 1.03883 * √(n : ℝ) := by
      refine (psiN_le _).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.nat_sqrt_le_real_sqrt) (by norm_num)
    have hfin := nonprime_final (N := n) (by
      have : ((10 ^ 12 : ℕ) : ℝ) ≤ n := by exact_mod_cast h.le
      norm_num at this ⊢; linarith)
    linarith

/-- **[B, (2.16)]** ((2.15) and partial summation for `y > 200000`, a computation for
`663 < y ≤ 200000`): `∑_{n ≤ y} Λ(n) n < 1.03884 y²/2` for `y > 663`. -/
theorem sum_vonMangoldt_mul_lt {y : ℝ} (hy : 663 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.03884 * y ^ 2 / 2 := by
  sorry

/-- **[B, (2.17)]** ([RR96, p. 423] and computations for `y < 10⁷`, partial summation):
`∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y > 1.6·10⁶`. -/
theorem sum_vonMangoldt_mul_lt' {y : ℝ} (hy : 1.6e6 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 := by
  sorry

/-- **[B, (2.18)]**: `∑_{n ≤ y} Λ(n)/√n < 2·1.0004 √y` for `y ≥ 1`. -/
theorem sum_vonMangoldt_div_sqrt_lt {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / √n < 2 * 1.0004 * √y := by
  sorry

/-- **[B, (2.19)]** ([RS75, Cor. 2] for `y ≥ 2·758699`, a computation for `117 ≤ y < 2·758699`):
`∑_{y/2 < p ≤ y} (log p)² ≤ (1/2) y log y` for `y ≥ 117`. -/
theorem sum_log_sq_primes_le {y : ℝ} (hy : 117 ≤ y) :
    ∑ p ∈ (Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y := by
  sorry

/-- **[B, (2.21)]** (Ramaré [Ram13]): `|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`. -/
theorem abs_sum_moebius_div_le_log {x : ℝ} (hx : 11815 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 0.03 / Real.log x := by
  sorry

/-- **[B, (2.22)]** (Ramaré [Ramb]): `|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ (4/5)(q/φ(q))/log(x/q)` for
`q < x` (stated in [B] for `q ≤ x`; at `q = x` the right side is `+∞`). -/
theorem abs_sum_moebius_div_coprime_le_log {x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqx : (q : ℝ) < x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤
      4 / 5 * (q / Nat.totient q) / Real.log (x / q) := by
  sorry

/-- **[B, (2.23)]** (Ramaré [Ramb]): `|∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n)| ≤ 1.00303 q/φ(q)`
for all `x > 0`, `q ≥ 1`. -/
theorem abs_sum_moebius_div_log_coprime_le {x : ℝ} (hx : 0 < x) {q : ℕ} (hq : 1 ≤ q) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0)| ≤
      1.00303 * (q / Nat.totient q) := by
  sorry

/-- **[B, (2.24)]** (a computation by Helfgott): `|∑_{n ≤ x} μ(n)/n| ≤ √(2/x)` for
`0 < x ≤ 10¹²`. -/
theorem abs_sum_moebius_div_le_sqrt {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1e12) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ √(2 / x) := by
  sorry

/-- **[B, Lemma C.2.2]** ([RS62, Thm. 15] for `q ≥ 27`, and `q/φ(q) ≤ 3 < Ϝ(r)` for `q < 27`):
`q/φ(q) < Ϝ(r) = e^γ log log r + 2.50637/log log r` for `q ≥ 1`, `r ≥ max(3, q)`. -/
theorem div_totient_lt {q : ℕ} (hq : 1 ≤ q) {r : ℝ} (hr : 3 ≤ r) (hqr : (q : ℝ) ≤ r) :
    (q : ℝ) / Nat.totient q < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) := by
  sorry

end TernaryGoldbach.Prelim
