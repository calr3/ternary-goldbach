import Mathlib
import TernaryGoldbach.Prelim.MoebiusCoprime
import TernaryGoldbach.Prelim.ThetaExplicit
import TernaryGoldbach.Prelim.SmallPsi
import TernaryGoldbach.Prelim.SmallMertens

/-!
# Explicit bounds on sums of `Λ` and `μ` [B, §2.5]

[B] quotes these from the literature (with some supplementary computations).

* The bounds on `ψ` and `θ` used here — (2.12)–(2.15), (2.17), (2.19), (5.5) — are **proved** from
  the explicit prime number theorem `theta_explicit` (`Prelim/ThetaExplicit.lean`:
  `|θ(n) − n| < n/log³ n + ε_pl(n) n` for `n ≥ 2·10⁸`, with a plateau `ε_pl = 2.2·10⁻¹¹` for
  `3400 < log n < 20000`; it replaces Dusart's bound [Dus18, Thm. 4.2]), Büthe's
  `|ψ(n) − n| ≤ 0.94 √n` for `12 ≤ n ≤ 10¹⁹` (`buthe_psi`), a kernel-checked computation for
  `n ≤ 586` (`Prelim/SmallPsi.lean`), and finite computer checks stated as numerical axioms
  (`scripts/psi_checks.py`).
* The bounds on sums of `μ` — (2.21), (2.22), (2.24) — are discussed at the end of the file (`sorry`-free),
  each with its source; (2.23) is proved (with a weaker constant) in `Prelim/MoebiusLog.lean`.  (2.16) and (2.18) are stated but unused.  Lemma C.2.2 (`div_totient_lt`) is
  proved in `Prelim/MertensProduct.lean`.

Two remarks.
* (2.16) is only claimed for `y > 663` (it fails, e.g., at `y = 3`), so results that use it need
  that hypothesis.
* (2.20) is **proved** (elementarily) in `Prelim/MoebiusCoprime.lean`.
-/

open Finset
open ArithmeticFunction (vonMangoldt moebius)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-! ### Numerical axioms (finite computer checks) -/

/-- **Numerical axiom** (`scripts/psi_checks.py`; maximum `1.4261933` at `n = 361`):
`ψ(n) − θ(n) < 1.4262 √n` for `1 ≤ n ≤ 10¹²` (checked at every prime power `p^k`, `k ≥ 2`). -/
axiom nonprime_small (n : ℕ) (h1 : 1 ≤ n) (h : n ≤ 10 ^ 12) :
    ∑ m ∈ Icc 1 n, (if m.Prime then 0 else (Λ m : ℝ)) < 1.4262 * √n

/-- `∑_{m ≤ n} Λ(m)/m ≤ log n` for `1 ≤ n ≤ 100` (kernel-checked, `Prelim/SmallMertens.lean`). -/
theorem mertens_small (n : ℕ) (h1 : 1 ≤ n) (h : n ≤ 100) :
    ∑ m ∈ Icc 1 n, (Λ m : ℝ) / m ≤ Real.log n :=
  Small.mertens_small' h1 h

/-- **Numerical axiom** (`scripts/psi_checks.py`; minimum margin `0.0141` at `n = 6`):
`∑_{m ≤ n} Λ(m)/m ≥ log(n+1) − log(3/√2)` for `3 ≤ n ≤ 10⁶` (at `n = 2` this is an equality,
proved below). -/
axiom mertens_lower_small (n : ℕ) (h1 : 3 ≤ n) (h2 : n ≤ 10 ^ 6) :
    Real.log (n + 1) - Real.log (3 / √2) ≤ ∑ m ∈ Icc 1 n, (Λ m : ℝ) / m

/-- **Numerical axiom** (`scripts/psi_checks.py`; value `−1.57721`): at `X = 10⁶`,
`∑_{m ≤ X} Λ(m)/m − ψ(X)/(X+1) − log(X+2) ≥ −1.5776`. -/
axiom mertens_point :
    -1.5776 ≤ ∑ m ∈ Icc 1 (10 ^ 6), (Λ m : ℝ) / m -
      (∑ m ∈ Icc 1 (10 ^ 6), (Λ m : ℝ)) / (10 ^ 6 + 1) - Real.log (10 ^ 6 + 2)

/-- **Numerical axiom** (`scripts/psi_checks.py`; minimum margin `2.14` at `n = 117`):
`∑_{n/2 < p ≤ n} (log p)² ≤ (1/2) n log n` for `117 ≤ n ≤ 10⁶`. -/
axiom logsq_small (n : ℕ) (h1 : 117 ≤ n) (h2 : n ≤ 10 ^ 6) :
    ∑ p ∈ (Ioc (n / 2) n).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * n * Real.log n

/-! ### The explicit prime number theorem

Dusart's `|θ(x) − x| < x/log³ x` ([Dus18, Thm. 4.2]) is replaced by `theta_explicit`
(`Prelim/ThetaExplicit.lean`), which has an extra plateau term `ε_pl(n) n`. -/

/-! ### `ψ` and `θ` -/

/-- `ψ(n)` for natural `n`. -/
noncomputable def psiN (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, (Λ m : ℝ)

theorem psiN_succ (n : ℕ) : psiN (n + 1) = psiN n + Λ (n + 1) := by
  rw [psiN, sum_Icc_succ_top (by omega), psiN]

/-- `θ(n) = ∑_{p ≤ n} log p`. -/
noncomputable def thetaN (n : ℕ) : ℝ := ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p

theorem psiN_eq (n : ℕ) :
    psiN n = thetaN n + ∑ m ∈ Icc 1 n, (if m.Prime then 0 else (Λ m : ℝ)) := by
  rw [psiN, thetaN, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h]; ring
  · ring

theorem thetaN_nonneg (n : ℕ) : 0 ≤ thetaN n :=
  sum_nonneg fun p _ => Real.log_natCast_nonneg p

theorem psiN_nonneg (n : ℕ) : 0 ≤ psiN n :=
  sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem thetaN_le_psiN (n : ℕ) : thetaN n ≤ psiN n := by
  rw [psiN_eq]
  have : 0 ≤ ∑ m ∈ Icc 1 n, (if m.Prime then 0 else (Λ m : ℝ)) :=
    sum_nonneg fun m _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  linarith

theorem thetaN_large {n : ℕ} (hn : 200000000 ≤ n) :
    |thetaN n - n| < n / Real.log n ^ 3 + epl n * n := by
  unfold thetaN; exact theta_explicit hn

theorem thetaN_sub {a b : ℕ} (hab : a ≤ b) :
    thetaN b - thetaN a = ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p := by
  rw [thetaN, thetaN, sum_filter, sum_filter, sum_filter, show Icc 1 b = Ioc 0 b from rfl,
    show Icc 1 a = Ioc 0 a from rfl, ← sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

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

/-- `N^{1/3} log N ≤ 6 √N`. -/
theorem cbrt_log_le {N : ℝ} (hN : 0 ≤ N) : N ^ ((1 / 3 : ℝ)) * Real.log N ≤ 6 * √N := by
  have h := Real.log_le_rpow_div hN (by norm_num : (0 : ℝ) < 1 / 6)
  have h3 : 0 ≤ N ^ ((1 / 3 : ℝ)) := Real.rpow_nonneg hN _
  calc N ^ ((1 / 3 : ℝ)) * Real.log N ≤ N ^ ((1 / 3 : ℝ)) * (N ^ ((1 / 6 : ℝ)) / (1 / 6)) :=
        mul_le_mul_of_nonneg_left h h3
    _ = 6 * (N ^ ((1 / 3 : ℝ)) * N ^ ((1 / 6 : ℝ))) := by ring
    _ = 6 * √N := by
        rw [← Real.rpow_add' hN (by norm_num), Real.sqrt_eq_rpow]; norm_num

/-- `√N ≤ N / a` when `a² ≤ N`. -/
theorem sqrt_le_div {N a : ℝ} (ha : 0 < a) (h : a ^ 2 ≤ N) : √N ≤ N / a := by
  have hs : a ≤ √N := Real.le_sqrt_of_sq_le h
  have hN : 0 ≤ N := le_trans (sq_nonneg a) h
  rw [le_div_iff₀ ha]
  calc √N * a ≤ √N * √N := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ = N := Real.mul_self_sqrt hN

/-- `c ≤ log N` from `exp c ≤ N`, for `c = k` a natural number, via `e < 2.7182818286`. -/
theorem nat_le_log {N : ℝ} {k : ℕ} (h : (2.7182818286 : ℝ) ^ k ≤ N) : (k : ℝ) ≤ Real.log N := by
  have hN : 0 < N := lt_of_lt_of_le (by positivity) h
  rw [Real.le_log_iff_exp_le hN]
  calc Real.exp k = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ (2.7182818286 : ℝ) ^ k := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le k
    _ ≤ N := h

/-- `x / log³ x ≤ x / k³` when `log x ≥ k`. -/
theorem div_log_cube_le {x : ℝ} {k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) (h : k ≤ Real.log x) :
    x / Real.log x ^ 3 ≤ x / k ^ 3 :=
  div_le_div_of_nonneg_left hx (by positivity) (pow_le_pow_left₀ hk.le h 3)

theorem log_ge_23 {x : ℝ} (hx : 10 ^ 10 ≤ x) : 23 ≤ Real.log x := by
  have := nat_le_log (N := x) (k := 23) (by norm_num; linarith)
  exact_mod_cast this

/-- `ψ(N) ≤ N + N/log³N + 7.04 √N` for `N ≥ 2·10⁸`, given `ψ(√N) ≤ 1.03883 √N`. -/
theorem psi_upper_of {N : ℕ} (hN : 200000000 ≤ N)
    (h : psiN (Nat.sqrt N) ≤ 1.03883 * (Nat.sqrt N : ℝ)) :
    psiN N ≤ N + N / Real.log N ^ 3 + epl N * N + 7.04 * √(N : ℝ) := by
  rw [psiN_eq]
  have h1 := (abs_lt.1 (thetaN_large hN)).2
  have h2 := nonprime_sum_le N (by omega)
  have h3 := cbrt_log_le (N := (N : ℝ)) (Nat.cast_nonneg N)
  have h4 : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have h5 := Real.sqrt_nonneg (N : ℝ)
  linarith

/-- `ψ(n) < 1.03883 n` for `1 ≤ n ≤ 10¹⁹`: a kernel-checked computation for `n ≤ 586`
(`Small.psi_lt_small`) and Büthe's `ψ(n) ≤ n + 0.94 √n` above. -/
theorem psi_lt_small' {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 10 ^ 19) : psiN n < 1.03883 * n := by
  rcases le_or_gt n 586 with h | h
  · exact Small.psi_lt_small h1 h
  · have hB := (abs_le.1 (buthe_psi n (by omega) h2)).2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs : (24.21 : ℝ) ≤ √(n : ℝ) :=
      Real.le_sqrt_of_sq_le (by
        have h587 : (587 : ℝ) ≤ n := by exact_mod_cast h
        norm_num; linarith)
    have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0
    unfold psiN; nlinarith

/-- `ψ(n) ≤ 1.03883 n` for all `n`, and `ψ(n) ≤ 1.0004 n` for `n ≥ 6·10⁶` (Büthe's bound up to
`10¹⁹`; above, strong induction with `theta_explicit` and `ψ − θ ≤ ψ(√n) + n^{1/3} log n`). -/
theorem psi_bounds (n : ℕ) : psiN n ≤ 1.03883 * n ∧ (6000000 ≤ n → psiN n ≤ 1.0004 * n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [psiN]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt n (10 ^ 19) with h2 | h2
  · refine ⟨(psi_lt_small' hpos h2).le, fun h6 => ?_⟩
    have hB := (abs_le.1 (buthe_psi n (by omega) h2)).2
    have hs : (2449 : ℝ) ≤ √(n : ℝ) :=
      Real.le_sqrt_of_sq_le (by
        have h6' : (6000000 : ℝ) ≤ n := by exact_mod_cast h6
        norm_num; linarith)
    have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0
    unfold psiN; nlinarith
  · have hsq : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
    have h9 : 1000000000 ≤ n := le_trans (by norm_num) h2.le
    have hup := psi_upper_of (N := n) (by omega) (ih _ hsq).1
    have hn9 : (1000000000 : ℝ) ≤ n := by exact_mod_cast h9
    have hlog : (20 : ℝ) ≤ Real.log n := by
      have := nat_le_log (N := n) (k := 20) (by norm_num; linarith)
      exact_mod_cast this
    have ha := div_log_cube_le hn0 (by norm_num) hlog
    have hb := sqrt_le_div (N := n) (a := 31622) (by norm_num) (by norm_num; linarith)
    have key : (n : ℝ) / Real.log n ^ 3 + epl n * n + 7.04 * √(n : ℝ) ≤ 0.0004 * n := by
      have : (n : ℝ) / (20 : ℝ) ^ 3 = n / 8000 := by norm_num
      have h7 : 7.04 * √(n : ℝ) ≤ 7.04 * ((n : ℝ) / 31622) := by linarith
      have : (n : ℝ) / 8000 + 7.04 * ((n : ℝ) / 31622) ≤ 0.00039 * n := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; nlinarith
      have he := mul_le_mul_of_nonneg_right (epl_le n) hn0
      linarith
    exact ⟨by linarith, fun _ => by linarith⟩

/-! ### (2.14), (2.15) -/

/-- **[B, (2.14)]**, for `y ≥ 6·10⁶` ([B] states it for `y ≥ 2·10⁶`; we use it only for
`y ≥ 2.7·10⁷`): `∑_{n ≤ y} Λ(n) ≤ 1.0004 y`.  Proved from Büthe's bound and `theta_explicit`
(`psi_bounds`). -/
theorem sum_vonMangoldt_le_10004 {y : ℝ} (hy : 6e6 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y := by
  have hN : 6000000 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
  have h := (psi_bounds ⌊y⌋₊).2 hN
  have hy' : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  unfold psiN at h; linarith

/-- **[B, (2.15)]** ([RS62, Thm. 12]): `ψ(y) = ∑_{n ≤ y} Λ(n) < 1.03883 y` for `y > 0`.
Proved from (2.14) and `psi_lt_small'`. -/
theorem sum_vonMangoldt_lt {y : ℝ} (hy : 0 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) < 1.03883 * y := by
  rcases le_or_gt 6e6 y with h | h
  · have := sum_vonMangoldt_le_10004 h; linarith
  · set n := ⌊y⌋₊ with hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp; positivity
    · have hn2 : n < 6000000 :=
        Nat.floor_lt hy.le |>.2 (show y < ((6000000 : ℕ) : ℝ) by norm_num; linarith)
      have h1 := psi_lt_small' hpos (by omega : n ≤ 10 ^ 19)
      unfold psiN at h1
      have h2 : (n : ℝ) ≤ y := Nat.floor_le hy.le
      linarith

theorem psiN_le (n : ℕ) : psiN n ≤ 1.03883 * n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [psiN]
  have := sum_vonMangoldt_lt (y := n) (by exact_mod_cast h)
  rw [Nat.floor_natCast] at this; exact this.le

/-! ### (2.12) -/

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

/-! ### (5.5) -/

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

/-! ### (2.13) -/

theorem Ioo_succ_insert {a b : ℕ} (h : a < b) : Ioo a (b + 1) = insert b (Ioo a b) := by
  ext x; simp only [mem_Ioo, mem_insert]; omega

theorem Ioo_self_succ (a : ℕ) : Ioo a (a + 1) = ∅ := by
  ext x; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega

theorem sum_Ioo_id (N : ℕ) : ∑ n ∈ Ioo 0 N, (n : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; rw [Ioo_self_succ]; simp
    rw [Ioo_succ_insert h, sum_insert (by simp), ih]
    push_cast; ring

/-- `∑_{a < n < b} 1/(n+1) ≥ log(b+1) − log(a+2)`. -/
theorem sum_inv_succ_ge {a b : ℕ} (hab : a < b) :
    Real.log (b + 1) - Real.log (a + 2) ≤ ∑ n ∈ Ioo a b, (1 : ℝ) / (n + 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h | h
    · rw [Ioo_succ_insert h, sum_insert (by simp)]
      have ih := ih h
      have hb : (0 : ℝ) < b + 1 := by positivity
      have hl := Real.log_le_sub_one_of_pos (x := ((b : ℝ) + 1 + 1) / (b + 1)) (by positivity)
      rw [Real.log_div (by positivity) hb.ne'] at hl
      have e : ((b : ℝ) + 1 + 1) / (b + 1) - 1 = 1 / (b + 1) := by field_simp; ring
      push_cast
      linarith
    · have : a = b := by omega
      subst this
      rw [Ioo_self_succ]
      push_cast; ring_nf; simp

/-- `1/(√b (b+1)) ≤ 2/√b − 2/√(b+1)`. -/
theorem inv_sqrt_tele {b : ℝ} (hb : 0 < b) :
    1 / (√b * (b + 1)) ≤ 2 / √b - 2 / √(b + 1) := by
  set s := √b with hs
  set t := √(b + 1) with ht
  have hs0 : 0 < s := Real.sqrt_pos.2 hb
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hss : s ^ 2 = b := Real.sq_sqrt hb.le
  have htt : t ^ 2 = b + 1 := Real.sq_sqrt (by linarith)
  have hst : s ≤ t := Real.sqrt_le_sqrt (by linarith)
  rw [← htt, div_sub_div _ _ hs0.ne' ht0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hd : (t - s) * (t + s) = 1 := by nlinarith
  nlinarith [mul_pos hs0 ht0, mul_pos (mul_pos hs0 ht0) ht0]

/-- `∑_{a < n < b} 1/(√n (n+1)) ≤ 2/√(a+1) − 2/√b`. -/
theorem sum_inv_sqrt_le {a b : ℕ} (hab : a < b) :
    ∑ n ∈ Ioo a b, (1 : ℝ) / (√n * (n + 1)) ≤ 2 / √((a : ℝ) + 1) - 2 / √(b : ℝ) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h | h
    · rw [Ioo_succ_insert h, sum_insert (by simp)]
      have := inv_sqrt_tele (b := (b : ℝ)) (by exact_mod_cast (by omega : 0 < b))
      have := ih h
      push_cast; linarith
    · have : a = b := by omega
      subst this
      rw [Ioo_self_succ]
      push_cast; simp

/-- `1/((b+1) log³ b) ≤ 2/log² b − 2/log²(b+1)` for `b ≥ 3`. -/
theorem inv_log_cube_tele {b : ℝ} (hb : 3 ≤ b) :
    1 / ((b + 1) * Real.log b ^ 3) ≤ 2 / Real.log b ^ 2 - 2 / Real.log (b + 1) ^ 2 := by
  have hb0 : 0 < b := by linarith
  set L := Real.log b with hL
  set M := Real.log (b + 1) with hM
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hb0]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hb
  have hLM : L ≤ M := Real.log_le_log hb0 (by linarith)
  have hM2 : M ≤ 2 * L := by
    rw [hM, hL, ← Real.log_rpow hb0]
    exact Real.log_le_log (by linarith) (by norm_num; nlinarith)
  have hd : 1 / (b + 1) ≤ M - L := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (b + 1) / b) (by positivity)
    rw [Real.log_div (by linarith) hb0.ne'] at h
    have e : 1 - ((b + 1) / b)⁻¹ = 1 / (b + 1) := by field_simp; ring
    rw [e] at h; exact h
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have hb1 : 0 < b + 1 := by linarith
  have h1 : 2 / L ^ 2 - 2 / M ^ 2 = 2 * (M - L) * (M + L) / (L ^ 2 * M ^ 2) := by
    field_simp; ring
  have h2 : 2 * (1 / (b + 1)) * (M + L) / (L ^ 2 * M ^ 2) ≤
      2 * (M - L) * (M + L) / (L ^ 2 * M ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_right hd (by linarith : (0 : ℝ) ≤ 2 * (M + L))
    nlinarith
  have h3 : 1 / ((b + 1) * L ^ 3) ≤ 2 * (1 / (b + 1)) * (M + L) / (L ^ 2 * M ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : M ^ 2 ≤ 2 * L * (M + L) := by nlinarith
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ L ^ 2 * (b + 1))]
  linarith

/-- `∑_{a < n < b} 1/((n+1) log³ n) ≤ 2/log²(a+1) − 2/log² b` for `a ≥ 2`. -/
theorem sum_inv_log_cube_le {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    ∑ n ∈ Ioo a b, (1 : ℝ) / ((n + 1) * Real.log n ^ 3) ≤
      2 / Real.log ((a : ℝ) + 1) ^ 2 - 2 / Real.log (b : ℝ) ^ 2 := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h | h
    · rw [Ioo_succ_insert h, sum_insert (by simp)]
      have := inv_log_cube_tele (b := (b : ℝ)) (by exact_mod_cast (by omega : 3 ≤ b))
      have := ih h
      push_cast; linarith
    · have : a = b := by omega
      subst this
      rw [Ioo_self_succ]
      push_cast; simp

/-- `ψ(n) ≥ n − 0.95 √n − n/log³ n` for `n ≥ 12`. -/
theorem psi_lower2 {n : ℕ} (hn : 12 ≤ n) :
    (n : ℝ) - 0.95 * √(n : ℝ) - n / Real.log n ^ 3 - epl n * n ≤ psiN n := by
  have hepl := mul_nonneg (epl_nonneg n) (Nat.cast_nonneg n)
  have hl : 0 ≤ (n : ℝ) / Real.log n ^ 3 := by
    have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    positivity
  have hs := Real.sqrt_nonneg (n : ℝ)
  rcases le_or_gt n (10 ^ 10) with h | h
  · have := (abs_le.1 (buthe_psi n hn (h.trans (by norm_num)))).1
    unfold psiN; linarith
  · have h1 := (abs_lt.1 (thetaN_large (n := n) (by omega))).1
    have h2 := thetaN_le_psiN n
    linarith

/-- The Abel summation term: `ψ(n)(1/n − 1/(n+1)) ≥ 1/(n+1) − 0.95/(√n (n+1)) − 1/((n+1) log³ n)`. -/
theorem abel_term_ge {n : ℕ} (hn : 12 ≤ n) :
    1 / ((n : ℝ) + 1) - 0.95 * (1 / (√(n : ℝ) * (n + 1))) - 1 / ((n + 1) * Real.log n ^ 3) -
        epl n / ((n : ℝ) + 1) ≤
      psiN n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hk : 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) = 1 / (n * (n + 1)) := by
    push_cast; field_simp; ring
  rw [hk]
  have hk0 : (0 : ℝ) ≤ 1 / (n * (n + 1)) := by positivity
  have h := mul_le_mul_of_nonneg_right (psi_lower2 hn) hk0
  have e1 : (n : ℝ) * (1 / (n * (n + 1))) = 1 / (n + 1) := by field_simp
  have e2 : √(n : ℝ) * (1 / (n * (n + 1))) = 1 / (√(n : ℝ) * (n + 1)) := by
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), ← mul_assoc, hss]; ring
  have e3 : (n : ℝ) / Real.log n ^ 3 * (1 / (n * (n + 1))) = 1 / ((n + 1) * Real.log n ^ 3) := by
    field_simp
  have e4 : epl n * n * (1 / (n * (n + 1))) = epl n / ((n : ℝ) + 1) := by field_simp
  have : ((n : ℝ) - 0.95 * √(n : ℝ) - n / Real.log n ^ 3 - epl n * n) * (1 / (n * (n + 1))) =
      1 / ((n : ℝ) + 1) - 0.95 * (1 / (√(n : ℝ) * (n + 1))) - 1 / ((n + 1) * Real.log n ^ 3) -
        epl n / ((n : ℝ) + 1) := by
    rw [sub_mul, sub_mul, sub_mul, mul_assoc, e1, e2, e3, e4]
  linarith

/-- **[B, (2.13)]** for integers: `∑_{n ≤ N} Λ(n)/n ≥ log(N+1) − log(3/√2)`, `N ≥ 1`. -/
theorem mertens_lower_nat {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N + 1) - Real.log (3 / √2) ≤ ∑ n ∈ Icc 1 N, (Λ n : ℝ) / n := by
  have hlog32 : Real.log (3 / √2) = Real.log 3 - Real.log 2 / 2 := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_sqrt (by norm_num)]
  rcases lt_or_ge N 3 with h3 | h3
  · interval_cases N
    · -- `N = 1`: `log 2 ≤ log(3/√2)`
      have : Real.log 2 ≤ Real.log (3 / √2) := by
        apply Real.log_le_log (by norm_num)
        rw [le_div_iff₀ (by positivity)]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      have hs : ∑ n ∈ Icc 1 1, (Λ n : ℝ) / n = 0 := by simp
      rw [hs, show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]; linarith
    · -- `N = 2`: equality
      have hs : ∑ n ∈ Icc 1 2, (Λ n : ℝ) / n = Real.log 2 / 2 := by
        rw [show Icc 1 2 = {1, 2} by rfl, sum_pair (by norm_num),
          ArithmeticFunction.vonMangoldt_apply_one,
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        push_cast; ring
      rw [hs, hlog32, show ((2 : ℕ) : ℝ) + 1 = 3 by norm_num]; linarith
  rcases le_or_gt N (10 ^ 6) with h6 | h6
  · exact mertens_lower_small N h3 h6
  -- `N > 10⁶`: summation by parts from `X = 10⁶`
  set X : ℕ := 10 ^ 6 with hX
  have hsplit : ∑ n ∈ Icc 1 N, (Λ n : ℝ) / n =
      ∑ n ∈ Icc 1 X, (Λ n : ℝ) / n + ∑ n ∈ Ioc X N, (Λ n : ℝ) * (fun n : ℕ => 1 / (n : ℝ)) n := by
    simp only [mul_one_div]
    rw [show Icc 1 N = Ioc 0 N from rfl, show Icc 1 X = Ioc 0 X from rfl,
      sum_Ioc_consecutive _ (Nat.zero_le X) h6.le]
  rw [hsplit, abel_Ioc _ X N h6]
  -- the interior terms
  have hint : ∑ n ∈ Ioo X N, (1 / ((n : ℝ) + 1) - 0.95 * (1 / (√(n : ℝ) * (n + 1))) -
      1 / ((n + 1) * Real.log n ^ 3) - epl n / ((n : ℝ) + 1)) ≤
      ∑ n ∈ Ioo X N, psiN n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) :=
    sum_le_sum fun n hn => abel_term_ge (by have := (mem_Ioo.1 hn).1; omega)
  rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum] at hint
  have hep : ∑ n ∈ Ioo X N, epl n / ((n : ℝ) + 1) ≤ 3.66e-7 :=
    (sum_epl_div_le X N).trans (by split_ifs <;> norm_num)
  have h1 := sum_inv_succ_ge h6
  have h2 := sum_inv_sqrt_le h6
  have h3' := sum_inv_log_cube_le (a := X) (by norm_num) h6
  have hb2 : 0 ≤ 2 / √(N : ℝ) := by positivity
  have hb3 : 0 ≤ 2 / Real.log (N : ℝ) ^ 2 := by positivity
  -- numerical bounds at `X + 1 = 10⁶ + 1`
  have hX1 : ((X : ℕ) : ℝ) + 1 = 1000001 := by norm_num [hX]
  have hsX : 2 / √(((X : ℕ) : ℝ) + 1) ≤ 0.002 := by
    rw [hX1, div_le_iff₀ (by positivity)]
    have : (1000 : ℝ) ≤ √1000001 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have hlX : (13 : ℝ) ≤ Real.log (((X : ℕ) : ℝ) + 1) := by
    rw [hX1]; exact_mod_cast nat_le_log (N := 1000001) (k := 13) (by norm_num)
  have hlX2 : 2 / Real.log (((X : ℕ) : ℝ) + 1) ^ 2 ≤ 2 / 169 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13) hlX 2])
  -- the boundary term at `N`
  have hNb : 1 - 0.95 / 1000 - 1 / 2197 - 2.2e-11 ≤ psiN N * (1 / (N : ℝ)) := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hl := psi_lower2 (n := N) (by omega)
    have hlN : (13 : ℝ) ≤ Real.log N :=
      le_trans hlX (Real.log_le_log (by positivity) (by rw [hX1]; exact_mod_cast h6))
    have hsN : (1000 : ℝ) ≤ √(N : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast (by omega : 10 ^ 6 ≤ N))
    have hss : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN0.le
    have e : ((N : ℝ) - 0.95 * √(N : ℝ) - N / Real.log N ^ 3 - epl N * N) * (1 / (N : ℝ)) =
        1 - 0.95 / √(N : ℝ) - 1 / Real.log N ^ 3 - epl N := by
      have hs0 : 0 < √(N : ℝ) := by linarith
      have e1 : (N : ℝ) * (1 / N) = 1 := by field_simp
      have e2 : 0.95 * √(N : ℝ) * (1 / N) = 0.95 / √(N : ℝ) := by
        rw [mul_one_div, div_eq_div_iff hN0.ne' hs0.ne', mul_assoc, hss]
      have e3 : (N : ℝ) / Real.log N ^ 3 * (1 / N) = 1 / Real.log N ^ 3 := by field_simp
      have e4 : epl N * N * (1 / (N : ℝ)) = epl N := by field_simp
      rw [sub_mul, sub_mul, sub_mul, e1, e2, e3, e4]
    have h1' : 0.95 / √(N : ℝ) ≤ 0.95 / 1000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsN
    have h2' : 1 / Real.log N ^ 3 ≤ 1 / 2197 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13) hlN 3])
    have := mul_le_mul_of_nonneg_right hl (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))
    have := epl_le (N : ℝ)
    linarith
  have hpt := mertens_point
  have hpX : psiN X * (1 / ((X + 1 : ℕ) : ℝ)) =
      (∑ m ∈ Icc 1 (10 ^ 6), (Λ m : ℝ)) / (10 ^ 6 + 1) := by
    rw [psiN, hX]; push_cast; ring
  have hlog2 : Real.log ((X : ℕ) + 2 : ℝ) = Real.log (10 ^ 6 + 2) := by rw [hX]; push_cast; ring_nf
  have hl32 : Real.log 2 ≤ Real.log (3 / √2) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hl2 := Real.log_two_gt_d9
  rw [hpX]
  have hcast : ((N : ℕ) : ℝ) + 1 = (N : ℝ) + 1 := rfl
  linarith

/-- **[B, (2.13)]**: `∑_{n ≤ x} Λ(n)/n ≥ log x − log(3/√2)` for `x ≥ 1`. -/
theorem log_sub_le_sum_vonMangoldt_div {x : ℝ} (hx : 1 ≤ x) :
    Real.log x - Real.log (3 / √2) ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℝ) / n := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h := mertens_lower_nat hN
  have : Real.log x ≤ Real.log (⌊x⌋₊ + 1) :=
    Real.log_le_log (by linarith) (Nat.lt_floor_add_one x).le
  linarith

/-! ### (2.16)–(2.18) -/

/- [B, (2.16)] is proved in `Prelim/LambdaMuExtra.lean` (from (2.17) and a finite check). -/

/-- `ψ(m) ≥ (1 − 1/12000) m − 0.95 √m − 11` for all `m`. -/
theorem psi_lower_all (m : ℕ) :
    (1 - 1 / 12000) * (m : ℝ) - 0.95 * √(m : ℝ) - 11 ≤ psiN m := by
  have hs := Real.sqrt_nonneg (m : ℝ)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases lt_or_ge m 12 with h | h
  · have : (m : ℝ) ≤ 11 := by exact_mod_cast (by omega : m ≤ 11)
    have := psiN_nonneg m
    nlinarith
  rcases le_or_gt m (10 ^ 10) with h' | h'
  · have := (abs_le.1 (buthe_psi m h (h'.trans (by norm_num)))).1
    unfold psiN; nlinarith
  · have h1 := (abs_lt.1 (thetaN_large (n := m) (by omega))).1
    have h2 := thetaN_le_psiN m
    have hx : (10 : ℝ) ^ 10 ≤ m := by exact_mod_cast h'.le
    have h3 := div_log_cube_le hm0 (by norm_num) (log_ge_23 hx)
    have : (m : ℝ) / 23 ^ 3 + 2.2e-11 * m ≤ m / 12000 := by
      rw [div_add' _ _ _ (by norm_num), div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    have he := mul_le_mul_of_nonneg_right (epl_le m) hm0
    linarith

/-- `ψ(N) ≤ (1 + 1.6·10⁻⁴) N + 0.95 √N` for `N ≥ 11`. -/
theorem psi_upper_all {N : ℕ} (hN : 11 ≤ N) :
    psiN N ≤ (1 + 0.00016) * N + 0.95 * √(N : ℝ) := by
  have hs := Real.sqrt_nonneg (N : ℝ)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rcases le_or_gt N (10 ^ 10) with h | h
  · rcases (show N = 11 ∨ 12 ≤ N by omega) with h11 | h12
    · subst h11
      have := psiN_le 11
      have h3 : (3 : ℝ) ≤ √((11 : ℕ) : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
      push_cast at this h3 ⊢; nlinarith
    have := (abs_le.1 (buthe_psi N h12 (h.trans (by norm_num)))).2
    unfold psiN; nlinarith
  · have hsq : Nat.sqrt N < N := Nat.sqrt_lt_self (by omega)
    have hup := psi_upper_of (N := N) (by omega) (psi_bounds _).1
    have hx : (10 : ℝ) ^ 10 ≤ N := by exact_mod_cast h.le
    have h3 := div_log_cube_le hN0 (by norm_num) (log_ge_23 hx)
    have h4 := sqrt_le_div (N := (N : ℝ)) (a := 100000) (by norm_num) (by norm_num; linarith)
    have : (N : ℝ) / 23 ^ 3 + 7.04 * ((N : ℝ) / 100000) ≤ 0.000159 * N := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; nlinarith
    have he := mul_le_mul_of_nonneg_right (epl_le N) hN0
    nlinarith

/-- **[B, (2.17)]**, `N ≥ 10⁸`. -/
theorem psi_mul_large {N : ℕ} (hN : 10 ^ 8 ≤ N) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) * n < 1.0008 * (N : ℝ) ^ 2 / 2 := by
  have hab := abel_Ioc (fun n => (n : ℝ)) 0 N (by omega)
  have hpsi0 : psiN 0 = 0 := by simp [psiN]
  rw [show Icc 1 N = Ioc 0 N from rfl, hab, hpsi0]
  simp only [zero_mul, sub_zero]
  have e : ∑ n ∈ Ioo 0 N, psiN n * ((n : ℝ) - ((n + 1 : ℕ) : ℝ)) = -∑ n ∈ Ioo 0 N, psiN n := by
    rw [← sum_neg_distrib]; refine sum_congr rfl fun n _ => ?_; push_cast; ring
  rw [e]
  have hlow : ∑ n ∈ Ioo 0 N, ((1 - 1 / 12000) * (n : ℝ) - 0.95 * √(n : ℝ) - 11) ≤
      ∑ n ∈ Ioo 0 N, psiN n := sum_le_sum fun n _ => psi_lower_all n
  have hcard : ((Ioo 0 N).card : ℝ) ≤ N := by
    rw [Nat.card_Ioo]; exact_mod_cast (by omega : N - 0 - 1 ≤ N)
  have hsq : ∑ n ∈ Ioo 0 N, √(n : ℝ) ≤ N * √(N : ℝ) := by
    calc ∑ n ∈ Ioo 0 N, √(n : ℝ) ≤ ∑ _n ∈ Ioo 0 N, √(N : ℝ) :=
          sum_le_sum fun n hn => Real.sqrt_le_sqrt (by exact_mod_cast (mem_Ioo.1 hn).2.le)
      _ = (Ioo 0 N).card * √(N : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ N * √(N : ℝ) := mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)
  have hlow' : (1 - 1 / 12000) * ((N : ℝ) * (N - 1) / 2) - 0.95 * (N * √(N : ℝ)) - 11 * N ≤
      ∑ n ∈ Ioo 0 N, psiN n := by
    refine le_trans ?_ hlow
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_Ioo_id, sum_const, nsmul_eq_mul]
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hup := psi_upper_all (N := N) (by omega)
  set s := √(N : ℝ) with hs
  have hs2 : s ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs4 : (10000 : ℝ) ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]; exact_mod_cast (by omega : 10 ^ 8 ≤ N)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hup' : psiN N * N ≤ ((1 + 0.00016) * N + 0.95 * s) * N := mul_le_mul_of_nonneg_right hup hN0
  rw [← hs2] at hup' hlow' ⊢
  nlinarith [mul_pos (by linarith : (0 : ℝ) < s) (by linarith : (0 : ℝ) < s)]

/-- `ψ(m) ≥ m − 0.94 √m − 11` for `m ≤ 10¹⁹` (Büthe for `m ≥ 12`, trivially below). -/
theorem psi_lower_buthe {m : ℕ} (hm : m ≤ 10 ^ 19) :
    (m : ℝ) - 0.94 * √(m : ℝ) - 11 ≤ psiN m := by
  have hs := Real.sqrt_nonneg (m : ℝ)
  rcases lt_or_ge m 12 with h | h
  · have : (m : ℝ) ≤ 11 := by exact_mod_cast (by omega : m ≤ 11)
    have := psiN_nonneg m
    linarith
  · have := (abs_le.1 (buthe_psi m h hm)).1
    unfold psiN; linarith

/-- **[B, (2.17)]** for `2.5·10⁷ ≤ N ≤ 10¹⁹`, from Büthe's bound by partial summation. -/
theorem psi_mul_buthe {N : ℕ} (hN : 25000000 ≤ N) (hN19 : N ≤ 10 ^ 19) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) * n < 1.0008 * (N : ℝ) ^ 2 / 2 := by
  have hab := abel_Ioc (fun n => (n : ℝ)) 0 N (by omega)
  have hpsi0 : psiN 0 = 0 := by simp [psiN]
  rw [show Icc 1 N = Ioc 0 N from rfl, hab, hpsi0]
  simp only [zero_mul, sub_zero]
  have e : ∑ n ∈ Ioo 0 N, psiN n * ((n : ℝ) - ((n + 1 : ℕ) : ℝ)) = -∑ n ∈ Ioo 0 N, psiN n := by
    rw [← sum_neg_distrib]; refine sum_congr rfl fun n _ => ?_; push_cast; ring
  rw [e]
  have hlow : ∑ n ∈ Ioo 0 N, ((n : ℝ) - 0.94 * √(n : ℝ) - 11) ≤ ∑ n ∈ Ioo 0 N, psiN n :=
    sum_le_sum fun n hn => psi_lower_buthe (le_trans (mem_Ioo.1 hn).2.le hN19)
  have hcard : ((Ioo 0 N).card : ℝ) ≤ N := by
    rw [Nat.card_Ioo]; exact_mod_cast (by omega : N - 0 - 1 ≤ N)
  have hsq : ∑ n ∈ Ioo 0 N, √(n : ℝ) ≤ N * √(N : ℝ) := by
    calc ∑ n ∈ Ioo 0 N, √(n : ℝ) ≤ ∑ _n ∈ Ioo 0 N, √(N : ℝ) :=
          sum_le_sum fun n hn => Real.sqrt_le_sqrt (by exact_mod_cast (mem_Ioo.1 hn).2.le)
      _ = (Ioo 0 N).card * √(N : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ N * √(N : ℝ) := mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)
  have hlow' : (N : ℝ) * (N - 1) / 2 - 0.94 * (N * √(N : ℝ)) - 11 * N ≤
      ∑ n ∈ Ioo 0 N, psiN n := by
    refine le_trans ?_ hlow
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_Ioo_id, sum_const, nsmul_eq_mul]
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hup : psiN N ≤ N + 0.94 * √(N : ℝ) := by
    have := (abs_le.1 (buthe_psi N (by omega) hN19)).2
    unfold psiN; linarith
  set s := √(N : ℝ) with hs
  have hs2 : s ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs4 : (5000 : ℝ) ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
    exact_mod_cast (by omega : 25000000 ≤ N)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hup' : psiN N * N ≤ (N + 0.94 * s) * N := mul_le_mul_of_nonneg_right hup hN0
  rw [← hs2] at hup' hlow' ⊢
  have hs0 : (0 : ℝ) < s := by linarith
  have key : 1.88 * s ^ 3 + 11.5 * s ^ 2 < 0.0004 * s ^ 4 := by
    have h1 : 1.88 * s + 11.5 < 0.0004 * s ^ 2 := by nlinarith
    have h2 : 0 < s ^ 2 := by positivity
    nlinarith
  nlinarith

/-- **[B, (2.17)]**, for `y ≥ 2.5·10⁷` ([B] states it for `y > 1.6·10⁶`; we use it only for
`y ≥ 2.7·10⁷`): `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2`. From Büthe's bound up to `10⁸` and
`theta_explicit` above. -/
theorem sum_vonMangoldt_mul_lt' {y : ℝ} (hy : 2.5e7 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 := by
  set N := ⌊y⌋₊
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hN : 25000000 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hmono : 1.0008 * (N : ℝ) ^ 2 / 2 ≤ 1.0008 * y ^ 2 / 2 := by
    have : (N : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNy 2
    linarith
  rcases le_or_gt N (10 ^ 8) with h | h
  · exact (psi_mul_buthe hN (h.trans (by norm_num))).trans_le hmono
  · exact (psi_mul_large h.le).trans_le hmono

/- [B, (2.18)] is proved in `Prelim/LambdaMuExtra.lean` (from (2.14) by summation by parts and finite
checks). -/

/-! ### (2.19) -/

/-- `|θ(n) − n| ≤ 1.95 √n + n/log³ n` for `n ≥ 5·10⁵`. -/
theorem thetaN_close {n : ℕ} (hn : 500000 ≤ n) :
    |thetaN n - n| ≤ 1.95 * √(n : ℝ) + n / Real.log n ^ 3 + epl n * n := by
  have hepl := mul_nonneg (epl_nonneg n) (Nat.cast_nonneg n)
  have hl : 0 ≤ (n : ℝ) / Real.log n ^ 3 := by
    have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    positivity
  have hs := Real.sqrt_nonneg (n : ℝ)
  rcases le_or_gt n (10 ^ 10) with h | h
  · -- [Büthe 2018, Thm 2] (`buthe_theta`, `1423 ≤ n ≤ 10¹⁹`)
    have := buthe_theta n (by omega) (h.trans (by norm_num))
    unfold thetaN; linarith
  · have := thetaN_large (n := n) (by omega)
    linarith

theorem sum_logsq_le_mul (a b : ℕ) :
    ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p ^ 2 ≤
      Real.log b * ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p := by
  rw [mul_sum]
  refine sum_le_sum fun p hp => ?_
  have hp := mem_filter.1 hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
  have h1 : Real.log p ≤ Real.log b :=
    Real.log_le_log hp0 (by exact_mod_cast (mem_Ioc.1 hp.1).2)
  have h2 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  nlinarith

set_option maxHeartbeats 800000 in
/-- **[B, (2.19)]** for integers `N > 10⁶`. -/
theorem logsq_large {N : ℕ} (hN : 10 ^ 6 < N) :
    ∑ p ∈ (Ioc (N / 2) N).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * N * Real.log N := by
  set a := N / 2 with ha
  set b := 3 * N / 4 with hb
  have hab : a ≤ b := by omega
  have hbN : b ≤ N := by omega
  have ha5 : 500000 ≤ a := by omega
  have hNr : (1000000 : ℝ) < N := by exact_mod_cast hN
  have har1 : (a : ℝ) ≤ N / 2 := by
    have : 2 * a ≤ N := by omega
    have : (2 : ℝ) * a ≤ N := by exact_mod_cast this
    linarith
  have har2 : ((N : ℝ) - 1) / 2 ≤ a := by
    have : N ≤ 2 * a + 1 := by omega
    have : (N : ℝ) ≤ 2 * a + 1 := by exact_mod_cast this
    linarith
  have hbr1 : (b : ℝ) ≤ 3 * N / 4 := by
    have : 4 * b ≤ 3 * N := by omega
    have : (4 : ℝ) * b ≤ 3 * N := by exact_mod_cast this
    linarith
  have hbr2 : (3 * (N : ℝ) - 3) / 4 ≤ b := by
    have : 3 * N ≤ 4 * b + 3 := by omega
    have : (3 : ℝ) * N ≤ 4 * b + 3 := by exact_mod_cast this
    linarith
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hN0 : (0 : ℝ) < N := by linarith
  -- split at `b`
  have hsplit : ∑ p ∈ (Ioc a N).filter Nat.Prime, Real.log p ^ 2 =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p ^ 2 +
        ∑ p ∈ (Ioc b N).filter Nat.Prime, Real.log p ^ 2 := by
    rw [sum_filter, sum_filter, sum_filter, sum_Ioc_consecutive _ hab hbN]
  rw [hsplit]
  have h1 := sum_logsq_le_mul a b
  have h2 := sum_logsq_le_mul b N
  rw [← thetaN_sub hab] at h1
  rw [← thetaN_sub hbN] at h2
  have hθab : 0 ≤ thetaN b - thetaN a := by
    rw [thetaN_sub hab]; exact sum_nonneg fun p _ => Real.log_natCast_nonneg p
  -- `log N − log b ≥ log(4/3) ≥ 0.2876`
  have hl43 : 0.2876 ≤ Real.log N - Real.log b := by
    have : Real.log b ≤ Real.log (3 * N / 4) := Real.log_le_log hb0 hbr1
    have e : Real.log (3 * (N : ℝ) / 4) = Real.log N - (2 * Real.log 2 - Real.log 3) := by
      rw [show (3 : ℝ) * N / 4 = 3 * N / 2 ^ 2 by norm_num, Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num) hN0.ne', Real.log_pow]; push_cast; ring
    have := Real.log_two_gt_d9
    have := Real.log_three_lt_d9
    linarith
  -- logarithms
  set L := Real.log a with hL
  have hL13 : (13 : ℝ) ≤ L := by
    rw [hL]; exact_mod_cast nat_le_log (N := (a : ℝ)) (k := 13)
      (le_trans (by norm_num : (2.7182818286 : ℝ) ^ 13 ≤ 500000) (by exact_mod_cast ha5))
  have hL0 : 0 < L := by linarith
  have hlN : Real.log N ≤ L + 1.1 := by
    have : Real.log N ≤ Real.log (3 * a) := Real.log_le_log hN0 (by linarith)
    rw [Real.log_mul (by norm_num) ha0.ne'] at this
    have : Real.log 3 < 1.1 := Real.log_three_lt_d9.trans (by norm_num)
    linarith
  have hlNa : L ≤ Real.log N := Real.log_le_log ha0 (by linarith)
  -- `log N / √N ≤ 0.014`
  have hsN : (1000 : ℝ) ≤ √(N : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hss : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN0.le
  have hlsq : Real.log N ≤ 0.014 * √(N : ℝ) := by
    have he2 : Real.exp 2 ≤ (1000000 : ℝ) := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]; nlinarith [Real.exp_pos 1]
    have hanti := Real.log_div_sqrt_antitoneOn (a := (1000000 : ℝ)) (b := (N : ℝ))
      (Set.mem_Ici.2 he2) (Set.mem_Ici.2 (he2.trans hNr.le)) hNr.le
    have h14 : Real.log (1000000 : ℝ) ≤ 14 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      calc (1000000 : ℝ) ≤ 2.7182818283 ^ 14 := by norm_num
        _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) this.le 14
        _ = Real.exp 14 := by rw [← Real.exp_nat_mul, mul_one]; norm_num
    have hs6 : √(1000000 : ℝ) = 1000 := by
      rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp only at hanti
    rw [hs6, div_le_div_iff₀ (by linarith) (by norm_num)] at hanti
    nlinarith
  -- θ bounds at `a`, `b`, `N`
  set Pa : ℝ := if L < 20000 then 2.2e-11 * N else 0 with hPa
  have hPa0 : 0 ≤ Pa := by rw [hPa]; split_ifs <;> positivity
  have hPa1 : Pa ≤ 2.2e-11 * N := by rw [hPa]; split_ifs <;> [exact le_rfl; positivity]
  have hPa2 : Real.log N * Pa ≤ 4.41e-7 * N := by
    rw [hPa]; split_ifs with hL2
    · have : Real.log N ≤ 20001.1 := by linarith
      have hlN0' : 0 ≤ Real.log N := by linarith
      nlinarith
    · simp; positivity
  have hcl : ∀ n : ℕ, a ≤ n → n ≤ N →
      |thetaN n - n| ≤ 1.95 * √(N : ℝ) + N / L ^ 3 + Pa := by
    intro n hn hnN
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hepl : epl n * n ≤ Pa := by
      rw [hPa]; split_ifs with hL2
      · exact mul_le_mul (epl_le n) hnN' (Nat.cast_nonneg n) (by norm_num)
      · have : 20000 ≤ Real.log n := by
          push Not at hL2; exact hL2.trans (Real.log_le_log ha0 (by exact_mod_cast hn))
        rw [epl_eq_zero this, zero_mul]
    have h := thetaN_close (le_trans ha5 hn)
    have hs : √(n : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt hnN'
    have hLn : L ≤ Real.log n := Real.log_le_log ha0 (by exact_mod_cast hn)
    have : (n : ℝ) / Real.log n ^ 3 ≤ N / L ^ 3 := by
      calc (n : ℝ) / Real.log n ^ 3 ≤ N / Real.log n ^ 3 :=
            div_le_div_of_nonneg_right hnN' (by positivity)
        _ ≤ N / L ^ 3 := div_le_div_of_nonneg_left hN0.le (by positivity)
            (pow_le_pow_left₀ hL0.le hLn 3)
    linarith
  have hθa := abs_le.1 (hcl a le_rfl (by omega))
  have hθb := abs_le.1 (hcl b hab hbN)
  have hθN := abs_le.1 (hcl N (by omega) le_rfl)
  set E := 1.95 * √(N : ℝ) + N / L ^ 3 + Pa with hE
  have hU : thetaN N - thetaN a ≤ (N + 1) / 2 + 2 * E := by linarith
  have hLo : (N : ℝ) / 4 - 1 - 2 * E ≤ thetaN b - thetaN a := by linarith
  -- assemble
  set t3 := (N : ℝ) / L ^ 3 with ht3
  have ht3b : t3 ≤ N / 2197 := div_le_div_of_nonneg_left hN0.le (by norm_num)
    (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13) hL13 3])
  have ht3L : t3 * L ≤ N / 169 := by
    have e : t3 * L = N / L ^ 2 := by rw [ht3]; field_simp
    rw [e]; exact div_le_div_of_nonneg_left hN0.le (by norm_num)
      (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13) hL13 2])
  have ht30 : 0 ≤ t3 := by positivity
  have hlN0 : 0 ≤ Real.log N := by linarith
  have hsN' : √(N : ℝ) ≤ N / 1000 := sqrt_le_div (by norm_num) (by linarith)
  have hE' : E ≤ 1.95 * (N / 1000) + N / 2197 + 2.2e-11 * N := by linarith
  have hBr : 0 ≤ (N : ℝ) / 4 - 1 - 2 * E := by linarith
  have k1 : Real.log b * (thetaN b - thetaN a) + Real.log N * (thetaN N - thetaN b) =
      Real.log N * (thetaN N - thetaN a) - (Real.log N - Real.log b) * (thetaN b - thetaN a) := by
    ring
  have k2 : Real.log N * (thetaN N - thetaN a) ≤ Real.log N * ((N + 1) / 2 + 2 * E) :=
    mul_le_mul_of_nonneg_left hU hlN0
  have k3 : 0.2876 * ((N : ℝ) / 4 - 1 - 2 * E) ≤ (Real.log N - Real.log b) * (thetaN b - thetaN a) :=
    mul_le_mul hl43 hLo hBr (by linarith)
  -- `log N · E ≤ 1.95 · 0.014 N + t3 L + 1.1 t3`
  have k4 : Real.log N * E ≤ 1.95 * (0.014 * N) + (N / 169 + 1.1 * t3) + 4.41e-7 * N := by
    have ha : Real.log N * √(N : ℝ) ≤ 0.014 * N := by
      have := mul_le_mul_of_nonneg_right hlsq (Real.sqrt_nonneg (N : ℝ))
      rw [mul_assoc, hss] at this; exact this
    have hb : Real.log N * t3 ≤ (L + 1.1) * t3 := mul_le_mul_of_nonneg_right hlN ht30
    have e1 : Real.log N * E = 1.95 * (Real.log N * √(N : ℝ)) + Real.log N * t3 + Real.log N * Pa := by
      rw [hE, ht3]; ring
    have e2 : (L + 1.1) * t3 = t3 * L + 1.1 * t3 := by ring
    linarith only [ha, hb, e1, e2, ht3L, hPa2]
  have k5 : Real.log N * ((N + 1) / 2) ≤ Real.log N * N / 2 + 0.007 * (N / 1000) := by
    have e : Real.log N * ((N + 1) / 2) = Real.log N * N / 2 + Real.log N / 2 := by ring
    linarith only [e, hlsq, hsN']
  have e3 : Real.log N * ((N + 1) / 2 + 2 * E) = Real.log N * ((N + 1) / 2) + 2 * (Real.log N * E) := by
    ring
  have e4 : 1 / 2 * (N : ℝ) * Real.log N = Real.log N * N / 2 := by ring
  linarith only [h1, h2, k1, k2, k3, k4, k5, e3, e4, hE', ht3b, hNr]

/-- **[B, (2.19)]** ([RS75, Cor. 2] for `y ≥ 2·758699`, a computation for `117 ≤ y < 2·758699`):
`∑_{y/2 < p ≤ y} (log p)² ≤ (1/2) y log y` for `y ≥ 117`. -/
theorem sum_log_sq_primes_le {y : ℝ} (hy : 117 ≤ y) :
    ∑ p ∈ (Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y := by
  set N := ⌊y⌋₊
  have hN : 117 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsub : (Ioc ⌊y / 2⌋₊ N).filter Nat.Prime ⊆ (Ioc (N / 2) N).filter Nat.Prime := by
    apply filter_subset_filter
    apply Ioc_subset_Ioc_left
    apply Nat.le_floor
    have : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
    linarith
  have hmono := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg (Real.log p))
  have hrhs : 1 / 2 * (N : ℝ) * Real.log N ≤ 1 / 2 * y * Real.log y := by
    have h1 : Real.log N ≤ Real.log y := Real.log_le_log hN0 hNy
    have h2 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    nlinarith
  refine hmono.trans (le_trans ?_ hrhs)
  rcases le_or_gt N (10 ^ 6) with h | h
  · exact logsq_small N hN h
  · exact logsq_large h

/-! ### Sums of `μ` (trusted) -/

/- [B, (2.21)] (Ramaré [Ram13]: `|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`) is not used by the
formalization and is not stated here; our weaker substitute is `MoebiusBound.abs_sum_moebius_div_le`
(`0.55/(log x − 0.7521)` for `x ≥ 10¹⁰`). -/

/- [B, (2.22)] (Ramaré [Ramb]: constant `4/5`) is proved with constant `2.8` in
`Prelim/LiouvilleBound.lean` (`abs_sum_moebius_div_coprime_le_log`), by Ramaré's Liouville route
(Acta Arith. 165 (2014)) from our own `q = 1` bound (`Prelim/MoebiusBound.lean`). -/

/- [B, (2.24)] (Helfgott's computation, `x ≤ 10¹²`) is proved for `0 < x < 10¹⁰` in
`Prelim/LiouvilleBound.lean` (`abs_sum_moebius_div_le_sqrt`) from our own sieve. -/

end TernaryGoldbach.Prelim
