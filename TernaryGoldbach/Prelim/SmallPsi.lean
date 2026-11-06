import Mathlib

/-!
# Kernel-checked bounds for small arguments

`ψ(n) = log lcm(1, …, n)` (Mathlib, `Chebyshev.psi_eq_log_lcmUpto`), so `ψ(n) < c n` is equivalent to
`lcm(1, …, n) < e^{cn}`. We check `lcm(1, …, n) < e_lo^a · T(f)` with `cn = a + f`, `0 ≤ f < 1`,
`e_lo = 2.7182818283 < e` and `T(f) = ∑_{i<12} f^i/i! ≤ e^f`. The check is a rational inequality
evaluated by the kernel (`decide +kernel`, GMP arithmetic). The lcm is carried along a structurally
recursive loop with `lcm(1, …, n+1) = lcm(lcm(1, …, n), n+1)`. No `native_decide`, so only the three
standard axioms.

The same check with `L = p`, `n = 1` gives upper bounds `log p < c` for single integers.
-/

open Finset

namespace TernaryGoldbach.Prelim.Small

/-- `T(f) = ∑_{i<12} f^i/i!`. -/
def T12 (f : ℚ) : ℚ := ∑ i ∈ range 12, f ^ i / (i.factorial : ℚ)

/-- `e_lo^a` with `e_lo = 2.7182818283`, from natural-number powers. -/
def ELpow (a : ℕ) : ℚ := ((27182818283 ^ a : ℕ) : ℚ) / ((10 ^ (10 * a) : ℕ) : ℚ)

/-- The check `L < e_lo^a · T(f)` where `(cN/cD) n = a + f`. -/
def chkStep (cN cD n L : ℕ) : Bool :=
  decide (((L : ℕ) : ℚ) < ELpow (cN * n / cD) * T12 (((cN * n % cD : ℕ) : ℚ) / cD))

/-- Checks `chkStep` at `n+1, …, n+k`, carrying `L = lcm(1, …, n)`. -/
def loop (cN cD : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | k + 1, n, L =>
    chkStep cN cD (n + 1) (Nat.lcm L (n + 1)) && loop cN cD k (n + 1) (Nat.lcm L (n + 1))

theorem lcmUpto_succ (n : ℕ) : Nat.lcmUpto (n + 1) = Nat.lcm (Nat.lcmUpto n) (n + 1) := by
  have h : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
    ext m; simp only [mem_Icc, mem_insert]; omega
  rw [Nat.lcmUpto, h, Finset.lcm_insert, Nat.lcmUpto]
  simp only [id, lcm_eq_nat_lcm, Nat.lcm_comm]

theorem lcmUpto_zero : Nat.lcmUpto 0 = 1 := by simp [Nat.lcmUpto]

theorem loop_spec (cN cD : ℕ) : ∀ k n, loop cN cD k n (Nat.lcmUpto n) = true →
    ∀ m, n < m → m ≤ n + k → chkStep cN cD m (Nat.lcmUpto m) = true := by
  intro k
  induction k with
  | zero => intro n _ m h1 h2; omega
  | succ k ih =>
    intro n h m h1 h2
    rw [loop, Bool.and_eq_true, ← lcmUpto_succ] at h
    rcases (show m = n + 1 ∨ n + 1 < m by omega) with rfl | hm
    · exact h.1
    · exact ih (n + 1) h.2 m hm (by omega)

theorem T12_le_exp {f : ℚ} (hf : 0 ≤ f) : ((T12 f : ℚ) : ℝ) ≤ Real.exp f := by
  have h := Real.sum_le_exp_of_nonneg (x := (f : ℝ)) (by exact_mod_cast hf) 12
  unfold T12; push_cast; exact h

theorem ELpow_le (a : ℕ) : ((ELpow a : ℚ) : ℝ) ≤ Real.exp a := by
  have he := Real.exp_one_gt_d9
  have e : ((ELpow a : ℚ) : ℝ) = (2.7182818283 : ℝ) ^ a := by
    unfold ELpow; push_cast
    rw [pow_mul, ← div_pow]; norm_num
  rw [e, ← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) he.le a

/-- A successful check gives `log L < (cN/cD) n`. -/
theorem log_lt_of_chk {cN cD n L : ℕ} (hD : 0 < cD) (hL : 0 < L)
    (h : chkStep cN cD n L = true) : Real.log L < (cN : ℝ) / cD * n := by
  unfold chkStep at h
  have h' := of_decide_eq_true h
  set a := cN * n / cD
  set r := cN * n % cD
  have hr0 : (0 : ℚ) ≤ ((r : ℕ) : ℚ) / cD := by positivity
  have hq : ((L : ℕ) : ℝ) < ((ELpow a : ℚ) : ℝ) * ((T12 (((r : ℕ) : ℚ) / cD) : ℚ) : ℝ) := by
    exact_mod_cast h'
  have hE : ((ELpow a : ℚ) : ℝ) * ((T12 (((r : ℕ) : ℚ) / cD) : ℚ) : ℝ) ≤
      Real.exp a * Real.exp (((((r : ℕ) : ℚ) / cD : ℚ) : ℝ)) :=
    mul_le_mul (ELpow_le a) (T12_le_exp hr0) (by
      have := T12_le_exp hr0; have := Real.exp_pos (((((r : ℕ) : ℚ) / cD : ℚ) : ℝ))
      unfold T12; positivity) (Real.exp_pos _).le
  have hsum : (a : ℝ) + ((((r : ℕ) : ℚ) / cD : ℚ) : ℝ) = (cN : ℝ) / cD * n := by
    have hdm := Nat.div_add_mod (cN * n) cD
    have hD' : (cD : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have : (cD : ℝ) * a + r = cN * n := by exact_mod_cast hdm
    push_cast
    field_simp
    linarith
  rw [Real.log_lt_iff_lt_exp (by exact_mod_cast hL), ← hsum, Real.exp_add]
  exact hq.trans_le hE

theorem loop_586 : loop 103883 100000 586 0 1 = true := by decide +kernel

/-- `ψ(n) < 1.03883 n` for `1 ≤ n ≤ 586` (kernel-checked; [RS62, Thm 12] in this range). -/
theorem psi_lt_small {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 586) :
    ∑ m ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt m : ℝ) < 1.03883 * n := by
  have hchk := loop_spec 103883 100000 586 0 (by rw [lcmUpto_zero]; exact loop_586) n
    (by omega) (by omega)
  have hlog := log_lt_of_chk (by norm_num) (Nat.lcmUpto_pos n) hchk
  have hψ := Chebyshev.psi_eq_log_lcmUpto n
  have e : Chebyshev.psi n = ∑ m ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt m : ℝ) := by
    rw [Chebyshev.psi, Nat.floor_natCast]; rfl
  rw [← e, hψ]
  norm_num at hlog ⊢
  linarith

end TernaryGoldbach.Prelim.Small
