import TernaryGoldbach.Prelim.SmallPsi

/-!
# `∑_{m ≤ n} Λ(m)/m ≤ log n` for `n ≤ 100`, checked by the kernel

`∑_{m ≤ n} Λ(m)/m = ∑_{p ≤ n} log p ∑_{k ≤ log_p n} p^{−k}`. We use upper bounds `log p < U(p)`
(checked as `p < e_lo^{U(p)}`) and lower bounds `V(n) ≤ log n` (checked as `e_hi^{V(n)} ≤ n`, with
`e_hi = 2.7182818286 > e` and an upper Taylor bound for `e^f`). The resulting rational inequality
`∑_p U(p) ∑_k p^{−k} ≤ V(n)` is checked for every `n ≤ 100` by `decide +kernel`.
-/

open Finset

namespace TernaryGoldbach.Prelim.Small

/-- `e_hi^a` with `e_hi = 2.7182818286 > e`. -/
def EHpow (a : ℕ) : ℚ := ((27182818286 ^ a : ℕ) : ℚ) / ((10 ^ (10 * a) : ℕ) : ℚ)

/-- An upper bound for `e^f`, `0 ≤ f ≤ 1`: `∑_{i<12} f^i/i! + f^12 · 13/(12! · 12)`. -/
def T12up (f : ℚ) : ℚ := T12 f + f ^ 12 * (13 / ((Nat.factorial 12 : ℚ) * 12))

/-- The check `e_hi^a · T12up(f) ≤ L` where `cN/cD = a + f`. -/
def chkLow (cN cD L : ℕ) : Bool :=
  decide (EHpow (cN / cD) * T12up (((cN % cD : ℕ) : ℚ) / cD) ≤ ((L : ℕ) : ℚ))

theorem EHpow_ge (a : ℕ) : Real.exp a ≤ ((EHpow a : ℚ) : ℝ) := by
  have he := Real.exp_one_lt_d9
  have e : ((EHpow a : ℚ) : ℝ) = (2.7182818286 : ℝ) ^ a := by
    unfold EHpow; push_cast
    rw [pow_mul, ← div_pow]; norm_num
  rw [e, ← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le he.le a

theorem exp_le_T12up {f : ℚ} (h0 : 0 ≤ f) (h1 : f ≤ 1) : Real.exp f ≤ ((T12up f : ℚ) : ℝ) := by
  have hf0 : (0 : ℝ) ≤ f := by exact_mod_cast h0
  have hf1 : |(f : ℝ)| ≤ 1 := by rw [abs_of_nonneg hf0]; exact_mod_cast h1
  have h := Real.exp_bound hf1 (n := 12) (by norm_num)
  rw [abs_of_nonneg hf0] at h
  have h' := (abs_le.1 h).2
  unfold T12up T12; push_cast
  norm_num [Nat.factorial] at h' ⊢
  linarith

/-- A successful check gives `cN/cD ≤ log L`. -/
theorem le_log_of_chk {cN cD L : ℕ} (hD : 0 < cD) (hL : 0 < L)
    (h : chkLow cN cD L = true) : (cN : ℝ) / cD ≤ Real.log L := by
  unfold chkLow at h
  have h' := of_decide_eq_true h
  set a := cN / cD
  set r := cN % cD
  have hr0 : (0 : ℚ) ≤ ((r : ℕ) : ℚ) / cD := by positivity
  have hr1 : ((r : ℕ) : ℚ) / cD ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hD)]; exact_mod_cast (Nat.mod_lt _ hD).le
  have hq : ((EHpow a : ℚ) : ℝ) * ((T12up (((r : ℕ) : ℚ) / cD) : ℚ) : ℝ) ≤ ((L : ℕ) : ℝ) := by
    exact_mod_cast h'
  have hE : Real.exp a * Real.exp (((((r : ℕ) : ℚ) / cD : ℚ) : ℝ)) ≤
      ((EHpow a : ℚ) : ℝ) * ((T12up (((r : ℕ) : ℚ) / cD) : ℚ) : ℝ) :=
    mul_le_mul (EHpow_ge a) (exp_le_T12up hr0 hr1) (Real.exp_pos _).le
      ((Real.exp_pos _).le.trans (EHpow_ge a))
  have hsum : (a : ℝ) + ((((r : ℕ) : ℚ) / cD : ℚ) : ℝ) = (cN : ℝ) / cD := by
    have hdm := Nat.div_add_mod cN cD
    have hD' : (cD : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have : (cD : ℝ) * a + r = cN := by exact_mod_cast hdm
    push_cast
    field_simp
    linarith
  rw [Real.le_log_iff_exp_le (by exact_mod_cast hL), ← hsum, Real.exp_add]
  exact hE.trans hq

/-- `∑_{m ≤ n} Λ(m) f(m) = ∑_{p ≤ n} ∑_{k ≤ log_p n} log p · f(p^k)` (as in Mathlib's
`Chebyshev.psi_eq_sum_mul_log_prime`, with a weight). -/
theorem sum_vonMangoldt_mul_eq (n : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt m : ℝ) * f m =
      ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (p.log n), Real.log p * f (p ^ k) := calc
  _ = ∑ m ∈ ((Icc 1 n).filter Nat.Prime).biUnion fun p ↦ image (p ^ ·) (Icc 1 (p.log n)),
        (ArithmeticFunction.vonMangoldt m : ℝ) * f m := by
    refine (sum_subset (fun q hq ↦ ?_) fun x hx ↦ ?_).symm
    · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image] at hq ⊢
      obtain ⟨p, _, k, ⟨_, hk⟩, rfl⟩ := hq
      exact ⟨by grind, Nat.pow_le_of_le_log (by linarith) hk⟩
    · intro hnot
      refine mul_eq_zero_of_left ?_ _
      simp only [mem_biUnion, mem_filter, mem_Icc, mem_image, not_exists, not_and, and_imp] at hnot
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
      rintro ⟨p, k, hp, hk, rfl⟩
      simp only [mem_Icc] at hx
      have hpn : p ≤ n := (Nat.le_of_dvd (by lia) (dvd_pow_self p hk.ne')).trans hx.2
      exact hnot p hp.one_le hpn hp k (by lia) (Nat.le_log_of_pow_le hp.one_lt hx.2) rfl
  _ = ∑ p ∈ Icc 1 n with p.Prime, ∑ q ∈ image (fun k ↦ p ^ k) (Icc 1 (p.log n)),
        (ArithmeticFunction.vonMangoldt q : ℝ) * f q := by
      rw [sum_biUnion <| by rw [pairwiseDisjoint_iff]; grind [Nat.Prime.pow_inj']]
  _ = ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (p.log n),
        (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) * f (p ^ k) := by
      refine sum_congr (Nat.primesLE_eq_filter_Icc_one n).symm fun p hp ↦ ?_
      exact sum_image fun a _ b _ hab ↦
        Nat.pow_right_injective (Nat.two_le_of_mem_primesLE hp) hab
  _ = _ := by
      refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ?_
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by simp at hk; lia),
        ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]

/-- Upper bounds `log p < U(p)/1000` for the primes `p ≤ 100`. -/
def Utab : List (ℕ × ℕ) := [(2, 695), (3, 1100), (5, 1611), (7, 1947), (11, 2399), (13, 2566), (17, 2835), (19, 2946), (23, 3137), (29, 3369), (31, 3435), (37, 3612), (41, 3715), (43, 3763), (47, 3852), (53, 3972), (59, 4079), (61, 4112), (67, 4206), (71, 4264), (73, 4292), (79, 4371), (83, 4420), (89, 4490), (97, 4576)]

def U (p : ℕ) : ℕ := (Utab.lookup p).getD 0

/-- Lower bounds `V(n)/1000 ≤ log n` for `n ≤ 100`. -/
def Vtab : List ℕ := [0, 0, 692, 1097, 1385, 1608, 1790, 1944, 2078, 2196, 2301, 2396, 2483, 2563, 2638, 2707, 2771, 2832, 2889, 2943, 2994, 3043, 3090, 3134, 3177, 3217, 3257, 3294, 3331, 3366, 3400, 3432, 3464, 3495, 3525, 3554, 3582, 3609, 3636, 3662, 3687, 3712, 3736, 3760, 3783, 3805, 3827, 3849, 3870, 3890, 3911, 3930, 3950, 3969, 3987, 4006, 4024, 4042, 4059, 4076, 4093, 4109, 4126, 4142, 4157, 4173, 4188, 4203, 4218, 4233, 4247, 4261, 4275, 4289, 4303, 4316, 4329, 4342, 4355, 4368, 4381, 4393, 4405, 4417, 4429, 4441, 4453, 4464, 4476, 4487, 4498, 4509, 4520, 4531, 4542, 4552, 4563, 4573, 4583, 4594, 4604]

def V (n : ℕ) : ℕ := Vtab.getD n 0

theorem U_ok : ∀ p ∈ Nat.primesBelow 101, chkStep (U p) 1000 1 p = true := by decide +kernel

theorem V_ok : ∀ n ∈ Icc 1 100, chkLow (V n) 1000 n = true := by decide +kernel

/-- The rational majorant `∑_{p ≤ n} U(p) ∑_{k ≤ log_p n} p^{−k}`. -/
def Rm (n : ℕ) : ℚ :=
  ∑ p ∈ Nat.primesBelow (n + 1), ((U p : ℚ) / 1000) * ∑ k ∈ Icc 1 (Nat.log p n), 1 / (p : ℚ) ^ k

theorem R_ok : ∀ n ∈ Icc 1 100, Rm n ≤ (V n : ℚ) / 1000 := by decide +kernel

/-- **`∑_{m ≤ n} Λ(m)/m ≤ log n` for `1 ≤ n ≤ 100`** (kernel-checked). -/
theorem mertens_small' {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 100) :
    ∑ m ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt m : ℝ) / m ≤ Real.log n := by
  have hmem : n ∈ Icc 1 100 := mem_Icc.2 ⟨h1, h2⟩
  have hdec := sum_vonMangoldt_mul_eq n (fun m => 1 / (m : ℝ))
  simp only [mul_one_div] at hdec
  rw [hdec]
  have hU : ∀ p ∈ Nat.primesLE n, Real.log p ≤ (U p : ℝ) / 1000 := by
    intro p hp
    have hpb : p ∈ Nat.primesBelow 101 := by
      rw [Nat.primesLE] at hp
      exact Nat.mem_primesBelow.2 ⟨by have := (Nat.mem_primesBelow.1 hp).1; omega,
        (Nat.mem_primesBelow.1 hp).2⟩
    have h := log_lt_of_chk (by norm_num) (Nat.prime_of_mem_primesLE hp).pos (U_ok p hpb)
    push_cast at h; linarith
  have hstep : ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (p.log n), Real.log p / ((p ^ k : ℕ) : ℝ) ≤
      ((Rm n : ℚ) : ℝ) := by
    unfold Rm
    push_cast
    rw [show Nat.primesBelow (n + 1) = Nat.primesLE n from rfl]
    refine sum_le_sum fun p hp => ?_
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos) k
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hU p hp) (by positivity)
  have hR : ((Rm n : ℚ) : ℝ) ≤ (V n : ℝ) / 1000 := by
    have h := R_ok n hmem
    have h' : ((Rm n : ℚ) : ℝ) ≤ ((((V n : ℚ) / 1000 : ℚ)) : ℝ) := Rat.cast_le.2 h
    push_cast at h'; exact h'
  have hV := le_log_of_chk (by norm_num) (by omega) (V_ok n hmem)
  push_cast at hV
  linarith

end TernaryGoldbach.Prelim.Small
