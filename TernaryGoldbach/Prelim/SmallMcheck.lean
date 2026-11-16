import TernaryGoldbach.Prelim.Mcheck

/-!
# `|m̌(x)| ≤ 1.00303` for `1 ≤ x ≤ 2·10⁵`, checked by the kernel: definitions and specifications

The kernel walks `k = 1, …, 2·10⁵` at scale `B = 10²⁰`, keeping `M(k)` exactly and integer bounds
for `B m(k)`, `B m̌(k)` and `B ∑_{t < k} |M(t)|/t`; `μ(k)` is computed by trial division (`muTD`,
proved correct). Since `m̌(k+1) = m̌(k) + m(k) log(1 + 1/k)`, it needs bounds for `log(1 + 1/k)`:
the Taylor series of `log(1 + u)` at `u = 1/k` with Mathlib's error bound (`logB`), and Mathlib's
bounds for `log 2` at `k = 1`. On `[k, k+1]`, `m̌(x) = m̌(k) + m(k) log(x/k)` is monotone, so
checking `|m̌(k)| ≤ 1.00303` at the integers covers every real `x`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.SmallMcheck

open TernaryGoldbach.Prelim (mcheck msumR mertR)

/-! ### `μ` by trial division -/

/-- `μ(m)` by trial division from `d` (`d = 2` or odd), or `none` when out of fuel. -/
def muTD : ℕ → ℕ → ℕ → Option ℤ
  | 0, _, _ => none
  | f + 1, m, d =>
    if m < 2 then some 1
    else if m < d * d then some (-1)
    else if m % d = 0 then
      if (m / d) % d = 0 then some 0 else (muTD f (m / d) d).map (fun v => -v)
    else muTD f m (if d = 2 then 3 else d + 2)

theorem muTD_spec : ∀ (f m d : ℕ) (v : ℤ), 1 ≤ m → 2 ≤ d → (d = 2 ∨ d % 2 = 1) →
    (∀ p, p.Prime → p ∣ m → d ≤ p) → muTD f m d = some v → μ m = v := by
  intro f
  induction f with
  | zero => intro m d v _ _ _ _ h; simp [muTD] at h
  | succ f ih =>
    intro m d v hm1 hd hodd hinv h
    rw [muTD] at h
    split_ifs at h with h1 h2 h3 h4 h5
    · cases h
      have : m = 1 := by omega
      subst this; simp
    · cases h
      have hm2 : 2 ≤ m := by omega
      have hp : m.Prime := by
        by_contra hnp
        have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
        have hle := hinv _ hmf (Nat.minFac_dvd m)
        have hsq := Nat.minFac_sq_le_self (by omega) hnp
        have : d * d ≤ m.minFac ^ 2 := by rw [sq]; exact Nat.mul_le_mul hle hle
        omega
      exact moebius_apply_prime hp
    · -- `d² ∣ m`
      cases h
      have hdm : d ∣ m := Nat.dvd_of_mod_eq_zero h3
      have hdd : d ∣ m / d := Nat.dvd_of_mod_eq_zero h4
      apply moebius_eq_zero_of_not_squarefree
      intro hsq
      have hdd' : d * d ∣ m := by
        obtain ⟨c, hc⟩ := hdd
        exact ⟨c, by rw [← Nat.mul_div_cancel' hdm, hc]; ring⟩
      have := hsq d hdd'
      rw [Nat.isUnit_iff] at this
      omega
    · obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.1 h
      have hdm : d ∣ m := Nat.dvd_of_mod_eq_zero h3
      have hdp : d.Prime := by
        rw [Nat.prime_def_minFac]
        refine ⟨hd, ?_⟩
        have hmf := Nat.minFac_prime (show d ≠ 1 by omega)
        have h1' := hinv _ hmf ((Nat.minFac_dvd d).trans hdm)
        have h2' := Nat.minFac_le (show 0 < d by omega)
        omega
      have hq1 : 1 ≤ m / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdm) (by omega)
      have ih' := ih (m / d) d v' hq1 hd hodd
        (fun p hp hpd => hinv p hp (hpd.trans (Nat.div_dvd_of_dvd hdm))) hv'
      have hcop : Nat.Coprime d (m / d) :=
        (Nat.Prime.coprime_iff_not_dvd hdp).2 (fun hd' => h4 (Nat.mod_eq_zero_of_dvd hd'))
      rw [← Nat.mul_div_cancel' hdm, isMultiplicative_moebius.map_mul_of_coprime hcop,
        moebius_apply_prime hdp, ih']
      ring
    · refine ih m 3 v hm1 (by norm_num) (by norm_num) ?_ h
      intro p hp hpm
      have hdp := hinv p hp hpm
      have hne : p ≠ d := fun e => h3 (Nat.mod_eq_zero_of_dvd (e ▸ hpm))
      omega
    · have h6 : d % 2 = 1 := by
        rcases hodd with h6 | h6
        · exact absurd h6 h5
        · exact h6
      refine ih m (d + 2) v hm1 (by omega) (Or.inr (by omega)) ?_ h
      intro p hp hpm
      have hdp := hinv p hp hpm
      have hne : p ≠ d := fun e => h3 (Nat.mod_eq_zero_of_dvd (e ▸ hpm))
      by_contra hlt
      have hp1 : p = d + 1 := by omega
      have hev : 2 ∣ p := by omega
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hev
      omega

/-- `μ(n)` by trial division. -/
def muB (n : ℕ) : Option ℤ := muTD (n + 1) n 2

theorem muB_spec {n : ℕ} (hn : 1 ≤ n) {v : ℤ} (h : muB n = some v) : μ n = v :=
  muTD_spec _ n 2 v hn le_rfl (Or.inl rfl) (fun _ hp _ => hp.two_le) h

example : muB 30 = some (-1) ∧ muB 12 = some 0 ∧ muB 199999 = some (-1) ∧ muB 1 = some 1 := by
  decide +kernel

/-! ### `log(1 + 1/k)` at scale `B = 10²⁰` -/

/-- The scale `B = 10²⁰`. -/
def B : ℕ := 10 ^ 20

/-- `∑_{i < n} (−1)^i ⌊B/((i+1) k^{i+1})⌋`. -/
def pSum (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => pSum k i + (-1) ^ i * ((B / ((i + 1) * k ^ (i + 1)) : ℕ) : ℤ)

/-- The number of terms of the series. -/
def nT (k : ℕ) : ℕ := if k < 64 then 32 else if k < 4096 then 6 else 3

/-- An upper bound for `B/(kⁿ (k−1))`, the series' tail. -/
def errB (k n : ℕ) : ℕ := B / (k ^ n * (k - 1)) + 1

/-- Lower bound for `B log(1 + 1/k)`. -/
def logLo (k : ℕ) : ℤ :=
  if k = 1 then 69314718030000000000 else pSum k (nT k) - nT k - errB k (nT k)

/-- Upper bound for `B log(1 + 1/k)`. -/
def logHi (k : ℕ) : ℤ :=
  if k = 1 then 69314718080000000000 else pSum k (nT k) + nT k + errB k (nT k)

theorem pSum_eq (k n : ℕ) :
    pSum k n = ∑ i ∈ range n, (-1) ^ i * ((B / ((i + 1) * k ^ (i + 1)) : ℕ) : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pSum, ih, sum_range_succ]

/-- `|B ∑_{i<n} (−1)^i/((i+1)k^{i+1}) − pSum k n| ≤ n`. -/
theorem abs_pSum_sub_le {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    |(B : ℝ) * ∑ i ∈ range n, (-1 : ℝ) ^ i / ((i + 1) * (k : ℝ) ^ (i + 1)) - (pSum k n : ℝ)| ≤ n := by
  rw [pSum_eq, mul_sum]
  push_cast
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ range n, |(B : ℝ) * ((-1 : ℝ) ^ i / ((i + 1) * (k : ℝ) ^ (i + 1))) -
      (-1) ^ i * (((B / ((i + 1) * k ^ (i + 1)) : ℕ) : ℝ))| ≤ 1 := by
    intro i _
    have hd : (0 : ℝ) < ((i + 1) * k ^ (i + 1) : ℕ) := by
      have : 0 < (i + 1) * k ^ (i + 1) := Nat.mul_pos (Nat.succ_pos i) (pow_pos hk _)
      exact_mod_cast this
    have hfl := Nat.floor_div_eq_div (K := ℝ) B ((i + 1) * k ^ (i + 1))
    have h1 : (((B / ((i + 1) * k ^ (i + 1)) : ℕ) : ℝ)) ≤ (B : ℝ) / ((i + 1) * k ^ (i + 1) : ℕ) :=
      Nat.cast_div_le
    have h2 : (B : ℝ) / ((i + 1) * k ^ (i + 1) : ℕ) < ((B / ((i + 1) * k ^ (i + 1)) : ℕ) : ℝ) + 1 := by
      rw [← hfl]; exact Nat.lt_floor_add_one _
    have e : (B : ℝ) * ((-1 : ℝ) ^ i / ((i + 1) * (k : ℝ) ^ (i + 1))) =
        (-1) ^ i * ((B : ℝ) / ((i + 1) * k ^ (i + 1) : ℕ)) := by
      push_cast; ring
    rw [e, ← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_le]
    constructor <;> linarith
  refine (sum_le_sum hterm).trans ?_
  simp

theorem log_bounds {k : ℕ} (hk : 1 ≤ k) :
    (logLo k : ℝ) ≤ B * Real.log (1 + 1 / (k : ℝ)) ∧ B * Real.log (1 + 1 / (k : ℝ)) ≤ logHi k := by
  have hB : (B : ℝ) = 10 ^ 20 := by norm_num [B]
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · have h1 := Real.log_two_gt_d9
    have h2 := Real.log_two_lt_d9
    simp only [logLo, logHi, ite_true, Nat.cast_one, div_one]
    rw [show (1 : ℝ) + 1 = 2 by norm_num, hB]
    push_cast
    constructor <;> nlinarith
  · have hk1 : k ≠ 1 := by omega
    simp only [logLo, logHi, hk1, ite_false]
    set n := nT k
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkx : |(-1 / (k : ℝ))| < 1 := by
      rw [abs_div, abs_neg, abs_one, abs_of_pos hk0, div_lt_one hk0]
      exact_mod_cast (by omega : 1 < k)
    have hser := Real.abs_log_sub_add_sum_range_le hkx n
    have hsum : ∑ i ∈ range n, (-1 / (k : ℝ)) ^ (i + 1) / (i + 1) =
        -∑ i ∈ range n, (-1 : ℝ) ^ i / ((i + 1) * (k : ℝ) ^ (i + 1)) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [div_pow, pow_succ]
      field_simp
    rw [hsum, show (1 : ℝ) - -1 / k = 1 + 1 / k by ring, abs_div, abs_neg, abs_one,
      abs_of_pos hk0] at hser
    -- the tail
    have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hkne : (k : ℝ) ≠ 0 := hk0.ne'
    have hk1ne : (k : ℝ) - 1 ≠ 0 := by linarith
    have htail : (1 / (k : ℝ)) ^ (n + 1) / (1 - 1 / k) = 1 / ((k : ℝ) ^ n * ((k : ℝ) - 1)) := by
      rw [one_div_pow, one_sub_div hkne, div_div_eq_mul_div, pow_succ]
      field_simp
    rw [htail] at hser
    have hden : (0 : ℝ) < ((k ^ n * (k - 1) : ℕ) : ℝ) := by
      have : 0 < k ^ n * (k - 1) := Nat.mul_pos (pow_pos (by omega) _) (by omega)
      exact_mod_cast this
    have hcast : (((k ^ n * (k - 1) : ℕ) : ℝ)) = (k : ℝ) ^ n * ((k : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega)]; push_cast; ring
    have herr : (B : ℝ) * (1 / ((k : ℝ) ^ n * ((k : ℝ) - 1))) ≤ (errB k n : ℝ) := by
      have hfl := Nat.floor_div_eq_div (K := ℝ) B (k ^ n * (k - 1))
      have h2 : (B : ℝ) / ((k ^ n * (k - 1) : ℕ) : ℝ) < ((B / (k ^ n * (k - 1)) : ℕ) : ℝ) + 1 := by
        rw [← hfl]; exact Nat.lt_floor_add_one _
      rw [hcast] at h2
      simp only [errB]; push_cast
      rw [mul_one_div]; linarith
    have hP := abs_pSum_sub_le (by omega : 1 ≤ k) n
    set P := ∑ i ∈ range n, (-1 : ℝ) ^ i / ((i + 1) * (k : ℝ) ^ (i + 1))
    have hB0 : (0 : ℝ) ≤ B := by positivity
    have hlog : |(B : ℝ) * Real.log (1 + 1 / k) - B * P| ≤ B * (1 / ((k : ℝ) ^ n * ((k : ℝ) - 1))) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hB0]
      refine mul_le_mul_of_nonneg_left ?_ hB0
      rwa [neg_add_eq_sub] at hser
    rw [abs_le] at hlog hP
    push_cast
    constructor <;> linarith [hlog.1, hlog.2, hP.1, hP.2, herr]

/-! ### From `k` to `k + 1` -/

theorem msumR_succ (k : ℕ) : msumR ((k + 1 : ℕ) : ℝ) = msumR (k : ℝ) + (μ (k + 1) : ℝ) / (k + 1 : ℕ) := by
  rw [msumR, msumR, Nat.floor_natCast, Nat.floor_natCast, sum_Icc_succ_top (by omega)]

theorem mertR_succ (k : ℕ) : mertR ((k + 1 : ℕ) : ℝ) = mertR (k : ℝ) + (μ (k + 1) : ℝ) := by
  rw [mertR, mertR, Nat.floor_natCast, Nat.floor_natCast, sum_Icc_succ_top (by omega)]

/-- On `[k, k+1)`: `m̌(x) = m̌(k) + m(k) log(x/k)`. -/
theorem mcheck_eq_of_mem {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (h1 : (k : ℝ) ≤ x) (h2 : x < k + 1) :
    mcheck x = mcheck k + msumR k * Real.log (x / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hfl : ⌊x⌋₊ = k := (Nat.floor_eq_iff (by linarith)).2 ⟨h1, h2⟩
  rw [mcheck, mcheck, msumR, hfl, Nat.floor_natCast, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
  rw [← mul_add, ← Real.log_mul (by positivity) (div_pos (by linarith) hk0).ne']
  congr 2
  field_simp

theorem mcheck_succ {k : ℕ} (hk : 1 ≤ k) :
    mcheck ((k + 1 : ℕ) : ℝ) = mcheck k + msumR k * Real.log (1 + 1 / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [mcheck, mcheck, msumR, Nat.floor_natCast, Nat.floor_natCast, sum_Icc_succ_top (by omega),
    sum_mul, div_self (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0), Real.log_one, mul_zero, add_zero,
    ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
  rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
  congr 2
  push_cast
  field_simp

/-- If `|m̌(k)|, |m̌(k+1)| ≤ C` then `|m̌(x)| ≤ C` on `[k, k+1]`. -/
theorem abs_mcheck_le_of_ends {k : ℕ} (hk : 1 ≤ k) {C : ℝ} (h0 : |mcheck k| ≤ C)
    (h1 : |mcheck ((k + 1 : ℕ) : ℝ)| ≤ C) {x : ℝ} (hx1 : (k : ℝ) ≤ x) (hx2 : x ≤ k + 1) :
    |mcheck x| ≤ C := by
  rcases hx2.lt_or_eq with hx2 | hx2
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [mcheck_eq_of_mem hk hx1 hx2]
    rw [mcheck_succ hk] at h1
    have hl0 : 0 ≤ Real.log (x / k) := Real.log_nonneg (by rw [le_div_iff₀ hk0]; linarith)
    have hl1 : Real.log (x / k) ≤ Real.log (1 + 1 / (k : ℝ)) :=
      Real.log_le_log (div_pos (by linarith) hk0) (by rw [div_le_iff₀ hk0]; field_simp; linarith)
    rw [abs_le] at h0 h1 ⊢
    rcases le_total 0 (msumR k) with hm | hm
    · constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl1 hm, mul_nonneg hm hl0]
    · constructor <;> nlinarith [mul_le_mul_of_nonpos_left hl1 hm, mul_nonpos_of_nonpos_of_nonneg hm hl0]
  · rw [hx2]; exact_mod_cast h1

/-! ### Rounding and interval products -/

theorem cast_ediv_le (a : ℤ) {b : ℤ} (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have h := Int.ediv_mul_le a hb.ne'
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']; exact_mod_cast h

theorem le_cast_neg_ediv_neg (a : ℤ) {b : ℤ} (hb : 0 < b) : (a : ℝ) / b ≤ ((-((-a) / b) : ℤ) : ℝ) := by
  have h := cast_ediv_le (-a) hb
  push_cast at h ⊢
  have : (-(a : ℝ)) / b = -((a : ℝ) / b) := by ring
  linarith

theorem le_nat_ceil_div (x k : ℕ) (hk : 1 ≤ k) : (x : ℝ) / k ≤ (((x + k - 1) / k : ℕ) : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hk0]
  have h1 := Nat.div_add_mod (x + k - 1) k
  have h2 := Nat.mod_lt (x + k - 1) (by omega : 0 < k)
  have : x ≤ (x + k - 1) / k * k := by
    have := Nat.mul_comm k ((x + k - 1) / k)
    omega
  exact_mod_cast this

theorem mul_mem_box {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  constructor
  · rcases le_total 0 y with hy | hy
    · have h1 : a * y ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy
      have h2 : min (a * c) (a * d) ≤ a * y := by
        rcases le_total 0 a with ha | ha
        · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy1 ha)
        · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy2 ha)
      exact (min_le_left _ _).trans (h2.trans h1)
    · have h1 : b * y ≤ x * y := mul_le_mul_of_nonpos_right hx2 hy
      have h2 : min (b * c) (b * d) ≤ b * y := by
        rcases le_total 0 b with hb | hb
        · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy1 hb)
        · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy2 hb)
      exact (min_le_right _ _).trans (h2.trans h1)
  · rcases le_total 0 y with hy | hy
    · have h1 : x * y ≤ b * y := mul_le_mul_of_nonneg_right hx2 hy
      have h2 : b * y ≤ max (b * c) (b * d) := by
        rcases le_total 0 b with hb | hb
        · exact (mul_le_mul_of_nonneg_left hy2 hb).trans (le_max_right _ _)
        · exact (mul_le_mul_of_nonpos_left hy1 hb).trans (le_max_left _ _)
      exact (h1.trans h2).trans (le_max_right _ _)
    · have h1 : x * y ≤ a * y := mul_le_mul_of_nonpos_right hx1 hy
      have h2 : a * y ≤ max (a * c) (a * d) := by
        rcases le_total 0 a with ha | ha
        · exact (mul_le_mul_of_nonneg_left hy2 ha).trans (le_max_right _ _)
        · exact (mul_le_mul_of_nonpos_left hy1 ha).trans (le_max_left _ _)
      exact (h1.trans h2).trans (le_max_left _ _)

/-! ### The walk -/

/-- The state at `k`: `M(k)`, bounds `mlo ≤ B m(k) ≤ mhi`, `clo ≤ B m̌(k) ≤ chi`, and
`B ∑_{t < k} |M(t)|/t ≤ shi`. -/
structure St where
  k : ℕ
  M : ℤ
  mlo : ℤ
  mhi : ℤ
  clo : ℤ
  chi : ℤ
  shi : ℕ
  deriving DecidableEq

/-- `1.00303 B`. -/
def Cb : ℤ := 100303000000000000000

/-- From `k` to `k + 1`, checking `|m̌(k+1)| ≤ 1.00303`. -/
def step (s : St) : Option St :=
  let p1 := s.mlo * logLo s.k
  let p2 := s.mlo * logHi s.k
  let p3 := s.mhi * logLo s.k
  let p4 := s.mhi * logHi s.k
  let clo' := s.clo + min (min p1 p2) (min p3 p4) / (B : ℤ)
  let chi' := s.chi + -((-(max (max p1 p2) (max p3 p4))) / (B : ℤ))
  let shi' := s.shi + (s.M.natAbs * B + s.k - 1) / s.k
  match muB (s.k + 1) with
  | none => none
  | some v =>
    if -Cb ≤ clo' ∧ chi' ≤ Cb then
      some ⟨s.k + 1, s.M + v, s.mlo + v * B / ((s.k + 1 : ℕ) : ℤ),
        s.mhi + -((-(v * B)) / ((s.k + 1 : ℕ) : ℤ)), clo', chi', shi'⟩
    else none

/-- `n` steps. -/
def walk : ℕ → St → Option St
  | 0, s => some s
  | n + 1, s =>
    match step s with
    | none => none
    | some s' => walk n s'

/-- The invariant. -/
def Good (s : St) : Prop :=
  1 ≤ s.k ∧ (s.M : ℝ) = mertR s.k ∧
  (s.mlo : ℝ) ≤ B * msumR s.k ∧ (B : ℝ) * msumR s.k ≤ s.mhi ∧
  (s.clo : ℝ) ≤ B * mcheck s.k ∧ (B : ℝ) * mcheck s.k ≤ s.chi ∧
  (B : ℝ) * ∑ t ∈ Ico (1 : ℕ) s.k, |mertR t| / (t : ℝ) ≤ s.shi

theorem step_spec {s s' : St} (hs : Good s) (h : step s = some s') :
    Good s' ∧ s'.k = s.k + 1 ∧ |mcheck (s'.k : ℝ)| ≤ 1.00303 := by
  obtain ⟨hk, hM, hmlo, hmhi, hclo, hchi, hshi⟩ := hs
  unfold step at h
  split at h
  · exact absurd h (by simp)
  rename_i v hv
  dsimp only at h
  split_ifs at h with hc
  cases h
  have hμ := muB_spec (by omega : 1 ≤ s.k + 1) hv
  have hB0 : (0 : ℝ) < B := by norm_num [B]
  have hBz : (0 : ℤ) < (B : ℤ) := by norm_num [B]
  have hk1z : (0 : ℤ) < ((s.k + 1 : ℕ) : ℤ) := by positivity
  have hk0 : (0 : ℝ) < s.k := by exact_mod_cast hk
  -- `m̌`: the interval product
  obtain ⟨hL1, hL2⟩ := log_bounds hk
  obtain ⟨hp1, hp2⟩ := mul_mem_box hmlo hmhi hL1 hL2
  have hprod : (B : ℝ) * msumR s.k * (B * Real.log (1 + 1 / (s.k : ℝ))) / B =
      B * (msumR s.k * Real.log (1 + 1 / (s.k : ℝ))) := by field_simp
  have hmc := mcheck_succ hk
  have hlo := cast_ediv_le (min (min (s.mlo * logLo s.k) (s.mlo * logHi s.k))
    (min (s.mhi * logLo s.k) (s.mhi * logHi s.k))) hBz
  have hhi := le_cast_neg_ediv_neg (max (max (s.mlo * logLo s.k) (s.mlo * logHi s.k))
    (max (s.mhi * logLo s.k) (s.mhi * logHi s.k))) hBz
  push_cast at hlo hhi hp1 hp2
  have hdivlo : (min (min ((s.mlo : ℝ) * logLo s.k) (s.mlo * logHi s.k))
      (min ((s.mhi : ℝ) * logLo s.k) (s.mhi * logHi s.k))) / B ≤
      B * (msumR s.k * Real.log (1 + 1 / (s.k : ℝ))) := by
    rw [← hprod]; exact div_le_div_of_nonneg_right hp1 hB0.le
  have hdivhi : B * (msumR s.k * Real.log (1 + 1 / (s.k : ℝ))) ≤
      (max (max ((s.mlo : ℝ) * logLo s.k) (s.mlo * logHi s.k))
      (max ((s.mhi : ℝ) * logLo s.k) (s.mhi * logHi s.k))) / B := by
    rw [← hprod]; exact div_le_div_of_nonneg_right hp2 hB0.le
  have hclo' : ((s.clo + min (min (s.mlo * logLo s.k) (s.mlo * logHi s.k))
      (min (s.mhi * logLo s.k) (s.mhi * logHi s.k)) / (B : ℤ) : ℤ) : ℝ) ≤
      B * mcheck ((s.k + 1 : ℕ) : ℝ) := by
    rw [hmc]; push_cast; nlinarith
  have hchi' : (B : ℝ) * mcheck ((s.k + 1 : ℕ) : ℝ) ≤
      ((s.chi + -((-(max (max (s.mlo * logLo s.k) (s.mlo * logHi s.k))
        (max (s.mhi * logLo s.k) (s.mhi * logHi s.k)))) / (B : ℤ)) : ℤ) : ℝ) := by
    rw [hmc]; push_cast; nlinarith
  refine ⟨⟨?_, ?_, ?_, ?_, hclo', hchi', ?_⟩, rfl, ?_⟩
  · show 1 ≤ s.k + 1
    omega
  · -- `M`
    show ((s.M + v : ℤ) : ℝ) = mertR ((s.k + 1 : ℕ) : ℝ)
    rw [mertR_succ, ← hM, hμ]; push_cast; ring
  · -- `m`, lower
    show ((s.mlo + v * B / ((s.k + 1 : ℕ) : ℤ) : ℤ) : ℝ) ≤ B * msumR ((s.k + 1 : ℕ) : ℝ)
    have h1 := cast_ediv_le (v * B) hk1z
    rw [msumR_succ, hμ]
    push_cast at h1 ⊢
    have : (B : ℝ) * ((msumR s.k) + (v : ℝ) / ((s.k : ℝ) + 1)) =
        B * msumR s.k + (v : ℝ) * B / ((s.k : ℝ) + 1) := by ring
    rw [this]; linarith
  · -- `m`, upper
    show (B : ℝ) * msumR ((s.k + 1 : ℕ) : ℝ) ≤
      ((s.mhi + -((-(v * B)) / ((s.k + 1 : ℕ) : ℤ)) : ℤ) : ℝ)
    have h1 := le_cast_neg_ediv_neg (v * B) hk1z
    rw [msumR_succ, hμ]
    push_cast at h1 ⊢
    have : (B : ℝ) * ((msumR s.k) + (v : ℝ) / ((s.k : ℝ) + 1)) =
        B * msumR s.k + (v : ℝ) * B / ((s.k : ℝ) + 1) := by ring
    rw [this]; linarith
  · -- the sum of `|M(t)|/t`
    show (B : ℝ) * ∑ t ∈ Ico (1 : ℕ) (s.k + 1), |mertR t| / (t : ℝ) ≤
      ((s.shi + (s.M.natAbs * B + s.k - 1) / s.k : ℕ) : ℝ)
    rw [Finset.sum_Ico_succ_top hk, mul_add]
    have h1 := le_nat_ceil_div (s.M.natAbs * B) s.k hk
    have h2 : (B : ℝ) * (|mertR s.k| / s.k) = ((s.M.natAbs * B : ℕ) : ℝ) / s.k := by
      rw [← hM, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]; ring
    push_cast at h1 ⊢
    rw [h2] at *
    push_cast at h2 ⊢
    linarith
  · -- the check
    obtain ⟨hc1, hc2⟩ := hc
    have hc1' : ((-Cb : ℤ) : ℝ) ≤ _ := Int.cast_le.2 hc1
    have hc2' : _ ≤ ((Cb : ℤ) : ℝ) := Int.cast_le.2 hc2
    have hCb : ((Cb : ℤ) : ℝ) = 1.00303 * B := by norm_num [Cb, B]
    rw [abs_le]
    push_cast at hc1' hc2'
    constructor <;> nlinarith

theorem walk_spec : ∀ (n : ℕ) (s s' : St), Good s → walk n s = some s' →
    Good s' ∧ s'.k = s.k + n ∧ ∀ j : ℕ, s.k < j → j ≤ s'.k → |mcheck (j : ℝ)| ≤ 1.00303 := by
  intro n
  induction n with
  | zero =>
    intro s s' hs h
    simp only [walk, Option.some.injEq] at h
    subst h
    exact ⟨hs, rfl, fun j h1 h2 => absurd h2 (by omega)⟩
  | succ n ih =>
    intro s s' hs h
    simp only [walk] at h
    split at h
    · exact absurd h (by simp)
    rename_i s1 hs1
    obtain ⟨hg1, hk1, hc1⟩ := step_spec hs hs1
    obtain ⟨hg', hk', hc'⟩ := ih s1 s' hg1 h
    refine ⟨hg', by omega, fun j h1 h2 => ?_⟩
    rcases (show j = s1.k ∨ s1.k < j by omega) with rfl | hj
    · exact hc1
    · exact hc' j hj h2

/-- The state at `k = 1`: `M(1) = m(1) = 1`, `m̌(1) = 0`. -/
def s0 : St := ⟨1, 1, B, B, 0, 0, 0⟩

theorem good_s0 : Good s0 := by
  have hm : mertR 1 = 1 := by simp [mertR]
  have hs : msumR 1 = 1 := by simp [msumR]
  have hc : mcheck 1 = 0 := by simp [mcheck]
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s0, hm, hs, hc]

theorem good_init : Good s0 ∧ ∀ j : ℕ, 1 ≤ j → j ≤ s0.k → |mcheck (j : ℝ)| ≤ 1.00303 := by
  refine ⟨good_s0, fun j h1 h2 => ?_⟩
  have hj : j = 1 := by simp only [s0] at h2; omega
  subst hj
  have : mcheck ((1 : ℕ) : ℝ) = 0 := by simp [mcheck]
  rw [this, abs_zero]; norm_num

theorem chain {s s' : St} {n : ℕ} (hs : Good s)
    (hP : ∀ j : ℕ, 1 ≤ j → j ≤ s.k → |mcheck (j : ℝ)| ≤ 1.00303) (h : walk n s = some s') :
    Good s' ∧ ∀ j : ℕ, 1 ≤ j → j ≤ s'.k → |mcheck (j : ℝ)| ≤ 1.00303 := by
  obtain ⟨hg, -, hc⟩ := walk_spec n s s' hs h
  refine ⟨hg, fun j h1 h2 => ?_⟩
  rcases le_or_gt j s.k with hj | hj
  · exact hP j h1 hj
  · exact hc j hj h2

end TernaryGoldbach.Prelim.SmallMcheck
