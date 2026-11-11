/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Squarefree

/-!
# Lemma 5(c) of the note, with the computation (q)

`κ log i + 0.96 ≤ Q₁(i) ≤ κ log i + 1.17` for every natural `i ≥ 1`.

* For `i ≤ T = 10⁴` this is the computation (q): `μ²(n)` for `n ≤ 10⁴` by trial division, `Q₁`
  accumulated with outward rounding to multiples of `10⁻¹⁵`, and the bound checked on 53 blocks
  `(a, b]` via `Q₁(a+1) − κ log b ≤ Q₁(i) − κ log i ≤ Q₁(b) − κ log(a+1)`. The whole check is
  `qcheck = true`, proved by `decide +kernel`.
* For `i > T`, Lemma 5(a) gives `|E(i) − E(T)| ≤ 8/√T + 3/T + κ/T < 0.0804` for
  `E = Q₁ − κ log`, and the computation gives `E(T) ∈ [1.0441, 1.0443]`.

The note's (c) concerns the real variable and has the range `[0.578, 1.166]`. The discrete Lemma 5(d)
only needs integers: there the values for `i ≤ 10⁴` lie in `[0.9905, 1.1655]` (minimum at `i = 4`,
maximum at `i = 3`), and those for `i > 10⁴` in `[0.963, 1.125]`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius

/-! ### Squarefree test by trial division -/

/-- `true` iff no `e ≥ d` with `e² ≤ n` has `e² ∣ n` (with fuel). -/
def noSqDivFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, d => decide (n < d * d)
  | f + 1, d => if n < d * d then true else if n % (d * d) = 0 then false else noSqDivFrom n f (d + 1)

/-- The squarefree test. -/
def sqf (n : ℕ) : Bool := noSqDivFrom n n 2

theorem noSqDivFrom_true {n : ℕ} : ∀ (f d : ℕ), noSqDivFrom n f d = true →
    ∀ e, d ≤ e → e * e ≤ n → ¬ (e * e ∣ n) := by
  intro f
  induction f with
  | zero =>
    intro d h e hde he
    simp only [noSqDivFrom, decide_eq_true_eq] at h
    have : d * d ≤ e * e := Nat.mul_le_mul hde hde
    omega
  | succ f ih =>
    intro d h e hde he hdiv
    simp only [noSqDivFrom] at h
    split_ifs at h with h1 h2
    · have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · rcases eq_or_lt_of_le hde with rfl | hlt
      · exact h2 (Nat.mod_eq_zero_of_dvd hdiv)
      · exact ih (d + 1) h e hlt he hdiv

theorem noSqDivFrom_false {n : ℕ} : ∀ (f d : ℕ), n < (d + f) * (d + f) →
    noSqDivFrom n f d = false → ∃ e, d ≤ e ∧ e * e ∣ n := by
  intro f
  induction f with
  | zero =>
    intro d hfd h
    simp only [noSqDivFrom, decide_eq_false_iff_not, not_lt] at h
    simp at hfd; omega
  | succ f ih =>
    intro d hfd h
    simp only [noSqDivFrom] at h
    split_ifs at h with h1 h2
    · exact ⟨d, le_rfl, Nat.dvd_of_mod_eq_zero h2⟩
    · obtain ⟨e, he, hdiv⟩ := ih (d + 1) (by rw [show d + 1 + f = d + (f + 1) by ring]; exact hfd) h
      exact ⟨e, by omega, hdiv⟩

theorem sqf_iff {n : ℕ} (hn : 1 ≤ n) : sqf n = true ↔ Squarefree n := by
  constructor
  · intro h
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdiv
    have hp2 := hp.two_le
    have hle : p * p ≤ n := Nat.le_of_dvd (by omega) hdiv
    exact noSqDivFrom_true n 2 h p hp2 hle hdiv
  · intro h
    by_contra hc
    have hf : sqf n = false := by simpa using hc
    obtain ⟨e, he, hdiv⟩ := noSqDivFrom_false n 2 (by nlinarith) hf
    have := h e hdiv
    rw [Nat.isUnit_iff] at this
    omega

theorem moebius_sq_eq_sqf {n : ℕ} (hn : 1 ≤ n) :
    (μ n : ℝ) ^ 2 = if sqf n then 1 else 0 := by
  by_cases h : sqf n = true
  · rw [if_pos h]
    have := moebius_sq_eq_one_of_squarefree ((sqf_iff hn).1 h)
    exact_mod_cast this
  · rw [if_neg h]
    have : ¬ Squarefree n := fun hs => h ((sqf_iff hn).2 hs)
    rw [moebius_eq_zero_of_not_squarefree this]; simp

/-! ### `Q₁` with outward rounding -/

/-- The scale `10¹⁵` of the rounded partial sums of `Q₁`. -/
def qB : ℕ := 10 ^ 15

/-- Add the terms `n+1, …, n+c` of `Q₁` to `(lo, hi)`, rounding outward. -/
def q1acc : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | _, lo, hi, 0 => (lo, hi)
  | n, lo, hi, c + 1 =>
    if sqf (n + 1) then q1acc (n + 1) (lo + qB / (n + 1)) (hi + (qB + n) / (n + 1)) c
    else q1acc (n + 1) lo hi c

theorem Q1_mono {a b : ℕ} (hab : a ≤ b) : Q1 a ≤ Q1 b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    rw [Q1_succ]
    have : 0 ≤ (μ (b + 1) : ℝ) ^ 2 / (b + 1) := by positivity
    linarith

theorem q1acc_sound : ∀ (c n lo hi : ℕ), (lo : ℝ) ≤ qB * Q1 n → (qB : ℝ) * Q1 n ≤ hi →
    ((q1acc n lo hi c).1 : ℝ) ≤ qB * Q1 (n + c) ∧ (qB : ℝ) * Q1 (n + c) ≤ (q1acc n lo hi c).2 := by
  intro c
  induction c with
  | zero => intro n lo hi h1 h2; simp only [q1acc, add_zero]; exact ⟨h1, h2⟩
  | succ c ih =>
    intro n lo hi h1 h2
    rw [show n + (c + 1) = (n + 1) + c by ring]
    have hm : 1 ≤ n + 1 := by omega
    have hQ := Q1_succ n
    rw [moebius_sq_eq_sqf hm] at hQ
    simp only [q1acc]
    split_ifs with hs
    · apply ih
      · rw [hQ, if_pos hs]
        have : ((qB / (n + 1) : ℕ) : ℝ) ≤ (qB : ℝ) / (n + 1) := by
          have := Nat.cast_div_le (α := ℝ) (m := qB) (n := n + 1); exact_mod_cast this
        push_cast
        have e : (qB : ℝ) * (Q1 n + 1 / ((n : ℝ) + 1)) = qB * Q1 n + qB / (n + 1) := by ring
        rw [e]; linarith
      · rw [hQ, if_pos hs]
        have hdiv : qB ≤ (qB + n) / (n + 1) * (n + 1) := by
          have h1 := Nat.div_add_mod (qB + n) (n + 1)
          have h2 := Nat.mod_lt (qB + n) (show n + 1 > 0 by omega)
          nlinarith
        have : (qB : ℝ) / (n + 1) ≤ (((qB + n) / (n + 1) : ℕ) : ℝ) := by
          rw [div_le_iff₀ (by positivity)]; exact_mod_cast hdiv
        push_cast
        have e : (qB : ℝ) * (Q1 n + 1 / ((n : ℝ) + 1)) = qB * Q1 n + qB / (n + 1) := by ring
        rw [e]; push_cast at this; linarith
    · apply ih
      · rw [hQ, if_neg hs]; simpa using h1
      · rw [hQ, if_neg hs]; simpa using h2

/-! ### The block check -/

/-- `κ ∈ [kLo, kHi]`. -/
def kLo : ℚ := 6079267 / 10 ^ 7
def kHi : ℚ := 6079274 / 10 ^ 7
/-- The range of `Q₁(i) − κ log i` at integers `i ≥ 1`. -/
def eLoQ : ℚ := 96 / 100
def eHiQ : ℚ := 117 / 100
/-- The enclosure of `E(10⁴) = Q₁(10⁴) − κ log 10⁴`. -/
def ETlo : ℚ := 10441 / 10 ^ 4
def EThi : ℚ := 10443 / 10 ^ 4

/-- The test for the block `(a, b]`, from `lo₁ ≤ 10¹⁵ Q₁(a+1)` and `10¹⁵ Q₁(b) ≤ hi_b`. -/
def blockOk (a b lo1 hiB : ℕ) : Bool :=
  decide (eLoQ ≤ (lo1 : ℚ) / qB - kHi * LogCert.logHi b) &&
    decide ((hiB : ℚ) / qB - kLo * LogCert.logLo (a + 1) ≤ eHiQ)

/-- The check (q) over consecutive blocks. -/
def checkBlocks : ℕ → ℕ → ℕ → List ℕ → Bool
  | a, lo, hi, [] =>
    decide (a = 10 ^ 4) && decide (ETlo ≤ (lo : ℚ) / qB - kHi * LogCert.logHi a) &&
      decide ((hi : ℚ) / qB - kLo * LogCert.logLo a ≤ EThi)
  | a, lo, hi, b :: rest =>
    decide (a < b) &&
      blockOk a b (q1acc a lo hi 1).1 (q1acc (a + 1) (q1acc a lo hi 1).1 (q1acc a lo hi 1).2 (b - (a + 1))).2 &&
      checkBlocks b (q1acc (a + 1) (q1acc a lo hi 1).1 (q1acc a lo hi 1).2 (b - (a + 1))).1
        (q1acc (a + 1) (q1acc a lo hi 1).1 (q1acc a lo hi 1).2 (b - (a + 1))).2 rest

/-- The 53 block endpoints. -/
def qblocks : List ℕ := [1,2,4,5,6,9,11,13,16,20,24,28,32,37,45,54,62,71,82,96,113,134,154,177,201,231,269,311,358,411,471,545,628,723,834,963,1102,1262,1451,1668,1922,2203,2527,2903,3326,3823,4387,5037,5789,6638,7623,8748,10000]

set_option maxRecDepth 100000 in
/-- **The computation (q)**. -/
theorem qcheck : checkBlocks 0 0 0 qblocks = true := by decide +kernel

theorem κ_mem : (kLo : ℝ) ≤ κ ∧ κ ≤ (kHi : ℝ) := by
  constructor
  · have := κ_lo; simp only [kLo]; push_cast; linarith
  · have := κ_hi; simp only [kHi]; push_cast; linarith

theorem checkBlocks_sound : ∀ (bs : List ℕ) (a lo hi : ℕ), checkBlocks a lo hi bs = true →
    (lo : ℝ) ≤ qB * Q1 a → (qB : ℝ) * Q1 a ≤ hi →
    (∀ i : ℕ, a < i → i ≤ 10 ^ 4 →
      (eLoQ : ℝ) ≤ Q1 i - κ * Real.log i ∧ Q1 i - κ * Real.log i ≤ eHiQ) ∧
    ((ETlo : ℝ) ≤ Q1 (10 ^ 4) - κ * Real.log (10 ^ 4 : ℕ) ∧
      Q1 (10 ^ 4) - κ * Real.log (10 ^ 4 : ℕ) ≤ EThi) := by
  have hqB : (0 : ℝ) < qB := by norm_num [qB]
  obtain ⟨hk1, hk2⟩ := κ_mem
  have hk0 : (0 : ℝ) ≤ kLo := by norm_num [kLo]
  intro bs
  induction bs with
  | nil =>
    intro a lo hi h h1 h2
    simp only [checkBlocks, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hlo⟩, hhi⟩ := h
    subst ha
    refine ⟨fun i hi1 hi2 => by omega, ?_, ?_⟩
    · have hl := LogCert.le_logHi (q := (10 ^ 4 : ℕ)) (by norm_num)
      have hlog : 0 ≤ Real.log ((10 ^ 4 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
      have hlo' := (Rat.cast_le (K := ℝ)).mpr hlo
      push_cast at hlo'
      have : (lo : ℝ) / qB ≤ Q1 (10 ^ 4) := by rw [div_le_iff₀ hqB]; linarith
      push_cast at hl hlog hlo' ⊢
      nlinarith
    · have hl := LogCert.logLo_le (q := (10 ^ 4 : ℕ)) (by norm_num)
      have hlog : 0 ≤ Real.log ((10 ^ 4 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
      have hhi' := (Rat.cast_le (K := ℝ)).mpr hhi
      push_cast at hhi'
      have : Q1 (10 ^ 4) ≤ (hi : ℝ) / qB := by rw [le_div_iff₀ hqB]; linarith
      push_cast at hl hlog hhi' ⊢
      nlinarith
  | cons b rest ih =>
    intro a lo hi h h1 h2
    simp only [checkBlocks, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hab, hblk⟩, hrest⟩ := h
    set p1 := q1acc a lo hi 1 with hp1
    set p2 := q1acc (a + 1) p1.1 p1.2 (b - (a + 1)) with hp2
    have s1 := q1acc_sound 1 a lo hi h1 h2
    rw [← hp1] at s1
    have s2 := q1acc_sound (b - (a + 1)) (a + 1) p1.1 p1.2 s1.1 s1.2
    rw [← hp2, show a + 1 + (b - (a + 1)) = b by omega] at s2
    have hrec := ih b p2.1 p2.2 hrest s2.1 s2.2
    refine ⟨fun i hi1 hi2 => ?_, hrec.2⟩
    by_cases hib : i ≤ b
    · simp only [blockOk, Bool.and_eq_true, decide_eq_true_eq] at hblk
      obtain ⟨hb1, hb2⟩ := hblk
      have hi0 : (1 : ℝ) ≤ i := by exact_mod_cast (by omega : 1 ≤ i)
      have hlogi : 0 ≤ Real.log i := Real.log_nonneg hi0
      constructor
      · have hQ : (p1.1 : ℝ) / qB ≤ Q1 i := by
          rw [div_le_iff₀ hqB]
          have := Q1_mono (show a + 1 ≤ i by omega)
          nlinarith
        have hlb : Real.log i ≤ LogCert.logHi b := by
          have := LogCert.le_logHi (q := (b : ℚ)) (by exact_mod_cast (by omega : 0 < b))
          push_cast at this
          exact (Real.log_le_log (by linarith) (by exact_mod_cast hib)).trans this
        have hb1' := (Rat.cast_le (K := ℝ)).mpr hb1
        push_cast at hb1'
        have : κ * Real.log i ≤ kHi * LogCert.logHi b := by
          have hkh0 : (0 : ℝ) ≤ kHi := by norm_num [kHi]
          calc κ * Real.log i ≤ kHi * Real.log i := mul_le_mul_of_nonneg_right hk2 hlogi
            _ ≤ kHi * LogCert.logHi b := mul_le_mul_of_nonneg_left hlb hkh0
        linarith
      · have hQ : Q1 i ≤ (p2.2 : ℝ) / qB := by
          rw [le_div_iff₀ hqB]
          have := Q1_mono hib
          nlinarith
        have hla : (LogCert.logLo ((a : ℚ) + 1) : ℝ) ≤ Real.log i := by
          have := LogCert.logLo_le (q := (a : ℚ) + 1) (by positivity)
          push_cast at this ⊢
          exact this.trans (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : a + 1 ≤ i)))
        have hb2' := (Rat.cast_le (K := ℝ)).mpr hb2
        push_cast at hb2'
        have : (kLo : ℝ) * LogCert.logLo ((a : ℚ) + 1) ≤ κ * Real.log i := by
          calc (kLo : ℝ) * LogCert.logLo ((a : ℚ) + 1) ≤ kLo * Real.log i :=
                mul_le_mul_of_nonneg_left hla hk0
            _ ≤ κ * Real.log i := mul_le_mul_of_nonneg_right hk1 hlogi
        linarith
    · exact hrec.1 i (by omega) hi2

/-! ### Beyond `10⁴` -/

theorem Q1_diff {T : ℕ} (hT : 1 ≤ T) {i : ℕ} (hTi : T ≤ i) :
    Q1 i - Q1 T = Q i / i - Q T / T + ∑ n ∈ Ico T i, Q n / ((n : ℝ) * (n + 1)) := by
  induction i, hTi using Nat.le_induction with
  | base => simp
  | succ i hTi ih =>
    rw [sum_Ico_succ_top hTi, Q1_succ, Q_succ]
    have hi : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    push_cast
    have e : Q1 i + (μ (i + 1) : ℝ) ^ 2 / ((i : ℝ) + 1) - Q1 T =
        (Q1 i - Q1 T) + (μ (i + 1) : ℝ) ^ 2 / ((i : ℝ) + 1) := by ring
    rw [e, ih]
    field_simp
    ring

theorem inv_sqrt_mul_succ_le {n : ℕ} (hn : 1 ≤ n) :
    1 / (Real.sqrt n * ((n : ℝ) + 1)) ≤ 2 * (1 / Real.sqrt n - 1 / Real.sqrt (n + 1 : ℕ)) := by
  set a := Real.sqrt n
  set b := Real.sqrt (n + 1 : ℕ)
  have ha : 0 < a := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = n := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = n + 1 := by rw [Real.sq_sqrt (by positivity)]; push_cast; ring
  have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
  rw [← hb2, div_sub_div _ _ ha.ne' hb.ne', one_mul, mul_one, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  -- `a b ≤ 2 (b − a) a b²`, i.e. `1 ≤ 2 (b − a) b`, i.e. `1 = (b−a)(b+a) ≤ 2(b−a) b`
  have h1 : (b - a) * (b + a) = 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hab), mul_pos ha hb]

theorem E_tail_gen {T i : ℕ} (hT : 1 ≤ T) (hi : T ≤ i) :
    |(Q1 i - κ * Real.log i) - (Q1 T - κ * Real.log T)| ≤
      8 / Real.sqrt T + 3 / T + κ / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hipos : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have hTi : (T : ℝ) ≤ i := by exact_mod_cast hi
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hsi : Real.sqrt T ≤ Real.sqrt i := Real.sqrt_le_sqrt hTi
  have hκ0 := κ_pos
  set R : ℕ → ℝ := fun n => Q n - κ * n with hR
  have hRb : ∀ n : ℕ, |R n| ≤ 2 * Real.sqrt n + 1 := fun n => abs_Q_sub_le n
  have hdiff := Q1_diff hT hi
  have hsplit : ∑ n ∈ Ico T i, Q n / ((n : ℝ) * (n + 1)) =
      ∑ n ∈ Ico T i, R n / ((n : ℝ) * (n + 1)) + κ * ∑ n ∈ Ico T i, 1 / ((n : ℝ) + 1) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have : (0 : ℝ) < n := by exact_mod_cast (by have := (mem_Ico.1 hn).1; omega)
    simp only [hR]; field_simp; ring
  have hQi : Q i / i = κ + R i / i := by simp only [hR]; field_simp; ring
  have hQT : Q T / T = κ + R T / T := by simp only [hR]; field_simp; ring
  have hharm_hi : ∑ n ∈ Ico T i, 1 / ((n : ℝ) + 1) ≤ Real.log i - Real.log T := by
    have h1 := sum_log_one_add_inv i
    have h2 := sum_log_one_add_inv T
    have h3 := sum_Ico_consecutive (fun n : ℕ => Real.log (1 + 1 / (n : ℝ))) hT hi
    have h4 : ∑ n ∈ Ico T i, 1 / ((n : ℝ) + 1) ≤ ∑ n ∈ Ico T i, Real.log (1 + 1 / (n : ℝ)) := by
      refine sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := le_trans hT (mem_Ico.1 hn).1
      have := two_div_le_log n hn1
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      calc 1 / ((n : ℝ) + 1) ≤ 2 / (2 * n + 1) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
        _ ≤ _ := this
    linarith
  have hharm_lo : Real.log i - Real.log T - 1 / T ≤ ∑ n ∈ Ico T i, 1 / ((n : ℝ) + 1) := by
    have h1 : ∑ n ∈ Ico T i, Real.log (1 + 1 / ((n : ℝ) + 1)) =
        Real.log ((i : ℝ) + 1) - Real.log ((T : ℝ) + 1) := by
      have := sum_Ico_sub_telescope (fun n : ℕ => Real.log ((n : ℝ) + 1)) hi
      rw [← this]
      refine sum_congr rfl fun n _ => ?_
      push_cast
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1; field_simp
    have h2 : ∑ n ∈ Ico T i, Real.log (1 + 1 / ((n : ℝ) + 1)) ≤ ∑ n ∈ Ico T i, 1 / ((n : ℝ) + 1) := by
      refine sum_le_sum fun n _ => ?_
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) by positivity)
      linarith
    have h3 : Real.log (i : ℝ) ≤ Real.log ((i : ℝ) + 1) := Real.log_le_log hipos (by linarith)
    have h4 : Real.log ((T : ℝ) + 1) - Real.log T ≤ 1 / T := by
      rw [← Real.log_div (by positivity) hTpos.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((T : ℝ) + 1) / T by positivity)
      have e : ((T : ℝ) + 1) / T - 1 = 1 / T := by field_simp; ring
      linarith
    linarith
  have hRx : ∀ x : ℕ, T ≤ x → |R x / x| ≤ 2 / Real.sqrt T + 1 / T := by
    intro x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hTx : (T : ℝ) ≤ x := by exact_mod_cast hx
    have hsx : Real.sqrt T ≤ Real.sqrt x := Real.sqrt_le_sqrt hTx
    have hsx0 : 0 < Real.sqrt x := lt_of_lt_of_le hsT hsx
    have hsq : Real.sqrt (x : ℝ) * Real.sqrt x = x := Real.mul_self_sqrt (by positivity)
    rw [abs_div, abs_of_pos hxpos]
    calc |R x| / x ≤ (2 * Real.sqrt x + 1) / x := by gcongr; exact hRb x
      _ = 2 / Real.sqrt x + 1 / x := by first | (field_simp; done) | (field_simp; nlinarith [hsq])
      _ ≤ 2 / Real.sqrt T + 1 / T := by gcongr
  have hRsum : |∑ n ∈ Ico T i, R n / ((n : ℝ) * (n + 1))| ≤ 4 / Real.sqrt T + 1 / T := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ n ∈ Ico T i, |R n / ((n : ℝ) * (n + 1))| ≤
        2 * (2 * (1 / Real.sqrt n - 1 / Real.sqrt (n + 1 : ℕ))) + (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
      intro n hn
      have hn1 : 1 ≤ n := le_trans hT (mem_Ico.1 hn).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) * (n + 1))]
      have h1 := hRb n
      have h2 := inv_sqrt_mul_succ_le hn1
      have e1 : (2 * Real.sqrt n + 1) / ((n : ℝ) * (n + 1)) =
          2 * (1 / (Real.sqrt n * ((n : ℝ) + 1))) + (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
        have hsq : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
        push_cast
        field_simp
        nlinarith [hsq]
      calc |R n| / ((n : ℝ) * (n + 1)) ≤ (2 * Real.sqrt n + 1) / ((n : ℝ) * (n + 1)) := by
            gcongr
        _ = _ := e1
        _ ≤ _ := by linarith
    refine (sum_le_sum hpt).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have t1 := sum_Ico_sub_telescope (fun n : ℕ => -(1 / Real.sqrt n)) hi
    have t2 := sum_Ico_sub_telescope (fun n : ℕ => -(1 / (n : ℝ))) hi
    rw [show ∑ n ∈ Ico T i, (1 / Real.sqrt n - 1 / Real.sqrt (n + 1 : ℕ)) =
      ∑ n ∈ Ico T i, (-(1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) - -(1 / Real.sqrt (n : ℝ))) from
      sum_congr rfl fun _ _ => by ring, t1]
    rw [show ∑ n ∈ Ico T i, (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) =
      ∑ n ∈ Ico T i, (-(1 / ((n + 1 : ℕ) : ℝ)) - -(1 / (n : ℝ))) from
      sum_congr rfl fun _ _ => by ring, t2]
    have : 0 ≤ 1 / Real.sqrt i := by positivity
    have : 0 ≤ 1 / (i : ℝ) := by positivity
    have : 4 / Real.sqrt T = 4 * (1 / Real.sqrt T) := by ring
    linarith
  have hmain : (Q1 i - κ * Real.log i) - (Q1 T - κ * Real.log T) =
      R i / i - R T / T + ∑ n ∈ Ico T i, R n / ((n : ℝ) * (n + 1)) +
        κ * (∑ n ∈ Ico T i, 1 / ((n : ℝ) + 1) - (Real.log i - Real.log T)) := by
    rw [hsplit, hQi, hQT] at hdiff
    linarith
  rw [hmain]
  have hk : |κ * (∑ n ∈ Ico T i, 1 / ((n : ℝ) + 1) - (Real.log i - Real.log T))| ≤ κ * (1 / T) := by
    rw [abs_mul, abs_of_pos hκ0]
    gcongr
    rw [abs_le]; constructor <;> linarith
  have h3 := abs_add_three (R i / i - R T / T) (∑ n ∈ Ico T i, R n / ((n : ℝ) * (n + 1)))
    (κ * (∑ n ∈ Ico T i, 1 / ((n : ℝ) + 1) - (Real.log i - Real.log T)))
  have hsub := abs_sub (R i / i) (R T / T)
  have hRi := hRx i hi
  have hRT := hRx T le_rfl
  have : κ * (1 / (T : ℝ)) = κ / T := by ring
  have e8 : 8 / Real.sqrt T = 2 / Real.sqrt T + 2 / Real.sqrt T + 4 / Real.sqrt T := by ring
  have e3 : 3 / (T : ℝ) = 1 / T + 1 / T + 1 / T := by ring
  linarith

theorem E_tail {i : ℕ} (hi : 10 ^ 4 ≤ i) :
    |(Q1 i - κ * Real.log i) - (Q1 (10 ^ 4) - κ * Real.log (10 ^ 4 : ℕ))| ≤ 804 / 10 ^ 4 := by
  have h := E_tail_gen (T := 10 ^ 4) (by norm_num) hi
  have hs : Real.sqrt ((10 ^ 4 : ℕ) : ℝ) = 100 := by
    rw [show ((10 ^ 4 : ℕ) : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs] at h
  have := κ_hi
  refine h.trans ?_
  push_cast
  nlinarith

/-- The constants of Lemma 5(c). -/
noncomputable def eLo : ℝ := 0.96
noncomputable def eHi : ℝ := 1.17

/-- **Lemma 5(c)** at integers: `κ log i + 0.96 ≤ Q₁(i) ≤ κ log i + 1.17` for `i ≥ 1`. -/
theorem Q1_bounds {i : ℕ} (hi : 1 ≤ i) :
    κ * Real.log i + eLo ≤ Q1 i ∧ Q1 i ≤ κ * Real.log i + eHi := by
  have hc := checkBlocks_sound qblocks 0 0 0 qcheck (by simp [Q1]) (by simp [Q1])
  by_cases hiT : i ≤ 10 ^ 4
  · obtain ⟨h1, h2⟩ := hc.1 i (by omega) hiT
    have e1 : (eLoQ : ℝ) = eLo := by norm_num [eLoQ, eLo]
    have e2 : (eHiQ : ℝ) = eHi := by norm_num [eHiQ, eHi]
    rw [e1] at h1; rw [e2] at h2
    constructor <;> linarith
  · have ht := E_tail (i := i) (by omega)
    obtain ⟨h3, h4⟩ := hc.2
    have e3 : (ETlo : ℝ) = 10441 / 10 ^ 4 := by norm_num [ETlo]
    have e4 : (EThi : ℝ) = 10443 / 10 ^ 4 := by norm_num [EThi]
    rw [e3] at h3; rw [e4] at h4
    rw [abs_le] at ht
    constructor
    · simp only [eLo]; linarith [ht.1]
    · simp only [eHi]; linarith [ht.2]

end TernaryGoldbach.RSBounds.Moebius003
