import TernaryGoldbach.Prelim.RamareWalk

/-!
# `∏_{p ≤ x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)` for primes `5 ≤ x ≤ 10⁵`, by the kernel

[RS62, Thm 15] on the range below the analytic bound of `MertensProduct.lean`.

The kernel walks `n ≤ 10⁵` (`scripts/gen_mertens_prod.py`) with `D = 10³⁰`. The state bounds:
* `D log n`, using the artanh walk `LogWalk.incr_bounds`;
* `D θ(n)` and `D ∏_{p≤n} p/(p−1)`, with primality decided by trial division (`isP_iff`);
* `D log m` for an integer `1 ≤ m ≤ θ(n)`, which advances with `θ`.

At every prime `x ≥ 5` it bounds `log θ = log m + log(1 + (θ − m)/m)`, where the second term comes
from 12 terms of the artanh series (`q_bounds`). It uses `e^γ ≥ G/D` (Taylor, with `γ` from
`RamareWalk`) and checks `D F(x) < G log θ + 2.50637 D/log θ` in fixed point.
The tightest case is `x = 23`, with margin `2.4·10⁻⁷`.

The final state also gives `∏_{p ≤ 10⁵} p/(p−1) ≤ 20.5116` (`prod_le_1e5`), which bounds the
singular series (`MajorArcs.prod_p_div_le`).
-/

open Finset Real

namespace TernaryGoldbach.Prelim.MertProd

open TernaryGoldbach.Prelim.LogWalk
open TernaryGoldbach.Prelim.RamPf (Hn harm_bounds log_one_add_inv_bounds)

/-! ### `γ` and `e^γ` -/

theorem harmonic_eq_Hn : ∀ n, ((harmonic n : ℚ) : ℝ) = Hn n
  | 0 => by simp [Hn]
  | n + 1 => by
    rw [harmonic_succ, Rat.cast_add, harmonic_eq_Hn n, Hn, Hn, sum_Icc_succ_top (by omega)]
    push_cast; ring

theorem gamma_bounds : (0.5772156646 : ℝ) ≤ eulerMascheroniConstant ∧
    eulerMascheroniConstant ≤ 0.577215666 := by
  obtain ⟨b1, b2⟩ := harm_bounds (n := 20000) (by norm_num)
  rw [harmonic_eq_Hn] at b1 b2
  obtain ⟨l1, l2, h1, h2, -⟩ := RamPf.inv_20000
  dsimp only at l1 l2 h1 h2
  push_cast at b1 b2 l1 l2 h1 h2
  constructor <;> linarith

/-- `G ≤ 10³⁰ e^γ`. -/
def Glo : ℕ := 1781072417453146124173531684687

theorem Glo_le : (Glo : ℝ) ≤ 10 ^ 30 * Real.exp eulerMascheroniConstant := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 0.5772156646) (by norm_num) 22
  have h2 : Real.exp 0.5772156646 ≤ Real.exp eulerMascheroniConstant :=
    Real.exp_le_exp.2 gamma_bounds.1
  have h3 : (Glo : ℝ) ≤ 10 ^ 30 * ∑ i ∈ range 22, (0.5772156646 : ℝ) ^ i / i.factorial := by
    unfold Glo
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]
    norm_num
  nlinarith

/-- `e^γ ≤ 1.7811`. -/
theorem exp_gamma_le : Real.exp eulerMascheroniConstant ≤ 1.7811 := by
  have h1 := Real.exp_bound (x := 0.577215666) (by rw [abs_le]; constructor <;> norm_num)
    (n := 12) (by norm_num)
  have h2 : Real.exp eulerMascheroniConstant ≤ Real.exp 0.577215666 :=
    Real.exp_le_exp.2 gamma_bounds.2
  rw [abs_le] at h1
  have h3 : ∑ m ∈ range 12, (0.577215666 : ℝ) ^ m / m.factorial +
      |(0.577215666 : ℝ)| ^ 12 * ((Nat.succ 12 : ℕ) / ((Nat.factorial 12 : ℕ) * (12 : ℕ))) ≤ 1.7811 := by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  linarith [h1.2]

/-! ### Primality by trial division -/

def tdiv (p : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 => if p < d * d then true else if p % d = 0 then false else tdiv p (d + 1) fuel

def isP (p : ℕ) : Bool := 2 ≤ p && tdiv p 2 p

theorem tdiv_sound {p : ℕ} (hp : 2 ≤ p) : ∀ fuel d, 2 ≤ d →
    (∀ e, 2 ≤ e → e < d → ¬ e ∣ p) → tdiv p d fuel = true → p.Prime := by
  intro fuel
  induction fuel with
  | zero => intro d _ _ h; simp [tdiv] at h
  | succ f ih =>
    intro d hd hno h
    unfold tdiv at h
    split_ifs at h with h1 h2
    · rw [Nat.prime_def_le_sqrt]
      refine ⟨hp, fun m hm2 hms hdvd => ?_⟩
      have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
      have hmd : m < d := by nlinarith
      exact hno m hm2 hmd hdvd
    · exact ih (d + 1) (by omega) (fun e he1 he2 hdvd => by
        rcases Nat.lt_or_ge e d with h3 | h3
        · exact hno e he1 h3 hdvd
        · have : e = d := by omega
          subst this
          exact h2 (Nat.mod_eq_zero_of_dvd hdvd)) h

theorem tdiv_complete {p : ℕ} (hp : p.Prime) : ∀ fuel d, 2 ≤ d → d ≤ p + 1 → p + 2 ≤ d + fuel →
    tdiv p d fuel = true := by
  intro fuel
  induction fuel with
  | zero => intro d hd hdp hf; omega
  | succ f ih =>
    intro d hd hdp hf
    have hp2 := hp.two_le
    unfold tdiv
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero h2
      rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
      · omega
      · subst h; nlinarith
    · exact ih (d + 1) (by omega) (by nlinarith) (by omega)

theorem isP_iff (p : ℕ) : isP p = true ↔ p.Prime := by
  unfold isP
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h2, h⟩
    exact tdiv_sound h2 p 2 le_rfl (fun e h1 h2 => by omega) h
  · intro hp
    exact ⟨hp.two_le, tdiv_complete hp p 2 le_rfl (by have := hp.two_le; omega) (by omega)⟩

/-! ### `log(1 + b/a)` by the artanh series -/

/-- `∑_{j<k} ⌊2·10³⁰ b^{2j+1}/((2j+1)(2a+b)^{2j+1})⌋`. -/
def qAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b => qAux k a b + 2 * 10 ^ 30 * b ^ (2 * k + 1) / ((2 * k + 1) * (2 * a + b) ^ (2 * k + 1))

def qLo (a b : ℕ) : ℕ := qAux 12 a b
def qHi (a b : ℕ) : ℕ := qAux 12 a b + 12 + 3 * 10 ^ 30 * b ^ 25 / (25 * (2 * a + b) ^ 25) + 1

theorem qAux_le (a b : ℕ) (hb : 0 < b) : ∀ k, (qAux k a b : ℝ) ≤
    10 ^ 30 * ∑ j ∈ range k, (2 : ℝ) * (1 / (2 * j + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * j + 1)
  | 0 => by simp [qAux]
  | k + 1 => by
    rw [qAux, sum_range_succ, mul_add, Nat.cast_add]
    refine add_le_add (qAux_le a b hb k) ?_
    have := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 30 * b ^ (2 * k + 1))
      (n := (2 * k + 1) * (2 * a + b) ^ (2 * k + 1))
    refine this.trans (le_of_eq ?_)
    have : (0 : ℝ) < 2 * a + b := by positivity
    rw [div_pow]
    push_cast
    field_simp
    norm_num

theorem le_qAux (a b : ℕ) (hb : 0 < b) : ∀ k, 10 ^ 30 * ∑ j ∈ range k,
    (2 : ℝ) * (1 / (2 * j + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * j + 1) ≤ (qAux k a b : ℝ) + k
  | 0 => by simp [qAux]
  | k + 1 => by
    rw [qAux, sum_range_succ, mul_add, Nat.cast_add, Nat.cast_succ]
    have h1 := le_qAux a b hb k
    have hpos : 0 < (2 * k + 1) * (2 * a + b) ^ (2 * k + 1) := by positivity
    obtain ⟨-, h2⟩ := floor_div_bounds (2 * 10 ^ 30 * b ^ (2 * k + 1)) _ hpos
    have e : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * k + 1)) =
        ((2 * 10 ^ 30 * b ^ (2 * k + 1) : ℕ) : ℝ) / (((2 * k + 1) * (2 * a + b) ^ (2 * k + 1) : ℕ) : ℝ) := by
      have : (0 : ℝ) < 2 * a + b := by positivity
      rw [div_pow]; push_cast; field_simp; norm_num
    linarith

/-- **`qLo/D ≤ log(1 + b/a) ≤ qHi/D`** for `0 < b ≤ a`. -/
theorem q_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (qLo a b : ℝ) ≤ 10 ^ 30 * Real.log (1 + (b : ℝ) / a) ∧
      10 ^ 30 * Real.log (1 + (b : ℝ) / a) ≤ (qHi a b : ℝ) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  set r : ℝ := (a : ℝ) / b with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨h1, h2⟩ := log_one_add_inv_bounds hr0 12
  have ey : 1 / (2 * r + 1) = (b : ℝ) / (2 * a + b) := by rw [hr]; field_simp
  have el : 1 + r⁻¹ = 1 + (b : ℝ) / a := by rw [hr, inv_div]
  rw [ey, el] at h1 h2
  refine ⟨(qAux_le a b hb 12).trans (by nlinarith), ?_⟩
  have h3 := le_qAux a b hb 12
  set y : ℝ := (b : ℝ) / (2 * a + b) with hy
  have hy0 : 0 < y := by positivity
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (b : ℝ) ≤ a := by exact_mod_cast hba
    linarith
  have htail : 2 / (2 * ((12 : ℕ) : ℝ) + 1) * y ^ (2 * 12 + 1) / (1 - y ^ 2) ≤ 3 / 25 * y ^ 25 := by
    have h1y : 8 / 9 ≤ 1 - y ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have : 0 ≤ y ^ 25 := by positivity
    nlinarith
  have hfl : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) ≤
      ((3 * 10 ^ 30 * b ^ 25 / (25 * (2 * a + b) ^ 25) : ℕ) : ℝ) + 1 := by
    have hpos : 0 < 25 * (2 * a + b) ^ 25 := by positivity
    obtain ⟨-, h4⟩ := floor_div_bounds (3 * 10 ^ 30 * b ^ 25) _ hpos
    have e : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) =
        ((3 * 10 ^ 30 * b ^ 25 : ℕ) : ℝ) / ((25 * (2 * a + b) ^ 25 : ℕ) : ℝ) := by
      have : (0 : ℝ) < 2 * a + b := by positivity
      rw [hy, div_pow]; push_cast; field_simp; norm_num
    linarith
  unfold qHi
  push_cast
  push_cast at h3
  nlinarith

/-! ### The walk -/

/-- `θ(n)` and `∏_{p ≤ n} p/(p−1)`. -/
noncomputable def th (n : ℕ) : ℝ := ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p
noncomputable def Fp (n : ℕ) : ℝ := ∏ p ∈ (Icc 1 n).filter Nat.Prime, ((p : ℝ) / (p - 1))

theorem th_succ (n : ℕ) : th (n + 1) = th n + if (n + 1).Prime then Real.log (n + 1 : ℕ) else 0 := by
  unfold th
  rw [sum_filter, sum_filter, sum_Icc_succ_top (by omega)]

theorem Fp_succ (n : ℕ) : Fp (n + 1) = Fp n * if (n + 1).Prime then
    (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) - 1)) else 1 := by
  unfold Fp
  rw [prod_filter, prod_filter, prod_Icc_succ_top (by omega)]

/-- `⌈x/y⌉`. -/
def cdiv (x y : ℕ) : ℕ := (x + y - 1) / y

theorem cdiv_ge (x y : ℕ) (hy : 0 < y) : (x : ℝ) / y ≤ (cdiv x y : ℝ) := by
  unfold cdiv
  have h1 := Nat.div_add_mod (x + y - 1) y
  have h2 := Nat.mod_lt (x + y - 1) hy
  have h3 : x ≤ y * ((x + y - 1) / y) := by omega
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  rw [div_le_iff₀ hy']
  have : (x : ℝ) ≤ (y : ℝ) * (((x + y - 1) / y : ℕ) : ℝ) := by exact_mod_cast h3
  linarith

/-- Advance `m` while `D (m + 1) ≤ T`. -/
def adv : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, m, lo, hi => (m, lo, hi)
  | f + 1, T, m, lo, hi =>
    if 10 ^ 30 * (m + 1) ≤ T then adv f T (m + 1) (lo + incrLo m) (hi + incrHi m) else (m, lo, hi)

theorem adv_spec : ∀ (f T m lo hi : ℕ), 1 ≤ m → (lo : ℝ) ≤ 10 ^ 30 * Real.log m →
    10 ^ 30 * Real.log m ≤ hi →
    1 ≤ (adv f T m lo hi).1 ∧ ((adv f T m lo hi).2.1 : ℝ) ≤ 10 ^ 30 * Real.log (adv f T m lo hi).1 ∧
      10 ^ 30 * Real.log (adv f T m lo hi).1 ≤ (adv f T m lo hi).2.2 := by
  intro f
  induction f with
  | zero => intro T m lo hi hm h1 h2; exact ⟨hm, h1, h2⟩
  | succ f ih =>
    intro T m lo hi hm h1 h2
    unfold adv
    split_ifs with hc
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      obtain ⟨i1, i2⟩ := incr_bounds hm
      have hlog : Real.log ((m + 1 : ℕ) : ℝ) = Real.log m + Real.log (1 + (m : ℝ)⁻¹) := by
        rw [← Real.log_mul hm0.ne' (by positivity)]; congr 1; push_cast; field_simp
      apply ih T (m + 1) _ _ (by omega)
      · rw [hlog]; push_cast; linarith
      · rw [hlog]; push_cast; linarith
    · exact ⟨hm, h1, h2⟩

/-- The claim at a prime `x`. -/
def Claim (x : ℕ) : Prop :=
  Fp x < Real.exp eulerMascheroniConstant * Real.log (th x) + 2.50637 / Real.log (th x)

structure PS where
  Llo : ℕ
  Lhi : ℕ
  Tlo : ℕ
  Thi : ℕ
  Fhi : ℕ
  m : ℕ
  Mlo : ℕ
  Mhi : ℕ
deriving DecidableEq

/-- The step at a prime `n + 1`, given the advanced `(m, log m)`. -/
def pstepR (n : ℕ) (s : PS) (r : ℕ × ℕ × ℕ) : PS :=
  ⟨s.Llo + incrLo n, s.Lhi + incrHi n, s.Tlo + (s.Llo + incrLo n), s.Thi + (s.Lhi + incrHi n),
    cdiv (s.Fhi * (n + 1)) n, r.1, r.2.1, r.2.2⟩

/-- The step at a prime `n + 1`. -/
def pstepP (n : ℕ) (s : PS) : PS :=
  pstepR n s (adv 30 (s.Tlo + (s.Llo + incrLo n)) s.m s.Mlo s.Mhi)

/-- The step at a composite `n + 1`. -/
def pstepN (n : ℕ) (s : PS) : PS :=
  ⟨s.Llo + incrLo n, s.Lhi + incrHi n, s.Tlo, s.Thi, s.Fhi, s.m, s.Mlo, s.Mhi⟩

def pstep (n : ℕ) (s : PS) : PS := if isP (n + 1) then pstepP n s else pstepN n s

/-- The check at a prime `x ≥ 5`, on the state at `x`. -/
def chk (s : PS) : Bool :=
  decide (10 ^ 30 * s.m < s.Tlo) && decide (s.Thi - 10 ^ 30 * s.m ≤ 10 ^ 30 * s.m) &&
    decide (s.Fhi < Glo * (s.Mlo + qLo (10 ^ 30 * s.m) (s.Tlo - 10 ^ 30 * s.m)) / 10 ^ 30 +
      250637 * 10 ^ 55 / (s.Mhi + qHi (10 ^ 30 * s.m) (s.Thi - 10 ^ 30 * s.m)))

def walkP : ℕ → ℕ → PS → Option PS
  | _, 0, s => some s
  | n, len + 1, s =>
    let s' := pstep n s
    if s'.Lhi + s'.Thi + s'.Fhi + s'.Mhi < 10 ^ 200 ∧ (isP (n + 1) = false ∨ n + 1 < 5 ∨ chk s' = true) then
      walkP (n + 1) len s' else none

def Inv (n : ℕ) (s : PS) : Prop :=
  (s.Llo : ℝ) ≤ 10 ^ 30 * Real.log n ∧ 10 ^ 30 * Real.log n ≤ s.Lhi ∧
  (s.Tlo : ℝ) ≤ 10 ^ 30 * th n ∧ 10 ^ 30 * th n ≤ s.Thi ∧
  10 ^ 30 * Fp n ≤ s.Fhi ∧
  1 ≤ s.m ∧ (s.Mlo : ℝ) ≤ 10 ^ 30 * Real.log s.m ∧ 10 ^ 30 * Real.log s.m ≤ s.Mhi ∧
  ∀ x, 5 ≤ x → x ≤ n → x.Prime → Claim x

theorem th_nonneg (n : ℕ) : 0 ≤ th n :=
  sum_nonneg fun p _ => Real.log_natCast_nonneg p

theorem log_q_lo {a T : ℕ} (ha : 0 < a) (hT : a < T) (hba : T - a ≤ a) :
    (qLo a (T - a) : ℝ) ≤ 10 ^ 30 * Real.log ((T : ℝ) / a) := by
  obtain ⟨q, -⟩ := q_bounds ha (by omega) hba
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have e : (1 : ℝ) + ((T - a : ℕ) : ℝ) / a = (T : ℝ) / a := by
    rw [Nat.cast_sub hT.le]; field_simp; ring
  rwa [e] at q

theorem log_q_hi {a T : ℕ} (ha : 0 < a) (hT : a < T) (hba : T - a ≤ a) :
    10 ^ 30 * Real.log ((T : ℝ) / a) ≤ (qHi a (T - a) : ℝ) := by
  obtain ⟨-, q⟩ := q_bounds ha (by omega) hba
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have e : (1 : ℝ) + ((T - a : ℕ) : ℝ) / a = (T : ℝ) / a := by
    rw [Nat.cast_sub hT.le]; field_simp; ring
  rwa [e] at q

/-- The check gives the claim. -/
theorem chk_claim {x : ℕ} {s : PS} (hT1 : (s.Tlo : ℝ) ≤ 10 ^ 30 * th x)
    (hT2 : 10 ^ 30 * th x ≤ s.Thi) (hF : 10 ^ 30 * Fp x ≤ s.Fhi) (hm : 1 ≤ s.m)
    (hM1 : (s.Mlo : ℝ) ≤ 10 ^ 30 * Real.log s.m) (hM2 : 10 ^ 30 * Real.log s.m ≤ s.Mhi)
    (hc : chk s = true) : Claim x := by
  unfold chk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc
  have hm0 : (0 : ℝ) < s.m := by exact_mod_cast hm
  have ha0 : 0 < 10 ^ 30 * s.m := Nat.mul_pos (by norm_num) hm
  have hTT : s.Tlo ≤ s.Thi := by exact_mod_cast hT1.trans hT2
  have q1 := log_q_lo ha0 c1 (by omega)
  have q2 := log_q_hi ha0 (lt_of_lt_of_le c1 hTT) c2
  have hac : ((10 ^ 30 * s.m : ℕ) : ℝ) = 10 ^ 30 * s.m := by push_cast; ring
  rw [hac] at q1 q2
  have hTa : 10 ^ 30 * (s.m : ℝ) < s.Tlo := by rw [← hac]; exact_mod_cast c1
  have hth : (s.m : ℝ) < th x := by
    have : 10 ^ 30 * (s.m : ℝ) < 10 ^ 30 * th x := by linarith
    linarith
  have hth0 : 0 < th x := by linarith
  have hTlo0 : (0 : ℝ) < s.Tlo := by linarith
  -- `log θ` from below and above
  have hsplit1 : Real.log ((s.Tlo : ℝ) / 10 ^ 30) = Real.log s.m + Real.log ((s.Tlo : ℝ) / (10 ^ 30 * s.m)) := by
    rw [← Real.log_mul hm0.ne' (by positivity)]; congr 1; field_simp
  have hsplit2 : Real.log ((s.Thi : ℝ) / 10 ^ 30) = Real.log s.m + Real.log ((s.Thi : ℝ) / (10 ^ 30 * s.m)) := by
    have : (0 : ℝ) < s.Thi := by linarith
    rw [← Real.log_mul hm0.ne' (by positivity)]; congr 1; field_simp
  have hl1 : Real.log ((s.Tlo : ℝ) / 10 ^ 30) ≤ Real.log (th x) :=
    Real.log_le_log (by positivity) (by rw [div_le_iff₀ (by norm_num)]; linarith)
  have hl2 : Real.log (th x) ≤ Real.log ((s.Thi : ℝ) / 10 ^ 30) :=
    Real.log_le_log hth0 (by rw [le_div_iff₀ (by norm_num)]; linarith)
  set A := s.Mlo + qLo (10 ^ 30 * s.m) (s.Tlo - 10 ^ 30 * s.m) with hA
  set B := s.Mhi + qHi (10 ^ 30 * s.m) (s.Thi - 10 ^ 30 * s.m) with hB
  have hlo : (A : ℝ) ≤ 10 ^ 30 * Real.log (th x) := by
    rw [hA, Nat.cast_add]
    calc (s.Mlo : ℝ) + (qLo (10 ^ 30 * s.m) (s.Tlo - 10 ^ 30 * s.m) : ℝ)
        ≤ 10 ^ 30 * Real.log s.m + 10 ^ 30 * Real.log ((s.Tlo : ℝ) / (10 ^ 30 * s.m)) :=
          add_le_add hM1 q1
      _ = 10 ^ 30 * Real.log ((s.Tlo : ℝ) / 10 ^ 30) := by rw [hsplit1]; ring
      _ ≤ 10 ^ 30 * Real.log (th x) := mul_le_mul_of_nonneg_left hl1 (by norm_num)
  have hhi : 10 ^ 30 * Real.log (th x) ≤ (B : ℝ) := by
    rw [hB, Nat.cast_add]
    calc 10 ^ 30 * Real.log (th x) ≤ 10 ^ 30 * Real.log ((s.Thi : ℝ) / 10 ^ 30) :=
          mul_le_mul_of_nonneg_left hl2 (by norm_num)
      _ = 10 ^ 30 * Real.log s.m + 10 ^ 30 * Real.log ((s.Thi : ℝ) / (10 ^ 30 * s.m)) := by
          rw [hsplit2]; ring
      _ ≤ (s.Mhi : ℝ) + (qHi (10 ^ 30 * s.m) (s.Thi - 10 ^ 30 * s.m) : ℝ) := add_le_add hM2 q2
  have hlogθ : 0 < Real.log (th x) := Real.log_pos (by
    have : (1 : ℝ) ≤ s.m := by exact_mod_cast hm
    linarith)
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le (by positivity) hhi
  -- the right-hand side
  have hG := Glo_le
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  obtain ⟨f1, -⟩ := floor_div_bounds (Glo * A) (10 ^ 30) (by positivity)
  obtain ⟨f2, -⟩ := floor_div_bounds (250637 * 10 ^ 55) B (by exact_mod_cast hB0)
  have hR1 : ((Glo * A / 10 ^ 30 : ℕ) : ℝ) ≤
      10 ^ 30 * (Real.exp eulerMascheroniConstant * Real.log (th x)) := by
    refine f1.trans ?_
    rw [div_le_iff₀ (by positivity), Nat.cast_mul]
    have := mul_le_mul hG hlo hA0 (by positivity)
    push_cast
    linarith only [this]
  have hR2 : ((250637 * 10 ^ 55 / B : ℕ) : ℝ) ≤ 10 ^ 30 * (2.50637 / Real.log (th x)) := by
    refine f2.trans ?_
    have h1 : ((250637 * 10 ^ 55 : ℕ) : ℝ) / B ≤
        ((250637 * 10 ^ 55 : ℕ) : ℝ) / (10 ^ 30 * Real.log (th x)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hhi
    have h2 : ((250637 * 10 ^ 55 : ℕ) : ℝ) / (10 ^ 30 * Real.log (th x)) =
        10 ^ 30 * (2.50637 / Real.log (th x)) := by
      push_cast; field_simp; norm_num
    linarith
  have hc3 := (Nat.cast_lt (α := ℝ)).2 c3
  rw [Nat.cast_add] at hc3
  unfold Claim
  linarith

/-- The step at a prime `n + 1`, for any advanced `r = (m, log m bounds)`. -/
theorem Inv_stepR {n : ℕ} (hn : 1 ≤ n) {s : PS} (h : Inv n s) (hpr : (n + 1).Prime)
    (r : ℕ × ℕ × ℕ) (a1 : 1 ≤ r.1) (a2 : (r.2.1 : ℝ) ≤ 10 ^ 30 * Real.log r.1)
    (a3 : 10 ^ 30 * Real.log r.1 ≤ r.2.2) (hc : n + 1 < 5 ∨ chk (pstepR n s r) = true) :
    Inv (n + 1) (pstepR n s r) := by
  obtain ⟨l1, l2, t1, t2, f1, m1, m2, m3, hcl⟩ := h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i1, i2⟩ := incr_bounds hn
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
  have hL1 : ((s.Llo + incrLo n : ℕ) : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [hlog]; push_cast; linarith
  have hL2 : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ ((s.Lhi + incrHi n : ℕ) : ℝ) := by
    rw [hlog]; push_cast; linarith
  have hth := th_succ n
  have hFp := Fp_succ n
  rw [if_pos hpr] at hth hFp
  have hT1 : ((s.Tlo + (s.Llo + incrLo n) : ℕ) : ℝ) ≤ 10 ^ 30 * th (n + 1) := by
    rw [hth, Nat.cast_add s.Tlo, mul_add]; linarith
  have hT2 : 10 ^ 30 * th (n + 1) ≤ ((s.Thi + (s.Lhi + incrHi n) : ℕ) : ℝ) := by
    rw [hth, Nat.cast_add s.Thi, mul_add]; linarith
  have hF1 : 10 ^ 30 * Fp (n + 1) ≤ ((cdiv (s.Fhi * (n + 1)) n : ℕ) : ℝ) := by
    refine le_trans ?_ (cdiv_ge _ _ (by omega))
    rw [hFp]
    have e : (((n + 1 : ℕ) : ℝ) - 1) = n := by push_cast; ring
    rw [e]
    push_cast
    rw [← mul_assoc, mul_div_assoc', le_div_iff₀ hn0, div_mul_cancel₀ _ hn0.ne']
    exact mul_le_mul_of_nonneg_right f1 (by positivity)
  refine ⟨hL1, hL2, hT1, hT2, hF1, a1, a2, a3, fun x hx5 hxn hxp => ?_⟩
  rcases Nat.lt_or_ge x (n + 1) with hlt | hge
  · exact hcl x hx5 (by omega) hxp
  · have hxe : x = n + 1 := by omega
    subst hxe
    rcases hc with hc | hc
    · omega
    · exact chk_claim (s := pstepR n s r) hT1 hT2 hF1 a1 a2 a3 hc

theorem Inv_step {n : ℕ} (hn : 1 ≤ n) {s : PS} (h : Inv n s)
    (hc : isP (n + 1) = false ∨ n + 1 < 5 ∨ chk (pstep n s) = true) : Inv (n + 1) (pstep n s) := by
  by_cases hp : isP (n + 1) = true
  · have hpr := (isP_iff _).1 hp
    have hps : pstep n s = pstepR n s (adv 30 (s.Tlo + (s.Llo + incrLo n)) s.m s.Mlo s.Mhi) := by
      unfold pstep pstepP; rw [if_pos hp]
    rw [hps] at hc ⊢
    have hh := h
    obtain ⟨-, -, -, -, -, m1, m2, m3, -⟩ := hh
    obtain ⟨a1, a2, a3⟩ := adv_spec 30 (s.Tlo + (s.Llo + incrLo n)) s.m s.Mlo s.Mhi m1 m2 m3
    refine Inv_stepR hn h hpr _ a1 a2 a3 ?_
    rcases hc with hc | hc
    · rw [hp] at hc; exact absurd hc (by decide)
    · exact hc
  · obtain ⟨l1, l2, t1, t2, f1, m1, m2, m3, hcl⟩ := h
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨i1, i2⟩ := incr_bounds hn
    have hlog : Real.log ((n + 1 : ℕ) : ℝ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
      rw [← Real.log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
    have hL1 : ((s.Llo + incrLo n : ℕ) : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
      rw [hlog]; push_cast; linarith
    have hL2 : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ ((s.Lhi + incrHi n : ℕ) : ℝ) := by
      rw [hlog]; push_cast; linarith
    have hth := th_succ n
    have hFp := Fp_succ n
    have hnp : ¬ (n + 1).Prime := fun h' => hp ((isP_iff _).2 h')
    rw [if_neg hnp] at hth hFp
    have hps : pstep n s = pstepN n s := by unfold pstep; rw [if_neg hp]
    rw [hps]
    unfold pstepN
    refine ⟨hL1, hL2, ?_, ?_, ?_, m1, m2, m3, fun x hx5 hxn hxp => ?_⟩
    · rw [hth, add_zero]; exact t1
    · rw [hth, add_zero]; exact t2
    · rw [hFp, mul_one]; exact f1
    · rcases Nat.lt_or_ge x (n + 1) with hlt | hge
      · exact hcl x hx5 (by omega) hxp
      · have hxe : x = n + 1 := by omega
        subst hxe
        exact absurd hxp hnp

theorem walkP_spec : ∀ (len n : ℕ) (s s' : PS), 1 ≤ n → Inv n s → walkP n len s = some s' →
    Inv (n + len) s' := by
  intro len
  induction len with
  | zero => intro n s s' _ h hw; simp only [walkP, Option.some.injEq] at hw; subst hw; simpa using h
  | succ len ih =>
    intro n s s' hn h hw
    rw [walkP] at hw
    try simp only at hw
    split_ifs at hw with hc
    rw [show n + (len + 1) = n + 1 + len by ring]
    exact ih (n + 1) _ _ (by omega) (Inv_step hn h hc.2) hw

theorem filter_one : (Icc 1 1).filter Nat.Prime = ∅ := by decide

theorem Inv_one : Inv 1 ⟨0, 0, 0, 0, 10 ^ 30, 1, 0, 0⟩ := by
  refine ⟨by simp, by simp, ?_, ?_, ?_, le_rfl, by simp, by simp, fun x h5 h1 _ => by omega⟩
  · unfold th; rw [filter_one]; simp
  · unfold th; rw [filter_one]; simp
  · unfold Fp; rw [filter_one]; norm_num

theorem wk_1 : walkP 1 999 ⟨0, 0, 0, 0, 1000000000000000000000000000000, 1, 0, 0⟩ = some ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 956245265120041185057801216681779, 956245265120064978670464274002504, 12350975673851661433752563348540, 956, 6862757913051296031304299359206, 6862757913051437659953501090768⟩ := by decide +kernel
theorem wk_2 : walkP 1000 1000 ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 956245265120041185057801216681779, 956245265120064978670464274002504, 12350975673851661433752563348540, 956, 6862757913051296031304299359206, 6862757913051437659953501090768⟩ = some ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 1939839200302529137722656397952172, 1939839200302572051202961689967986, 13573750018230555889558589728144, 1939, 7569927655242546550481421812974, 7569927655242688179130623557315⟩ := by decide +kernel
theorem wk_3 : walkP 2000 1000 ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 1939839200302529137722656397952172, 1939839200302572051202961689967986, 13573750018230555889558589728144, 1939, 7569927655242546550481421812974, 7569927655242688179130623557315⟩ = some ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 2932359211878681560809477014706588, 2932359211878742461128230929170469, 14292705320286832607211284089042, 2932, 7983440063006436856610284459685, 7983440063006578485259486216935⟩ := by decide +kernel
theorem wk_4 : walkP 3000 1000 ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 2932359211878681560809477014706588, 2932359211878742461128230929170469, 14292705320286832607211284089042, 2932, 7983440063006436856610284459685, 7983440063006578485259486216935⟩ = some ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 3911145399581146234184563977051654, 3911145399581224129941222103267507, 14794980092780920480403729936233, 3911, 8271548374755408864918456900448, 8271548374755550493567658670425⟩ := by decide +kernel
theorem wk_5 : walkP 4000 1000 ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 3911145399581146234184563977051654, 3911145399581224129941222103267507, 14794980092780920480403729936233, 3911, 8271548374755408864918456900448, 8271548374755550493567658670425⟩ = some ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 4911695351706793129045591750696542, 4911695351706887878611504888439518, 15193938509953073002604175149013, 4911, 8499232866039139340202225931599, 8499232866039280968851427714576⟩ := by decide +kernel
theorem wk_6 : walkP 5000 1000 ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 4911695351706793129045591750696542, 4911695351706887878611504888439518, 15193938509953073002604175149013, 4911, 8499232866039139340202225931599, 8499232866039280968851427714576⟩ = some ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 5893297457247982535544997772414871, 5893297457248093430776919914284897, 15513240551838087406167217410743, 5893, 8681520484837808090311598267942, 8681520484837949718960800063685⟩ := by decide +kernel
theorem wk_7 : walkP 6000 1000 ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 5893297457247982535544997772414871, 5893297457248093430776919914284897, 15513240551838087406167217410743, 5893, 8681520484837808090311598267942, 8681520484837949718960800063685⟩ = some ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 6920421029943578693429679087107379, 6920421029943706159213557840005664, 15795529761036456458107752562449, 6920, 8842171048611609995292627596117, 8842171048611751623941829405211⟩ := by decide +kernel
theorem wk_8 : walkP 7000 1000 ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 6920421029943578693429679087107379, 6920421029943706159213557840005664, 15795529761036456458107752562449, 6920, 8842171048611609995292627596117, 8842171048611751623941829405211⟩ = some ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 7875150384797318841402588918268461, 7875150384797461461451932265554319, 16022658793765949879912368357066, 7875, 8971448463693728557204792725168, 8971448463693870185853994546677⟩ := by decide +kernel
theorem wk_9 : walkP 8000 1000 ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 7875150384797318841402588918268461, 7875150384797461461451932265554319, 16022658793765949879912368357066, 7875, 8971448463693728557204792725168, 8971448463693870185853994546677⟩ = some ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 8870374992657703076233879134508550, 8870374992657861275434634683057060, 16231557913277557526140618061403, 8870, 9090430075303519919927711613621, 9090430075303661548576913448065⟩ := by decide +kernel
theorem wk_10 : walkP 9000 1000 ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 8870374992657703076233879134508550, 8870374992657861275434634683057060, 16231557913277557526140618061403, 8870, 9090430075303519919927711613621, 9090430075303661548576913448065⟩ = some ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 9895991379156857954896927845751462, 9895991379157032016506394000656858, 16424489632190082652598750113685, 9895, 9199784858036560847269531442029, 9199784858036702475918733289798⟩ := by decide +kernel
theorem wk_11 : walkP 10000 1000 ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 9895991379156857954896927845751462, 9895991379157032016506394000656858, 16424489632190082652598750113685, 9895, 9199784858036560847269531442029, 9199784858036702475918733289798⟩ = some ⟨9305650551780402341622589444417, 9305650551780543970271791306551, 10877341630469408712480218853540655, 10877341630469597786726500405132725, 16591396345718166430766667106024, 10877, 9294405747093745015591208635131, 9294405747093886644240410495666⟩ := by decide +kernel
theorem wk_12 : walkP 11000 1000 ⟨9305650551780402341622589444417, 9305650551780543970271791306551, 10877341630469408712480218853540655, 10877341630469597786726500405132725, 16591396345718166430766667106024, 10877, 9294405747093745015591208635131, 9294405747093886644240410495666⟩ = some ⟨9392661928770032107790355344703, 9392661928770173736439557219837, 11840485753872092189936240972598197, 11840485753872295851933390316677106, 16740598896265369369201550347168, 11840, 9379238908437891420978919234058, 9379238908438033049628121107112⟩ := by decide +kernel
theorem wk_13 : walkP 12000 1000 ⟨9392661928770032107790355344703, 9392661928770173736439557219837, 11840485753872092189936240972598197, 11840485753872295851933390316677106, 16740598896265369369201550347168, 11840, 9379238908437891420978919234058, 9379238908438033049628121107112⟩ = some ⟨9472704636443568533614133304897, 9472704636443710162263335193031, 12868728097423735358580478510330948, 12868728097423954458100390859511304, 16887268936263214245420751085592, 12868, 9462498888358811711779225197196, 9462498888358953340428427083614⟩ := by decide +kernel
theorem wk_14 : walkP 13000 1000 ⟨9472704636443568533614133304897, 9472704636443710162263335193031, 12868728097423735358580478510330948, 12868728097423954458100390859511304, 16887268936263214245420751085592, 12868, 9462498888358811711779225197196, 9462498888358953340428427083614⟩ = some ⟨9546812608597290412083230726710, 9546812608597432040732432627844, 13867292527692335367030028700651706, 13867292527692569337558107248767319, 17019203430389799538683218913866, 13867, 9537267195753758980363364131641, 9537267195753900609012566031046⟩ := by decide +kernel
theorem wk_15 : walkP 14000 1000 ⟨9546812608597290412083230726710, 9546812608597432040732432627844, 13867292527692335367030028700651706, 13867292527692569337558107248767319, 17019203430389799538683218913866, 13867, 9537267195753758980363364131641, 9537267195753900609012566031046⟩ = some ⟨9615805480084241863556650430424, 9615805480084383492205852344558, 14844791692165104101792976519992357, 14844791692165352518443273662717552, 17139202096899285735594265291104, 14844, 9605351022180382955169606070807, 9605351022180524583818807982913⟩ := by decide +kernel
theorem wk_16 : walkP 15000 1000 ⟨9615805480084241863556650430424, 9615805480084383492205852344558, 14844791692165104101792976519992357, 14844791692165352518443273662717552, 17139202096899285735594265291104, 14844, 9605351022180382955169606070807, 9605351022180524583818807982913⟩ = some ⟨9680344001221813035229574344616, 9680344001221954663878776271750, 15886792468421075601943335383136468, 15886792468421339314487746333284103, 17259117036680770222905980731817, 15886, 9673193497192972113851829169266, 9673193497193113742501031094918⟩ := by decide +kernel
theorem wk_17 : walkP 16000 1000 ⟨9680344001221813035229574344616, 9680344001221954663878776271750, 15886792468421075601943335383136468, 15886792468421339314487746333284103, 17259117036680770222905980731817, 15886, 9673193497192972113851829169266, 9673193497193113742501031094918⟩ = some ⟨9740968623038247877810180475156, 9740968623038389506459382415290, 16838472455535699058768888695707996, 16838472455535976650920921435353115, 17361960193246478827482998389278, 16838, 9731393515897504043397815833643, 9731393515897645672047017771671⟩ := by decide +kernel
theorem wk_18 : walkP 17000 1000 ⟨9740968623038247877810180475156, 9740968623038389506459382415290, 16838472455535699058768888695707996, 16838472455535976650920921435353115, 17361960193246478827482998389278, 16838, 9731393515897504043397815833643, 9731393515897645672047017771671⟩ = some ⟨9798127036878196489768368451090, 9798127036878338118417570404224, 17854574994286053279939995767937295, 17854574994286345601471545510041814, 17465437430840249850898365021003, 17854, 9789982851739202117678980648508, 9789982851739343746328182599744⟩ := by decide +kernel
theorem wk_19 : walkP 18000 1000 ⟨9798127036878196489768368451090, 9798127036878338118417570404224, 17854574994286053279939995767937295, 17854574994286345601471545510041814, 17465437430840249850898365021003, 17854, 9789982851739202117678980648508, 9789982851739343746328182599744⟩ = some ⟨9852194258148472257569673286171, 9852194258148613886218875252305, 18777952331436118539016720125187880, 18777952331436424173641294851447191, 17554630089268333015627634402718, 18777, 9840387995592705901946045114838, 9840387995592847530595247078073⟩ := by decide +kernel
theorem wk_20 : walkP 19000 1000 ⟨9852194258148472257569673286171, 9852194258148613886218875252305, 18777952331436118539016720125187880, 18777952331436424173641294851447191, 17554630089268333015627634402718, 18777, 9840387995592705901946045114838, 9840387995592847530595247078073⟩ = some ⟨9903487552536022790995869428895, 9903487552536164419645071408029, 19805309624307629247228627352260355, 19805309624307949611232719083683508, 17648492637505432660762838770836, 19805, 9893689710055911765659190314765, 9893689710056053394308392291364⟩ := by decide +kernel
theorem wk_21 : walkP 20000 1000 ⟨9903487552536022790995869428895, 9903487552536164419645071408029, 19805309624307629247228627352260355, 19805309624307949611232719083683508, 17648492637505432660762838770836, 19805, 9893689710055911765659190314765, 9893689710056053394308392291364⟩ = some ⟨9952277716705454794061243831594, 9952277716705596422710445823728, 20778193058130709664326966098860664, 20778193058131043907938679624857749, 17733141359621799525824365376609, 20778, 9941650013630371708020841681234, 9941650013630513336670043670482⟩ := by decide +kernel
theorem wk_22 : walkP 21000 1000 ⟨9952277716705454794061243831594, 9952277716705596422710445823728, 20778193058130709664326966098860664, 20778193058131043907938679624857749, 17733141359621799525824365376609, 20778, 9941650013630371708020841681234, 9941650013630513336670043670482⟩ = some ⟨9998797732340347651039821549134, 9998797732340489279689023554268, 21815610747470111763360210788524199, 21815610747470460736351441322363282, 17819192842429500474687766640023, 21815, 9990353085557604725132378230179, 9990353085557746353781580232908⟩ := by decide +kernel
theorem wk_23 : walkP 22000 1000 ⟨9998797732340347651039821549134, 9998797732340489279689023554268, 21815610747470111763360210788524199, 21815610747470460736351441322363282, 17819192842429500474687766640023, 21815, 9990353085557604725132378230179, 9990353085557746353781580232908⟩ = some ⟨10043249494911181488367398680012, 10043249494911323117016600698146, 22817635724195170854561128385106668, 22817635724195533990417279120081773, 17898655247210210886367583399828, 22817, 10035261151145465015972858028895, 10035261151145606644622060044650⟩ := by decide +kernel
theorem wk_24 : walkP 23000 1000 ⟨10043249494911181488367398680012, 10043249494911323117016600698146, 22817635724195170854561128385106668, 22817635724195533990417279120081773, 17898655247210210886367583399828, 22817, 10035261151145465015972858028895, 10035261151145606644622060044650⟩ = some ⟨10085809109329977417207587448011, 10085809109330119045856789479145, 23864331538659962301821130152319550, 23864331538660340167056797897847361, 17978079775495337918038856985620, 23864, 10080126326194479191191840515537, 10080126326194620819841042544903⟩ := by decide +kernel
theorem wk_25 : walkP 24000 1000 ⟨10085809109329977417207587448011, 10085809109330119045856789479145, 23864331538659962301821130152319550, 23864331538660340167056797897847361, 17978079775495337918038856985620, 23864, 10080126326194479191191840515537, 10080126326194620819841042544903⟩ = some ⟨10126631103850232546762164511661, 10126631103850374175411366555795, 24814245437040723505859209433366121, 24814245437041114684187902170405112, 18047262858570956076189996812999, 24814, 10119163289002711576345882105981, 10119163289002853204995084147697⟩ := by decide +kernel
theorem wk_26 : walkP 25000 1000 ⟨10126631103850232546762164511661, 10126631103850374175411366555795, 24814245437040723505859209433366121, 24814245437041114684187902170405112, 18047262858570956076189996812999, 24814, 10119163289002711576345882105981, 10119163289002853204995084147697⟩ = some ⟨10165851817003513843031365406771, 10165851817003655471680567463905, 25808635507716280892652931211781799, 25808635507716685950589245749798106, 18116732098822771102556694914710, 25808, 10158439800364884844679316305461, 10158439800365026473328518360099⟩ := by decide +kernel
theorem wk_27 : walkP 26000 1000 ⟨10165851817003513843031365406771, 10165851817003655471680567463905, 25808635507716280892652931211781799, 25808635507716685950589245749798106, 18116732098822771102556694914710, 25808, 10158439800364884844679316305461, 10158439800365026473328518360099⟩ = some ⟨10203592144986360871746381552992, 10203592144986502500395583623126, 26837348714082415704276855786970604, 26837348714082835066706739733429220, 18185891686112329328272245648229, 26837, 10197536811365963549057588344131, 10197536811366105177706790412146⟩ := by decide +kernel
theorem wk_28 : walkP 27000 1000 ⟨10203592144986360871746381552992, 10203592144986502500395583623126, 26837348714082415704276855786970604, 26837348714082835066706739733429220, 18185891686112329328272245648229, 26837, 10197536811365963549057588344131, 10197536811366105177706790412146⟩ = some ⟨10239959789157235721500462827090, 10239959789157377350149664910224, 27798293923604116436279747036371002, 27798293923604549111802655978064726, 18248110562048748137817125502668, 27798, 10232719354644598118768043702025, 10232719354644739747417245782533⟩ := by decide +kernel
theorem wk_29 : walkP 28000 1000 ⟨10239959789157235721500462827090, 10239959789157377350149664910224, 27798293923604116436279747036371002, 27798293923604549111802655978064726, 18248110562048748137817125502668, 27798, 10232719354644598118768043702025, 10232719354644739747417245782533⟩ = some ⟨10275051108968505824743917871600, 10275051108968647453393119967734, 28803557736131767501019367308615266, 28803557736132214056149898055099700, 18310962016413661313851354667287, 28803, 10268234827365628218655575513991, 10268234827365769847304777607564⟩ := by decide +kernel
theorem wk_30 : walkP 29000 1000 ⟨10275051108968505824743917871600, 10275051108968647453393119967734, 28803557736131767501019367308615266, 28803557736132214056149898055099700, 18310962016413661313851354667287, 28803, 10268234827365628218655575513991, 10268234827365769847304777607564⟩ = some ⟨10308952660644187172973882529344, 10308952660644328801623084638478, 29750341743931991044119182450100094, 29750341743932450629085439789992718, 18368218366862861875764825000480, 29750, 10300584410973670564081068956505, 10300584410973812192730271062389⟩ := by decide +kernel
theorem wk_31 : walkP 30000 1000 ⟨10308952660644187172973882529344, 10308952660644328801623084638478, 29750341743931991044119182450100094, 29750341743932450629085439789992718, 18368218366862861875764825000480, 29750, 10300584410973670564081068956505, 10300584410973812192730271062389⟩ = some ⟨10341742483467178043489810160793, 10341742483467319672139012282927, 30731246027007697700759929751507393, 30731246027008170740447861292380424, 18425533578140496023519087079822, 30731, 10333027196085362532528237247711, 10333027196085504161177439366348⟩ := by decide +kernel
theorem wk_32 : walkP 31000 1000 ⟨10341742483467178043489810160793, 10341742483467319672139012282927, 30731246027007697700759929751507393, 30731246027008170740447861292380424, 18425533578140496023519087079822, 30731, 10333027196085362532528237247711, 10333027196085504161177439366348⟩ = some ⟨10373491181781758344646806442015, 10373491181781899973296008577149, 31684046410867523262965220864863097, 31684046410868009332488879001526152, 18479495247571093131345647408013, 31684, 10363567100584065040976766795427, 10363567100584206669625968926453⟩ := by decide +kernel
theorem wk_33 : walkP 32000 1000 ⟨10373491181781758344646806442015, 10373491181781899973296008577149, 31684046410867523262965220864863097, 31684046410868009332488879001526152, 18479495247571093131345647408013, 31684, 10363567100584065040976766795427, 10363567100584206669625968926453⟩ = some ⟨10404262840448512033017834648112, 10404262840448653661667036796246, 32785251380575740134134323026735285, 32785251380576241216294796590401300, 18539884888822858052853417314885, 32785, 10397726372697614537755848567499, 10397726372697756166405050712838⟩ := by decide +kernel
theorem wk_34 : walkP 33000 1000 ⟨10404262840448512033017834648112, 10404262840448653661667036796246, 32785251380575740134134323026735285, 32785251380576241216294796590401300, 18539884888822858052853417314885, 32785, 10397726372697614537755848567499, 10397726372697756166405050712838⟩ = some ⟨10434115803598193187227412571042, 10434115803598334815876614732176, 33827185146329436336742227397943290, 33827185146329951581767621177075825, 18595311217555972636794581792160, 33827, 10429014579154906198538713805269, 10429014579155047827187915964154⟩ := by decide +kernel
theorem wk_35 : walkP 34000 1000 ⟨10434115803598193187227412571042, 10434115803598334815876614732176, 33827185146329436336742227397943290, 33827185146329951581767621177075825, 18595311217555972636794581792160, 33827, 10429014579154906198538713805269, 10429014579155047827187915964154⟩ = some ⟨10463103340471445477266757906889, 10463103340471587105915960081023, 34809363631338296358353134973531766, 34809363631338824916471553756422885, 18646048458757435157439240917585, 34809, 10457631253015549865414667223209, 10457631253015691494063869394860⟩ := by decide +kernel
theorem wk_36 : walkP 35000 1000 ⟨10463103340471445477266757906889, 10463103340471587105915960081023, 34809363631338296358353134973531766, 34809363631338824916471553756422885, 18646048458757435157439240917585, 34809, 10457631253015549865414667223209, 10457631253015691494063869394860⟩ = some ⟨10491274217438141799185600545519, 10491274217438283427834802732653, 35773269616072639623775615339006549, 35773269616073181211729760722515398, 18694438029827971008317643800488, 35773, 10484948697900240456729810494650, 10484948697900382085379012678833⟩ := by decide +kernel
theorem wk_37 : walkP 36000 1000 ⟨10491274217438141799185600545519, 10491274217438283427834802732653, 35773269616072639623775615339006549, 35773269616073181211729760722515398, 18694438029827971008317643800488, 35773, 10484948697900240456729810494650, 10484948697900382085379012678833⟩ = some ⟨10518673191626256241928741498308, 10518673191626397870577943698442, 36813320098893925345363757637620188, 36813320098894480954554174038323438, 18745189557459863590869679213161, 36813, 10513606322644552240575450706086, 10513606322644693869224652903789⟩ := by decide +kernel
theorem wk_38 : walkP 37000 1000 ⟨10518673191626256241928741498308, 10518673191626397870577943698442, 36813320098893925345363757637620188, 36813320098894480954554174038323438, 18745189557459863590869679213161, 36813, 10513606322644552240575450706086, 10513606322644693869224652903789⟩ = some ⟨10545341438708417566986905379121, 10545341438708559195636107592255, 37803336694988822694251186489172069, 37803336694989391616534627897300033, 18792238666243816584930296321358, 37803, 10540143743537697595724463517167, 10540143743537839224373665727740⟩ := by decide +kernel
theorem wk_39 : walkP 38000 1000 ⟨10545341438708417566986905379121, 10545341438708559195636107592255, 37803336694988822694251186489172069, 37803336694989391616534627897300033, 18792238666243816584930296321358, 37803, 10540143743537697595724463517167, 10540143743537839224373665727740⟩ = some ⟨10571316925111678225009378502774, 10571316925111819853658580728908, 38753652264104901990361686685723621, 38753652264105483659223556293649065, 18836193170104376041573977900492, 38753, 10564963451139502925718972553334, 10564963451139644554368174776257⟩ := by decide +kernel
theorem wk_40 : walkP 39000 1000 ⟨10571316925111678225009378502774, 10571316925111819853658580728908, 38753652264104901990361686685723621, 38753652264105483659223556293649065, 18836193170104376041573977900492, 38753, 10564963451139502925718972553334, 10564963451139644554368174776257⟩ = some ⟨10596634733095968100413101520397, 10596634733096109729062303759531, 39769713423932329378915196394728397, 39769713423932924644127389416983819, 18882033692926987074599376989925, 39769, 10590842993304158050093887982999, 10590842993304299678743090219130⟩ := by decide +kernel
theorem wk_41 : walkP 40000 1000 ⟨10596634733095968100413101520397, 10596634733096109729062303759531, 39769713423932329378915196394728397, 39769713423932924644127389416983819, 18882033692926987074599376989925, 39769, 10590842993304158050093887982999, 10590842993304299678743090219130⟩ = some ⟨10621327345686339601427409194326, 10621327345686481230076611446460, 40703322413734975747067665542731792, 40703322413735583475600988362610520, 18923101934687245143915394902726, 40703, 10614057078787837178373521490701, 10614057078787978807022723738974⟩ := by decide +kernel
theorem wk_42 : walkP 41000 1000 ⟨10621327345686339601427409194326, 10621327345686481230076611446460, 40703322413734975747067665542731792, 40703322413735583475600988362610520, 18923101934687245143915394902726, 40703, 10614057078787837178373521490701, 10614057078787978807022723738974⟩ = some ⟨10645424897265400103478475921615, 10645424897265541732127678186749, 41777314385235059564258941855850219, 41777314385235681597285834103859730, 18969207323759810956608125059732, 41777, 10640101227841131442615408637655, 10640101227841273071264610899890⟩ := by decide +kernel
theorem wk_43 : walkP 42000 1000 ⟨10645424897265400103478475921615, 10645424897265541732127678186749, 41777314385235059564258941855850219, 41777314385235681597285834103859730, 18969207323759810956608125059732, 41777, 10640101227841131442615408637655, 10640101227841273071264610899890⟩ = some ⟨10668955394675594221033488331625, 10668955394675735849682690609759, 42864348819748854516464872987472208, 42864348819749490995613983867186307, 19014792335629893768540288296312, 42864, 10665787591784284721400823278854, 10665787591784426350050025555220⟩ := by decide +kernel
theorem wk_44 : walkP 43000 1000 ⟨10668955394675594221033488331625, 10668955394675735849682690609759, 42864348819748854516464872987472208, 42864348819749490995613983867186307, 19014792335629893768540288296312, 42864, 10665787591784284721400823278854, 10665787591784426350050025555220⟩ = some ⟨10691944912900292960457053637669, 10691944912900434589106255928803, 43772227664512208892924404973609985, 43772227664512857410508698047538865, 19051969980214278842041344667661, 43772, 10686749622538228377666020137719, 10686749622538370006315222425889⟩ := by decide +kernel
theorem wk_45 : walkP 44000 1000 ⟨10691944912900292960457053637669, 10691944912900434589106255928803, 43772227664512208892924404973609985, 43772227664512857410508698047538865, 19051969980214278842041344667661, 43772, 10686749622538228377666020137719, 10686749622538370006315222425889⟩ = some ⟨10714417768752351554951895622355, 10714417768752493183601097926489, 44799737827000986426827685072508907, 44799737827001648540762301567011119, 19093117155948789230260433590950, 44799, 10709941096725273052594423268652, 10709941096725414681243625570173⟩ := by decide +kernel
theorem wk_46 : walkP 45000 1000 ⟨10714417768752351554951895622355, 10714417768752493183601097926489, 44799737827000986426827685072508907, 44799737827001648540762301567011119, 19093117155948789230260433590950, 44799, 10709941096725273052594423268652, 10709941096725414681243625570173⟩ = some ⟨10736396675471126797784630767037, 10736396675471268426433833084171, 45722141344584906727434995185740462, 45722141344585581021433443078966038, 19129234866284973400995907596225, 45722, 10730334861483811077498781698645, 10730334861483952706147984012165⟩ := by decide +kernel
theorem wk_47 : walkP 46000 1000 ⟨10736396675471126797784630767037, 10736396675471268426433833084171, 45722141344584906727434995185740462, 45722141344585581021433443078966038, 19129234866284973400995907596225, 45722, 10730334861483811077498781698645, 10730334861483952706147984012165⟩ = some ⟨10757902880692090384381596482033, 10757902880692232013030798812167, 46689380651138726742758397018788241, 46689380651139413783335273121136171, 19166299965141047059199386711540, 46689, 10751263869873014437854659556240, 10751263869873156066503861882331⟩ := by decide +kernel
theorem wk_48 : walkP 47000 1000 ⟨10757902880692090384381596482033, 10757902880692232013030798812167, 46689380651138726742758397018788241, 46689380651139413783335273121136171, 19166299965141047059199386711540, 46689, 10751263869873014437854659556240, 10751263869873156066503861882331⟩ = some ⟨10778956289889922726624819533524, 10778956289890064355274021876658, 47712415063789690014699741956690884, 47712415063790390509998292281037569, 19204660541237377951347119271320, 47712, 10772938217564359710422884567319, 10772938217564501339072086906709⟩ := by decide +kernel
theorem wk_49 : walkP 48000 1000 ⟨10778956289889922726624819533524, 10778956289890064355274021876658, 47712415063789690014699741956690884, 47712415063790390509998292281037569, 19204660541237377951347119271320, 47712, 10772938217564359710422884567319, 10772938217564501339072086906709⟩ = some ⟨10799575577092658407771351296154, 10799575577092800036420553652288, 48672685592903073744048161362340131, 48672685592903786844296490695818477, 19239926992709937510006395898057, 48672, 10792859195058914147490297409971, 10792859195059055776139499761841⟩ := by decide +kernel
theorem wk_50 : walkP 49000 1000 ⟨10799575577092658407771351296154, 10799575577092800036420553652288, 48672685592903073744048161362340131, 48672685592903786844296490695818477, 19239926992709937510006395898057, 48672, 10792859195058914147490297409971, 10792859195059055776139499761841⟩ = some ⟨10819778284410177856179396595709, 10819778284410319484828598964843, 49732018402956314603630354987867840, 49732018402957041583486306152872228, 19278064951716576450112944812727, 49732, 10814403868072722922052541215509, 10814403868072864550701743581159⟩ := by decide +kernel
theorem wk_51 : walkP 50000 1000 ⟨10819778284410177856179396595709, 10819778284410319484828598964843, 49732018402956314603630354987867840, 49732018402957041583486306152872228, 19278064951716576450112944812727, 49732, 10814403868072722922052541215509, 10814403868072864550701743581159⟩ = some ⟨10839580911706357569205425661089, 10839580911706499197854628043223, 50695834529702683146551768959337524, 50695834529703422731357499135754839, 19312082403890598740687418825093, 50695, 10833582565386574912337843277952, 10833582565386716540987045656121⟩ := by decide +kernel
theorem wk_52 : walkP 51000 1000 ⟨10839580911706357569205425661089, 10839580911706499197854628043223, 50695834529702683146551768959337524, 50695834529703422731357499135754839, 19312082403890598740687418825093, 50695, 10833582565386574912337843277952, 10833582565386716540987045656121⟩ = some ⟨10858998997563459152448597489285, 10858998997563600781097799884419, 51748240161189245860635291303182488, 51748240161189999183419994111311588, 19348484286624653458290459894835, 51748, 10854141063037687280946049049773, 10854141063037828909595251441631⟩ := by decide +kernel
theorem wk_53 : walkP 52000 1000 ⟨10858998997563459152448597489285, 10858998997563600781097799884419, 51748240161189245860635291303182488, 51748240161189999183419994111311588, 19348484286624653458290459894835, 51748, 10854141063037687280946049049773, 10854141063037828909595251441631⟩ = some ⟨10878047192534153631705114942352, 10878047192534295260354317350486, 52715565259274268424676359122089426, 52715565259275034352410840943980267, 19381304912518766684604548130059, 52715, 10872655324010944777361298888206, 10872655324011086406010501292635⟩ := by decide +kernel
theorem wk_54 : walkP 53000 1000 ⟨10878047192534153631705114942352, 10878047192534295260354317350486, 52715565259274268424676359122089426, 52715565259275034352410840943980267, 19381304912518766684604548130059, 52715, 10872655324010944777361298888206, 10872655324011086406010501292635⟩ = some ⟨10896739325546306181163613634034, 10896739325546447809812816055168, 53717212172339203445182548248706763, 53717212172339982402752756692746766, 19414662004476298519534137852548, 53717, 10891484803954812422162086725352, 10891484803954954050811289142807⟩ := by decide +kernel
theorem wk_55 : walkP 54000 1000 ⟨10896739325546306181163613634034, 10896739325546447809812816055168, 53717212172339203445182548248706763, 53717212172339982402752756692746766, 19414662004476298519534137852548, 53717, 10891484803954812422162086725352, 10891484803954954050811289142807⟩ = some ⟨10915088464214502716223348711498, 10915088464214644344872551145632, 54698749591139355623882855672487058, 54698749591140147328031492335015915, 19446749614048637133102026520516, 54698, 10909582424670223945112899562649, 10909582424670365573762101992857⟩ := by decide +kernel
theorem wk_56 : walkP 55000 1000 ⟨10915088464214502716223348711498, 10915088464214644344872551145632, 54698749591139355623882855672487058, 54698749591140147328031492335015915, 19446749614048637133102026520516, 54698, 10909582424670223945112899562649, 10909582424670365573762101992857⟩ = some ⟨10933106969717181030917694906639, 10933106969717322659566897353773, 55714725386084185571025707707716462, 55714725386084990446638720197247538, 19479353270406670492083779880043, 55714, 10927986740832133109920484406584, 10927986740832274738569686850000⟩ := by decide +kernel
theorem wk_57 : walkP 56000 1000 ⟨10933106969717181030917694906639, 10933106969717322659566897353773, 55714725386084185571025707707716462, 55714725386084990446638720197247538, 19479353270406670492083779880043, 55714, 10927986740832133109920484406584, 10927986740832274738569686850000⟩ = some ⟨10950806546816581948964918466149, 10950806546816723577614120926283, 56798034128668319659940573243466365, 56798034128669138556789856775945752, 19513498252295803158614445369127, 56798, 10947256392821600593704085750892, 10947256392821742222353288208400⟩ := by decide +kernel
theorem wk_58 : walkP 57000 1000 ⟨10950806546816581948964918466149, 10950806546816723577614120926283, 56798034128668319659940573243466365, 56798034128669138556789856775945752, 19513498252295803158614445369127, 56798, 10947256392821600593704085750892, 10947256392821742222353288208400⟩ = some ⟨10968198289528451134161149949651, 10968198289528592762810352422785, 57795352332064112067468046721904137, 57795352332064943852524407678848089, 19544405570434135109665986760948, 57795, 10964657545728262398320236074060, 10964657545728404026969438544529⟩ := by decide +kernel
theorem wk_59 : walkP 58000 1000 ⟨10968198289528451134161149949651, 10968198289528592762810352422785, 57795352332064112067468046721904137, 57795352332064943852524407678848089, 19544405570434135109665986760948, 57795, 10964657545728262398320236074060, 10964657545728404026969438544529⟩ = some ⟨10985292722887751248176696168074, 10985292722887892876825898654208, 58783229709792545743261619069605681, 58783229709793390274896408249692461, 19574508711639954620178587634693, 58783, 10981607976438368808619005728172, 10981607976438510437268208211485⟩ := by decide +kernel
theorem wk_60 : walkP 59000 1000 ⟨10985292722887751248176696168074, 10985292722887892876825898654208, 58783229709792545743261619069605681, 58783229709793390274896408249692461, 19574508711639954620178587634693, 58783, 10981607976438368808619005728172, 10981607976438510437268208211485⟩ = some ⟨11002099841204132482391114605923, 11002099841204274111040317105057, 59816575291537034055304060750318863, 59816575291537891900031874964663657, 19605479684974584900703924659301, 59816, 10999028462679646216524290351370, 10999028462679787845173492848112⟩ := by decide +kernel
theorem wk_61 : walkP 60000 1000 ⟨11002099841204132482391114605923, 11002099841204274111040317105057, 59816575291537034055304060750318863, 59816575291537891900031874964663657, 19605479684974584900703924659301, 59816, 10999028462679646216524290351370, 10999028462679787845173492848112⟩ = some ⟨11018629143155343046312034894785, 11018629143155484674961237406919, 60785485354001141753653905376298367, 60785485354002012061702849411135807, 19634019691242620242485855593434, 60785, 11015098326989789072781743244126, 11015098326989930701430945753465⟩ := by decide +kernel
theorem wk_62 : walkP 61000 1000 ⟨11018629143155343046312034894785, 11018629143155484674961237406919, 60785485354001141753653905376298367, 60785485354002012061702849411135807, 19634019691242620242485855593434, 60785, 11015098326989789072781743244126, 11015098326989930701430945753465⟩ = some ⟨11034889664027123352907042235866, 11034889664027264981556244761000, 61744833473319631434973717118807219, 61744833473320514064715141772780286, 19661809330393870531419424615553, 61744, 11030752083777294738438516106738, 11030752083777436367087718628544⟩ := by decide +kernel
theorem wk_63 : walkP 62000 1000 ⟨11034889664027123352907042235866, 11034889664027264981556244761000, 61744833473319631434973717118807219, 61744833473320514064715141772780286, 19661809330393870531419424615553, 61744, 11030752083777294738438516106738, 11030752083777436367087718628544⟩ = some ⟨11050890005373564485456489005642, 11050890005373706114105691543776, 62716613550026775932643794370743677, 62716613550027671025706348847503760, 19689512266374749559348515492637, 62716, 11046371877480235803947223726853, 11046371877480377432596426261295⟩ := by decide +kernel
theorem wk_64 : walkP 63000 1000 ⟨11050890005373564485456489005642, 11050890005373706114105691543776, 62716613550026775932643794370743677, 62716613550027671025706348847503760, 19689512266374749559348515492637, 62716, 11046371877480235803947223726853, 11046371877480377432596426261295⟩ = some ⟨11066638362341703654064038515584, 11066638362341845282713241066718, 63745100672228584816901680463088279, 63745100672229493081428610776515795, 19718364519355677615665794074809, 63745, 11062646028572117372929790869668, 11062646028572259001578993417487⟩ := by decide +kernel
theorem wk_65 : walkP 64000 1000 ⟨11066638362341703654064038515584, 11066638362341845282713241066718, 63745100672228584816901680463088279, 63745100672229493081428610776515795, 19718364519355677615665794074809, 63745, 11062646028572117372929790869668, 11062646028572259001578993417487⟩ = some ⟨11082142548877668908214892560138, 11082142548877810536864095124272, 64631051757883529662009656792068096, 64631051757884449256828523310104876, 19742837801167498457666273397009, 64631, 11076449450827835954291579524374, 11076449450827977582940782083711⟩ := by decide +kernel
theorem wk_66 : walkP 65000 1000 ⟨11082142548877668908214892560138, 11082142548877810536864095124272, 64631051757883529662009656792068096, 64631051757884449256828523310104876, 19742837801167498457666273397009, 64631, 11076449450827835954291579524374, 11076449450827977582940782083711⟩ = some ⟨11097410021008457342435066720200, 11097410021008598971084269297334, 65717846387065822660776399278326507, 65717846387066756135202887648280869, 19772401230090627106153008209230, 65717, 11093112922904684177339468051323, 11093112922904825805988670624778⟩ := by decide +kernel
theorem wk_67 : walkP 66000 1000 ⟨11097410021008457342435066720200, 11097410021008598971084269297334, 65717846387065822660776399278326507, 65717846387066756135202887648280869, 19772401230090627106153008209230, 65717, 11093112922904684177339468051323, 11093112922904825805988670624778⟩ = some ⟨11112447898372997857230717778718, 11112447898373139485879920368852, 66650688600796707343087120891566775, 66650688600797652714320142278569377, 19797385412765465453048009575777, 66650, 11107210325606749473527429044637, 11107210325606891102176631630221⟩ := by decide +kernel
theorem wk_68 : walkP 67000 1000 ⟨11112447898372997857230717778718, 11112447898373139485879920368852, 66650688600796707343087120891566775, 66650688600797652714320142278569377, 19797385412765465453048009575777, 66650, 11107210325606749473527429044637, 11107210325606891102176631630221⟩ = some ⟨11127262984158138496644644641645, 11127262984158280125293847244779, 67751566283086189744021946220316264, 67751566283087149136491238664394589, 19826440645074276442518168440828, 67751, 11123594498780513648108815290299, 11123594498780655276758017890196⟩ := by decide +kernel
theorem wk_69 : walkP 68000 1000 ⟨11127262984158138496644644641645, 11127262984158280125293847244779, 67751566283086189744021946220316264, 67751566283087149136491238664394589, 19826440645074276442518168440828, 67751, 11123594498780513648108815290299, 11123594498780655276758017890196⟩ = some ⟨11141861783579291179762643848102, 11141861783579432808411846464236, 68642357960872817186326831524693734, 68642357960873787909088060177565243, 19849602386334015617018092722880, 68642, 11136659871266386611419474886658, 11136659871266528240068677498138⟩ := by decide +kernel
theorem wk_70 : walkP 69000 1000 ⟨11141861783579291179762643848102, 11141861783579432808411846464236, 68642357960872817186326831524693734, 68642357960873787909088060177565243, 19849602386334015617018092722880, 68642, 11136659871266386611419474886658, 11136659871266528240068677498138⟩ = some ⟨11156250521031390786683989976007, 11156250521031532415333192605141, 69545412324660232429117879984078193, 69545412324661214623799694049364479, 19872756399091077165152947541804, 69545, 11149729304041125273519771251891, 11149729304041266902168973875110⟩ := by decide +kernel
theorem wk_71 : walkP 70000 1000 ⟨11156250521031390786683989976007, 11156250521031532415333192605141, 69545412324660232429117879984078193, 69545412324661214623799694049364479, 19872756399091077165152947541804, 69545, 11149729304041125273519771251891, 11149729304041266902168973875110⟩ = some ⟨11170435156023347218890100308898, 11170435156023488847539302951032, 70639421632610595875718511074200048, 70639421632611591950007946997778622, 19900400819250635654901957360816, 70639, 11165337678892144504140640915111, 11165337678892286132789843552552⟩ := by decide +kernel
theorem wk_72 : walkP 71000 1000 ⟨11170435156023347218890100308898, 11170435156023488847539302951032, 70639421632610595875718511074200048, 70639421632611591950007946997778622, 19900400819250635654901957360816, 70639, 11165337678892144504140640915111, 11165337678892286132789843552552⟩ = some ⟨11184421397998087108602832613103, 11184421397998228737252035268237, 71701303082393625298890208513011907, 71701303082394634827901318688233214, 19926853351281253929402941729691, 71701, 11180259973491742652397404394426, 11180259973491884281046607045673⟩ := by decide +kernel
theorem wk_73 : walkP 72000 1000 ⟨11184421397998087108602832613103, 11184421397998228737252035268237, 71701303082393625298890208513011907, 71701303082394634827901318688233214, 19926853351281253929402941729691, 71701, 11180259973491742652397404394426, 11180259973491884281046607045673⟩ = some ⟨11198214720130422926652754630848, 11198214720130564555301957298982, 72708539285585175465005836950464868, 72708539285586197740595375365248497, 19951601625293896145437125425834, 72708, 11194206698732884108303961970355, 11194206698733025736953164634693⟩ := by decide +kernel
theorem wk_74 : walkP 73000 1000 ⟨11198214720130422926652754630848, 11198214720130564555301957298982, 72708539285585175465005836950464868, 72708539285586197740595375365248497, 19951601625293896145437125425834, 72708, 11194206698732884108303961970355, 11194206698733025736953164634693⟩ = some ⟨11211820372186201551345973564435, 11211820372186343179995176245569, 73638565409193754516820550239413803, 73638565409194788547587972476200049, 19974142948254137791880154163005, 73638, 11206916475825458002990984627515, 11206916475825599631640187303943⟩ := by decide +kernel
theorem wk_75 : walkP 74000 1000 ⟨11211820372186201551345973564435, 11211820372186343179995176245569, 73638565409193754516820550239413803, 73638565409194788547587972476200049, 19974142948254137791880154163005, 73638, 11206916475825458002990984627515, 11206916475825599631640187303943⟩ = some ⟨11225243392518342238157409673823, 11225243392518483866806612367957, 74670660374385365143054944228818168, 74670660374386412203658093112855718, 19998827814657769766613193785455, 74670, 11220833684029642125078359541551, 11220833684029783753727562231395⟩ := by decide +kernel
theorem wk_76 : walkP 75000 1000 ⟨11225243392518342238157409673823, 11225243392518483866806612367957, 74670660374385365143054944228818168, 74670660374386412203658093112855718, 19998827814657769766613193785455, 74670, 11220833684029642125078359541551, 11220833684029783753727562231395⟩ = some ⟨11238488619268362876404137443767, 11238488619268504505053340150901, 75692767608092593893551044313857873, 75692767608093653842361270643659084, 20022945785633448565378785251102, 75692, 11234427753523835778381004731103, 11234427753523977407030207434233⟩ := by decide +kernel
theorem wk_77 : walkP 76000 1000 ⟨11238488619268362876404137443767, 11238488619268504505053340150901, 75692767608092593893551044313857873, 75692767608093653842361270643659084, 20022945785633448565378785251102, 75692, 11234427753523835778381004731103, 11234427753523977407030207434233⟩ = some ⟨11251560700835715646727942088850, 11251560700835857275377144808984, 76626107621597625253507227668298377, 76626107621598696957495337823332965, 20044681795682930890442494740013, 76626, 11246691723724211788039670564416, 11246691723724353416688873279688⟩ := by decide +kernel
theorem wk_78 : walkP 77000 1000 ⟨11251560700835715646727942088850, 11251560700835857275377144808984, 76626107621597625253507227668298377, 76626107621598696957495337823332965, 20044681795682930890442494740013, 76626, 11246691723724211788039670564416, 11246691723724353416688873279688⟩ = some ⟨11264464105671623534426610565886, 11264464105671765163075813299020, 77695616734249567293093875297669268, 77695616734250652451803659711730615, 20069269122130152105187473380558, 77695, 11260546184220729271791430692272, 11260546184220870900440633421441⟩ := by decide +kernel
theorem wk_79 : walkP 78000 1000 ⟨11264464105671623534426610565886, 11264464105671765163075813299020, 77695616734249567293093875297669268, 77695616734250652451803659711730615, 20069269122130152105187473380558, 77695, 11260546184220729271791430692272, 11260546184220870900440633421441⟩ = some ⟨11277203131449053291733591305931, 11277203131449194920382794052065, 78642371184128056804223043870107045, 78642371184129153859739361314301002, 20090755597318875386219386508839, 78642, 11272661186847495316315722928859, 11272661186847636944964925670339⟩ := by decide +kernel
theorem wk_80 : walkP 79000 1000 ⟨11277203131449053291733591305931, 11277203131449194920382794052065, 78642371184128056804223043870107045, 78642371184129153859739361314301002, 20090755597318875386219386508839, 78642, 11272661186847495316315722928859, 11272661186847636944964925670339⟩ = some ⟨11289781913655913409830333581991, 11289781913656055038479536341125, 79669201918711604566317184359091704, 79669201918712714510040579253808128, 20113758152667375169243589724844, 79669, 11285635830519455958500663523264, 11285635830519597587149866278095⟩ := by decide +kernel
theorem wk_81 : walkP 80000 1000 ⟨11289781913655913409830333581991, 11289781913656055038479536341125, 79669201918711604566317184359091704, 79669201918712714510040579253808128, 20113758152667375169243589724844, 79669, 11285635830519455958500663523264, 11285635830519597587149866278095⟩ = some ⟨11302204433654470563141626709132, 11302204433654612191790829481266, 80663266889400139364846564613437586, 80663266889401261771891089351546962, 20135754182971478834882264836867, 80663, 11298035260892064801161686694253, 11298035260892206429810889462006⟩ := by decide +kernel
theorem wk_82 : walkP 81000 1000 ⟨11302204433654470563141626709132, 11302204433654612191790829481266, 80663266889400139364846564613437586, 80663266889401261771891089351546962, 20135754182971478834882264836867, 80663, 11298035260892064801161686694253, 11298035260892206429810889462006⟩ = some ⟨11314474526246284910844641254441, 11314474526246426539493844039575, 81703613673905868706060471439050422, 81703613673907004142940722832771298, 20158502730230189924406859415420, 81703, 11310845999880079436879721611013, 11310845999880221065528924392286⟩ := by decide +kernel
theorem wk_83 : walkP 82000 1000 ⟨11314474526246284910844641254441, 11314474526246426539493844039575, 81703613673905868706060471439050422, 81703613673907004142940722832771298, 20158502730230189924406859415420, 81703, 11310845999880079436879721611013, 11310845999880221065528924392286⟩ = some ⟨11326595886778629721036117981736, 11326595886778771349685320779870, 82711107866087121864970965670458672, 82711107866088269906800996112597937, 20180270057591639706987054099238, 82711, 11323107883049222880427221773625, 11323107883049364509076424568002⟩ := by decide +kernel
theorem wk_84 : walkP 83000 1000 ⟨11326595886778629721036117981736, 11326595886778771349685320779870, 82711107866087121864970965670458672, 82711107866088269906800996112597937, 20180270057591639706987054099238, 82711, 11323107883049222880427221773625, 11323107883049364509076424568002⟩ = some ⟨11338572077825345412895707980219, 11338572077825487041544910791353, 83663029940963905115099945191392092, 83663029940965065053736508669103245, 20200585609859590027188232903862, 83663, 11334552103784180498274656357698, 11334552103784322126923859164451⟩ := by decide +kernel
theorem wk_85 : walkP 84000 1000 ⟨11338572077825345412895707980219, 11338572077825487041544910791353, 83663029940963905115099945191392092, 83663029940965065053736508669103245, 20200585609859590027188232903862, 83663, 11334552103784180498274656357698, 11334552103784322126923859164451⟩ = some ⟨11350406535472348252410939706533, 11350406535472489881060142530667, 84649986084130558107538453034077692, 84649986084131730367867497156906012, 20221398611868290173456180696333, 84649, 11346268574142313496411091607028, 11346268574142455125060294426599⟩ := by decide +kernel
theorem wk_86 : walkP 85000 1000 ⟨11350406535472348252410939706533, 11350406535472489881060142530667, 84649986084130558107538453034077692, 84649986084131730367867497156906012, 20221398611868290173456180696333, 84649, 11346268574142313496411091607028, 11346268574142455125060294426599⟩ = some ⟨11362102575235539530450720388741, 11362102575235681159099923225875, 85615245075155866970522596104507167, 85615245075157051269286822467913104, 20241517685440113429665542173658, 85615, 11357615780422966270325650562599, 11357615780423107898974853394728⟩ := by decide +kernel
theorem wk_87 : walkP 86000 1000 ⟨11362102575235539530450720388741, 11362102575235681159099923225875, 85615245075155866970522596104507167, 85615245075157051269286822467913104, 20241517685440113429665542173658, 85615, 11357615780422966270325650562599, 11357615780423107898974853394728⟩ = some ⟨11373663397636615516139163021714, 11373663397636757144788365871848, 86615595840347500554119442327874108, 86615595840348697316204798541492927, 20262126638853393610728224379432, 86615, 11369228289712936013846431307209, 11369228289713077642495634152338⟩ := by decide +kernel
theorem wk_88 : walkP 87000 1000 ⟨11373663397636615516139163021714, 11373663397636757144788365871848, 86615595840347500554119442327874108, 86615595840348697316204798541492927, 20262126638853393610728224379432, 86615, 11369228289712936013846431307209, 11369228289713077642495634152338⟩ = some ⟨11385092093460238269874285693291, 11385092093460379898523488556425, 87673889128125281137928439286585593, 87673889128126491071478171365882879, 20283671832516897461036267894946, 87673, 11381369263228269415591617955036, 11381369263228411044240820813919⟩ := by decide +kernel
theorem wk_89 : walkP 88000 1000 ⟨11385092093460238269874285693291, 11385092093460379898523488556425, 87673889128125281137928439286585593, 87673889128126491071478171365882879, 20283671832516897461036267894946, 87673, 11381369263228269415591617955036, 11381369263228411044240820813919⟩ = some ⟨11396391648714171635878461290136, 11396391648714313264527664166270, 88539620018266393287126057016251286, 88539620018267613984453128513679548, 20301090618070942864930205058601, 88539, 11391198411891999119752353412746, 11391198411892140748401556282887⟩ := by decide +kernel
theorem wk_90 : walkP 89000 1000 ⟨11396391648714171635878461290136, 11396391648714313264527664166270, 88539620018266393287126057016251286, 88539620018267613984453128513679548, 20301090618070942864930205058601, 88539, 11391198411891999119752353412746, 11391198411892140748401556282887⟩ = some ⟨11407564949312296864369127676496, 11407564949312438493018330565630, 89611398626731265565220383148273943, 89611398626732499575640479716660129, 20322425871275198948304504393466, 89611, 11403233359284702794736733507125, 11403233359284844423385936391202⟩ := by decide +kernel
theorem wk_91 : walkP 90000 1000 ⟨11407564949312296864369127676496, 11407564949312438493018330565630, 89611398626731265565220383148273943, 89611398626732499575640479716660129, 20322425871275198948304504393466, 89611, 11403233359284702794736733507125, 11403233359284844423385936391202⟩ = some ⟨11418614785498881838719485931465, 11418614785499023467368688833599, 90627134461045965210925131551529902, 90627134461047211826295007177592193, 20342428375556432976355280426329, 90627, 11414507460878871850330545491415, 11414507460879013478979748388700⟩ := by decide +kernel
theorem wk_92 : walkP 91000 1000 ⟨11418614785498881838719485931465, 11418614785499023467368688833599, 90627134461045965210925131551529902, 90627134461047211826295007177592193, 20342428375556432976355280426329, 90627, 11414507460878871850330545491415, 11414507460879013478979748388700⟩ = some ⟨11429543856031072107201862819673, 11429543856031213735851065734807, 91598176441725452998055557140046978, 91598176441726711651860615013336490, 20361336033304246618804735574832, 91598, 11425164716362614427127748459296, 11425164716362756055776951369204⟩ := by decide +kernel
theorem wk_93 : walkP 92000 1000 ⟨11429543856031072107201862819673, 11429543856031213735851065734807, 91598176441725452998055557140046978, 91598176441726711651860615013336490, 20361336033304246618804735574832, 91598, 11425164716362614427127748459296, 11425164716362756055776951369204⟩ = some ⟨11440354772135287734885055304935, 11440354772135429363534258233069, 92707379532405650798973980464466139, 92707379532406923190758011021168618, 20382696779096923302367949236428, 92707, 11437199261108532578513887188161, 11437199261108674207163090112486⟩ := by decide +kernel
theorem wk_94 : walkP 93000 1000 ⟨11440354772135287734885055304935, 11440354772135429363534258233069, 92707379532405650798973980464466139, 92707379532406923190758011021168618, 20382696779096923302367949236428, 92707, 11437199261108532578513887188161, 11437199261108674207163090112486⟩ = some ⟨11451050061252035693798828533205, 11451050061252177322448031474339, 93691709584461049461298765123059242, 93691709584462334033146627132138841, 20401453664969937637180900155967, 93691, 11447757412385872522743707896333, 11447757412386014151392910833450⟩ := by decide +kernel
theorem wk_95 : walkP 94000 1000 ⟨11451050061252035693798828533205, 11451050061252177322448031474339, 93691709584461049461298765123059242, 93691709584462334033146627132138841, 20401453664969937637180900155967, 93691, 11447757412385872522743707896333, 11447757412386014151392910833450⟩ = some ⟨11461632170582572632170432505585, 11461632170582714260819635459719, 94688414219855020668663991832761356, 94688414219856317562204334498287726, 20420244410988571069315368917504, 94688, 11458342555199830942874728742637, 11458342555199972571523931692715⟩ := by decide +kernel
theorem wk_96 : walkP 95000 1000 ⟨11461632170582572632170432505585, 11461632170582714260819635459719, 94688414219855020668663991832761356, 94688414219856317562204334498287726, 20420244410988571069315368917504, 94688, 11458342555199830942874728742637, 11458342555199972571523931692715⟩ = some ⟨11472103470449868036042051583178, 11472103470450009664691254550312, 95777761040379621322041586061161740, 95777761040380931670303603007940293, 20440569533327016584093268099509, 95777, 11469777851626880885885876109884, 11469777851627022514535079074119⟩ := by decide +kernel
theorem wk_97 : walkP 96000 1000 ⟨11472103470449868036042051583178, 11472103470450009664691254550312, 95777761040379621322041586061161740, 95777761040380931670303603007940293, 20440569533327016584093268099509, 95777, 11469777851626880885885876109884, 11469777851627022514535079074119⟩ = some ⟨11482466257485414619677367359161, 11482466257485556248326570339295, 96741865018760527220127348887680062, 96741865018761849465195898884258041, 20458367962743243617213557775487, 96741, 11479792583309177631475783646873, 11479792583309319260124986623640⟩ := by decide +kernel
theorem wk_98 : walkP 97000 1000 ⟨11482466257485414619677367359161, 11482466257485556248326570339295, 96741865018760527220127348887680062, 96741865018761849465195898884258041, 20458367962743243617213557775487, 96741, 11479792583309177631475783646873, 11479792583309319260124986623640⟩ = some ⟨11492722757652603717188583344281, 11492722757652745345837786337415, 97683856811305401661395772475741908, 97683856811306735520013557117234431, 20475579704156449091372562437862, 97683, 11489482820843573453336899793410, 11489482820843715081986102782423⟩ := by decide +kernel
theorem wk_99 : walkP 98000 1000 ⟨11492722757652603717188583344281, 11492722757652745345837786337415, 97683856811305401661395772475741908, 97683856811306735520013557117234431, 20475579704156449091372562437862, 97683, 11489482820843573453336899793410, 11489482820843715081986102782423⟩ = some ⟨11502875129116621724413079786259, 11502875129116763353062282792393, 98684199977112422672051798184345711, 98684199977113768852362063486849825, 20493665916732371728496933865800, 98684, 11499678104884493635224661126796, 11499678104884635263873864128822⟩ := by decide +kernel
theorem wk_100 : walkP 99000 1000 ⟨11502875129116621724413079786259, 11502875129116763353062282792393, 98684199977112422672051798184345711, 98684199977113768852362063486849825, 20493665916732371728496933865800, 98684, 11499678104884493635224661126796, 11499678104884635263873864128822⟩ = some ⟨11512925464970123165596628642300, 11512925464970264794245831661434, 99685389268611541235524122736998713, 99685389268612899737526868701603584, 20511592825190780161845326219264, 99685, 11509770493276821973487737331393, 11509770493276963602136940346432⟩ := by decide +kernel

theorem inv_1 : Inv 1 ⟨0, 0, 0, 0, 1000000000000000000000000000000, 1, 0, 0⟩ := Inv_one
theorem inv_1000 : Inv 1000 ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 956245265120041185057801216681779, 956245265120064978670464274002504, 12350975673851661433752563348540, 956, 6862757913051296031304299359206, 6862757913051437659953501090768⟩ := walkP_spec 999 1 _ _ (by norm_num) inv_1 wk_1
theorem inv_2000 : Inv 2000 ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 1939839200302529137722656397952172, 1939839200302572051202961689967986, 13573750018230555889558589728144, 1939, 7569927655242546550481421812974, 7569927655242688179130623557315⟩ := walkP_spec 1000 1000 _ _ (by norm_num) inv_1000 wk_2
theorem inv_3000 : Inv 3000 ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 2932359211878681560809477014706588, 2932359211878742461128230929170469, 14292705320286832607211284089042, 2932, 7983440063006436856610284459685, 7983440063006578485259486216935⟩ := walkP_spec 1000 2000 _ _ (by norm_num) inv_2000 wk_3
theorem inv_4000 : Inv 4000 ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 3911145399581146234184563977051654, 3911145399581224129941222103267507, 14794980092780920480403729936233, 3911, 8271548374755408864918456900448, 8271548374755550493567658670425⟩ := walkP_spec 1000 3000 _ _ (by norm_num) inv_3000 wk_4
theorem inv_5000 : Inv 5000 ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 4911695351706793129045591750696542, 4911695351706887878611504888439518, 15193938509953073002604175149013, 4911, 8499232866039139340202225931599, 8499232866039280968851427714576⟩ := walkP_spec 1000 4000 _ _ (by norm_num) inv_4000 wk_5
theorem inv_6000 : Inv 6000 ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 5893297457247982535544997772414871, 5893297457248093430776919914284897, 15513240551838087406167217410743, 5893, 8681520484837808090311598267942, 8681520484837949718960800063685⟩ := walkP_spec 1000 5000 _ _ (by norm_num) inv_5000 wk_6
theorem inv_7000 : Inv 7000 ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 6920421029943578693429679087107379, 6920421029943706159213557840005664, 15795529761036456458107752562449, 6920, 8842171048611609995292627596117, 8842171048611751623941829405211⟩ := walkP_spec 1000 6000 _ _ (by norm_num) inv_6000 wk_7
theorem inv_8000 : Inv 8000 ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 7875150384797318841402588918268461, 7875150384797461461451932265554319, 16022658793765949879912368357066, 7875, 8971448463693728557204792725168, 8971448463693870185853994546677⟩ := walkP_spec 1000 7000 _ _ (by norm_num) inv_7000 wk_8
theorem inv_9000 : Inv 9000 ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 8870374992657703076233879134508550, 8870374992657861275434634683057060, 16231557913277557526140618061403, 8870, 9090430075303519919927711613621, 9090430075303661548576913448065⟩ := walkP_spec 1000 8000 _ _ (by norm_num) inv_8000 wk_9
theorem inv_10000 : Inv 10000 ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 9895991379156857954896927845751462, 9895991379157032016506394000656858, 16424489632190082652598750113685, 9895, 9199784858036560847269531442029, 9199784858036702475918733289798⟩ := walkP_spec 1000 9000 _ _ (by norm_num) inv_9000 wk_10
theorem inv_11000 : Inv 11000 ⟨9305650551780402341622589444417, 9305650551780543970271791306551, 10877341630469408712480218853540655, 10877341630469597786726500405132725, 16591396345718166430766667106024, 10877, 9294405747093745015591208635131, 9294405747093886644240410495666⟩ := walkP_spec 1000 10000 _ _ (by norm_num) inv_10000 wk_11
theorem inv_12000 : Inv 12000 ⟨9392661928770032107790355344703, 9392661928770173736439557219837, 11840485753872092189936240972598197, 11840485753872295851933390316677106, 16740598896265369369201550347168, 11840, 9379238908437891420978919234058, 9379238908438033049628121107112⟩ := walkP_spec 1000 11000 _ _ (by norm_num) inv_11000 wk_12
theorem inv_13000 : Inv 13000 ⟨9472704636443568533614133304897, 9472704636443710162263335193031, 12868728097423735358580478510330948, 12868728097423954458100390859511304, 16887268936263214245420751085592, 12868, 9462498888358811711779225197196, 9462498888358953340428427083614⟩ := walkP_spec 1000 12000 _ _ (by norm_num) inv_12000 wk_13
theorem inv_14000 : Inv 14000 ⟨9546812608597290412083230726710, 9546812608597432040732432627844, 13867292527692335367030028700651706, 13867292527692569337558107248767319, 17019203430389799538683218913866, 13867, 9537267195753758980363364131641, 9537267195753900609012566031046⟩ := walkP_spec 1000 13000 _ _ (by norm_num) inv_13000 wk_14
theorem inv_15000 : Inv 15000 ⟨9615805480084241863556650430424, 9615805480084383492205852344558, 14844791692165104101792976519992357, 14844791692165352518443273662717552, 17139202096899285735594265291104, 14844, 9605351022180382955169606070807, 9605351022180524583818807982913⟩ := walkP_spec 1000 14000 _ _ (by norm_num) inv_14000 wk_15
theorem inv_16000 : Inv 16000 ⟨9680344001221813035229574344616, 9680344001221954663878776271750, 15886792468421075601943335383136468, 15886792468421339314487746333284103, 17259117036680770222905980731817, 15886, 9673193497192972113851829169266, 9673193497193113742501031094918⟩ := walkP_spec 1000 15000 _ _ (by norm_num) inv_15000 wk_16
theorem inv_17000 : Inv 17000 ⟨9740968623038247877810180475156, 9740968623038389506459382415290, 16838472455535699058768888695707996, 16838472455535976650920921435353115, 17361960193246478827482998389278, 16838, 9731393515897504043397815833643, 9731393515897645672047017771671⟩ := walkP_spec 1000 16000 _ _ (by norm_num) inv_16000 wk_17
theorem inv_18000 : Inv 18000 ⟨9798127036878196489768368451090, 9798127036878338118417570404224, 17854574994286053279939995767937295, 17854574994286345601471545510041814, 17465437430840249850898365021003, 17854, 9789982851739202117678980648508, 9789982851739343746328182599744⟩ := walkP_spec 1000 17000 _ _ (by norm_num) inv_17000 wk_18
theorem inv_19000 : Inv 19000 ⟨9852194258148472257569673286171, 9852194258148613886218875252305, 18777952331436118539016720125187880, 18777952331436424173641294851447191, 17554630089268333015627634402718, 18777, 9840387995592705901946045114838, 9840387995592847530595247078073⟩ := walkP_spec 1000 18000 _ _ (by norm_num) inv_18000 wk_19
theorem inv_20000 : Inv 20000 ⟨9903487552536022790995869428895, 9903487552536164419645071408029, 19805309624307629247228627352260355, 19805309624307949611232719083683508, 17648492637505432660762838770836, 19805, 9893689710055911765659190314765, 9893689710056053394308392291364⟩ := walkP_spec 1000 19000 _ _ (by norm_num) inv_19000 wk_20
theorem inv_21000 : Inv 21000 ⟨9952277716705454794061243831594, 9952277716705596422710445823728, 20778193058130709664326966098860664, 20778193058131043907938679624857749, 17733141359621799525824365376609, 20778, 9941650013630371708020841681234, 9941650013630513336670043670482⟩ := walkP_spec 1000 20000 _ _ (by norm_num) inv_20000 wk_21
theorem inv_22000 : Inv 22000 ⟨9998797732340347651039821549134, 9998797732340489279689023554268, 21815610747470111763360210788524199, 21815610747470460736351441322363282, 17819192842429500474687766640023, 21815, 9990353085557604725132378230179, 9990353085557746353781580232908⟩ := walkP_spec 1000 21000 _ _ (by norm_num) inv_21000 wk_22
theorem inv_23000 : Inv 23000 ⟨10043249494911181488367398680012, 10043249494911323117016600698146, 22817635724195170854561128385106668, 22817635724195533990417279120081773, 17898655247210210886367583399828, 22817, 10035261151145465015972858028895, 10035261151145606644622060044650⟩ := walkP_spec 1000 22000 _ _ (by norm_num) inv_22000 wk_23
theorem inv_24000 : Inv 24000 ⟨10085809109329977417207587448011, 10085809109330119045856789479145, 23864331538659962301821130152319550, 23864331538660340167056797897847361, 17978079775495337918038856985620, 23864, 10080126326194479191191840515537, 10080126326194620819841042544903⟩ := walkP_spec 1000 23000 _ _ (by norm_num) inv_23000 wk_24
theorem inv_25000 : Inv 25000 ⟨10126631103850232546762164511661, 10126631103850374175411366555795, 24814245437040723505859209433366121, 24814245437041114684187902170405112, 18047262858570956076189996812999, 24814, 10119163289002711576345882105981, 10119163289002853204995084147697⟩ := walkP_spec 1000 24000 _ _ (by norm_num) inv_24000 wk_25
theorem inv_26000 : Inv 26000 ⟨10165851817003513843031365406771, 10165851817003655471680567463905, 25808635507716280892652931211781799, 25808635507716685950589245749798106, 18116732098822771102556694914710, 25808, 10158439800364884844679316305461, 10158439800365026473328518360099⟩ := walkP_spec 1000 25000 _ _ (by norm_num) inv_25000 wk_26
theorem inv_27000 : Inv 27000 ⟨10203592144986360871746381552992, 10203592144986502500395583623126, 26837348714082415704276855786970604, 26837348714082835066706739733429220, 18185891686112329328272245648229, 26837, 10197536811365963549057588344131, 10197536811366105177706790412146⟩ := walkP_spec 1000 26000 _ _ (by norm_num) inv_26000 wk_27
theorem inv_28000 : Inv 28000 ⟨10239959789157235721500462827090, 10239959789157377350149664910224, 27798293923604116436279747036371002, 27798293923604549111802655978064726, 18248110562048748137817125502668, 27798, 10232719354644598118768043702025, 10232719354644739747417245782533⟩ := walkP_spec 1000 27000 _ _ (by norm_num) inv_27000 wk_28
theorem inv_29000 : Inv 29000 ⟨10275051108968505824743917871600, 10275051108968647453393119967734, 28803557736131767501019367308615266, 28803557736132214056149898055099700, 18310962016413661313851354667287, 28803, 10268234827365628218655575513991, 10268234827365769847304777607564⟩ := walkP_spec 1000 28000 _ _ (by norm_num) inv_28000 wk_29
theorem inv_30000 : Inv 30000 ⟨10308952660644187172973882529344, 10308952660644328801623084638478, 29750341743931991044119182450100094, 29750341743932450629085439789992718, 18368218366862861875764825000480, 29750, 10300584410973670564081068956505, 10300584410973812192730271062389⟩ := walkP_spec 1000 29000 _ _ (by norm_num) inv_29000 wk_30
theorem inv_31000 : Inv 31000 ⟨10341742483467178043489810160793, 10341742483467319672139012282927, 30731246027007697700759929751507393, 30731246027008170740447861292380424, 18425533578140496023519087079822, 30731, 10333027196085362532528237247711, 10333027196085504161177439366348⟩ := walkP_spec 1000 30000 _ _ (by norm_num) inv_30000 wk_31
theorem inv_32000 : Inv 32000 ⟨10373491181781758344646806442015, 10373491181781899973296008577149, 31684046410867523262965220864863097, 31684046410868009332488879001526152, 18479495247571093131345647408013, 31684, 10363567100584065040976766795427, 10363567100584206669625968926453⟩ := walkP_spec 1000 31000 _ _ (by norm_num) inv_31000 wk_32
theorem inv_33000 : Inv 33000 ⟨10404262840448512033017834648112, 10404262840448653661667036796246, 32785251380575740134134323026735285, 32785251380576241216294796590401300, 18539884888822858052853417314885, 32785, 10397726372697614537755848567499, 10397726372697756166405050712838⟩ := walkP_spec 1000 32000 _ _ (by norm_num) inv_32000 wk_33
theorem inv_34000 : Inv 34000 ⟨10434115803598193187227412571042, 10434115803598334815876614732176, 33827185146329436336742227397943290, 33827185146329951581767621177075825, 18595311217555972636794581792160, 33827, 10429014579154906198538713805269, 10429014579155047827187915964154⟩ := walkP_spec 1000 33000 _ _ (by norm_num) inv_33000 wk_34
theorem inv_35000 : Inv 35000 ⟨10463103340471445477266757906889, 10463103340471587105915960081023, 34809363631338296358353134973531766, 34809363631338824916471553756422885, 18646048458757435157439240917585, 34809, 10457631253015549865414667223209, 10457631253015691494063869394860⟩ := walkP_spec 1000 34000 _ _ (by norm_num) inv_34000 wk_35
theorem inv_36000 : Inv 36000 ⟨10491274217438141799185600545519, 10491274217438283427834802732653, 35773269616072639623775615339006549, 35773269616073181211729760722515398, 18694438029827971008317643800488, 35773, 10484948697900240456729810494650, 10484948697900382085379012678833⟩ := walkP_spec 1000 35000 _ _ (by norm_num) inv_35000 wk_36
theorem inv_37000 : Inv 37000 ⟨10518673191626256241928741498308, 10518673191626397870577943698442, 36813320098893925345363757637620188, 36813320098894480954554174038323438, 18745189557459863590869679213161, 36813, 10513606322644552240575450706086, 10513606322644693869224652903789⟩ := walkP_spec 1000 36000 _ _ (by norm_num) inv_36000 wk_37
theorem inv_38000 : Inv 38000 ⟨10545341438708417566986905379121, 10545341438708559195636107592255, 37803336694988822694251186489172069, 37803336694989391616534627897300033, 18792238666243816584930296321358, 37803, 10540143743537697595724463517167, 10540143743537839224373665727740⟩ := walkP_spec 1000 37000 _ _ (by norm_num) inv_37000 wk_38
theorem inv_39000 : Inv 39000 ⟨10571316925111678225009378502774, 10571316925111819853658580728908, 38753652264104901990361686685723621, 38753652264105483659223556293649065, 18836193170104376041573977900492, 38753, 10564963451139502925718972553334, 10564963451139644554368174776257⟩ := walkP_spec 1000 38000 _ _ (by norm_num) inv_38000 wk_39
theorem inv_40000 : Inv 40000 ⟨10596634733095968100413101520397, 10596634733096109729062303759531, 39769713423932329378915196394728397, 39769713423932924644127389416983819, 18882033692926987074599376989925, 39769, 10590842993304158050093887982999, 10590842993304299678743090219130⟩ := walkP_spec 1000 39000 _ _ (by norm_num) inv_39000 wk_40
theorem inv_41000 : Inv 41000 ⟨10621327345686339601427409194326, 10621327345686481230076611446460, 40703322413734975747067665542731792, 40703322413735583475600988362610520, 18923101934687245143915394902726, 40703, 10614057078787837178373521490701, 10614057078787978807022723738974⟩ := walkP_spec 1000 40000 _ _ (by norm_num) inv_40000 wk_41
theorem inv_42000 : Inv 42000 ⟨10645424897265400103478475921615, 10645424897265541732127678186749, 41777314385235059564258941855850219, 41777314385235681597285834103859730, 18969207323759810956608125059732, 41777, 10640101227841131442615408637655, 10640101227841273071264610899890⟩ := walkP_spec 1000 41000 _ _ (by norm_num) inv_41000 wk_42
theorem inv_43000 : Inv 43000 ⟨10668955394675594221033488331625, 10668955394675735849682690609759, 42864348819748854516464872987472208, 42864348819749490995613983867186307, 19014792335629893768540288296312, 42864, 10665787591784284721400823278854, 10665787591784426350050025555220⟩ := walkP_spec 1000 42000 _ _ (by norm_num) inv_42000 wk_43
theorem inv_44000 : Inv 44000 ⟨10691944912900292960457053637669, 10691944912900434589106255928803, 43772227664512208892924404973609985, 43772227664512857410508698047538865, 19051969980214278842041344667661, 43772, 10686749622538228377666020137719, 10686749622538370006315222425889⟩ := walkP_spec 1000 43000 _ _ (by norm_num) inv_43000 wk_44
theorem inv_45000 : Inv 45000 ⟨10714417768752351554951895622355, 10714417768752493183601097926489, 44799737827000986426827685072508907, 44799737827001648540762301567011119, 19093117155948789230260433590950, 44799, 10709941096725273052594423268652, 10709941096725414681243625570173⟩ := walkP_spec 1000 44000 _ _ (by norm_num) inv_44000 wk_45
theorem inv_46000 : Inv 46000 ⟨10736396675471126797784630767037, 10736396675471268426433833084171, 45722141344584906727434995185740462, 45722141344585581021433443078966038, 19129234866284973400995907596225, 45722, 10730334861483811077498781698645, 10730334861483952706147984012165⟩ := walkP_spec 1000 45000 _ _ (by norm_num) inv_45000 wk_46
theorem inv_47000 : Inv 47000 ⟨10757902880692090384381596482033, 10757902880692232013030798812167, 46689380651138726742758397018788241, 46689380651139413783335273121136171, 19166299965141047059199386711540, 46689, 10751263869873014437854659556240, 10751263869873156066503861882331⟩ := walkP_spec 1000 46000 _ _ (by norm_num) inv_46000 wk_47
theorem inv_48000 : Inv 48000 ⟨10778956289889922726624819533524, 10778956289890064355274021876658, 47712415063789690014699741956690884, 47712415063790390509998292281037569, 19204660541237377951347119271320, 47712, 10772938217564359710422884567319, 10772938217564501339072086906709⟩ := walkP_spec 1000 47000 _ _ (by norm_num) inv_47000 wk_48
theorem inv_49000 : Inv 49000 ⟨10799575577092658407771351296154, 10799575577092800036420553652288, 48672685592903073744048161362340131, 48672685592903786844296490695818477, 19239926992709937510006395898057, 48672, 10792859195058914147490297409971, 10792859195059055776139499761841⟩ := walkP_spec 1000 48000 _ _ (by norm_num) inv_48000 wk_49
theorem inv_50000 : Inv 50000 ⟨10819778284410177856179396595709, 10819778284410319484828598964843, 49732018402956314603630354987867840, 49732018402957041583486306152872228, 19278064951716576450112944812727, 49732, 10814403868072722922052541215509, 10814403868072864550701743581159⟩ := walkP_spec 1000 49000 _ _ (by norm_num) inv_49000 wk_50
theorem inv_51000 : Inv 51000 ⟨10839580911706357569205425661089, 10839580911706499197854628043223, 50695834529702683146551768959337524, 50695834529703422731357499135754839, 19312082403890598740687418825093, 50695, 10833582565386574912337843277952, 10833582565386716540987045656121⟩ := walkP_spec 1000 50000 _ _ (by norm_num) inv_50000 wk_51
theorem inv_52000 : Inv 52000 ⟨10858998997563459152448597489285, 10858998997563600781097799884419, 51748240161189245860635291303182488, 51748240161189999183419994111311588, 19348484286624653458290459894835, 51748, 10854141063037687280946049049773, 10854141063037828909595251441631⟩ := walkP_spec 1000 51000 _ _ (by norm_num) inv_51000 wk_52
theorem inv_53000 : Inv 53000 ⟨10878047192534153631705114942352, 10878047192534295260354317350486, 52715565259274268424676359122089426, 52715565259275034352410840943980267, 19381304912518766684604548130059, 52715, 10872655324010944777361298888206, 10872655324011086406010501292635⟩ := walkP_spec 1000 52000 _ _ (by norm_num) inv_52000 wk_53
theorem inv_54000 : Inv 54000 ⟨10896739325546306181163613634034, 10896739325546447809812816055168, 53717212172339203445182548248706763, 53717212172339982402752756692746766, 19414662004476298519534137852548, 53717, 10891484803954812422162086725352, 10891484803954954050811289142807⟩ := walkP_spec 1000 53000 _ _ (by norm_num) inv_53000 wk_54
theorem inv_55000 : Inv 55000 ⟨10915088464214502716223348711498, 10915088464214644344872551145632, 54698749591139355623882855672487058, 54698749591140147328031492335015915, 19446749614048637133102026520516, 54698, 10909582424670223945112899562649, 10909582424670365573762101992857⟩ := walkP_spec 1000 54000 _ _ (by norm_num) inv_54000 wk_55
theorem inv_56000 : Inv 56000 ⟨10933106969717181030917694906639, 10933106969717322659566897353773, 55714725386084185571025707707716462, 55714725386084990446638720197247538, 19479353270406670492083779880043, 55714, 10927986740832133109920484406584, 10927986740832274738569686850000⟩ := walkP_spec 1000 55000 _ _ (by norm_num) inv_55000 wk_56
theorem inv_57000 : Inv 57000 ⟨10950806546816581948964918466149, 10950806546816723577614120926283, 56798034128668319659940573243466365, 56798034128669138556789856775945752, 19513498252295803158614445369127, 56798, 10947256392821600593704085750892, 10947256392821742222353288208400⟩ := walkP_spec 1000 56000 _ _ (by norm_num) inv_56000 wk_57
theorem inv_58000 : Inv 58000 ⟨10968198289528451134161149949651, 10968198289528592762810352422785, 57795352332064112067468046721904137, 57795352332064943852524407678848089, 19544405570434135109665986760948, 57795, 10964657545728262398320236074060, 10964657545728404026969438544529⟩ := walkP_spec 1000 57000 _ _ (by norm_num) inv_57000 wk_58
theorem inv_59000 : Inv 59000 ⟨10985292722887751248176696168074, 10985292722887892876825898654208, 58783229709792545743261619069605681, 58783229709793390274896408249692461, 19574508711639954620178587634693, 58783, 10981607976438368808619005728172, 10981607976438510437268208211485⟩ := walkP_spec 1000 58000 _ _ (by norm_num) inv_58000 wk_59
theorem inv_60000 : Inv 60000 ⟨11002099841204132482391114605923, 11002099841204274111040317105057, 59816575291537034055304060750318863, 59816575291537891900031874964663657, 19605479684974584900703924659301, 59816, 10999028462679646216524290351370, 10999028462679787845173492848112⟩ := walkP_spec 1000 59000 _ _ (by norm_num) inv_59000 wk_60
theorem inv_61000 : Inv 61000 ⟨11018629143155343046312034894785, 11018629143155484674961237406919, 60785485354001141753653905376298367, 60785485354002012061702849411135807, 19634019691242620242485855593434, 60785, 11015098326989789072781743244126, 11015098326989930701430945753465⟩ := walkP_spec 1000 60000 _ _ (by norm_num) inv_60000 wk_61
theorem inv_62000 : Inv 62000 ⟨11034889664027123352907042235866, 11034889664027264981556244761000, 61744833473319631434973717118807219, 61744833473320514064715141772780286, 19661809330393870531419424615553, 61744, 11030752083777294738438516106738, 11030752083777436367087718628544⟩ := walkP_spec 1000 61000 _ _ (by norm_num) inv_61000 wk_62
theorem inv_63000 : Inv 63000 ⟨11050890005373564485456489005642, 11050890005373706114105691543776, 62716613550026775932643794370743677, 62716613550027671025706348847503760, 19689512266374749559348515492637, 62716, 11046371877480235803947223726853, 11046371877480377432596426261295⟩ := walkP_spec 1000 62000 _ _ (by norm_num) inv_62000 wk_63
theorem inv_64000 : Inv 64000 ⟨11066638362341703654064038515584, 11066638362341845282713241066718, 63745100672228584816901680463088279, 63745100672229493081428610776515795, 19718364519355677615665794074809, 63745, 11062646028572117372929790869668, 11062646028572259001578993417487⟩ := walkP_spec 1000 63000 _ _ (by norm_num) inv_63000 wk_64
theorem inv_65000 : Inv 65000 ⟨11082142548877668908214892560138, 11082142548877810536864095124272, 64631051757883529662009656792068096, 64631051757884449256828523310104876, 19742837801167498457666273397009, 64631, 11076449450827835954291579524374, 11076449450827977582940782083711⟩ := walkP_spec 1000 64000 _ _ (by norm_num) inv_64000 wk_65
theorem inv_66000 : Inv 66000 ⟨11097410021008457342435066720200, 11097410021008598971084269297334, 65717846387065822660776399278326507, 65717846387066756135202887648280869, 19772401230090627106153008209230, 65717, 11093112922904684177339468051323, 11093112922904825805988670624778⟩ := walkP_spec 1000 65000 _ _ (by norm_num) inv_65000 wk_66
theorem inv_67000 : Inv 67000 ⟨11112447898372997857230717778718, 11112447898373139485879920368852, 66650688600796707343087120891566775, 66650688600797652714320142278569377, 19797385412765465453048009575777, 66650, 11107210325606749473527429044637, 11107210325606891102176631630221⟩ := walkP_spec 1000 66000 _ _ (by norm_num) inv_66000 wk_67
theorem inv_68000 : Inv 68000 ⟨11127262984158138496644644641645, 11127262984158280125293847244779, 67751566283086189744021946220316264, 67751566283087149136491238664394589, 19826440645074276442518168440828, 67751, 11123594498780513648108815290299, 11123594498780655276758017890196⟩ := walkP_spec 1000 67000 _ _ (by norm_num) inv_67000 wk_68
theorem inv_69000 : Inv 69000 ⟨11141861783579291179762643848102, 11141861783579432808411846464236, 68642357960872817186326831524693734, 68642357960873787909088060177565243, 19849602386334015617018092722880, 68642, 11136659871266386611419474886658, 11136659871266528240068677498138⟩ := walkP_spec 1000 68000 _ _ (by norm_num) inv_68000 wk_69
theorem inv_70000 : Inv 70000 ⟨11156250521031390786683989976007, 11156250521031532415333192605141, 69545412324660232429117879984078193, 69545412324661214623799694049364479, 19872756399091077165152947541804, 69545, 11149729304041125273519771251891, 11149729304041266902168973875110⟩ := walkP_spec 1000 69000 _ _ (by norm_num) inv_69000 wk_70
theorem inv_71000 : Inv 71000 ⟨11170435156023347218890100308898, 11170435156023488847539302951032, 70639421632610595875718511074200048, 70639421632611591950007946997778622, 19900400819250635654901957360816, 70639, 11165337678892144504140640915111, 11165337678892286132789843552552⟩ := walkP_spec 1000 70000 _ _ (by norm_num) inv_70000 wk_71
theorem inv_72000 : Inv 72000 ⟨11184421397998087108602832613103, 11184421397998228737252035268237, 71701303082393625298890208513011907, 71701303082394634827901318688233214, 19926853351281253929402941729691, 71701, 11180259973491742652397404394426, 11180259973491884281046607045673⟩ := walkP_spec 1000 71000 _ _ (by norm_num) inv_71000 wk_72
theorem inv_73000 : Inv 73000 ⟨11198214720130422926652754630848, 11198214720130564555301957298982, 72708539285585175465005836950464868, 72708539285586197740595375365248497, 19951601625293896145437125425834, 72708, 11194206698732884108303961970355, 11194206698733025736953164634693⟩ := walkP_spec 1000 72000 _ _ (by norm_num) inv_72000 wk_73
theorem inv_74000 : Inv 74000 ⟨11211820372186201551345973564435, 11211820372186343179995176245569, 73638565409193754516820550239413803, 73638565409194788547587972476200049, 19974142948254137791880154163005, 73638, 11206916475825458002990984627515, 11206916475825599631640187303943⟩ := walkP_spec 1000 73000 _ _ (by norm_num) inv_73000 wk_74
theorem inv_75000 : Inv 75000 ⟨11225243392518342238157409673823, 11225243392518483866806612367957, 74670660374385365143054944228818168, 74670660374386412203658093112855718, 19998827814657769766613193785455, 74670, 11220833684029642125078359541551, 11220833684029783753727562231395⟩ := walkP_spec 1000 74000 _ _ (by norm_num) inv_74000 wk_75
theorem inv_76000 : Inv 76000 ⟨11238488619268362876404137443767, 11238488619268504505053340150901, 75692767608092593893551044313857873, 75692767608093653842361270643659084, 20022945785633448565378785251102, 75692, 11234427753523835778381004731103, 11234427753523977407030207434233⟩ := walkP_spec 1000 75000 _ _ (by norm_num) inv_75000 wk_76
theorem inv_77000 : Inv 77000 ⟨11251560700835715646727942088850, 11251560700835857275377144808984, 76626107621597625253507227668298377, 76626107621598696957495337823332965, 20044681795682930890442494740013, 76626, 11246691723724211788039670564416, 11246691723724353416688873279688⟩ := walkP_spec 1000 76000 _ _ (by norm_num) inv_76000 wk_77
theorem inv_78000 : Inv 78000 ⟨11264464105671623534426610565886, 11264464105671765163075813299020, 77695616734249567293093875297669268, 77695616734250652451803659711730615, 20069269122130152105187473380558, 77695, 11260546184220729271791430692272, 11260546184220870900440633421441⟩ := walkP_spec 1000 77000 _ _ (by norm_num) inv_77000 wk_78
theorem inv_79000 : Inv 79000 ⟨11277203131449053291733591305931, 11277203131449194920382794052065, 78642371184128056804223043870107045, 78642371184129153859739361314301002, 20090755597318875386219386508839, 78642, 11272661186847495316315722928859, 11272661186847636944964925670339⟩ := walkP_spec 1000 78000 _ _ (by norm_num) inv_78000 wk_79
theorem inv_80000 : Inv 80000 ⟨11289781913655913409830333581991, 11289781913656055038479536341125, 79669201918711604566317184359091704, 79669201918712714510040579253808128, 20113758152667375169243589724844, 79669, 11285635830519455958500663523264, 11285635830519597587149866278095⟩ := walkP_spec 1000 79000 _ _ (by norm_num) inv_79000 wk_80
theorem inv_81000 : Inv 81000 ⟨11302204433654470563141626709132, 11302204433654612191790829481266, 80663266889400139364846564613437586, 80663266889401261771891089351546962, 20135754182971478834882264836867, 80663, 11298035260892064801161686694253, 11298035260892206429810889462006⟩ := walkP_spec 1000 80000 _ _ (by norm_num) inv_80000 wk_81
theorem inv_82000 : Inv 82000 ⟨11314474526246284910844641254441, 11314474526246426539493844039575, 81703613673905868706060471439050422, 81703613673907004142940722832771298, 20158502730230189924406859415420, 81703, 11310845999880079436879721611013, 11310845999880221065528924392286⟩ := walkP_spec 1000 81000 _ _ (by norm_num) inv_81000 wk_82
theorem inv_83000 : Inv 83000 ⟨11326595886778629721036117981736, 11326595886778771349685320779870, 82711107866087121864970965670458672, 82711107866088269906800996112597937, 20180270057591639706987054099238, 82711, 11323107883049222880427221773625, 11323107883049364509076424568002⟩ := walkP_spec 1000 82000 _ _ (by norm_num) inv_82000 wk_83
theorem inv_84000 : Inv 84000 ⟨11338572077825345412895707980219, 11338572077825487041544910791353, 83663029940963905115099945191392092, 83663029940965065053736508669103245, 20200585609859590027188232903862, 83663, 11334552103784180498274656357698, 11334552103784322126923859164451⟩ := walkP_spec 1000 83000 _ _ (by norm_num) inv_83000 wk_84
theorem inv_85000 : Inv 85000 ⟨11350406535472348252410939706533, 11350406535472489881060142530667, 84649986084130558107538453034077692, 84649986084131730367867497156906012, 20221398611868290173456180696333, 84649, 11346268574142313496411091607028, 11346268574142455125060294426599⟩ := walkP_spec 1000 84000 _ _ (by norm_num) inv_84000 wk_85
theorem inv_86000 : Inv 86000 ⟨11362102575235539530450720388741, 11362102575235681159099923225875, 85615245075155866970522596104507167, 85615245075157051269286822467913104, 20241517685440113429665542173658, 85615, 11357615780422966270325650562599, 11357615780423107898974853394728⟩ := walkP_spec 1000 85000 _ _ (by norm_num) inv_85000 wk_86
theorem inv_87000 : Inv 87000 ⟨11373663397636615516139163021714, 11373663397636757144788365871848, 86615595840347500554119442327874108, 86615595840348697316204798541492927, 20262126638853393610728224379432, 86615, 11369228289712936013846431307209, 11369228289713077642495634152338⟩ := walkP_spec 1000 86000 _ _ (by norm_num) inv_86000 wk_87
theorem inv_88000 : Inv 88000 ⟨11385092093460238269874285693291, 11385092093460379898523488556425, 87673889128125281137928439286585593, 87673889128126491071478171365882879, 20283671832516897461036267894946, 87673, 11381369263228269415591617955036, 11381369263228411044240820813919⟩ := walkP_spec 1000 87000 _ _ (by norm_num) inv_87000 wk_88
theorem inv_89000 : Inv 89000 ⟨11396391648714171635878461290136, 11396391648714313264527664166270, 88539620018266393287126057016251286, 88539620018267613984453128513679548, 20301090618070942864930205058601, 88539, 11391198411891999119752353412746, 11391198411892140748401556282887⟩ := walkP_spec 1000 88000 _ _ (by norm_num) inv_88000 wk_89
theorem inv_90000 : Inv 90000 ⟨11407564949312296864369127676496, 11407564949312438493018330565630, 89611398626731265565220383148273943, 89611398626732499575640479716660129, 20322425871275198948304504393466, 89611, 11403233359284702794736733507125, 11403233359284844423385936391202⟩ := walkP_spec 1000 89000 _ _ (by norm_num) inv_89000 wk_90
theorem inv_91000 : Inv 91000 ⟨11418614785498881838719485931465, 11418614785499023467368688833599, 90627134461045965210925131551529902, 90627134461047211826295007177592193, 20342428375556432976355280426329, 90627, 11414507460878871850330545491415, 11414507460879013478979748388700⟩ := walkP_spec 1000 90000 _ _ (by norm_num) inv_90000 wk_91
theorem inv_92000 : Inv 92000 ⟨11429543856031072107201862819673, 11429543856031213735851065734807, 91598176441725452998055557140046978, 91598176441726711651860615013336490, 20361336033304246618804735574832, 91598, 11425164716362614427127748459296, 11425164716362756055776951369204⟩ := walkP_spec 1000 91000 _ _ (by norm_num) inv_91000 wk_92
theorem inv_93000 : Inv 93000 ⟨11440354772135287734885055304935, 11440354772135429363534258233069, 92707379532405650798973980464466139, 92707379532406923190758011021168618, 20382696779096923302367949236428, 92707, 11437199261108532578513887188161, 11437199261108674207163090112486⟩ := walkP_spec 1000 92000 _ _ (by norm_num) inv_92000 wk_93
theorem inv_94000 : Inv 94000 ⟨11451050061252035693798828533205, 11451050061252177322448031474339, 93691709584461049461298765123059242, 93691709584462334033146627132138841, 20401453664969937637180900155967, 93691, 11447757412385872522743707896333, 11447757412386014151392910833450⟩ := walkP_spec 1000 93000 _ _ (by norm_num) inv_93000 wk_94
theorem inv_95000 : Inv 95000 ⟨11461632170582572632170432505585, 11461632170582714260819635459719, 94688414219855020668663991832761356, 94688414219856317562204334498287726, 20420244410988571069315368917504, 94688, 11458342555199830942874728742637, 11458342555199972571523931692715⟩ := walkP_spec 1000 94000 _ _ (by norm_num) inv_94000 wk_95
theorem inv_96000 : Inv 96000 ⟨11472103470449868036042051583178, 11472103470450009664691254550312, 95777761040379621322041586061161740, 95777761040380931670303603007940293, 20440569533327016584093268099509, 95777, 11469777851626880885885876109884, 11469777851627022514535079074119⟩ := walkP_spec 1000 95000 _ _ (by norm_num) inv_95000 wk_96
theorem inv_97000 : Inv 97000 ⟨11482466257485414619677367359161, 11482466257485556248326570339295, 96741865018760527220127348887680062, 96741865018761849465195898884258041, 20458367962743243617213557775487, 96741, 11479792583309177631475783646873, 11479792583309319260124986623640⟩ := walkP_spec 1000 96000 _ _ (by norm_num) inv_96000 wk_97
theorem inv_98000 : Inv 98000 ⟨11492722757652603717188583344281, 11492722757652745345837786337415, 97683856811305401661395772475741908, 97683856811306735520013557117234431, 20475579704156449091372562437862, 97683, 11489482820843573453336899793410, 11489482820843715081986102782423⟩ := walkP_spec 1000 97000 _ _ (by norm_num) inv_97000 wk_98
theorem inv_99000 : Inv 99000 ⟨11502875129116621724413079786259, 11502875129116763353062282792393, 98684199977112422672051798184345711, 98684199977113768852362063486849825, 20493665916732371728496933865800, 98684, 11499678104884493635224661126796, 11499678104884635263873864128822⟩ := walkP_spec 1000 98000 _ _ (by norm_num) inv_98000 wk_99
theorem inv_100000 : Inv 100000 ⟨11512925464970123165596628642300, 11512925464970264794245831661434, 99685389268611541235524122736998713, 99685389268612899737526868701603584, 20511592825190780161845326219264, 99685, 11509770493276821973487737331393, 11509770493276963602136940346432⟩ := walkP_spec 1000 99000 _ _ (by norm_num) inv_99000 wk_100

/-- **`∏_{p ≤ x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)` for primes `5 ≤ x ≤ 10⁵`.** -/
theorem mertens_product_kernel (x : ℕ) (hx : x.Prime) (h5 : 5 ≤ x) (h : x ≤ 10 ^ 5) :
    ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) <
      Real.exp eulerMascheroniConstant *
          Real.log (∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log p) +
        2.50637 / Real.log (∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log p) :=
  inv_100000.2.2.2.2.2.2.2.2 x h5 (by omega) hx

/-- **`∏_{p ≤ 10⁵} p/(p−1) ≤ 20.5116`**, from the state of the walk at `10⁵`. -/
theorem prod_le_1e5 : ∏ p ∈ (Icc 1 100000).filter Nat.Prime, ((p : ℝ) / (p - 1)) ≤ 20.5116 := by
  have h := inv_100000.2.2.2.2.1
  change (10 : ℝ) ^ 30 * Fp 100000 ≤ ((20511592825190780161845326219264 : ℕ) : ℝ) at h
  unfold Fp at h
  push_cast at h
  linarith

end TernaryGoldbach.Prelim.MertProd
