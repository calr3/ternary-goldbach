import TernaryGoldbach.Prelim.SmallMcheck
import TernaryGoldbach.Prelim.SmallMstarTable
import TernaryGoldbach.Prelim.MstarReduce

/-!
# `S(k) log(k+1) ≤ 0.8` for `1 ≤ k ≤ 22026`: the walks

`S(y) = ∑_{w ≤ √y} |m(y/w²)|/w²` (`MstarReduce.lean`). Two kernel-checked walks
(`scripts/gen_mstar_small.py` writes their chunks):

* **The table walk** (`twalk`): `SmallMcheck`'s walk, whose states carry `mlo ≤ 10²⁰ m(k) ≤ mhi`,
  checking `max(−mlo, mhi) ≤ 10⁸ t_k` at each `k`; so `10¹² |m(j)| ≤ t_j` for `j ≤ 22027`
  (`SmallMstarTable.tget`).
* **The `S` walk** (`swalk`): the state carries `k`, `r = ⌊√k⌋`, `S = ∑_{w ≤ r} c(k, w)` with
  `c(k, w) = ⌈t_{⌊k/w²⌋}/w²⌉ ≥ 10¹² |m(⌊k/w²⌋)|/w²`, and `L ≥ 10²⁰ log(k+1)`, and checks
  `S·L ≤ 0.8·10³²`. From `k` to `k + 1` only the `w` with `w² ∣ k + 1` change `c` (`dsum`), and a new
  term appears when `k + 1` is a square, so `S` is updated, not recomputed.
-/

open Finset

namespace TernaryGoldbach.Prelim.SmallMstar

open SmallMcheck (St step Good B logHi)

/-! ## The table walk -/

/-- `n` steps of `SmallMcheck.step`, checking `max(−mlo, mhi) ≤ 10⁸ t_k` first at each `k`. -/
def twalk : ℕ → St → Option St
  | 0, s => some s
  | n + 1, s =>
    if max (-s.mlo) s.mhi ≤ (tget s.k : ℤ) * 100000000 then
      match step s with
      | none => none
      | some s' => twalk n s'
    else none

theorem tbound {s : St} (hs : Good s) (h : max (-s.mlo) s.mhi ≤ (tget s.k : ℤ) * 100000000) :
    (10 ^ 12 : ℝ) * |msumR (s.k : ℝ)| ≤ tget s.k := by
  obtain ⟨-, -, hlo, hhi, -⟩ := hs
  have hB : (B : ℝ) = 10 ^ 20 := by norm_num [B]
  rw [hB] at hlo hhi
  have h1 : (((-s.mlo : ℤ)) : ℝ) ≤ ((tget s.k : ℤ) * 100000000 : ℤ) :=
    by exact_mod_cast (le_max_left _ _).trans h
  have h2 : ((s.mhi : ℤ) : ℝ) ≤ ((tget s.k : ℤ) * 100000000 : ℤ) :=
    by exact_mod_cast (le_max_right _ _).trans h
  push_cast at h1 h2
  rcases abs_cases (msumR (s.k : ℝ)) with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] <;> linarith

theorem twalk_spec : ∀ (n : ℕ) (s s' : St), Good s → twalk n s = some s' →
    Good s' ∧ s'.k = s.k + n ∧
      ∀ j : ℕ, s.k ≤ j → j < s'.k → (10 ^ 12 : ℝ) * |msumR (j : ℝ)| ≤ tget j := by
  intro n
  induction n with
  | zero =>
    intro s s' hs h
    simp only [twalk, Option.some.injEq] at h
    subst h
    exact ⟨hs, rfl, fun j h1 h2 => absurd h2 (by omega)⟩
  | succ n ih =>
    intro s s' hs h
    by_cases hc : max (-s.mlo) s.mhi ≤ (tget s.k : ℤ) * 100000000
    swap
    · simp [twalk, hc] at h
    simp only [twalk, hc, ↓reduceIte] at h
    split at h
    · exact absurd h (by simp)
    rename_i s1 hs1
    obtain ⟨hg1, hk1, -⟩ := SmallMcheck.step_spec hs hs1
    obtain ⟨hg', hk', hc'⟩ := ih s1 s' hg1 h
    refine ⟨hg', by omega, fun j h1 h2 => ?_⟩
    rcases (show j = s.k ∨ s1.k ≤ j by omega) with rfl | hj
    · exact tbound hs hc
    · exact hc' j hj h2

theorem tgood_init : Good SmallMcheck.s0 ∧
    ∀ j : ℕ, 1 ≤ j → j < SmallMcheck.s0.k → (10 ^ 12 : ℝ) * |msumR (j : ℝ)| ≤ tget j :=
  ⟨SmallMcheck.good_s0, fun j h1 h2 => absurd h2 (by simp only [SmallMcheck.s0]; omega)⟩

theorem tchain {s s' : St} {n : ℕ} (hs : Good s)
    (hP : ∀ j : ℕ, 1 ≤ j → j < s.k → (10 ^ 12 : ℝ) * |msumR (j : ℝ)| ≤ tget j)
    (h : twalk n s = some s') :
    Good s' ∧ ∀ j : ℕ, 1 ≤ j → j < s'.k → (10 ^ 12 : ℝ) * |msumR (j : ℝ)| ≤ tget j := by
  obtain ⟨hg, -, hc⟩ := twalk_spec n s s' hs h
  refine ⟨hg, fun j h1 h2 => ?_⟩
  rcases lt_or_ge j s.k with hj | hj
  · exact hP j h1 hj
  · exact hc j hj h2

/-! ## The `S` walk -/

/-- `c(k, w) = ⌈t_{⌊k/w²⌋}/w²⌉`. -/
def cc (k w : ℕ) : ℤ := ((tget (k / (w * w)) + w * w - 1) / (w * w) : ℕ)

/-- `∑_{w ≤ n, w² ∣ k+1} (c(k+1, w) − c(k, w))`. -/
def dsum (k n : ℕ) : ℤ :=
  Nat.rec 0 (fun m acc => acc + cond (Nat.beq ((k + 1) % ((m + 1) * (m + 1))) 0)
    (cc (k + 1) (m + 1) - cc k (m + 1)) 0) n

/-- The state at `k`. -/
structure SS where
  k : ℕ
  r : ℕ
  S : ℤ
  L : ℤ
  deriving DecidableEq

/-- From `k` to `k + 1`. -/
def sstep (s : SS) : SS :=
  let r' := cond (Nat.beq ((s.r + 1) * (s.r + 1)) (s.k + 1)) (s.r + 1) s.r
  ⟨s.k + 1, r', s.S + dsum s.k s.r + cond (Nat.beq r' s.r) 0 (cc (s.k + 1) r'),
    s.L + logHi (s.k + 1)⟩

/-- `n` steps, checking `S·L ≤ 0.8·10³²` at each `k` first. -/
def swalk (n : ℕ) (s : SS) : Option SS :=
  (Nat.rec (fun s => some s)
    (fun _ ih s => cond (decide (s.S * s.L ≤ 80000000000000000000000000000000)) (ih (sstep s)) none)
    n : SS → Option SS) s

theorem swalk_zero (s : SS) : swalk 0 s = some s := rfl

theorem swalk_succ (n : ℕ) (s : SS) :
    swalk (n + 1) s =
      cond (decide (s.S * s.L ≤ 80000000000000000000000000000000)) (swalk n (sstep s)) none := rfl

theorem cond_beq {α : Type*} (a b : ℕ) (x y : α) : cond (Nat.beq a b) x y = if a = b then x else y := by
  by_cases h : a = b
  · subst h; simp
  · have hb : Nat.beq a b = false := by
      cases hb : Nat.beq a b with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [hb]; simp [h]

theorem dsum_eq (k n : ℕ) :
    dsum k n = ∑ w ∈ Icc 1 n, (if (k + 1) % (w * w) = 0 then cc (k + 1) w - cc k w else 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : dsum k (n + 1) = dsum k n + cond (Nat.beq ((k + 1) % ((n + 1) * (n + 1))) 0)
        (cc (k + 1) (n + 1) - cc k (n + 1)) 0 := rfl
    rw [h, ih, sum_Icc_succ_top (by omega), cond_beq]

theorem cc_succ {k w : ℕ} (h : ¬ w * w ∣ k + 1) : cc (k + 1) w = cc k w := by
  unfold cc
  rw [Nat.succ_div_of_not_dvd h]

theorem sum_cc_succ (k r : ℕ) :
    ∑ w ∈ Icc 1 r, cc (k + 1) w = ∑ w ∈ Icc 1 r, cc k w + dsum k r := by
  rw [dsum_eq, ← sum_add_distrib]
  refine sum_congr rfl fun w _ => ?_
  split_ifs with h
  · ring
  · rw [cc_succ (fun hd => h (Nat.mod_eq_zero_of_dvd hd)), add_zero]

/-- The invariant. -/
def SGood (s : SS) : Prop :=
  1 ≤ s.k ∧ s.r * s.r ≤ s.k ∧ s.k < (s.r + 1) * (s.r + 1) ∧
    s.S = ∑ w ∈ Icc 1 s.r, cc s.k w ∧ (B : ℝ) * Real.log (s.k + 1) ≤ s.L

theorem sstep_good {s : SS} (hs : SGood s) : SGood (sstep s) := by
  obtain ⟨hk, hr1, hr2, hS, hL⟩ := hs
  -- the logarithm
  have hL' : (B : ℝ) * Real.log ((s.k + 1 : ℕ) + 1) ≤ s.L + logHi (s.k + 1) := by
    have hb := (SmallMcheck.log_bounds (k := s.k + 1) (by omega)).2
    have hk0 : (0 : ℝ) < (s.k : ℝ) + 1 := by positivity
    have hsplit : Real.log ((s.k + 1 : ℕ) + 1) =
        Real.log ((s.k : ℝ) + 1) + Real.log (1 + 1 / ((s.k + 1 : ℕ) : ℝ)) := by
      rw [← Real.log_mul hk0.ne' (by positivity)]
      congr 1
      push_cast
      field_simp
    rw [hsplit, mul_add]
    push_cast at hb ⊢
    linarith
  by_cases hsq : (s.r + 1) * (s.r + 1) = s.k + 1
  · have hc1 : cond (Nat.beq ((s.r + 1) * (s.r + 1)) (s.k + 1)) (s.r + 1) s.r = s.r + 1 := by
      rw [cond_beq]; simp [hsq]
    have hc2 : cond (Nat.beq (s.r + 1) s.r) (0 : ℤ) (cc (s.k + 1) (s.r + 1)) = cc (s.k + 1) (s.r + 1) := by
      rw [cond_beq]; simp
    simp only [sstep, hc1, hc2]
    refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; nlinarith, ?_, ?_⟩
    · dsimp only; rw [sum_Icc_succ_top (by omega), sum_cc_succ, hS]
    · dsimp only; exact_mod_cast hL'
  · have hc1 : cond (Nat.beq ((s.r + 1) * (s.r + 1)) (s.k + 1)) (s.r + 1) s.r = s.r := by
      rw [cond_beq]; simp [hsq]
    have hc2 : cond (Nat.beq s.r s.r) (0 : ℤ) (cc (s.k + 1) s.r) = 0 := by
      rw [cond_beq]; simp
    simp only [sstep, hc1, hc2]
    refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, ?_, ?_⟩
    · dsimp only; rw [sum_cc_succ, hS, add_zero]
    · dsimp only; exact_mod_cast hL'

/-- At a good state that passes the check, `S(k) log(k+1) ≤ 0.8`. -/
theorem sok_bound {s : SS} (hs : SGood s)
    (htab : ∀ j : ℕ, 1 ≤ j → j ≤ s.k → (10 ^ 12 : ℝ) * |msumR (j : ℝ)| ≤ tget j)
    (h : s.S * s.L ≤ 80000000000000000000000000000000) :
    Sm (s.k : ℝ) * Real.log (s.k + 1) ≤ 0.8 := by
  obtain ⟨hk, hr1, hr2, hS, hL⟩ := hs
  have hsq : Nat.sqrt s.k = s.r := (Nat.eq_sqrt.2 ⟨hr1, hr2⟩).symm
  have hB : (B : ℝ) = 10 ^ 20 := by norm_num [B]
  -- `10¹² S(k) ≤ S`
  have hSm : Sm (s.k : ℝ) * 10 ^ 12 ≤ (s.S : ℝ) := by
    rw [Sm, Nat.floor_natCast, hsq, hS, sum_mul]
    push_cast
    refine sum_le_sum fun w hw => ?_
    have hw1 : 1 ≤ w := (mem_Icc.1 hw).1
    have hwr : w ≤ s.r := (mem_Icc.1 hw).2
    have hww : 1 ≤ w * w := Nat.mul_pos hw1 hw1
    have hwk : w * w ≤ s.k := le_trans (Nat.mul_le_mul hwr hwr) hr1
    set j := s.k / (w * w) with hj
    have hj1 : 1 ≤ j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have hjk : j ≤ s.k := Nat.div_le_self _ _
    have hmj : msumR ((s.k : ℝ) / ((w : ℝ) * w)) = msumR (j : ℝ) := by
      rw [msumR, msumR, ← Nat.cast_mul, Nat.floor_div_eq_div, Nat.floor_natCast]
    have hww0 : (0 : ℝ) < ((w * w : ℕ) : ℝ) := by exact_mod_cast hww
    have ht := htab j hj1 hjk
    have hceil := SmallMcheck.le_nat_ceil_div (tget j) (w * w) hww
    unfold cc
    rw [hmj, ← hj]
    push_cast at hceil ⊢
    calc |msumR (j : ℝ)| / ((w : ℝ) * w) * 10 ^ 12 = 10 ^ 12 * |msumR (j : ℝ)| / ((w : ℝ) * w) := by ring
      _ ≤ (tget j : ℝ) / ((w : ℝ) * w) := by gcongr
      _ ≤ _ := hceil
  have hlog0 : 0 ≤ Real.log ((s.k : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg s.k : (0 : ℝ) ≤ s.k)])
  have hSm0 := Sm_nonneg (s.k : ℝ)
  have hh : ((s.S * s.L : ℤ) : ℝ) ≤ (80000000000000000000000000000000 : ℤ) := by exact_mod_cast h
  push_cast at hh
  rw [hB] at hL
  have key : (Sm (s.k : ℝ) * 10 ^ 12) * (10 ^ 20 * Real.log ((s.k : ℝ) + 1)) ≤ (s.S : ℝ) * s.L :=
    mul_le_mul hSm hL (by positivity) ((le_of_le_of_eq (by positivity) rfl).trans hSm)
  nlinarith

theorem swalk_spec : ∀ (n : ℕ) (s s' : SS), SGood s →
    (∀ j : ℕ, 1 ≤ j → j < s.k + n → (10 ^ 12 : ℝ) * |msumR (j : ℝ)| ≤ tget j) →
    swalk n s = some s' →
    SGood s' ∧ s'.k = s.k + n ∧ ∀ k : ℕ, s.k ≤ k → k < s'.k → Sm (k : ℝ) * Real.log (k + 1) ≤ 0.8 := by
  intro n
  induction n with
  | zero =>
    intro s s' hs _ h
    rw [swalk_zero, Option.some.injEq] at h
    subst h
    exact ⟨hs, rfl, fun k h1 h2 => absurd h2 (by omega)⟩
  | succ n ih =>
    intro s s' hs htab h
    rw [swalk_succ] at h
    by_cases hc : s.S * s.L ≤ 80000000000000000000000000000000
    swap
    · simp [hc] at h
    simp only [hc, decide_true, Bool.cond_true] at h
    have hg1 := sstep_good hs
    have hk1 : (sstep s).k = s.k + 1 := rfl
    obtain ⟨hg', hk', hc'⟩ := ih (sstep s) s' hg1 (fun j h1 h2 => htab j h1 (by omega)) h
    refine ⟨hg', by omega, fun k h1 h2 => ?_⟩
    rcases (show k = s.k ∨ (sstep s).k ≤ k by omega) with rfl | hj
    · exact sok_bound hs (fun j h1 h2 => htab j h1 (by omega)) hc
    · exact hc' k hj h2

theorem sgood_init : SGood ⟨1, 1, 1000000000000, 69314718080000000000⟩ ∧
    ∀ k : ℕ, 1 ≤ k → k < 1 → Sm (k : ℝ) * Real.log (k + 1) ≤ 0.8 := by
  refine ⟨⟨le_rfl, le_rfl, by norm_num, ?_, ?_⟩, fun k h1 h2 => absurd h2 (by omega)⟩
  · have : cc 1 1 = 1000000000000 := by decide +kernel
    simp [this]
  · have hb := (SmallMcheck.log_bounds (k := 1) le_rfl).2
    have : logHi 1 = 69314718080000000000 := by decide +kernel
    rw [this] at hb
    norm_num at hb ⊢
    linarith

theorem schain {s s' : SS} {n : ℕ}
    (htab : ∀ j : ℕ, 1 ≤ j → j ≤ 22027 → (10 ^ 12 : ℝ) * |msumR (j : ℝ)| ≤ tget j) (hs : SGood s)
    (hP : ∀ k : ℕ, 1 ≤ k → k < s.k → Sm (k : ℝ) * Real.log (k + 1) ≤ 0.8)
    (h : swalk n s = some s') (hlim : s.k + n ≤ 22028) :
    SGood s' ∧ ∀ k : ℕ, 1 ≤ k → k < s'.k → Sm (k : ℝ) * Real.log (k + 1) ≤ 0.8 := by
  obtain ⟨hg, -, hc⟩ := swalk_spec n s s' hs (fun j h1 h2 => htab j h1 (by omega)) h
  refine ⟨hg, fun k h1 h2 => ?_⟩
  rcases lt_or_ge k s.k with hk | hk
  · exact hP k h1 hk
  · exact hc k hk h2

end TernaryGoldbach.Prelim.SmallMstar
