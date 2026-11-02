import Mathlib
import TernaryGoldbach.Prelim.SmallPsi

/-!
# [MV73, Lemma 8]: `∑_{r ≤ R} (1 + r/R)⁻¹ μ(r)²/φ(r) ≥ log R + 0.25068` for `R ≥ 2`

[H, p. 97]: true for `R ≥ 100` by [MV73, Lemma 8], "and easily verifiable numerically for
`2 ≤ R < 100`". We prove it

* for `2 ≤ R < 6` from the exact values at `n = ⌊R⌋ ≤ 5`: the endpoint value
  `∑_{r≤n} g(r)(n+1)/(n+1+r) > log(n+1) + 0.25068`, and `∑_{r≤n} g(r) r(n+1)/((n+1+r)(n+r)) ≤ 1`,
  which makes `R ↦ W(R) − log R` reach its minimum over `[n, n+1)` at the right end;
* for `6 ≤ R < 1000` by a kernel check (`Prelim/SmallW.lean`);
* for `R ≥ 1000`, Abel summation against [MV73, Lemma 7], `G(r) = ∑_{s≤r} μ(s)²/φ(s) ≥
  log r + 1.07` (`r ≥ 6`), comparing `∑ f(r) log(r/(r−1))` with `Φ(t) = log(t/(R+t))`.

Here `g(r) = μ(r)²/φ(r)` and `f(r) = (1 + r/R)⁻¹`.
-/

open Finset Real

namespace TernaryGoldbach.Prelim.MV

/-- `g(r) = μ(r)²/φ(r)`. -/
noncomputable def gS (r : ℕ) : ℝ := if Squarefree r then 1 / (Nat.totient r : ℝ) else 0

/-- `G(n) = ∑_{r ≤ n} μ(r)²/φ(r)`. -/
noncomputable def GS (n : ℕ) : ℝ := ∑ r ∈ Icc 1 n, gS r

theorem gS_nonneg (r : ℕ) : 0 ≤ gS r := by unfold gS; split_ifs <;> positivity

/-- Summation by parts: `∑_{r=1}^N f(r)(a(r) − a(r−1)) = f(N)a(N) + ∑_{r=1}^{N−1}(f(r)−f(r+1))a(r)`
(with `a(0) = 0`). -/
theorem abel (f a : ℕ → ℝ) (ha0 : a 0 = 0) (N : ℕ) :
    ∑ r ∈ Icc 1 N, f r * (a r - a (r - 1)) =
      f N * a N + ∑ r ∈ Ico 1 N, (f r - f (r + 1)) * a r := by
  induction N with
  | zero => simp [ha0]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp [ha0]
    · rw [sum_Ico_succ_top h, show N + 1 - 1 = N by omega]; ring

/-- Abel lower bound: if `f` is non-increasing and non-negative on `[1, N]` and `G ≥ L` on
`[1, N]` (`G(0) = L(0) = 0`), then `∑ f(r) g(r) ≥ ∑ f(r)(L(r) − L(r−1))`. -/
theorem abel_lower (f L : ℕ → ℝ) (N : ℕ) (hL0 : L 0 = 0)
    (hf : ∀ r, 1 ≤ r → r < N → f (r + 1) ≤ f r) (hf0 : 0 ≤ f N)
    (hGL : ∀ r, 1 ≤ r → r ≤ N → L r ≤ GS r) :
    ∑ r ∈ Icc 1 N, f r * (L r - L (r - 1)) ≤ ∑ r ∈ Icc 1 N, f r * gS r := by
  have hG : ∀ r, 1 ≤ r → gS r = GS r - GS (r - 1) := by
    intro r hr
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    simp only [GS, Nat.add_sub_cancel]
    rw [sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    ring
  have hG0 : GS 0 = 0 := by simp [GS]
  conv_rhs => rw [sum_congr rfl fun r hr => by rw [hG r (mem_Icc.1 hr).1]]
  rw [abel f L hL0, abel f GS hG0]
  have h1 : f N * L N ≤ f N * GS N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; rw [hL0, hG0]
    · exact mul_le_mul_of_nonneg_left (hGL N h le_rfl) hf0
  have h2 : ∑ r ∈ Ico 1 N, (f r - f (r + 1)) * L r ≤ ∑ r ∈ Ico 1 N, (f r - f (r + 1)) * GS r :=
    sum_le_sum fun r hr => by
      have := mem_Ico.1 hr
      exact mul_le_mul_of_nonneg_left (hGL r this.1 this.2.le) (by linarith [hf r this.1 this.2])
  linarith

/-- `t log(1 + 1/t)` is non-decreasing: `a log(1 + 1/a) ≤ b log(1 + 1/b)` for `0 < a ≤ b`. -/
theorem mul_log_one_add_inv_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a * Real.log (1 + 1 / a) ≤ b * Real.log (1 + 1 / b) := by
  have hmono : MonotoneOn (fun t : ℝ => t * Real.log (1 + 1 / t)) (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · refine ContinuousOn.mul continuousOn_id (ContinuousOn.log ?_ ?_)
      · exact continuousOn_const.add (continuousOn_const.div continuousOn_id fun t ht => ht.ne')
      · intro t ht; have : (0 : ℝ) < t := ht; positivity
    · intro t ht
      rw [interior_Ioi] at ht
      have ht' : (0 : ℝ) < t := ht
      refine DifferentiableAt.differentiableWithinAt ?_
      refine differentiableAt_id.mul (DifferentiableAt.log ?_ (by positivity))
      exact (differentiableAt_const _).add ((differentiableAt_const _).div differentiableAt_id ht'.ne')
    · intro t ht
      rw [interior_Ioi] at ht
      have ht' : (0 : ℝ) < t := ht
      have hd : HasDerivAt (fun t : ℝ => t * Real.log (1 + 1 / t))
          (1 * Real.log (1 + 1 / t) + t * ((-(1 / t ^ 2)) / (1 + 1 / t))) t := by
        refine (hasDerivAt_id t).mul ?_
        have h1 : HasDerivAt (fun t : ℝ => 1 + 1 / t) (-(1 / t ^ 2)) t := by
          have := (hasDerivAt_inv ht'.ne').const_add 1
          simpa [one_div] using this
        exact h1.log (by positivity)
      rw [hd.deriv]
      -- `log(1 + 1/t) ≥ 1/(t+1)`
      have hlog := Real.one_sub_inv_le_log_of_pos (x := 1 + 1 / t) (by positivity)
      have e1 : 1 - (1 + 1 / t)⁻¹ = 1 / (t + 1) := by field_simp; ring
      have e2 : t * ((-(1 / t ^ 2)) / (1 + 1 / t)) = -(1 / (t + 1)) := by field_simp
      rw [e1] at hlog
      rw [e2]; linarith
  exact hmono ha (lt_of_lt_of_le ha hab) hab

/-- `W(R) = ∑_{r ≤ R} g(r) R/(R + r)`. -/
noncomputable def WR (R : ℝ) : ℝ := ∑ r ∈ Icc 1 ⌊R⌋₊, gS r * (R / (R + r))

/-- Lemma 8 on `[n, n+1)`, `n = ⌊R⌋`, from the two finite sums at `n`. -/
theorem lemma8_of_num {R : ℝ} (hR2 : 2 ≤ R)
    (hA : Real.log (⌊R⌋₊ + 1) + 0.25068 < ∑ r ∈ Icc 1 ⌊R⌋₊, gS r * ((⌊R⌋₊ + 1) / (⌊R⌋₊ + 1 + r)))
    (hB : ∑ r ∈ Icc 1 ⌊R⌋₊, gS r * (r * (⌊R⌋₊ + 1) / ((⌊R⌋₊ + 1 + r) * (⌊R⌋₊ + r))) ≤ 1) :
    Real.log R + 0.25068 < WR R := by
  set n := ⌊R⌋₊ with hn
  have hR0 : 0 < R := by linarith
  have hnR : (n : ℝ) ≤ R := Nat.floor_le hR0.le
  have hRn : R < n + 1 := Nat.lt_floor_add_one R
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hR2)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- `A − W(R) ≤ (n+1−R)/(n+1) · B`
  have hdiff : ∑ r ∈ Icc 1 n, gS r * ((n + 1) / (n + 1 + r)) - WR R ≤
      (n + 1 - R) / (n + 1) * ∑ r ∈ Icc 1 n, gS r * (r * (n + 1) / ((n + 1 + r) * (n + r))) := by
    rw [WR, ← hn, ← sum_sub_distrib, mul_sum]
    refine sum_le_sum fun r hr => ?_
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (mem_Icc.1 hr).1
    have hg := gS_nonneg r
    have key : (n + 1 : ℝ) / (n + 1 + r) - R / (R + r) ≤
        (n + 1 - R) / (n + 1) * (r * (n + 1) / ((n + 1 + r) * (n + r))) := by
      have e : (n + 1 : ℝ) / (n + 1 + r) - R / (R + r) = r * (n + 1 - R) / ((n + 1 + r) * (R + r)) := by
        field_simp; ring
      rw [e]
      have e2 : (n + 1 - R) / (n + 1) * (r * (n + 1) / ((n + 1 + r) * (n + r))) =
          r * (n + 1 - R) / ((n + 1 + r) * (n + r)) := by field_simp
      rw [e2]
      exact div_le_div_of_nonneg_left (by nlinarith) (by positivity)
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    calc gS r * ((n + 1) / (n + 1 + r)) - gS r * (R / (R + r))
        = gS r * ((n + 1 : ℝ) / (n + 1 + r) - R / (R + r)) := by ring
      _ ≤ gS r * ((n + 1 - R) / (n + 1) * (r * (n + 1) / ((n + 1 + r) * (n + r)))) :=
          mul_le_mul_of_nonneg_left key hg
      _ = _ := by ring
  -- `(n+1−R)/(n+1) ≤ log((n+1)/R)`
  have hlog : (n + 1 - R) / (n + 1) ≤ Real.log (n + 1) - Real.log R := by
    have h := Real.log_le_sub_one_of_pos (x := R / (n + 1)) (by positivity)
    rw [Real.log_div hR0.ne' (by positivity)] at h
    have : R / (n + 1) - 1 = -((n + 1 - R) / (n + 1)) := by field_simp; ring
    linarith
  have hfac : 0 ≤ (n + 1 - R) / (n + 1) := div_nonneg (by linarith) (by positivity)
  have := mul_le_mul_of_nonneg_left hB hfac
  linarith

/-- `G(1..5)`. -/
theorem gS_small : gS 1 = 1 ∧ gS 2 = 1 ∧ gS 3 = 1 / 2 ∧ gS 4 = 0 ∧ gS 5 = 1 / 4 := by
  have h4 : ¬ Squarefree 4 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl]; exact fun h => by
      have := h 2 (dvd_refl _); norm_num at this
  refine ⟨by simp [gS], ?_, ?_, ?_, ?_⟩
  · simp [gS, Nat.prime_two.squarefree, Nat.totient_prime Nat.prime_two]
  · simp [gS, Nat.prime_three.squarefree, Nat.totient_prime Nat.prime_three]
  · simp [gS, h4]
  · simp [gS, Nat.prime_five.squarefree, Nat.totient_prime Nat.prime_five]

theorem GS_five : GS 5 = 11 / 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := gS_small
  simp [GS, sum_Icc_succ_top, h1, h2, h3, h4, h5]; norm_num

theorem log_lt_chk {u L : ℕ} (hL : 0 < L) (h : TernaryGoldbach.Prelim.Small.chkStep u (10 ^ 9) 1 L = true) :
    Real.log L < (u : ℝ) / 10 ^ 9 := by
  have := TernaryGoldbach.Prelim.Small.log_lt_of_chk (by norm_num) hL h
  push_cast at this; linarith

/-- The two finite sums for `2 ≤ n ≤ 5` (minimal margin `1.1·10⁻⁶`, at `n = 4`). -/
theorem lemma8_tiny_num (n : ℕ) (hn2 : 2 ≤ n) (hn : n ≤ 5) :
    Real.log (n + 1) + 0.25068 < ∑ r ∈ Icc 1 n, gS r * ((n + 1) / (n + 1 + r)) ∧
      ∑ r ∈ Icc 1 n, gS r * (r * (n + 1) / ((n + 1 + r) * (n + r))) ≤ 1 := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := gS_small
  have l3 := log_lt_chk (u := 1098612289) (L := 3) (by norm_num) (by decide +kernel)
  have l4 := log_lt_chk (u := 1386294362) (L := 4) (by norm_num) (by decide +kernel)
  have l5 := log_lt_chk (u := 1609437913) (L := 5) (by norm_num) (by decide +kernel)
  have l6 := log_lt_chk (u := 1791759470) (L := 6) (by norm_num) (by decide +kernel)
  interval_cases n
  · norm_num [sum_Icc_succ_top, g1, g2] at l3 ⊢; (try constructor) <;> linarith
  · norm_num [sum_Icc_succ_top, g1, g2, g3] at l4 ⊢; (try constructor) <;> linarith
  · norm_num [sum_Icc_succ_top, g1, g2, g3, g4] at l5 ⊢; (try constructor) <;> linarith
  · norm_num [sum_Icc_succ_top, g1, g2, g3, g4, g5] at l6 ⊢; (try constructor) <;> linarith

/-- Lemma 8 for `2 ≤ R < 6`. -/
theorem lemma8_tiny {R : ℝ} (hR2 : 2 ≤ R) (hR : R < 6) : Real.log R + 0.25068 < WR R := by
  have hR0 : 0 < R := by linarith
  have hn2 : 2 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR2)
  have hn5 : ⌊R⌋₊ ≤ 5 := by
    have h := (Nat.floor_lt hR0.le).2 (show R < ((6 : ℕ) : ℝ) by norm_num; linarith)
    omega
  obtain ⟨hA, hB⟩ := lemma8_tiny_num ⌊R⌋₊ hn2 hn5
  exact lemma8_of_num hR2 hA hB

theorem f_bounds {R : ℝ} (hR : 1000 ≤ R) {k : ℝ} (hk0 : 0 ≤ k) (hk6 : k ≤ 6) :
    1 - 6 / R ≤ R / (R + k) ∧ R / (R + k) ≤ 1 := by
  have hR0 : 0 < R := by linarith
  constructor
  · have e : R / (R + k) = 1 - k / (R + k) := by field_simp; ring
    rw [e]
    have : k / (R + k) ≤ 6 / R := by
      rw [div_le_div_iff₀ (by linarith) hR0]; nlinarith
    linarith
  · rw [div_le_one (by linarith)]; linarith

set_option maxHeartbeats 2000000 in
/-- Lemma 8 for `R ≥ 1000`, from Lemma 7. -/
theorem lemma8_large (h7 : ∀ r : ℕ, 6 ≤ r → Real.log r + 1.07 ≤ GS r) {R : ℝ} (hR : 1000 ≤ R) :
    Real.log R + 0.25068 ≤ WR R := by
  set N := ⌊R⌋₊ with hN
  have hR0 : 0 < R := by linarith
  have hNR : (N : ℝ) ≤ R := Nat.floor_le hR0.le
  have hRN : R < N + 1 := Nat.lt_floor_add_one R
  have hN7 : 7 ≤ N := Nat.le_floor (by norm_num; linarith)
  set f : ℕ → ℝ := fun r => R / (R + r) with hf
  set L : ℕ → ℝ := fun r => if r ≤ 5 then GS r else Real.log r + 1.07 with hL
  have hL0 : L 0 = 0 := by simp [hL, GS]
  have hab := abel_lower f L N hL0 (fun r _ _ => by
      simp only [hf]; push_cast
      exact div_le_div_of_nonneg_left hR0.le (by positivity) (by linarith))
    (by positivity) (fun r hr1 hrN => by
      simp only [hL]; split_ifs with h
      · exact le_rfl
      · exact h7 r (by omega))
  have hW : ∑ r ∈ Icc 1 N, f r * gS r = WR R := by
    rw [WR, ← hN]; exact sum_congr rfl fun r _ => by ring
  rw [hW] at hab
  refine le_trans ?_ hab
  -- split the sum at `6`
  have hsplit : ∑ r ∈ Icc 1 N, f r * (L r - L (r - 1)) =
      ∑ r ∈ Icc 1 6, f r * (L r - L (r - 1)) + ∑ r ∈ Icc 7 N, f r * (L r - L (r - 1)) := by
    rw [← sum_union]
    · congr 1; ext r; simp only [mem_union, mem_Icc]; omega
    · rw [disjoint_left]; intro r h1 h2; simp only [mem_Icc] at h1 h2; omega
  rw [hsplit]
  obtain ⟨g1, g2, g3, g4, g5⟩ := gS_small
  have hG : ∀ r, 1 ≤ r → r ≤ 5 → L r - L (r - 1) = gS r := by
    intro r h1 h5
    simp only [hL, if_pos h5, if_pos (by omega : r - 1 ≤ 5)]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    simp only [GS, Nat.add_sub_cancel]; rw [sum_Icc_succ_top (by omega)]; ring
  have hfirst : ∑ r ∈ Icc 1 6, f r * (L r - L (r - 1)) =
      f 1 * 1 + f 2 * 1 + f 3 * (1 / 2) + f 5 * (1 / 4) + f 6 * (Real.log 6 + 1.07 - 11 / 4) := by
    have e1 : L 1 - L 0 = 1 := by have := hG 1 le_rfl (by norm_num); simpa [g1] using this
    have e2 : L 2 - L 1 = 1 := by have := hG 2 (by norm_num) (by norm_num); simpa [g2] using this
    have e3 : L 3 - L 2 = 1 / 2 := by have := hG 3 (by norm_num) (by norm_num); simpa [g3] using this
    have e4 : L 4 - L 3 = 0 := by have := hG 4 (by norm_num) (by norm_num); simpa [g4] using this
    have e5 : L 5 - L 4 = 1 / 4 := by have := hG 5 (by norm_num) (by norm_num); simpa [g5] using this
    have e6 : L 6 - L 5 = Real.log 6 + 1.07 - 11 / 4 := by
      simp only [hL, show ¬ (6 : ℕ) ≤ 5 by norm_num, if_false, le_refl, if_true, GS_five]; push_cast; ring
    rw [sum_Icc_succ_top (by norm_num : 1 ≤ 6), sum_Icc_succ_top (by norm_num : 1 ≤ 5),
      sum_Icc_succ_top (by norm_num : 1 ≤ 4), sum_Icc_succ_top (by norm_num : 1 ≤ 3),
      sum_Icc_succ_top (by norm_num : 1 ≤ 2), Icc_self, sum_singleton]
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.sub_self]
    rw [e1, e2, e3, e4, e5, e6]; ring

  -- the tail `r ≥ 7`
  set Φ : ℕ → ℝ := fun t => Real.log t - Real.log (R + t) with hΦ
  have htail : ∀ r ∈ Icc 7 N, Φ r - Φ (r - 1) - (f (r - 1) - f r) * (1 / 6) ≤
      f r * (L r - L (r - 1)) := by
    intro r hr
    have hr7 := (mem_Icc.1 hr).1
    have hrc : (7 : ℝ) ≤ r := by exact_mod_cast hr7
    have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [hL, if_neg (show ¬ r ≤ 5 by omega), if_neg (show ¬ r - 1 ≤ 5 by omega), hr1]
    simp only [hΦ, hf, hr1]
    set a : ℝ := r - 1
    have ha : 0 < a := by simp only [a]; linarith
    have hb : a ≤ R + r - 1 := by simp only [a]; linarith
    have hmono := mul_log_one_add_inv_mono ha hb
    have hne : (r : ℝ) - 1 ≠ 0 := by linarith
    have hRr : R + (r : ℝ) ≠ 0 := by linarith
    have hRr1 : R + ((r : ℝ) - 1) ≠ 0 := by linarith
    have hRr1' : R + (r : ℝ) - 1 ≠ 0 := by linarith
    have e1 : Real.log r - Real.log (r - 1) = Real.log (1 + 1 / a) := by
      rw [← Real.log_div (by positivity) (by linarith)]; congr 1; simp only [a]; field_simp; ring
    have e2 : Real.log (R + r) - Real.log (R + (r - 1)) = Real.log (1 + 1 / (R + r - 1)) := by
      rw [← Real.log_div (by positivity) (by linarith)]; congr 1; field_simp; ring
    have hl1 : Real.log (1 + 1 / a) ≤ 1 / 6 := by
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [add_sub_cancel_left, div_le_div_iff₀ ha (by norm_num)]; simp only [a]; linarith
    have ha' : 0 < 1 / a := by positivity
    have hl0 : 0 ≤ Real.log (1 + 1 / a) := Real.log_nonneg (by linarith)
    have hfm : R / (R + r) ≤ R / (R + (r - 1)) :=
      div_le_div_of_nonneg_left hR0.le (by linarith) (by linarith)
    rw [show Real.log ↑r + 1.07 - (Real.log (↑r - 1) + 1.07) = Real.log r - Real.log (r - 1) by ring,
      e1]
    have key : Real.log (1 + 1 / a) - Real.log (1 + 1 / (R + r - 1)) ≤
        R / (R + (r - 1)) * Real.log (1 + 1 / a) := by
      have hb0 : 0 < R + r - 1 := by linarith
      have : R / (R + (r - 1)) = 1 - a / (R + r - 1) := by simp only [a]; field_simp; ring
      rw [this]
      have : a / (R + r - 1) * Real.log (1 + 1 / a) ≤ Real.log (1 + 1 / (R + r - 1)) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hb0]; linarith
      nlinarith
    have hdiff : (R / (R + (r - 1)) - R / (R + r)) * Real.log (1 + 1 / a) ≤
        (R / (R + (r - 1)) - R / (R + r)) * (1 / 6) :=
      mul_le_mul_of_nonneg_left hl1 (by linarith)
    rw [show Real.log r - Real.log (R + r) - (Real.log (r - 1) - Real.log (R + (r - 1))) =
      (Real.log r - Real.log (r - 1)) - (Real.log (R + r) - Real.log (R + (r - 1))) by ring, e1, e2]
    nlinarith
  have hsum_tail := sum_le_sum htail
  have htel : ∑ r ∈ Icc 7 N, (Φ r - Φ (r - 1) - (f (r - 1) - f r) * (1 / 6)) =
      Φ N - Φ 6 - (f 6 - f N) * (1 / 6) := by
    have h1 : ∀ M, 7 ≤ M → ∑ r ∈ Icc 7 M, (Φ r - Φ (r - 1) - (f (r - 1) - f r) * (1 / 6)) =
        Φ M - Φ 6 - (f 6 - f M) * (1 / 6) := by
      intro M hM
      induction M with
      | zero => omega
      | succ M ih =>
        rcases Nat.lt_or_ge M 7 with h | h
        · have : M = 6 := by omega
          subst this; simp
        · rw [sum_Icc_succ_top (by omega), ih h, show M + 1 - 1 = M by omega]; ring
    exact h1 N hN7
  rw [htel] at hsum_tail
  -- final numerics
  rw [hfirst]
  have hl2 := Real.log_two_lt_d9
  have hlogN : Φ N ≥ -Real.log 2 - 2 / R := by
    simp only [hΦ]
    have hN0 : (0 : ℝ) < N := by positivity
    rw [← Real.log_div hN0.ne' (by positivity)]
    have h1 : (R - 1) / (2 * R) ≤ N / (R + N) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hR1 : 1 / R < 1 := by rw [div_lt_one hR0]; linarith
    have h2 := Real.log_le_log (by apply div_pos <;> linarith) h1
    have h3 : Real.log ((R - 1) / (2 * R)) = -Real.log 2 + Real.log (1 - 1 / R) := by
      rw [show (R - 1) / (2 * R) = (1 - 1 / R) / 2 by field_simp]
      rw [Real.log_div (by linarith) (by norm_num)]
      ring
    have h4 : -(2 / R) ≤ Real.log (1 - 1 / R) := by
      have := Real.one_sub_inv_le_log_of_pos (x := 1 - 1 / R) (by linarith)
      have e : 1 - (1 - 1 / R)⁻¹ = -(1 / (R - 1)) := by
        have : R - 1 ≠ 0 := by linarith
        field_simp; ring
      rw [e] at this
      have : 1 / (R - 1) ≤ 2 / R := by rw [div_le_div_iff₀ (by linarith) hR0]; linarith
      linarith
    linarith
  have hΦ6 : Φ 6 = Real.log 6 - Real.log (R + 6) := by simp only [hΦ]; push_cast; ring
  have hlog6 : Real.log 6 ≤ 2.21 := by
    have := Real.log_le_sub_one_of_pos (x := 6 / Real.exp 1) (by positivity)
    rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at this
    have he := Real.exp_one_gt_d9
    have : 6 / Real.exp 1 ≤ 2.21 := by rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
    linarith
  have hlog6' : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hlogR6 : Real.log R ≤ Real.log (R + 6) := Real.log_le_log hR0 (by linarith)
  have fk : ∀ k : ℕ, k ≤ 6 → 1 - 6 / R ≤ f k ∧ f k ≤ 1 := fun k hk6 =>
    f_bounds hR (Nat.cast_nonneg k) (by exact_mod_cast hk6)
  have hfN : 1 / 2 ≤ f N := by
    simp only [hf]; rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨a1, -⟩ := fk 1 (by norm_num)
  obtain ⟨a2, -⟩ := fk 2 (by norm_num)
  obtain ⟨a3, -⟩ := fk 3 (by norm_num)
  obtain ⟨a5, -⟩ := fk 5 (by norm_num)
  obtain ⟨a6, b6⟩ := fk 6 (by norm_num)
  have h6R : 6 / R ≤ 6 / 1000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR
  have h2R : 2 / R ≤ 2 / 1000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR
  have h6R0 : 0 ≤ 6 / R := by positivity
  have hp : f 6 * Real.log 6 ≥ Real.log 6 - 6 / R * 2.21 := by
    have : (1 - f 6) * Real.log 6 ≤ 6 / R * 2.21 :=
      mul_le_mul (by linarith) hlog6 hlog6' h6R0
    have e : (1 - f 6) * Real.log 6 = Real.log 6 - f 6 * Real.log 6 := by ring
    linarith only [this, e]
  rw [hΦ6] at hsum_tail
  have hsplit6 : f 6 * (Real.log 6 + 1.07 - 11 / 4) = f 6 * Real.log 6 + f 6 * (1.07 - 11 / 4) := by
    ring
  rw [hsplit6]
  linarith only [hsum_tail, hlogN, hp, a1, a2, a3, a5, a6, b6, hfN, h6R, h2R, h6R0, hlogR6,
    hlog6, hlog6', hl2]

end TernaryGoldbach.Prelim.MV
