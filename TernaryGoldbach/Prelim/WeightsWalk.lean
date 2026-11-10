import TernaryGoldbach.Prelim.SqfreeWalk

/-!
# The weights `a_k = |Λ(k) − 1|` up to `10⁶`

`G(m) = ∑_{2 ≤ k ≤ m} a_k/k` and `H(m) = ∑_{2 ≤ k ≤ m} a_k/√k`. A kernel walk (`walkW`) keeps
fixed-point bounds (scale `S = 10¹²`) for both, from the bounds `lamT` for `Λ(k)/k` (`SmallEWalk`),
and a bracket for `log k` (from `k = 10` on). The data (`Prelim/WeightsData*.lean`) record the bounds
at the points the cells of `SchoenfeldCells.lean` use.
-/

open Finset

namespace TernaryGoldbach.Prelim.Wts
open TernaryGoldbach.Prelim.SmallE (S S_pos cdiv cdiv_ge lgLo lgHi log_succ_bounds div_le' lamT lamT_spec)

/-- `a_k = |Λ(k) − 1|`. -/
noncomputable def aw (k : ℕ) : ℝ := |(ArithmeticFunction.vonMangoldt k : ℝ) - 1|

/-- `G(m) = ∑_{2 ≤ k ≤ m} a_k/k`. -/
noncomputable def Gw (m : ℕ) : ℝ := ∑ k ∈ Icc 2 m, aw k / k
/-- `H(m) = ∑_{2 ≤ k ≤ m} a_k/√k`. -/
noncomputable def Hw (m : ℕ) : ℝ := ∑ k ∈ Icc 2 m, aw k / √(k : ℝ)

/-- Bounds for `S a_m/m` from bounds for `S log m`. -/
def aT (m lo hi : ℕ) : ℕ × ℕ :=
  let l := lamT m lo hi
  ((l.1 - cdiv S m) + (S / m - l.2), max (l.2 - S / m) (cdiv S m - l.1))

theorem aT_spec {m lo hi : ℕ} (h2 : 2 ≤ m) (h6 : m ≤ 1000000)
    (hlo : (lo : ℝ) / S ≤ Real.log m) (hhi : Real.log m ≤ (hi : ℝ) / S) :
    ((aT m lo hi).1 : ℝ) / S ≤ aw m / m ∧ aw m / m ≤ ((aT m lo hi).2 : ℝ) / S := by
  obtain ⟨l1, l2⟩ := lamT_spec h2 h6 hlo hhi
  have hS := S_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have r1 : (((S / m : ℕ) : ℕ) : ℝ) / S ≤ 1 / m := by
    rw [div_le_iff₀ hS]; calc (((S / m : ℕ) : ℕ) : ℝ) ≤ (S : ℝ) / m := div_le' _ _
      _ = 1 / m * S := by ring
  have r2 : 1 / (m : ℝ) ≤ ((cdiv S m : ℕ) : ℝ) / S := by
    rw [le_div_iff₀ hS]; calc 1 / (m : ℝ) * S = (S : ℝ) / m := by ring
      _ ≤ _ := cdiv_ge (by omega)
  set L1 := (lamT m lo hi).1
  set L2 := (lamT m lo hi).2
  have e : aw m / m = |(ArithmeticFunction.vonMangoldt m : ℝ) / m - 1 / m| := by
    unfold aw; rw [← sub_div, abs_div, abs_of_pos hm0]
  rw [e]
  unfold aT
  simp only
  constructor
  · -- lower bound: at most one of the truncated differences is positive
    by_cases hA : cdiv S m ≤ L1
    · have hz : S / m - L2 = 0 := by
        have : S / m ≤ cdiv S m := by
          unfold cdiv; exact Nat.div_le_div_right (by omega)
        have : (L1 : ℝ) / S ≤ L2 / S := le_trans l1 l2
        have : L1 ≤ L2 := by
          have := (div_le_div_iff_of_pos_right hS).1 this; exact_mod_cast this
        omega
      rw [hz, add_zero, Nat.cast_sub hA, sub_div]
      rw [le_abs]; left; linarith
    · rw [show L1 - cdiv S m = 0 by omega, zero_add]
      by_cases hB : L2 ≤ S / m
      · rw [Nat.cast_sub hB, sub_div, le_abs]; right; linarith
      · rw [show S / m - L2 = 0 by omega]; simp
  · rw [abs_le]
    constructor
    · have : ((cdiv S m - L1 : ℕ) : ℝ) / S ≤ ((max (L2 - S / m) (cdiv S m - L1) : ℕ) : ℝ) / S :=
        div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) hS.le
      have h3 : ((cdiv S m : ℕ) : ℝ) / S - (L1 : ℝ) / S ≤ ((cdiv S m - L1 : ℕ) : ℝ) / S := by
        rw [← sub_div]; exact div_le_div_of_nonneg_right (by
          have := Nat.sub_le_sub_right (le_refl (cdiv S m)) L1
          rcases le_total L1 (cdiv S m) with h | h
          · rw [Nat.cast_sub h]
          · rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h) hS.le
      linarith
    · have : ((L2 - S / m : ℕ) : ℝ) / S ≤ ((max (L2 - S / m) (cdiv S m - L1) : ℕ) : ℝ) / S :=
        div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hS.le
      have h3 : (L2 : ℝ) / S - (((S / m : ℕ) : ℕ) : ℝ) / S ≤ ((L2 - S / m : ℕ) : ℝ) / S := by
        rw [← sub_div]; exact div_le_div_of_nonneg_right (by
          rcases le_total (S / m) L2 with h | h
          · rw [Nat.cast_sub h]
          · rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h) hS.le
      linarith

/-- The invariant at `m`: bounds for `G(m)`, `H(m)`, and (from `m = 10` on) for `log m`. -/
def InvW (m : ℕ) (glo ghi : ℤ) (Glo Ghi Hlo Hhi : ℕ) : Prop :=
  (Glo : ℝ) / S ≤ Gw m ∧ Gw m ≤ (Ghi : ℝ) / S ∧ (Hlo : ℝ) / S ≤ Hw m ∧ Hw m ≤ (Hhi : ℝ) / S ∧
    (10 ≤ m → (glo : ℝ) / S ≤ Real.log m ∧ Real.log m ≤ (ghi : ℝ) / S)

/-- The certified brackets of `S log L`, `L = 2, …, 10` (`SqfreeWalk.logc2` … `logc10`). -/
def logTab : List (ℤ × ℤ) := [(693147180558, 693147180574), (1098612288616, 1098612288727), (1386294361068, 1386294361179), (1609437912382, 1609437912496), (1791759469175, 1791759469348), (1945910149001, 1945910149563), (2079441541576, 2079441541797), (2197224577232, 2197224577454), (2302585092890, 2302585093112)]

/-- The log bracket of `m + 1`. -/
def nextLog (m : ℕ) (glo ghi : ℤ) : ℤ × ℤ :=
  if m + 1 ≤ 10 then logTab.getD (m - 1) (0, 0) else (glo + lgLo m, ghi + lgHi m)

def walkW : ℕ → ℕ → ℤ → ℤ → ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℤ × ℤ × ℕ × ℕ × ℕ × ℕ)
  | 0, m, glo, ghi, Glo, Ghi, Hlo, Hhi => some (m, glo, ghi, Glo, Ghi, Hlo, Hhi)
  | f + 1, m, glo, ghi, Glo, Ghi, Hlo, Hhi =>
    let g := nextLog m glo ghi
    let a := aT (m + 1) g.1.toNat g.2.toNat
    let s := Nat.sqrt (m + 1)
    if 1 ≤ m && m + 1 ≤ 1000000 && 0 ≤ g.1 then
      walkW f (m + 1) g.1 g.2 (Glo + a.1) (Ghi + a.2) (Hlo + a.1 * s) (Hhi + a.2 * (s + 1))
    else none

theorem nextLog_spec {m : ℕ} {glo ghi : ℤ} (hm : 1 ≤ m)
    (hl : 10 ≤ m → (glo : ℝ) / S ≤ Real.log m ∧ Real.log m ≤ (ghi : ℝ) / S) :
    ((nextLog m glo ghi).1 : ℝ) / S ≤ Real.log ((m + 1 : ℕ) : ℝ) ∧
      Real.log ((m + 1 : ℕ) : ℝ) ≤ ((nextLog m glo ghi).2 : ℝ) / S := by
  unfold nextLog
  split_ifs with h1
  · have h9 : m ≤ 9 := by omega
    interval_cases m
    · have := Sqf.logc2; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
    · have := Sqf.logc3; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
    · have := Sqf.logc4; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
    · have := Sqf.logc5; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
    · have := Sqf.logc6; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
    · have := Sqf.logc7; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
    · have := Sqf.logc8; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
    · have := Sqf.logc9; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
    · have := Sqf.logc10; simp only [logTab, List.getD]; push_cast at this ⊢; exact this
  · obtain ⟨l1, l2⟩ := hl (by omega)
    obtain ⟨b1, b2⟩ := log_succ_bounds (n := m) (by omega)
    push_cast at b1 b2 ⊢
    constructor
    · rw [add_div]; linarith
    · rw [add_div]; linarith

theorem invW_step {m : ℕ} {glo ghi : ℤ} {Glo Ghi Hlo Hhi : ℕ} (hm : 1 ≤ m) (hm6 : m + 1 ≤ 1000000)
    (hg0 : 0 ≤ (nextLog m glo ghi).1) (hI : InvW m glo ghi Glo Ghi Hlo Hhi) :
    let g := nextLog m glo ghi
    let a := aT (m + 1) g.1.toNat g.2.toNat
    let s := Nat.sqrt (m + 1)
    InvW (m + 1) g.1 g.2 (Glo + a.1) (Ghi + a.2) (Hlo + a.1 * s) (Hhi + a.2 * (s + 1)) := by
  intro g a s
  obtain ⟨G1, G2, H1, H2, hl⟩ := hI
  obtain ⟨n1, n2⟩ := nextLog_spec hm hl
  have hg1 : (0 : ℤ) ≤ g.2 := by
    have : (0 : ℝ) ≤ (g.2 : ℝ) / S := le_trans (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m + 1))) n2
    have hS := S_pos
    have : (0 : ℝ) ≤ (g.2 : ℝ) := by
      by_contra h; push Not at h; have := div_neg_of_neg_of_pos h hS; linarith
    exact_mod_cast this
  have hlo : ((g.1.toNat : ℕ) : ℝ) / S ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    rw [show ((g.1.toNat : ℕ) : ℝ) = (g.1 : ℝ) by exact_mod_cast Int.toNat_of_nonneg hg0]; exact n1
  have hhi : Real.log ((m + 1 : ℕ) : ℝ) ≤ ((g.2.toNat : ℕ) : ℝ) / S := by
    rw [show ((g.2.toNat : ℕ) : ℝ) = (g.2 : ℝ) by exact_mod_cast Int.toNat_of_nonneg hg1]; exact n2
  have hspec := aT_spec (m := m + 1) (by omega) hm6 hlo hhi
  have a1 : ((a.1 : ℕ) : ℝ) / S ≤ aw (m + 1) / ((m + 1 : ℕ) : ℝ) := hspec.1
  have a2 : aw (m + 1) / ((m + 1 : ℕ) : ℝ) ≤ ((a.2 : ℕ) : ℝ) / S := hspec.2
  have hS := S_pos
  have hk0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hs1 : ((s : ℕ) : ℝ) ≤ √((m + 1 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have := Nat.sqrt_le' (m + 1)
    exact_mod_cast (by nlinarith [this] : (s : ℕ) ^ 2 ≤ m + 1)
  have hs2 : √((m + 1 : ℕ) : ℝ) ≤ ((s : ℕ) : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    have h := Nat.lt_succ_sqrt' (m + 1)
    have : m + 1 ≤ (s + 1) ^ 2 := h.le
    exact_mod_cast this
  have hsq := Real.mul_self_sqrt hk0.le
  have hsp : 0 < √((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hk0
  have haw : 0 ≤ aw (m + 1) / ((m + 1 : ℕ) : ℝ) := by unfold aw; positivity
  -- `a/√k = (a/k) √k`
  have eH : aw (m + 1) / √((m + 1 : ℕ) : ℝ) = aw (m + 1) / ((m + 1 : ℕ) : ℝ) * √((m + 1 : ℕ) : ℝ) := by
    field_simp; rw [Real.sq_sqrt hk0.le]
  have hGs : Gw (m + 1) = Gw m + aw (m + 1) / ((m + 1 : ℕ) : ℝ) := by
    unfold Gw; rw [Finset.sum_Icc_succ_top (by omega)]
  have hHs : Hw (m + 1) = Hw m + aw (m + 1) / √((m + 1 : ℕ) : ℝ) := by
    unfold Hw; rw [Finset.sum_Icc_succ_top (by omega)]
  refine ⟨?_, ?_, ?_, ?_, fun _ => ⟨n1, n2⟩⟩
  · rw [hGs]; push_cast at a1 ⊢; rw [add_div]; linarith
  · rw [hGs]; push_cast at a2 ⊢; rw [add_div]; linarith
  · rw [hHs, eH]; push_cast; rw [add_div]
    have : ((a.1 : ℝ) * (s : ℝ)) / S ≤ aw (m + 1) / ((m + 1 : ℕ) : ℝ) * √((m + 1 : ℕ) : ℝ) := by
      rw [mul_div_right_comm]
      exact mul_le_mul a1 hs1 (by positivity) haw
    push_cast at this ⊢
    linarith
  · rw [hHs, eH]; push_cast; rw [add_div]
    have : aw (m + 1) / ((m + 1 : ℕ) : ℝ) * √((m + 1 : ℕ) : ℝ) ≤ ((a.2 : ℝ) * ((s : ℝ) + 1)) / S := by
      rw [mul_div_right_comm]
      exact mul_le_mul a2 hs2 (by positivity) (by positivity)
    push_cast at this ⊢
    linarith

theorem walkW_spec : ∀ (f m : ℕ) (glo ghi : ℤ) (Glo Ghi Hlo Hhi m' : ℕ) (glo' ghi' : ℤ) (Glo' Ghi' Hlo' Hhi' : ℕ),
    InvW m glo ghi Glo Ghi Hlo Hhi →
    walkW f m glo ghi Glo Ghi Hlo Hhi = some (m', glo', ghi', Glo', Ghi', Hlo', Hhi') →
    InvW m' glo' ghi' Glo' Ghi' Hlo' Hhi' := by
  intro f
  induction f with
  | zero =>
    intro m glo ghi Glo Ghi Hlo Hhi m' glo' ghi' Glo' Ghi' Hlo' Hhi' hI h
    simp only [walkW, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact hI
  | succ f ih =>
    intro m glo ghi Glo Ghi Hlo Hhi m' glo' ghi' Glo' Ghi' Hlo' Hhi' hI h
    simp only [walkW] at h
    by_cases hc : (decide (1 ≤ m) && decide (m + 1 ≤ 1000000) && decide (0 ≤ (nextLog m glo ghi).1)) = true
    swap
    · rw [if_neg hc] at h; simp at h
    rw [if_pos hc] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ (invW_step hc.1.1 hc.1.2 hc.2 hI) h

def resEqW : Option (ℕ × ℤ × ℤ × ℕ × ℕ × ℕ × ℕ) → ℕ → ℤ → ℤ → ℕ → ℕ → ℕ → ℕ → Bool
  | some (a, b, c, d, e, f, g), a', b', c', d', e', f', g' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g'
  | none, _, _, _, _, _, _, _ => false

theorem resEqW_spec {r : Option (ℕ × ℤ × ℤ × ℕ × ℕ × ℕ × ℕ)} {a : ℕ} {b c : ℤ} {d e f g : ℕ}
    (h : resEqW r a b c d e f g = true) : r = some (a, b, c, d, e, f, g) := by
  match r, h with
  | some (a0, b0, c0, d0, e0, f0, g0), h =>
    simp only [resEqW, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    rw [h1, h2, h3, h4, h5, h6, h7]

theorem invW_one : InvW 1 0 0 0 0 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, fun h => by omega⟩ <;> simp [Gw, Hw]

end TernaryGoldbach.Prelim.Wts
