import TernaryGoldbach.Prelim.SmallPsiTable

/-!
# A kernel walk of `∑_{k ≤ n} Λ(k)/k` up to `10⁶`

With `S = 10¹²` the walk keeps integer bounds for `S L(n)`, `L(n) = ∑_{k ≤ n} Λ(k)/k`, for
`S H(n)`, `H(n) = ∑_{k ≤ n} 1/k`, and for `S log n`. `Λ(m)` comes from the smallest prime factor
(`SmallTab.spf`, `isPowOf`, `vonMangoldt_of_spf`); `log m` from a list of certified brackets for
`m ≤ 1001` (`chkLow`, `chkStep`, checked by the walk) and above from
`x − x²/2 + x³/3 − x⁴/4 − 2x⁵ ≤ log(1 + x) ≤ x − x²/2 + x³/3 + 2x⁴` (`x = 1/n ≤ 1/2`).
On each chunk `[a, b)` the walk checks `elo ≤ S(L(n) − log u) ≤ ehi` for `u ∈ [n, n + 1)`, i.e.
`elo/S ≤ E₁Λ(u) ≤ ehi/S` on the chunk. The fixed-point logarithms (`lgLo`, `lgHi`,
`log_succ_bounds`) and `lamT` are also used by the walks of `SqfreeWalk.lean` and `WeightsWalk.lean`.
-/

open Finset ArithmeticFunction

namespace TernaryGoldbach.Prelim.SmallE
open SmallTab (spf P1000 isPowOf lqLo lqHi lq_spec spf_eq_zero_iff vonMangoldt_of_spf spf_pos P1000_sorted)
open TernaryGoldbach.Prelim.Small (chkStep chkLow log_lt_of_chk le_log_of_chk)

def S : ℕ := 1000000000000

theorem S_pos : (0 : ℝ) < S := by unfold S; norm_num

noncomputable def Ls (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, (Λ k : ℝ) / k
noncomputable def Hs (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, (1 : ℝ) / k

/-- The invariant at `n`. -/
def Inv (n Llo Lhi Hlo Hhi glo ghi : ℕ) : Prop :=
  (Llo : ℝ) / S ≤ Ls n ∧ Ls n ≤ (Lhi : ℝ) / S ∧ (Hlo : ℝ) / S ≤ Hs n ∧ Hs n ≤ (Hhi : ℝ) / S ∧
    (glo : ℝ) / S ≤ Real.log n ∧ Real.log n ≤ (ghi : ℝ) / S

/-- `⌈a/b⌉`. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem cdiv_ge {a b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  unfold cdiv
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h := Nat.lt_div_mul_add (a := a + b - 1) hb
  have : a + b - 1 < (a + b - 1) / b * b + b := h
  have h2 : a ≤ (a + b - 1) / b * b := by omega
  exact_mod_cast h2

theorem div_le' (a b : ℕ) : (((a / b : ℕ) : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

/-- The increments of the log chain (`x = 1/n`). -/
def lgLo (n : ℕ) : ℤ := (S / n : ℕ) - (cdiv S (2 * n ^ 2) : ℕ) + (S / (3 * n ^ 3) : ℕ) -
  (cdiv S (4 * n ^ 4) : ℕ) - (cdiv (2 * S) (n ^ 5) : ℕ)
def lgHi (n : ℕ) : ℤ := (cdiv S n : ℕ) - (S / (2 * n ^ 2) : ℕ) + (cdiv S (3 * n ^ 3) : ℕ) +
  (cdiv (2 * S) (n ^ 4) : ℕ)

theorem log_succ_bounds {n : ℕ} (hn : 2 ≤ n) :
    ((lgLo n : ℝ)) / S ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ∧
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ ((lgHi n : ℝ)) / S := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := 1 / n with hx
  have hx0 : 0 < x := by positivity
  have hx2 : x ≤ 1 / 2 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hn2
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n = Real.log (1 + x) := by
    rw [← Real.log_div (by positivity) hn0.ne']; congr 1; rw [hx]; push_cast; field_simp
  rw [hlog]
  have habs : |(-x)| < 1 := by rw [abs_neg, abs_of_pos hx0]; linarith
  have h4 := Real.abs_log_sub_add_sum_range_le habs 4
  have h3 := Real.abs_log_sub_add_sum_range_le habs 3
  simp only [sum_range_succ, sum_range_zero, sub_neg_eq_add, abs_neg, abs_of_pos hx0] at h4 h3
  norm_num at h4 h3
  have hd : 0 < 1 - x := by linarith
  have k5 : x ^ 5 / (1 - x) ≤ 2 * x ^ 5 := by
    rw [div_le_iff₀ hd]; have : 0 ≤ x ^ 5 := by positivity
    nlinarith
  have k4 : x ^ 4 / (1 - x) ≤ 2 * x ^ 4 := by
    rw [div_le_iff₀ hd]; have : 0 ≤ x ^ 4 := by positivity
    nlinarith
  have hS := S_pos
  have e3 : (-x) ^ 3 = -x ^ 3 := by ring
  rw [e3] at h4 h3
  have lo : x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 - 2 * x ^ 5 ≤ Real.log (1 + x) := by
    have := (abs_le.1 h4).1; linarith
  have hi : Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 + 2 * x ^ 4 := by
    have := (abs_le.1 h3).2; linarith
  -- the integer roundings
  have hSn : ((S / n : ℕ) : ℝ) ≤ S * x := by rw [hx, mul_one_div]; exact div_le' _ _
  have hSn' : S * x ≤ (cdiv S n : ℝ) := by rw [hx, mul_one_div]; exact cdiv_ge (by omega)
  have e2 : S * (x ^ 2 / 2) = (S : ℝ) / ((2 * n ^ 2 : ℕ) : ℝ) := by rw [hx]; push_cast; field_simp
  have e3 : S * (x ^ 3 / 3) = (S : ℝ) / ((3 * n ^ 3 : ℕ) : ℝ) := by rw [hx]; push_cast; field_simp
  have e4 : S * (x ^ 4 / 4) = (S : ℝ) / ((4 * n ^ 4 : ℕ) : ℝ) := by rw [hx]; push_cast; field_simp
  have e5 : S * (2 * x ^ 5) = ((2 * S : ℕ) : ℝ) / ((n ^ 5 : ℕ) : ℝ) := by rw [hx]; push_cast; field_simp
  have e4' : S * (2 * x ^ 4) = ((2 * S : ℕ) : ℝ) / ((n ^ 4 : ℕ) : ℝ) := by rw [hx]; push_cast; field_simp
  have p2 : 0 < 2 * n ^ 2 := by positivity
  have p3 : 0 < 3 * n ^ 3 := by positivity
  have p4 : 0 < 4 * n ^ 4 := by positivity
  have p5 : 0 < n ^ 5 := by positivity
  have p4' : 0 < n ^ 4 := by positivity
  have c2 := cdiv_ge (a := S) p2
  have c4 := cdiv_ge (a := S) p4
  have c5 := cdiv_ge (a := 2 * S) p5
  have c3 := cdiv_ge (a := S) p3
  have c4' := cdiv_ge (a := 2 * S) p4'
  have d2 := div_le' S (2 * n ^ 2)
  have d3 := div_le' S (3 * n ^ 3)
  have h1 : ((S / n : ℕ) : ℝ) ≤ S * x := hSn
  have h2 : S * (x ^ 2 / 2) ≤ ((cdiv S (2 * n ^ 2) : ℕ) : ℝ) := by rw [e2]; exact c2
  have h3' : ((S / (3 * n ^ 3) : ℕ) : ℝ) ≤ S * (x ^ 3 / 3) := by rw [e3]; exact d3
  have h4' : S * (x ^ 4 / 4) ≤ ((cdiv S (4 * n ^ 4) : ℕ) : ℝ) := by rw [e4]; exact c4
  have h5 : S * (2 * x ^ 5) ≤ ((cdiv (2 * S) (n ^ 5) : ℕ) : ℝ) := by rw [e5]; exact c5
  have g1 : S * x ≤ ((cdiv S n : ℕ) : ℝ) := hSn'
  have g2 : ((S / (2 * n ^ 2) : ℕ) : ℝ) ≤ S * (x ^ 2 / 2) := by rw [e2]; exact d2
  have g3 : S * (x ^ 3 / 3) ≤ ((cdiv S (3 * n ^ 3) : ℕ) : ℝ) := by rw [e3]; exact c3
  have g4 : S * (2 * x ^ 4) ≤ ((cdiv (2 * S) (n ^ 4) : ℕ) : ℝ) := by rw [e4']; exact c4'
  have eLo : ((lgLo n : ℤ) : ℝ) = ((S / n : ℕ) : ℝ) - ((cdiv S (2 * n ^ 2) : ℕ) : ℝ) +
      ((S / (3 * n ^ 3) : ℕ) : ℝ) - ((cdiv S (4 * n ^ 4) : ℕ) : ℝ) - ((cdiv (2 * S) (n ^ 5) : ℕ) : ℝ) := by
    unfold lgLo; simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
  have eHi : ((lgHi n : ℤ) : ℝ) = ((cdiv S n : ℕ) : ℝ) - ((S / (2 * n ^ 2) : ℕ) : ℝ) +
      ((cdiv S (3 * n ^ 3) : ℕ) : ℝ) + ((cdiv (2 * S) (n ^ 4) : ℕ) : ℝ) := by
    unfold lgHi; simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
  constructor
  · rw [div_le_iff₀ hS, eLo, mul_comm (Real.log (1 + x))]
    have := mul_le_mul_of_nonneg_left lo hS.le
    have ex : (S : ℝ) * (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 - 2 * x ^ 5) =
        S * x - S * (x ^ 2 / 2) + S * (x ^ 3 / 3) - S * (x ^ 4 / 4) - S * (2 * x ^ 5) := by ring
    rw [ex] at this
    linarith
  · rw [le_div_iff₀ hS, eHi, mul_comm (Real.log (1 + x))]
    have := mul_le_mul_of_nonneg_left hi hS.le
    have ex : (S : ℝ) * (x - x ^ 2 / 2 + x ^ 3 / 3 + 2 * x ^ 4) =
        S * x - S * (x ^ 2 / 2) + S * (x ^ 3 / 3) + S * (2 * x ^ 4) := by ring
    rw [ex] at this
    linarith

/-- `log m` for the step to `m = n + 1`: the list entry (certified) or the chain. -/
def logStep (n glo ghi : ℕ) : List (ℕ × ℕ) → Option (ℕ × ℕ × List (ℕ × ℕ))
  | (lo, hi) :: rest =>
    if chkLow lo S (n + 1) && chkStep hi S 1 (n + 1) then some (lo, hi, rest) else none
  | [] =>
    if 2 ≤ n then some ((glo + lgLo n).toNat, (ghi + lgHi n).toNat, []) else none

theorem logStep_spec {n glo ghi : ℕ} {l : List (ℕ × ℕ)} {lo hi : ℕ} {rest : List (ℕ × ℕ)}
    (hn : 1 ≤ n) (hg1 : (glo : ℝ) / S ≤ Real.log n) (hg2 : Real.log n ≤ (ghi : ℝ) / S)
    (h : logStep n glo ghi l = some (lo, hi, rest)) :
    (lo : ℝ) / S ≤ Real.log ((n + 1 : ℕ) : ℝ) ∧ Real.log ((n + 1 : ℕ) : ℝ) ≤ (hi : ℝ) / S := by
  have hS0 : (0 : ℕ) < S := by unfold S; norm_num
  have hS := S_pos
  cases l with
  | nil =>
    simp only [logStep] at h
    split_ifs at h with h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨b1, b2⟩ := log_succ_bounds h2
    have l0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have l1 : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
    constructor
    · have : ((glo + lgLo n : ℤ) : ℝ) / S ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
        rw [Int.cast_add, Int.cast_natCast, add_div]; linarith
      rcases le_or_gt 0 (glo + lgLo n) with hp | hp
      · rw [show (((glo + lgLo n).toNat : ℕ) : ℝ) = ((glo + lgLo n : ℤ) : ℝ) by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hp]]
        exact this
      · rw [Int.toNat_of_nonpos hp.le]; simp only [Nat.cast_zero, zero_div]
        exact le_trans l0 l1
    · have : Real.log ((n + 1 : ℕ) : ℝ) ≤ ((ghi + lgHi n : ℤ) : ℝ) / S := by
        rw [Int.cast_add, Int.cast_natCast, add_div]; linarith
      refine this.trans ?_
      rw [div_le_div_iff_of_pos_right hS]
      have h' := Int.self_le_toNat (ghi + lgHi n)
      have : ((ghi + lgHi n : ℤ) : ℝ) ≤ (((ghi + lgHi n).toNat : ℤ) : ℝ) := by exact_mod_cast h'
      rw [Int.cast_natCast] at this
      exact this
  | cons hd rest' =>
    obtain ⟨lo', hi'⟩ := hd
    simp only [logStep] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    simp only [Bool.and_eq_true] at hc
    have hpos : 0 < n + 1 := by omega
    exact ⟨by simpa using le_log_of_chk hS0 hpos hc.1,
      by have := log_lt_of_chk hS0 hpos hc.2; push_cast at this ⊢; linarith⟩

/-! ### `Λ(m)/m`, `1/m` and the walk -/

/-- Bounds for `S Λ(m)/m`, given `S log m ∈ [lo, hi]`. -/
def lamT (m lo hi : ℕ) : ℕ × ℕ :=
  if spf P1000 m = 0 then (lo / m, cdiv hi m)
  else if isPowOf (spf P1000 m) 20 m then
    (lqLo (spf P1000 m) * 1000 / m, cdiv (lqHi (spf P1000 m) * 1000) m)
  else (0, 0)

theorem lamT_spec {m lo hi : ℕ} (h2 : 2 ≤ m) (h6 : m ≤ 1000000)
    (hlo : (lo : ℝ) / S ≤ Real.log m) (hhi : Real.log m ≤ (hi : ℝ) / S) :
    ((lamT m lo hi).1 : ℝ) / S ≤ (Λ m : ℝ) / m ∧ (Λ m : ℝ) / m ≤ ((lamT m lo hi).2 : ℝ) / S := by
  have hS := S_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm0' : 0 < m := by omega
  unfold lamT
  split_ifs with hq hp
  · have hpr := (spf_eq_zero_iff h2 h6).1 hq
    rw [vonMangoldt_apply_prime hpr]
    constructor
    · calc (((lo / m : ℕ) : ℕ) : ℝ) / S ≤ ((lo : ℝ) / m) / S :=
            div_le_div_of_nonneg_right (div_le' _ _) hS.le
        _ = ((lo : ℝ) / S) / m := by ring
        _ ≤ Real.log m / m := div_le_div_of_nonneg_right hlo hm0.le
    · calc Real.log m / m ≤ ((hi : ℝ) / S) / m := div_le_div_of_nonneg_right hhi hm0.le
        _ = ((hi : ℝ) / m) / S := by ring
        _ ≤ ((cdiv hi m : ℕ) : ℝ) / S := div_le_div_of_nonneg_right (cdiv_ge hm0') hS.le
  · have hv := vonMangoldt_of_spf h2 h6 rfl hq
    rw [if_pos hp] at hv
    rw [hv]
    have hmem := (spf_pos rfl hq P1000_sorted).1
    obtain ⟨l1, l2⟩ := lq_spec hmem
    have hS9 : ((SmallTab.S : ℕ) : ℝ) = 1000000000 := by unfold SmallTab.S; norm_num
    rw [hS9] at l1 l2
    have hSv : (S : ℝ) = 1000000000000 := by unfold S; norm_num
    constructor
    · calc ((((lqLo (spf P1000 m) * 1000) / m : ℕ) : ℕ) : ℝ) / S ≤
            (((lqLo (spf P1000 m) * 1000 : ℕ) : ℝ) / m) / S :=
            div_le_div_of_nonneg_right (div_le' _ _) hS.le
        _ = ((lqLo (spf P1000 m) : ℝ) / 1000000000) / m := by rw [hSv]; push_cast; ring
        _ ≤ Real.log (spf P1000 m : ℕ) / m := div_le_div_of_nonneg_right l1 hm0.le
    · calc Real.log (spf P1000 m : ℕ) / m ≤ ((lqHi (spf P1000 m) : ℝ) / 1000000000) / m :=
            div_le_div_of_nonneg_right l2 hm0.le
        _ = (((lqHi (spf P1000 m) * 1000 : ℕ) : ℝ) / m) / S := by rw [hSv]; push_cast; ring
        _ ≤ ((cdiv (lqHi (spf P1000 m) * 1000) m : ℕ) : ℝ) / S :=
            div_le_div_of_nonneg_right (cdiv_ge hm0') hS.le
  · have hv := vonMangoldt_of_spf h2 h6 rfl hq
    rw [if_neg hp] at hv
    rw [hv]; simp

/-- The state at `n + 1` from the state at `n` and the log bracket `[lo, hi]` of `n + 1`. -/
def stepE (n Llo Lhi Hlo Hhi lo hi : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (Llo + (lamT (n + 1) lo hi).1, Lhi + (lamT (n + 1) lo hi).2, Hlo + S / (n + 1),
    Hhi + cdiv S (n + 1), lo, hi)

/-- The walk on `[n, n + len)`, checking `elo ≤ S(L(k) − log u) ≤ ehi` for `u ∈ [k, k + 1)`. -/
def walkE (elo ehi : ℤ) : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → List (ℕ × ℕ) → ℕ →
    Option ((ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ))
  | _, st, l, 0 => some (st, l)
  | n, (Llo, Lhi, Hlo, Hhi, glo, ghi), l, len + 1 =>
    if Nat.ble 1 n && Nat.ble (n + 1) 1000000 then
      match logStep n glo ghi l with
      | none => none
      | some (lo, hi, rest) =>
        if decide ((Lhi : ℤ) - glo ≤ ehi) && decide (elo ≤ (Llo : ℤ) - hi) then
          walkE elo ehi (n + 1) (stepE n Llo Lhi Hlo Hhi lo hi) rest len
        else none
    else none

theorem Ls_succ (n : ℕ) : Ls (n + 1) = Ls n + (Λ (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  rw [Ls, Ls, sum_Icc_succ_top (by omega)]

theorem Hs_succ (n : ℕ) : Hs (n + 1) = Hs n + 1 / ((n + 1 : ℕ) : ℝ) := by
  rw [Hs, Hs, sum_Icc_succ_top (by omega)]

/-- `E₁Λ(u) = ∑_{d ≤ u} Λ(d)/d − log u` (as in `PNTMertens`). -/
noncomputable def E1 (u : ℝ) : ℝ := ∑ d ∈ Finset.Ioc 0 ⌊u⌋₊, (Λ d : ℝ) / d - Real.log u

/-- `E₁Λ(u) = L(k) − log u` for `u ∈ [k, k + 1)`. -/
theorem E1_eq {k : ℕ} {u : ℝ} (hk : (k : ℝ) ≤ u) (hu : u < k + 1) :
    E1 u = Ls k - Real.log u := by
  have hfl : ⌊u⌋₊ = k := by
    rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) hk)]; exact ⟨hk, hu⟩
  have e : Finset.Ioc 0 k = Finset.Icc 1 k := by ext j; simp; omega
  rw [E1, hfl, e, Ls]

theorem walkE_spec (elo ehi : ℤ) : ∀ (len n : ℕ) (Llo Lhi Hlo Hhi glo ghi : ℕ) (l : List (ℕ × ℕ))
    (st' : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (l' : List (ℕ × ℕ)),
    Inv n Llo Lhi Hlo Hhi glo ghi →
    walkE elo ehi n (Llo, Lhi, Hlo, Hhi, glo, ghi) l len = some (st', l') →
    Inv (n + len) st'.1 st'.2.1 st'.2.2.1 st'.2.2.2.1 st'.2.2.2.2.1 st'.2.2.2.2.2 ∧
      ∀ u : ℝ, (n : ℝ) ≤ u → u < ((n + len : ℕ) : ℝ) →
        (elo : ℝ) / S ≤ E1 u ∧
          E1 u ≤ (ehi : ℝ) / S := by
  intro len
  induction len with
  | zero =>
    intro n Llo Lhi Hlo Hhi glo ghi l st' l' hI h
    simp only [walkE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simpa using hI, fun u h1 h2 => ?_⟩
    simp at h2; linarith
  | succ len ih =>
    intro n Llo Lhi Hlo Hhi glo ghi l st' l' hI h
    have hS := S_pos
    simp only [walkE] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨hn1, hn6⟩ := hc
    rcases hls : logStep n glo ghi l with _ | ⟨lo, hi, rest⟩
    · rw [hls] at h; simp at h
    rw [hls] at h
    simp only at h
    split_ifs at h with hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨c1, c2⟩ := hchk
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI
    obtain ⟨g1, g2⟩ := logStep_spec hn1 i5 i6 hls
    obtain ⟨t1, t2⟩ := lamT_spec (m := n + 1) (by omega) hn6 g1 g2
    have hm0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hI' : Inv (n + 1) (Llo + (lamT (n + 1) lo hi).1) (Lhi + (lamT (n + 1) lo hi).2)
        (Hlo + S / (n + 1)) (Hhi + cdiv S (n + 1)) lo hi := by
      have q1 : ((Llo + (lamT (n + 1) lo hi).1 : ℕ) : ℝ) / S = (Llo : ℝ) / S + ((lamT (n + 1) lo hi).1 : ℝ) / S := by
        push_cast; ring
      have q2 : ((Lhi + (lamT (n + 1) lo hi).2 : ℕ) : ℝ) / S = (Lhi : ℝ) / S + ((lamT (n + 1) lo hi).2 : ℝ) / S := by
        push_cast; ring
      have q3 : ((Hlo + S / (n + 1) : ℕ) : ℝ) / S = (Hlo : ℝ) / S + ((S / (n + 1) : ℕ) : ℝ) / S := by
        push_cast; ring
      have q4 : ((Hhi + cdiv S (n + 1) : ℕ) : ℝ) / S = (Hhi : ℝ) / S + ((cdiv S (n + 1) : ℕ) : ℝ) / S := by
        push_cast; ring
      have h3 : ((S / (n + 1) : ℕ) : ℝ) / S ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
        rw [div_le_iff₀ hS]
        have := div_le' S (n + 1)
        calc ((S / (n + 1) : ℕ) : ℝ) ≤ (S : ℝ) / ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
          _ = 1 / ((n + 1 : ℕ) : ℝ) * S := by ring
      have h4 : 1 / ((n + 1 : ℕ) : ℝ) ≤ ((cdiv S (n + 1) : ℕ) : ℝ) / S := by
        rw [le_div_iff₀ hS]
        have := cdiv_ge (a := S) (by omega : 0 < n + 1)
        calc 1 / ((n + 1 : ℕ) : ℝ) * S = (S : ℝ) / ((n + 1 : ℕ) : ℝ) := by ring
          _ ≤ _ := this
      refine ⟨?_, ?_, ?_, ?_, g1, g2⟩
      · rw [Ls_succ, q1]; linarith
      · rw [Ls_succ, q2]; linarith
      · rw [Hs_succ, q3]; linarith
      · rw [Hs_succ, q4]; linarith
    obtain ⟨ihI, ihE⟩ := ih (n + 1) _ _ _ _ _ _ rest st' l' hI' h
    refine ⟨by rw [show n + (len + 1) = n + 1 + len by omega]; exact ihI, fun u hu1 hu2 => ?_⟩
    rcases lt_or_ge u ((n + 1 : ℕ) : ℝ) with hlt | hge
    · -- `u ∈ [n, n + 1)`
      have hu' : u < (n : ℝ) + 1 := by push_cast at hlt; exact hlt
      rw [E1_eq hu1 hu']
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have lu1 : Real.log n ≤ Real.log u := Real.log_le_log hn0 hu1
      have lu2 : Real.log u ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_le_log (by linarith) hlt.le
      have c1' : ((Lhi : ℤ) : ℝ) - glo ≤ ehi := by exact_mod_cast c1
      have c2' : (elo : ℝ) ≤ ((Llo : ℤ) : ℝ) - hi := by exact_mod_cast c2
      push_cast at c1' c2'
      constructor
      · rw [div_le_iff₀ hS]
        have : (Llo : ℝ) / S - (hi : ℝ) / S ≤ Ls n - Real.log u := by linarith
        have e : (Llo : ℝ) / S - (hi : ℝ) / S = ((Llo : ℝ) - hi) / S := by ring
        rw [e, div_le_iff₀ hS] at this
        linarith
      · rw [le_div_iff₀ hS]
        have : Ls n - Real.log u ≤ (Lhi : ℝ) / S - (glo : ℝ) / S := by linarith
        have e : (Lhi : ℝ) / S - (glo : ℝ) / S = ((Lhi : ℝ) - glo) / S := by ring
        rw [e, le_div_iff₀ hS] at this
        linarith
    · exact ihE u hge (by rw [show n + 1 + len = n + (len + 1) by omega]; exact hu2)

/-- Component-wise comparison of a walk result with a given final state and an empty list. -/
def resEqE : Option ((ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ)) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | some ((a, b, c, d, e, f), []), a', b', c', d', e', f' =>
    Nat.beq a a' && Nat.beq b b' && Nat.beq c c' && Nat.beq d d' && Nat.beq e e' && Nat.beq f f'
  | _, _, _, _, _, _, _ => false

theorem resEqE_spec {r : Option ((ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ))} {a' b' c' d' e' f' : ℕ}
    (h : resEqE r a' b' c' d' e' f' = true) : r = some ((a', b', c', d', e', f'), []) := by
  rcases r with _ | ⟨⟨a, b, c, d, e, f⟩, l⟩
  · simp [resEqE] at h
  · rcases l with _ | ⟨x, l⟩
    · simp only [resEqE, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
      rw [Nat.beq_eq] at h1 h2 h3 h4 h5 h6
      subst h1 h2 h3 h4 h5 h6
      rfl
    · simp [resEqE] at h

/-! ### Chaining the chunks -/

/-- A table entry `(a, b, elo, ehi)`: `elo/S ≤ E₁Λ(u) ≤ ehi/S` for `u ∈ [a, b)`. -/
def ChunkOK (c : ℕ × ℕ × ℤ × ℤ) : Prop :=
  ∀ u : ℝ, (c.1 : ℝ) ≤ u → u < (c.2.1 : ℝ) → (c.2.2.1 : ℝ) / S ≤ E1 u ∧ E1 u ≤ (c.2.2.2 : ℝ) / S

theorem inv_one : Inv 1 0 0 S S 0 0 := by
  have hS := S_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Ls, Hs, div_self hS.ne']

/-- One chunk: the invariant moves from `a` to `a + len` and the chunk's bounds hold. -/
theorem chunk_step {elo ehi : ℤ} {a len Llo Lhi Hlo Hhi glo ghi : ℕ} {l : List (ℕ × ℕ)}
    {a' b' c' d' e' f' : ℕ} (hI : Inv a Llo Lhi Hlo Hhi glo ghi)
    (hw : resEqE (walkE elo ehi a (Llo, Lhi, Hlo, Hhi, glo, ghi) l len) a' b' c' d' e' f' = true) :
    Inv (a + len) a' b' c' d' e' f' ∧ ChunkOK (a, a + len, elo, ehi) := by
  obtain ⟨h1, h2⟩ := walkE_spec elo ehi len a _ _ _ _ _ _ l _ [] hI (resEqE_spec hw)
  exact ⟨h1, fun u hu1 hu2 => h2 u hu1 hu2⟩

/-- `γ` from the harmonic sum at `N`: `H(N) − log(N + 1) < γ < H(N) − log N`. -/
theorem gamma_bounds {N Llo Lhi Hlo Hhi glo ghi : ℕ} (hN : 1 ≤ N) (hI : Inv N Llo Lhi Hlo Hhi glo ghi) :
    (Hlo : ℝ) / S - (ghi : ℝ) / S - 1 / N < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (Hhi : ℝ) / S - (glo : ℝ) / S := by
  obtain ⟨-, -, i3, i4, i5, i6⟩ := hI
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hH : Hs N = (harmonic N : ℝ) := by
    rw [Hs, harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  rw [Real.eulerMascheroniSeq] at h1
  rw [Real.eulerMascheroniSeq', if_neg (by omega)] at h2
  have hl : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 / N := by
    have := Real.log_le_sub_one_of_pos (show 0 < ((N : ℝ) + 1) / N by positivity)
    rw [Real.log_div (by positivity) hN0.ne'] at this
    have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
    linarith
  rw [← hH] at h1 h2
  push_cast at h1 h2
  constructor <;> linarith

end TernaryGoldbach.Prelim.SmallE
