import TernaryGoldbach.Prelim.SqfreeQ
import TernaryGoldbach.Prelim.SmallEWalk

/-!
# `Q₁(t) − κ log t` for `t ≤ 10⁴`

`Q₁(t) = ∑_{n ≤ t} μ²(n)/n`, `κ = 6/π²`. A kernel walk over `n ≤ 10⁴` (`walkQ`) keeps fixed-point
bounds (scale `S = 10¹²`) for `Q₁(n)` and `log n`, and checks `Q₁(n) − κ log n ≤ 1.166` and
`Q₁(n) − κ log(n+1) ≥ 0.578`, so `0.578 ≤ Q₁(t) − κ log t ≤ 1.166` on `[1, 10⁴)` (`Q1_small`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sqf
open TernaryGoldbach.Prelim.SmallE (S S_pos cdiv cdiv_ge lgLo lgHi log_succ_bounds div_le')

/-- `Q₁(t) = ∑_{n ≤ t} μ²(n)/n`. -/
noncomputable def Q1 (t : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊t⌋₊, sq n / n

/-- Trial division by `d² `, `2 ≤ d ≤ 100`. -/
def sqB (m : ℕ) : Bool := (List.range' 2 99).all (fun d => m < d * d || m % (d * d) != 0)

theorem sqB_iff {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ 10000) : sqB m = true ↔ Squarefree m := by
  unfold sqB
  simp only [List.all_eq_true, List.mem_range'_1, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  rw [Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h p hp hpp
    have hp2 := hp.two_le
    by_cases hp100 : p ≤ 100
    · rcases h p ⟨hp2, by omega⟩ with h' | h'
      · have := Nat.le_of_dvd (by omega) hpp; omega
      · exact h' (Nat.mod_eq_zero_of_dvd hpp)
    · have : 10000 < p * p := by nlinarith
      have := Nat.le_of_dvd (by omega) hpp; omega
  · intro h d hd
    by_cases hdd : m < d * d
    · exact Or.inl hdd
    · right; intro h0
      have hdv : d * d ∣ m := Nat.dvd_of_mod_eq_zero h0
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
      exact h p hp ((Nat.mul_dvd_mul hpd hpd).trans hdv)

/-- `κ` with denominator `S`: `kLo/S ≤ κ ≤ kHi/S`. -/
def kLo : ℕ := 607927101854
def kHi : ℕ := 607927101855

theorem kap_bounds : (kLo : ℝ) / S ≤ kap ∧ kap ≤ (kHi : ℝ) / S := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  have hp1 : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
  have hp2 : Real.pi ^ 2 < (3.14159265358979323847 : ℝ) ^ 2 := by nlinarith [Real.pi_pos]
  unfold kap kLo kHi
  rw [hS]
  norm_num at hp1 hp2
  constructor
  · rw [div_le_div_iff₀ (by norm_num) (by positivity)]; push_cast; nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; nlinarith

/-- The invariant at `n`. -/
def InvQ (n : ℕ) (qlo qhi : ℕ) (glo ghi : ℤ) : Prop :=
  (qlo : ℝ) / S ≤ Q1 n ∧ Q1 n ≤ (qhi : ℝ) / S ∧ (glo : ℝ) / S ≤ Real.log n ∧ Real.log n ≤ (ghi : ℝ) / S

def chkU (qhi : ℕ) (glo : ℤ) : Bool :=
  decide ((qhi : ℤ) * S - (kLo : ℤ) * glo ≤ 1166000000000000000000000)
def chkL (qlo : ℕ) (ghi : ℤ) : Bool :=
  decide (578000000000000000000000 ≤ (qlo : ℤ) * S - (kHi : ℤ) * ghi)

/-- The walk from `n` with fuel `f`: checks at `n`, then steps to `n + 1`. -/
def walkQ : ℕ → ℕ → ℕ → ℕ → ℤ → ℤ → Option (ℕ × ℕ × ℕ × ℤ × ℤ)
  | 0, n, qlo, qhi, glo, ghi => some (n, qlo, qhi, glo, ghi)
  | f + 1, n, qlo, qhi, glo, ghi =>
    let s := sqB (n + 1)
    let qlo' := if s then qlo + S / (n + 1) else qlo
    let qhi' := if s then qhi + cdiv S (n + 1) else qhi
    let glo' := glo + lgLo n
    let ghi' := ghi + lgHi n
    if 2 ≤ n && n + 1 ≤ 10000 && 0 ≤ glo && chkU qhi glo && chkL qlo ghi' then
      walkQ f (n + 1) qlo' qhi' glo' ghi'
    else none

/-- `0.578 ≤ Q₁(t) − κ log t ≤ 1.166` on `[n, n + 1)`. -/
def GoodQ (n : ℕ) : Prop :=
  ∀ t : ℝ, (n : ℝ) ≤ t → t < n + 1 → 0.578 ≤ Q1 t - kap * Real.log t ∧ Q1 t - kap * Real.log t ≤ 1.166

theorem Q1_nat_succ (n : ℕ) : Q1 ((n + 1 : ℕ) : ℝ) = Q1 n + sq (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  unfold Q1; rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_Icc_succ_top (by omega)]

theorem Q1_const {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) : Q1 t = Q1 n := by
  unfold Q1
  have : ⌊t⌋₊ = n := by
    rw [Nat.floor_eq_iff (by linarith [Nat.cast_nonneg (α := ℝ) n])]; exact ⟨h1, h2⟩
  rw [this, Nat.floor_natCast]

theorem goodQ_of {n qlo qhi : ℕ} {glo ghi ghi' : ℤ} (hn : 1 ≤ n) (hI : InvQ n qlo qhi glo ghi)
    (hlog1 : Real.log ((n + 1 : ℕ) : ℝ) ≤ (ghi' : ℝ) / S) (hg0 : 0 ≤ glo)
    (hU : chkU qhi glo = true) (hL : chkL qlo ghi' = true) : GoodQ n := by
  intro t h1 h2
  obtain ⟨q1, q2, g1, g2⟩ := hI
  have hS := S_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 < t := by linarith
  rw [Q1_const h1 h2]
  obtain ⟨k1, k2⟩ := kap_bounds
  have hlt1 : Real.log n ≤ Real.log t := Real.log_le_log hn0 h1
  have hlt2 : Real.log t ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_le_log ht0 (by push_cast; linarith)
  have hk0 : 0 ≤ kap := kap_pos.le
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  unfold chkU at hU
  unfold chkL at hL
  simp only [decide_eq_true_eq] at hU hL
  have hSv : (S : ℝ) = 1000000000000 := by norm_num [S]
  have hU' : (qhi : ℝ) * S - (kLo : ℝ) * (glo : ℝ) ≤ 1166 * (S : ℝ) * S / 1000 := by
    have := (Int.cast_le (R := ℝ)).2 hU
    push_cast at this; rw [hSv] at this ⊢; linarith
  have hL' : 578 * (S : ℝ) * S / 1000 ≤ (qlo : ℝ) * S - (kHi : ℝ) * (ghi' : ℝ) := by
    have := (Int.cast_le (R := ℝ)).2 hL
    push_cast at this; rw [hSv] at this ⊢; linarith
  constructor
  · -- lower
    have a1 : kap * Real.log t ≤ (kHi : ℝ) / S * ((ghi' : ℝ) / S) := by
      have hl0 : 0 ≤ Real.log t := le_trans hlogn0 hlt1
      calc kap * Real.log t ≤ (kHi : ℝ) / S * Real.log t := mul_le_mul_of_nonneg_right k2 hl0
        _ ≤ (kHi : ℝ) / S * ((ghi' : ℝ) / S) := mul_le_mul_of_nonneg_left (hlt2.trans hlog1) (by positivity)
    have e : (kHi : ℝ) / S * ((ghi' : ℝ) / S) = ((kHi : ℝ) * ghi') / (S * S) := by ring
    have e2 : (qlo : ℝ) / S = ((qlo : ℝ) * S) / (S * S) := by field_simp
    have : 0.578 ≤ (qlo : ℝ) / S - (kHi : ℝ) / S * ((ghi' : ℝ) / S) := by
      rw [e, e2, ← sub_div, le_div_iff₀ (by positivity)]; linarith
    linarith
  · -- upper
    have hg0r : (0 : ℝ) ≤ glo := by exact_mod_cast hg0
    have a1 : (kLo : ℝ) / S * ((glo : ℝ) / S) ≤ kap * Real.log t :=
      calc (kLo : ℝ) / S * ((glo : ℝ) / S) ≤ kap * ((glo : ℝ) / S) :=
            mul_le_mul_of_nonneg_right k1 (by positivity)
        _ ≤ kap * Real.log t := mul_le_mul_of_nonneg_left (g1.trans hlt1) hk0
    have e : (kLo : ℝ) / S * ((glo : ℝ) / S) = ((kLo : ℝ) * glo) / (S * S) := by ring
    have e2 : (qhi : ℝ) / S = ((qhi : ℝ) * S) / (S * S) := by field_simp
    have : (qhi : ℝ) / S - (kLo : ℝ) / S * ((glo : ℝ) / S) ≤ 1.166 := by
      rw [e, e2, ← sub_div, div_le_iff₀ (by positivity)]; linarith
    linarith

theorem invQ_step {n qlo qhi : ℕ} {glo ghi : ℤ} (hn : 2 ≤ n) (hn2 : n + 1 ≤ 10000)
    (hI : InvQ n qlo qhi glo ghi) :
    InvQ (n + 1) (if sqB (n + 1) then qlo + S / (n + 1) else qlo)
      (if sqB (n + 1) then qhi + cdiv S (n + 1) else qhi) (glo + lgLo n) (ghi + lgHi n) := by
  obtain ⟨q1, q2, g1, g2⟩ := hI
  obtain ⟨l1, l2⟩ := log_succ_bounds hn
  have hS := S_pos
  have hsq : sq (n + 1) = if sqB (n + 1) then 1 else 0 := by
    unfold sq
    by_cases h : sqB (n + 1)
    · rw [if_pos h, if_pos ((sqB_iff (by omega) hn2).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((sqB_iff (by omega) hn2).2 h'))]
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_nat_succ, hsq]
    split_ifs
    · push_cast
      have := div_le' S (n + 1)
      have : ((S / (n + 1) : ℕ) : ℝ) / S ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
        rw [div_le_iff₀ hS]; calc ((S / (n + 1) : ℕ) : ℝ) ≤ (S : ℝ) / ((n + 1 : ℕ) : ℝ) := this
          _ = 1 / ((n + 1 : ℕ) : ℝ) * S := by ring
      push_cast at this ⊢
      rw [add_div]; linarith
    · simp; linarith
  · rw [Q1_nat_succ, hsq]
    split_ifs
    · push_cast
      have := cdiv_ge (a := S) (b := n + 1) (by omega)
      have : 1 / ((n + 1 : ℕ) : ℝ) ≤ ((cdiv S (n + 1) : ℕ) : ℝ) / S := by
        rw [le_div_iff₀ hS]; calc 1 / ((n + 1 : ℕ) : ℝ) * S = (S : ℝ) / ((n + 1 : ℕ) : ℝ) := by ring
          _ ≤ _ := this
      push_cast at this ⊢
      rw [add_div]; linarith
    · simp; linarith
  · push_cast; rw [add_div]; push_cast at l1; linarith
  · push_cast; rw [add_div]; push_cast at l2; linarith

/-! ### The walk -/

theorem walkQ_spec : ∀ (f n qlo qhi : ℕ) (glo ghi : ℤ) (n' qlo' qhi' : ℕ) (glo' ghi' : ℤ),
    InvQ n qlo qhi glo ghi → walkQ f n qlo qhi glo ghi = some (n', qlo', qhi', glo', ghi') →
    InvQ n' qlo' qhi' glo' ghi' ∧ n ≤ n' ∧ ∀ k, n ≤ k → k < n' → GoodQ k := by
  intro f
  induction f with
  | zero =>
    intro n qlo qhi glo ghi n' qlo' qhi' glo' ghi' hI h
    simp only [walkQ, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hI, le_rfl, fun k h1 h2 => by omega⟩
  | succ f ih =>
    intro n qlo qhi glo ghi n' qlo' qhi' glo' ghi' hI h
    simp only [walkQ] at h
    by_cases hc : (decide (2 ≤ n) && decide (n + 1 ≤ 10000) && decide (0 ≤ glo) && chkU qhi glo &&
        chkL qlo (ghi + lgHi n)) = true
    swap
    · rw [if_neg hc] at h; simp at h
    rw [if_pos hc] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hn2, hn1⟩, hg0⟩, hU⟩, hL⟩ := hc
    have hI' := invQ_step hn2 hn1 hI
    obtain ⟨r1, r2, r3⟩ := ih _ _ _ _ _ _ _ _ _ _ hI' h
    refine ⟨r1, by omega, fun k hk1 hk2 => ?_⟩
    rcases eq_or_lt_of_le hk1 with rfl | hlt
    · exact goodQ_of (by omega) hI hI'.2.2.2 hg0 hU hL
    · exact r3 k hlt hk2

def resEqQ : Option (ℕ × ℕ × ℕ × ℤ × ℤ) → ℕ → ℕ → ℕ → ℤ → ℤ → Bool
  | some (a, b, c, d, e), a', b', c', d', e' => a == a' && b == b' && c == c' && d == d' && e == e'
  | none, _, _, _, _, _ => false

theorem resEqQ_spec {r : Option (ℕ × ℕ × ℕ × ℤ × ℤ)} {a b c : ℕ} {d e : ℤ}
    (h : resEqQ r a b c d e = true) : r = some (a, b, c, d, e) := by
  match r, h with
  | some (a0, b0, c0, d0, e0), h =>
    simp only [resEqQ, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, h3, h4, h5]

theorem sq_eq {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 10000) : sq n = if sqB n then 1 else 0 := by
  unfold sq
  by_cases h : sqB n
  · rw [if_pos h, if_pos ((sqB_iff h1 h2).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((sqB_iff h1 h2).2 h'))]

/-! ### `n ≤ 10` -/

theorem logc2 : (693147180558 : ℝ) / S ≤ Real.log (2 : ℕ) ∧ Real.log (2 : ℕ) ≤ (693147180574 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 693147180558) (cD := S) (L := 2) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 693147180574) (cD := S) (n := 1) (L := 2) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem logc3 : (1098612288616 : ℝ) / S ≤ Real.log (3 : ℕ) ∧ Real.log (3 : ℕ) ≤ (1098612288727 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 1098612288616) (cD := S) (L := 3) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 1098612288727) (cD := S) (n := 1) (L := 3) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem logc4 : (1386294361068 : ℝ) / S ≤ Real.log (4 : ℕ) ∧ Real.log (4 : ℕ) ≤ (1386294361179 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 1386294361068) (cD := S) (L := 4) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 1386294361179) (cD := S) (n := 1) (L := 4) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem logc5 : (1609437912382 : ℝ) / S ≤ Real.log (5 : ℕ) ∧ Real.log (5 : ℕ) ≤ (1609437912496 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 1609437912382) (cD := S) (L := 5) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 1609437912496) (cD := S) (n := 1) (L := 5) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem logc6 : (1791759469175 : ℝ) / S ≤ Real.log (6 : ℕ) ∧ Real.log (6 : ℕ) ≤ (1791759469348 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 1791759469175) (cD := S) (L := 6) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 1791759469348) (cD := S) (n := 1) (L := 6) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem logc7 : (1945910149001 : ℝ) / S ≤ Real.log (7 : ℕ) ∧ Real.log (7 : ℕ) ≤ (1945910149563 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 1945910149001) (cD := S) (L := 7) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 1945910149563) (cD := S) (n := 1) (L := 7) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem logc8 : (2079441541576 : ℝ) / S ≤ Real.log (8 : ℕ) ∧ Real.log (8 : ℕ) ≤ (2079441541797 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 2079441541576) (cD := S) (L := 8) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 2079441541797) (cD := S) (n := 1) (L := 8) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem logc9 : (2197224577232 : ℝ) / S ≤ Real.log (9 : ℕ) ∧ Real.log (9 : ℕ) ≤ (2197224577454 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 2197224577232) (cD := S) (L := 9) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 2197224577454) (cD := S) (n := 1) (L := 9) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem logc10 : (2302585092890 : ℝ) / S ≤ Real.log (10 : ℕ) ∧ Real.log (10 : ℕ) ≤ (2302585093112 : ℝ) / S := by
  have h1 := Small.le_log_of_chk (cN := 2302585092890) (cD := S) (L := 10) (by norm_num [S]) (by norm_num) (by decide +kernel)
  have h2 := Small.log_lt_of_chk (cN := 2302585093112) (cD := S) (n := 1) (L := 10) (by norm_num [S]) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  exact ⟨h1, by linarith⟩

theorem Q1_one : Q1 ((1 : ℕ) : ℝ) = 1 := by
  unfold Q1; rw [Nat.floor_natCast]; simp [sq, squarefree_one]

theorem Q1_2 : Q1 ((2 : ℕ) : ℝ) = 3 / 2 := by
  have h := Q1_nat_succ 1
  rw [sq_eq (by norm_num) (by norm_num), Q1_one] at h
  rw [h]; simp only [show sqB 2 = true by decide]; norm_num

theorem Q1_3 : Q1 ((3 : ℕ) : ℝ) = 11 / 6 := by
  have h := Q1_nat_succ 2
  rw [sq_eq (by norm_num) (by norm_num), Q1_2] at h
  rw [h]; simp only [show sqB 3 = true by decide]; norm_num

theorem Q1_4 : Q1 ((4 : ℕ) : ℝ) = 11 / 6 := by
  have h := Q1_nat_succ 3
  rw [sq_eq (by norm_num) (by norm_num), Q1_3] at h
  rw [h]; simp only [show sqB 4 = false by decide]; norm_num

theorem Q1_5 : Q1 ((5 : ℕ) : ℝ) = 61 / 30 := by
  have h := Q1_nat_succ 4
  rw [sq_eq (by norm_num) (by norm_num), Q1_4] at h
  rw [h]; simp only [show sqB 5 = true by decide]; norm_num

theorem Q1_6 : Q1 ((6 : ℕ) : ℝ) = 11 / 5 := by
  have h := Q1_nat_succ 5
  rw [sq_eq (by norm_num) (by norm_num), Q1_5] at h
  rw [h]; simp only [show sqB 6 = true by decide]; norm_num

theorem Q1_7 : Q1 ((7 : ℕ) : ℝ) = 82 / 35 := by
  have h := Q1_nat_succ 6
  rw [sq_eq (by norm_num) (by norm_num), Q1_6] at h
  rw [h]; simp only [show sqB 7 = true by decide]; norm_num

theorem Q1_8 : Q1 ((8 : ℕ) : ℝ) = 82 / 35 := by
  have h := Q1_nat_succ 7
  rw [sq_eq (by norm_num) (by norm_num), Q1_7] at h
  rw [h]; simp only [show sqB 8 = false by decide]; norm_num

theorem Q1_9 : Q1 ((9 : ℕ) : ℝ) = 82 / 35 := by
  have h := Q1_nat_succ 8
  rw [sq_eq (by norm_num) (by norm_num), Q1_8] at h
  rw [h]; simp only [show sqB 9 = false by decide]; norm_num

theorem Q1_10 : Q1 ((10 : ℕ) : ℝ) = 171 / 70 := by
  have h := Q1_nat_succ 9
  rw [sq_eq (by norm_num) (by norm_num), Q1_9] at h
  rw [h]; simp only [show sqB 10 = true by decide]; norm_num

theorem invQ_1 : InvQ 1 1000000000000 1000000000000 0 0 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_one, hS]; norm_num
  · rw [Q1_one, hS]; norm_num
  · simp
  · simp

theorem invQ_2 : InvQ 2 1500000000000 1500000000000 693147180558 693147180574 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_2, hS]; norm_num
  · rw [Q1_2, hS]; norm_num
  · have := logc2.1; push_cast at this ⊢; exact this
  · have := logc2.2; push_cast at this ⊢; exact this

theorem invQ_3 : InvQ 3 1833333333333 1833333333334 1098612288616 1098612288727 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_3, hS]; norm_num
  · rw [Q1_3, hS]; norm_num
  · have := logc3.1; push_cast at this ⊢; exact this
  · have := logc3.2; push_cast at this ⊢; exact this

theorem invQ_4 : InvQ 4 1833333333333 1833333333334 1386294361068 1386294361179 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_4, hS]; norm_num
  · rw [Q1_4, hS]; norm_num
  · have := logc4.1; push_cast at this ⊢; exact this
  · have := logc4.2; push_cast at this ⊢; exact this

theorem invQ_5 : InvQ 5 2033333333333 2033333333334 1609437912382 1609437912496 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_5, hS]; norm_num
  · rw [Q1_5, hS]; norm_num
  · have := logc5.1; push_cast at this ⊢; exact this
  · have := logc5.2; push_cast at this ⊢; exact this

theorem invQ_6 : InvQ 6 2200000000000 2200000000000 1791759469175 1791759469348 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_6, hS]; norm_num
  · rw [Q1_6, hS]; norm_num
  · have := logc6.1; push_cast at this ⊢; exact this
  · have := logc6.2; push_cast at this ⊢; exact this

theorem invQ_7 : InvQ 7 2342857142857 2342857142858 1945910149001 1945910149563 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_7, hS]; norm_num
  · rw [Q1_7, hS]; norm_num
  · have := logc7.1; push_cast at this ⊢; exact this
  · have := logc7.2; push_cast at this ⊢; exact this

theorem invQ_8 : InvQ 8 2342857142857 2342857142858 2079441541576 2079441541797 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_8, hS]; norm_num
  · rw [Q1_8, hS]; norm_num
  · have := logc8.1; push_cast at this ⊢; exact this
  · have := logc8.2; push_cast at this ⊢; exact this

theorem invQ_9 : InvQ 9 2342857142857 2342857142858 2197224577232 2197224577454 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_9, hS]; norm_num
  · rw [Q1_9, hS]; norm_num
  · have := logc9.1; push_cast at this ⊢; exact this
  · have := logc9.2; push_cast at this ⊢; exact this

theorem invQ_10 : InvQ 10 2442857142857 2442857142858 2302585092890 2302585093112 := by
  have hS : (S : ℝ) = 1000000000000 := by norm_num [S]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Q1_10, hS]; norm_num
  · rw [Q1_10, hS]; norm_num
  · have := logc10.1; push_cast at this ⊢; exact this
  · have := logc10.2; push_cast at this ⊢; exact this

theorem goodQ_1 : GoodQ 1 :=
  goodQ_of (ghi' := 693147180574) (by norm_num) invQ_1 (by have := logc2.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem goodQ_2 : GoodQ 2 :=
  goodQ_of (ghi' := 1098612288727) (by norm_num) invQ_2 (by have := logc3.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem goodQ_3 : GoodQ 3 :=
  goodQ_of (ghi' := 1386294361179) (by norm_num) invQ_3 (by have := logc4.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem goodQ_4 : GoodQ 4 :=
  goodQ_of (ghi' := 1609437912496) (by norm_num) invQ_4 (by have := logc5.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem goodQ_5 : GoodQ 5 :=
  goodQ_of (ghi' := 1791759469348) (by norm_num) invQ_5 (by have := logc6.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem goodQ_6 : GoodQ 6 :=
  goodQ_of (ghi' := 1945910149563) (by norm_num) invQ_6 (by have := logc7.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem goodQ_7 : GoodQ 7 :=
  goodQ_of (ghi' := 2079441541797) (by norm_num) invQ_7 (by have := logc8.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem goodQ_8 : GoodQ 8 :=
  goodQ_of (ghi' := 2197224577454) (by norm_num) invQ_8 (by have := logc9.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem goodQ_9 : GoodQ 9 :=
  goodQ_of (ghi' := 2302585093112) (by norm_num) invQ_9 (by have := logc10.2; push_cast at this ⊢; exact this)
    (by norm_num) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem chunkQ0 : resEqQ (walkQ 1000 10 2442857142857 2442857142858 (2302585092890) (2302585093112)) 1010 5250350431224 5250350431834 (6917639092100) (6918569886942) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ1 : resEqQ (walkQ 1000 1010 5250350431224 5250350431834 (6917639092100) (6918569886942)) 2010 5666813026000 5666813027215 (7605823479907) (7606754280922) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ2 : resEqQ (walkQ 1000 2010 5666813026000 5666813027215 (7605823479907) (7606754280922)) 3010 5913184279514 5913184281339 (8009628833120) (8010559640131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ3 : resEqQ (walkQ 1000 3010 5913184279514 5913184281339 (8009628833120) (8010559640131)) 4010 6087913483956 6087913486390 (8296479992162) (8297410805168) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ4 : resEqQ (walkQ 1000 4010 6087913483956 6087913486390 (8296479992162) (8297410805168)) 5010 6223646250814 6223646253858 (8519124662432) (8520055481435) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ5 : resEqQ (walkQ 1000 5010 6223646250814 6223646253858 (8519124662432) (8520055481435)) 6010 6333285909903 6333285913550 (8701113492363) (8702044317365) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ6 : resEqQ (walkQ 1000 6010 6333285909903 6333285913550 (8701113492363) (8702044317365)) 7010 6426894754660 6426894758915 (8855026441566) (8855957272565) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ7 : resEqQ (walkQ 1000 7010 6426894754660 6426894758915 (8855026441566) (8855957272565)) 8010 6508243734503 6508243739368 (8988379497800) (8989310334798) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ8 : resEqQ (walkQ 1000 8010 6508243734503 6508243739368 (8988379497800) (8989310334798)) 9010 6579904814224 6579904819698 (9106023804821) (9106954647819) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chunkQ9 : resEqQ (walkQ 990 9010 6579904814224 6579904819698 (9106023804821) (9106954647819)) 10000 6643413160908 6643413166985 (9210273822826) (9211204671764) = true := by
  decide +kernel

/-- **`0.578 ≤ Q₁(t) − κ log t ≤ 1.166` on `[n, n+1)` for `1 ≤ n < 10⁴`**, and the state at `10⁴`. -/
theorem goodQ_small : (∀ n, 1 ≤ n → n < 10000 → GoodQ n) ∧ InvQ 10000 6643413160908 6643413166985 (9210273822826) (9211204671764) := by
  have h0 := invQ_10
  obtain ⟨h1, -, g0⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h0 (resEqQ_spec chunkQ0)
  obtain ⟨h2, -, g1⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h1 (resEqQ_spec chunkQ1)
  obtain ⟨h3, -, g2⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h2 (resEqQ_spec chunkQ2)
  obtain ⟨h4, -, g3⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h3 (resEqQ_spec chunkQ3)
  obtain ⟨h5, -, g4⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h4 (resEqQ_spec chunkQ4)
  obtain ⟨h6, -, g5⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h5 (resEqQ_spec chunkQ5)
  obtain ⟨h7, -, g6⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h6 (resEqQ_spec chunkQ6)
  obtain ⟨h8, -, g7⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h7 (resEqQ_spec chunkQ7)
  obtain ⟨h9, -, g8⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h8 (resEqQ_spec chunkQ8)
  obtain ⟨h10, -, g9⟩ := walkQ_spec _ _ _ _ _ _ _ _ _ _ _ h9 (resEqQ_spec chunkQ9)
  refine ⟨fun n hn1 hn2 => ?_, h10⟩
  rcases lt_or_ge n 10 with hlt | hge
  · interval_cases n
    · exact goodQ_1
    · exact goodQ_2
    · exact goodQ_3
    · exact goodQ_4
    · exact goodQ_5
    · exact goodQ_6
    · exact goodQ_7
    · exact goodQ_8
    · exact goodQ_9
  rcases lt_or_ge n 1010 with c0 | c0
  · exact g0 n (by omega) c0
  rcases lt_or_ge n 2010 with c1 | c1
  · exact g1 n (by omega) c1
  rcases lt_or_ge n 3010 with c2 | c2
  · exact g2 n (by omega) c2
  rcases lt_or_ge n 4010 with c3 | c3
  · exact g3 n (by omega) c3
  rcases lt_or_ge n 5010 with c4 | c4
  · exact g4 n (by omega) c4
  rcases lt_or_ge n 6010 with c5 | c5
  · exact g5 n (by omega) c5
  rcases lt_or_ge n 7010 with c6 | c6
  · exact g6 n (by omega) c6
  rcases lt_or_ge n 8010 with c7 | c7
  · exact g7 n (by omega) c7
  rcases lt_or_ge n 9010 with c8 | c8
  · exact g8 n (by omega) c8
  rcases lt_or_ge n 10000 with c9 | c9
  · exact g9 n (by omega) c9
  omega

end TernaryGoldbach.Prelim.Sqf
