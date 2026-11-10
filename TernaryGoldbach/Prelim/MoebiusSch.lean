import TernaryGoldbach.Prelim.SchoenfeldTail

/-!
# `|m(x)| log x` from the bounds for `M`

El Marraki's inequality (`el_marraki`) with `∫₁^x |M(t)|/t² dt ≤ ∑_{n ≤ x} |M(n)|/n`, and the bounds
for `M`: `0.571 √u` below `X₀ = 10⁸` (`M_low`), `η u` on the cells (`st213`), and `M_tail` beyond.
-/

open Finset MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sch

/-- `S(N) = ∑_{n ≤ N} |M(n)|/n`. -/
noncomputable def Ssum (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, |Mn n| / n

noncomputable def phiM (n : ℕ) : ℝ := |Mn n| / n

theorem phiM_nonneg (n : ℕ) : 0 ≤ phiM n := by unfold phiM; positivity

theorem intervalIntegrable_phiM (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => phiM ⌊t⌋₊) volume a b := by
  have := intervalIntegrable_step phiM ha hab one_pos
  simp only [div_one] at this; exact this

theorem integral_phiM_unit (n : ℕ) : ∫ t in (n : ℝ)..((n : ℝ) + 1), phiM ⌊t⌋₊ = phiM n := by
  have : ∫ t in (n : ℝ)..((n : ℝ) + 1), phiM ⌊t⌋₊ = ∫ t in (n : ℝ)..((n : ℝ) + 1), phiM n := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_pt ((n : ℝ) + 1)] with t ht hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have h1 : (n : ℝ) ≤ t := hmem.1.le
    have h2 : t < (n : ℝ) + 1 := lt_of_le_of_ne hmem.2 ht
    have h0 : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg n) h1
    rw [show ⌊t⌋₊ = n from (Nat.floor_eq_iff h0).2 ⟨h1, h2⟩]
  rw [this]; simp

theorem integral_phiM_sum (N : ℕ) : ∫ t in (1 : ℝ)..((N : ℝ) + 1), phiM ⌊t⌋₊ = ∑ n ∈ Icc 1 N, phiM n := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hI1 := intervalIntegrable_phiM 1 ((N : ℝ) + 1) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
    have hI2 := intervalIntegrable_phiM ((N : ℝ) + 1) ((N : ℝ) + 1 + 1) (by positivity) (by linarith)
    rw [show (((N + 1 : ℕ) : ℝ) + 1) = (N : ℝ) + 1 + 1 by push_cast; ring,
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, ih,
      show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring, integral_phiM_unit,
      Finset.sum_Icc_succ_top (by omega)]

/-- `∫₁^x |M(t)|/t² dt ≤ ∑_{n ≤ x} |M(n)|/n`. -/
theorem integral_gM_le {x : ℝ} (hx : 1 ≤ x) : ∫ t in (1 : ℝ)..x, |gM t| ≤ Ssum ⌊x⌋₊ := by
  have hx0 : 0 ≤ x := by linarith
  have hfx : x ≤ (⌊x⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have h1 : ∫ t in (1 : ℝ)..x, |gM t| ≤ ∫ t in (1 : ℝ)..x, phiM ⌊t⌋₊ := by
    refine intervalIntegral.integral_mono_on hx ((intervalIntegrable_gM one_pos hx).abs)
      (intervalIntegrable_phiM 1 x (by norm_num) hx) fun t ht => ?_
    have ht1 : 1 ≤ t := ht.1
    have hf1 : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast ht1)
    have hft : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
    unfold gM Mr phiM
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < t)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hft
  have h2 : ∫ t in (1 : ℝ)..x, phiM ⌊t⌋₊ ≤ ∫ t in (1 : ℝ)..((⌊x⌋₊ : ℝ) + 1), phiM ⌊t⌋₊ := by
    refine intervalIntegral.integral_mono_interval le_rfl hx hfx ?_
      (intervalIntegrable_phiM 1 _ (by norm_num) (by linarith))
    exact Filter.Eventually.of_forall fun t => phiM_nonneg _
  rw [integral_phiM_sum] at h2
  exact le_trans h1 (le_of_le_of_eq h2 rfl)

/-- **El Marraki with sums**: `|m(x)| ≤ |M(x)|/x + (log x + S(⌊x⌋))/x`. -/
theorem m_le_S {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ |Mn ⌊x⌋₊| / x + (Real.log x + Ssum ⌊x⌋₊) / x := by
  have h := el_marraki hx
  have h2 := integral_gM_le hx
  have hx0 : 0 < x := by linarith
  refine le_trans h ?_
  unfold Mr
  gcongr

/-! ### Below `X₀ + 1` -/

theorem Ssum_low {N : ℕ} (hN : N ≤ 100001092) : Ssum N ≤ 99 + 1.142 * √(N : ℝ) := by
  have hsN := Real.sqrt_nonneg (N : ℝ)
  rcases le_or_gt N 99 with h | h
  · have : Ssum N ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) := by
      refine sum_le_sum fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Icc.1 hn).1; omega)
      rw [div_le_one hn0]; exact abs_Mn_le n
    have h2 : ∑ n ∈ Icc 1 N, (1 : ℝ) ≤ 99 := by
      rw [sum_const, Nat.card_Icc]; simp; exact_mod_cast (by omega : N + 1 - 1 ≤ 99)
    linarith
  · have e : Ssum N = ∑ n ∈ Icc 1 99, |Mn n| / n + ∑ n ∈ Ioc 99 N, |Mn n| / n := by
      unfold Ssum
      rw [show Icc 1 N = Ioc 0 N by ext; simp; omega, show Icc 1 99 = Ioc 0 99 by ext; simp; omega,
        Finset.sum_Ioc_consecutive _ (by norm_num) h.le]
    have h1 : ∑ n ∈ Icc 1 99, |Mn n| / (n : ℝ) ≤ 99 := by
      have : ∑ n ∈ Icc 1 99, |Mn n| / (n : ℝ) ≤ ∑ n ∈ Icc 1 99, (1 : ℝ) := by
        refine sum_le_sum fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Icc.1 hn).1; omega)
        rw [div_le_one hn0]; exact abs_Mn_le n
      have h2 : ∑ n ∈ Icc 1 99, (1 : ℝ) = 99 := by rw [sum_const, Nat.card_Icc]; norm_num
      linarith
    have h2 : ∑ n ∈ Ioc 99 N, |Mn n| / (n : ℝ) ≤ ∑ n ∈ Ioc 99 N, 0.571 * (1 / √(n : ℝ)) := by
      refine sum_le_sum fun n hn => ?_
      obtain ⟨n1, n2⟩ := mem_Ioc.1 hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hM := M_low (u := n) (by omega) (by omega)
      calc |Mn n| / (n : ℝ) ≤ 0.571 * √(n : ℝ) / n := div_le_div_of_nonneg_right hM hn0.le
        _ = 0.571 * (√(n : ℝ) / n) := by ring
        _ = 0.571 * (1 / √(n : ℝ)) := by rw [Real.sqrt_div_self']
    have h3 := sum_inv_sqrt_Ioc' (a := 99) (b := N) h.le
    rw [← mul_sum] at h2
    have h99 := Real.sqrt_nonneg ((99 : ℕ) : ℝ)
    set Q := ∑ n ∈ Ioc 99 N, (1 / √(n : ℝ))
    set r := √((99 : ℕ) : ℝ)
    set q := √(N : ℝ)
    rw [e]; nlinarith

theorem log_X01_le : Real.log ((100000001 : ℕ) : ℝ) ≤ 18.43 := by
  have := logUp_spec (q := 1843 / 100) (L := 100000001) (by decide +kernel)
  norm_num at this ⊢; exact this

/-- `|m(x)| log x ≤ 0.03` for `2 160 535 ≤ x < X₀ + 1`. -/
theorem m_mid {x : ℝ} (h1 : 2160535 ≤ x) (h2 : x < 100000001) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| * Real.log x ≤ 0.03 := by
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 2160535 ≤ N := Nat.le_floor (by exact_mod_cast h1)
  have hN2 : N ≤ 100000000 := by
    have : N < 100000001 := (Nat.floor_lt hx0.le).2 (by exact_mod_cast h2)
    omega
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hm := m_le_S (x := x) (by linarith)
  rw [← hNdef] at hm
  have hM := M_low (u := N) (by omega) (by omega)
  have hS := Ssum_low (N := N) (by omega)
  have hsN : √(N : ℝ) ≤ √x := Real.sqrt_le_sqrt hNx
  have hsx : 1469.8 ≤ √x := by
    rw [show (1469.8 : ℝ) = √(1469.8 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hlx : Real.log x ≤ 18.43 :=
    le_trans (Real.log_le_log hx0 (by push_cast; linarith)) log_X01_le
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsx0 : 0 < √x := by linarith
  have hxx : √x * √x = x := Real.mul_self_sqrt hx0.le
  -- `|m(x)| ≤ 1.713/√x + (log x + 99)/x`
  have hb : |∑ n ∈ Icc 1 N, (μ n : ℝ) / n| ≤ 1.713 / √x + (18.43 + 99) / 2160535 := by
    refine le_trans hm ?_
    have t1 : |Mn N| / x ≤ 0.571 / √x := by
      rw [div_le_div_iff₀ hx0 hsx0]
      calc |Mn N| * √x ≤ 0.571 * √(N : ℝ) * √x := mul_le_mul_of_nonneg_right hM hsx0.le
        _ ≤ 0.571 * √x * √x := by gcongr
        _ = 0.571 * x := by rw [mul_assoc, hxx]
    have t2 : (Real.log x + Ssum N) / x ≤ 1.142 / √x + (18.43 + 99) / 2160535 := by
      have : (Real.log x + Ssum N) / x ≤ (18.43 + 99) / x + 1.142 * √x / x := by
        rw [← add_div]; exact div_le_div_of_nonneg_right (by nlinarith) hx0.le
      have e : 1.142 * √x / x = 1.142 / √x := by
        rw [mul_div_assoc, Real.sqrt_div_self']; ring
      have h3 : (18.43 + 99) / x ≤ (18.43 + 99) / 2160535 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
      linarith
    have : 0.571 / √x + 1.142 / √x = 1.713 / √x := by ring
    linarith
  have h4 : 1.713 / √x ≤ 1.713 / 1469.8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsx
  calc |∑ n ∈ Icc 1 N, (μ n : ℝ) / n| * Real.log x ≤ (1.713 / 1469.8 + (18.43 + 99) / 2160535) * 18.43 :=
        mul_le_mul (by linarith) hlx hlx0 (by positivity)
    _ ≤ 0.03 := by norm_num

/-! ### On the cells -/

/-- The points where the step bound for `|m(x)| log x` changes. -/
def bndsM : List ℕ := [100000001, 9001713129, 1525381771989686, 747499893696668303884288,
  5273264915796702340408371151172679619749656857014800716447501879607296]

/-- The step bound, at `n = ⌊x⌋`. -/
def profq (n : ℕ) : ℚ :=
  if n < 100000001 then 3 / 100 else if n < 9001713129 then 92 / 1000
  else if n < 1525381771989686 then 9 / 100 else if n < 747499893696668303884288 then 8 / 100
  else if n < 5273264915796702340408371151172679619749656857014800716447501879607296 then 35 / 1000
  else 75 / 1000

theorem profq_const {a n : ℕ} (h1 : a ≤ n) (h : bndsM.all (fun B => !(decide (a < B) && decide (B ≤ n))) = true) :
    profq n = profq a := by
  simp only [bndsM, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, not_le] at h
  obtain ⟨b1, b2, b3, b4, b5⟩ := h
  unfold profq
  have e1 : n < 100000001 ↔ a < 100000001 := by omega
  have e2 : n < 9001713129 ↔ a < 9001713129 := by omega
  have e3 : n < 1525381771989686 ↔ a < 1525381771989686 := by omega
  have e4 : n < 747499893696668303884288 ↔ a < 747499893696668303884288 := by omega
  have e5 : n < 5273264915796702340408371151172679619749656857014800716447501879607296 ↔
      a < 5273264915796702340408371151172679619749656857014800716447501879607296 := by omega
  simp only [e1, e2, e3, e4, e5]

/-- The bound for `|m(x)|` on the cell `[s, b)`, `η`, `S ≥ S(s − 1)`, `log b ≤ ub`. -/
def mqv (s b : ℕ) (η S ub : ℚ) : ℚ := 2 * η + max ((ub + S - η * (s - 1)) / s) ((ub + S - η * (s - 1)) / b)

def mChk : ℕ → ℚ → List (ℕ × ℚ) → List ℚ → Bool
  | _, _, [], _ => true
  | s, S, (b, η) :: cs, ub :: ubs =>
    decide (2 ≤ s) && decide (s < b) && decide (0 ≤ η) && logUp ub b &&
      bndsM.all (fun B => !(decide (s < B) && decide (B ≤ b - 1))) &&
      decide (mqv s b η S ub * ub ≤ profq s) && mChk b (S + η * (b - s)) cs ubs
  | _, _, _ :: _, [] => false

/-- The bound for `S` at the end of the cells. -/
def mFin : ℕ → ℚ → List (ℕ × ℚ) → ℚ
  | _, S, [] => S
  | s, S, (b, η) :: cs => mFin b (S + η * (b - s)) cs

theorem Ssum_split {a N : ℕ} (h : a ≤ N) : Ssum N = Ssum a + ∑ n ∈ Ioc a N, |Mn n| / n := by
  unfold Ssum
  rw [show Icc 1 N = Ioc 0 N by ext; simp; omega, show Icc 1 a = Ioc 0 a by ext; simp; omega,
    Finset.sum_Ioc_consecutive _ (Nat.zero_le a) h]

theorem Ssum_cell {s N : ℕ} (hs : 1 ≤ s) (hsN : s ≤ N + 1) {η : ℚ} (hη : 0 ≤ η)
    (hM : ∀ u, s ≤ u → u ≤ N → |Mn u| ≤ (η : ℝ) * u) :
    Ssum N ≤ Ssum (s - 1) + η * ((N : ℝ) + 1 - s) := by
  rw [Ssum_split (show s - 1 ≤ N by omega)]
  have h : ∑ n ∈ Ioc (s - 1) N, |Mn n| / (n : ℝ) ≤ ∑ n ∈ Ioc (s - 1) N, (η : ℝ) := by
    refine sum_le_sum fun n hn => ?_
    obtain ⟨n1, n2⟩ := mem_Ioc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_le_iff₀ hn0]; exact hM n (by omega) n2
  rw [sum_const, Nat.card_Ioc, nsmul_eq_mul] at h
  have e : ((N - (s - 1) : ℕ) : ℝ) = (N : ℝ) + 1 - s := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hs]; push_cast; ring
  rw [e] at h; linarith

theorem mChk_spec : ∀ (cs : List (ℕ × ℚ)) (ubs : List ℚ) (s : ℕ) (S : ℚ), McovR s cs → Ssum (s - 1) ≤ S →
    mChk s S cs ubs = true →
    (∀ x : ℝ, (s : ℝ) ≤ x → x < endC s cs →
      |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| * Real.log x ≤ profq ⌊x⌋₊) ∧
    Ssum (endC s cs - 1) ≤ mFin s S cs
  | [], _, s, S, _, hS, _ => ⟨fun x h1 h2 => by simp [endC] at h2; linarith, by simpa [endC, mFin] using hS⟩
  | (b, η) :: cs, [], s, S, _, _, h => by simp [mChk] at h
  | (b, η) :: cs, ub :: ubs, s, S, ⟨hc, hr⟩, hS, h => by
    simp only [mChk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h2s, hsb⟩, hη⟩, hub⟩, hbd⟩, hv⟩, hrest⟩ := h
    have hη' : (0 : ℝ) ≤ η := by exact_mod_cast hη
    have hS' : Ssum (b - 1) ≤ ((S + η * (b - s) : ℚ) : ℝ) := by
      have := Ssum_cell (s := s) (N := b - 1) (by omega) (by omega) hη (fun u h1 h2 => hc u h1 (by omega))
      push_cast
      have e : (((b - 1 : ℕ) : ℝ) + 1 - s) = (b : ℝ) - s := by rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [e] at this; linarith
    obtain ⟨ih1, ih2⟩ := mChk_spec cs ubs b (S + η * (b - s)) hr hS' hrest
    refine ⟨fun x h1 h2 => ?_, by simpa [endC, mFin] using ih2⟩
    have h2s' : (2 : ℝ) ≤ s := by exact_mod_cast h2s
    rcases lt_or_ge x b with hxb | hxb
    · -- `x` in this cell
      have hx0 : 0 < x := by linarith
      set N := ⌊x⌋₊ with hNdef
      have hN1 : s ≤ N := Nat.le_floor h1
      have hN2 : N < b := (Nat.floor_lt hx0.le).2 hxb
      have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
      have hm := m_le_S (x := x) (by linarith)
      rw [← hNdef] at hm
      have hMN := hc N hN1 hN2
      have hSN := Ssum_cell (s := s) (N := N) (by omega) (by omega) hη (fun u h1 h2 => hc u h1 (by omega))
      have hlx : Real.log x ≤ ub := le_trans (Real.log_le_log hx0 hxb.le) (logUp_spec hub)
      have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
      -- `|m(x)| ≤ 2η + (ub + W)/x`
      set W : ℝ := (S : ℝ) - η * ((s : ℝ) - 1) with hW
      have hm2 : |∑ n ∈ Icc 1 N, (μ n : ℝ) / n| ≤ 2 * η + (ub + W) / x := by
        refine le_trans hm ?_
        have t1 : |Mn N| / x ≤ η := by
          rw [div_le_iff₀ hx0]; exact le_trans hMN (mul_le_mul_of_nonneg_left hNx hη')
        have t2 : (Real.log x + Ssum N) / x ≤ η + (ub + W) / x := by
          rw [div_le_iff₀ hx0, add_mul, div_mul_cancel₀ _ hx0.ne']
          have : Ssum N ≤ S + η * (x + 1 - s) := by
            have := mul_le_mul_of_nonneg_left (show (N : ℝ) + 1 - s ≤ x + 1 - s by linarith) hη'
            linarith
          rw [hW]; nlinarith
        linarith
      have hmax : (ub + W) / x ≤ max (((ub : ℝ) + W) / s) ((ub + W) / b) := by
        rcases le_or_gt 0 ((ub : ℝ) + W) with hp | hp
        · exact le_trans (div_le_div_of_nonneg_left hp hs0 h1) (le_max_left _ _)
        · refine le_trans ?_ (le_max_right _ _)
          have hb0 : (0 : ℝ) < b := by linarith
          rw [div_le_div_iff₀ hx0 hb0]; nlinarith
      have hmq : |∑ n ∈ Icc 1 N, (μ n : ℝ) / n| ≤ ((mqv s b η S ub : ℚ) : ℝ) := by
        have e : ((mqv s b η S ub : ℚ) : ℝ) = 2 * η + max (((ub : ℝ) + W) / s) ((ub + W) / b) := by
          unfold mqv; push_cast
          rw [show ((ub : ℝ) + S - η * ((s : ℝ) - 1)) = ub + W by rw [hW]; ring]
        rw [e]; linarith
      have hv' : ((mqv s b η S ub : ℚ) : ℝ) * ub ≤ profq s := by exact_mod_cast hv
      rw [profq_const hN1 (by
        refine List.all_eq_true.2 fun B hB => ?_
        have := List.all_eq_true.1 hbd B hB
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, not_le] at this ⊢
        omega)]
      calc |∑ n ∈ Icc 1 N, (μ n : ℝ) / n| * Real.log x ≤ ((mqv s b η S ub : ℚ) : ℝ) * ub :=
            mul_le_mul hmq hlx hlx0 (le_trans (abs_nonneg _) hmq)
        _ ≤ profq s := hv'
    · exact ih1 x (by exact_mod_cast hxb) (by simpa [endC] using h2)

/-! ### Beyond the cells -/

variable [Fact TernaryGoldbach.PlattGRH]

set_option maxHeartbeats 1000000 in
/-- `|m(x)| log x ≤ 0.075` for `x ≥ T`, given `S(T − 1) ≤ S_f ≤ 3.62·10⁻⁵ T`. -/
theorem m_tail {x : ℝ} (hx : (TT : ℝ) ≤ x) {Sf : ℝ} (hS : Ssum (TT - 1) ≤ Sf) (hSf : Sf ≤ 0.0000362 * TT) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| * Real.log x ≤ 0.075 := by
  have hT := logT_ge
  have hT' := logT_le
  have hT0 : 0 < TT := lt_of_lt_of_le (by norm_num [X0]) X0_lt_T
  have hTr : (0 : ℝ) < TT := by exact_mod_cast hT0
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  have hL : 160.54 ≤ L := le_trans hT (Real.log_le_log hTr hx)
  set N := ⌊x⌋₊ with hNdef
  have hN1 : TT ≤ N := Nat.le_floor hx
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  set l := Real.log N with hldef
  have hl : 160.54 ≤ l := le_trans hT (Real.log_le_log hTr (by exact_mod_cast hN1))
  have hlL : l ≤ L := Real.log_le_log hN0 hNx
  -- `x ≥ 10⁶⁹`
  have hxbig : (1e69 : ℝ) ≤ x := by
    have : (1e69 : ℝ) ≤ TT := by
      have h' : ((10 ^ 69 : ℕ) : ℝ) ≤ TT := by exact_mod_cast (show 10 ^ 69 ≤ TT by decide +kernel)
      norm_num at h' ⊢; linarith
    linarith
  -- `L ≤ l + 2/x`
  have hLl : L ≤ l + 1e-60 := by
    have h := log_floor_ge (x := x) (by linarith)
    rw [← hNdef] at h
    have : 2 / x ≤ 1e-60 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  have hm := m_le_S (x := x) (by linarith)
  rw [← hNdef] at hm
  have hMN := M_tail hN1
  rw [← hldef] at hMN
  -- `S(N) ≤ S_f + 0.033 (x+1)/(L−2) + 0.04 (x+1)/L²`
  have hSN : Ssum N ≤ Sf + 0.033 * ((x + 1) / (L - 2)) + 0.033 * 1.013 * ((x + 1) / L ^ 2) +
      0.0395 * 1.013 * ((x + 1) / L ^ 2) := by
    rw [Ssum_split (show TT - 1 ≤ N by omega)]
    have e : Ioc (TT - 1) N = Ico TT (N + 1) := by ext; simp; omega
    rw [e]
    have hlog1 : L ≤ Real.log ((N + 1 : ℕ) : ℝ) := Real.log_le_log hx0 (by push_cast; linarith)
    have hNp : ((N + 1 : ℕ) : ℝ) ≤ x + 1 := by push_cast; linarith
    have h1 : ∑ n ∈ Ico TT (N + 1), |Mn n| / (n : ℝ) ≤
        ∑ n ∈ Ico TT (N + 1), (0.033 * (1 / Real.log n) + 0.0395 * (1 / Real.log n ^ 2)) := by
      refine sum_le_sum fun n hn => ?_
      obtain ⟨n1, n2⟩ := mem_Ico.1 hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have := M_tail n1
      rw [div_le_iff₀ hn0]
      calc |Mn n| ≤ (0.033 / Real.log n + 0.0395 / Real.log n ^ 2) * n := this
        _ = (0.033 * (1 / Real.log n) + 0.0395 * (1 / Real.log n ^ 2)) * n := by ring
    rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h1
    have hs1 := sum_inv_log_le (a := TT) (by linarith) (N + 1) (by omega)
    have hs2 := sum_inv_log_sq_le (a := TT) (by linarith) (N + 1) (by omega)
    have hT2 : 0 ≤ (TT : ℝ) / (Real.log TT - 2) := div_nonneg hTr.le (by linarith)
    have hT3 : 0 ≤ (TT : ℝ) / Real.log TT ^ 2 := by positivity
    have q1 : ((N + 1 : ℕ) : ℝ) / (Real.log ((N + 1 : ℕ) : ℝ) - 2) ≤ (x + 1) / (L - 2) :=
      div_le_div₀ (by linarith) hNp (by linarith) (by linarith)
    have q2 : ((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ) ^ 2 ≤ (x + 1) / L ^ 2 :=
      div_le_div₀ (by linarith) hNp (by positivity) (pow_le_pow_left₀ (by linarith) hlog1 2)
    set A1 := ∑ n ∈ Ico TT (N + 1), 1 / Real.log n
    set A2 := ∑ n ∈ Ico TT (N + 1), 1 / Real.log n ^ 2
    set A0 := ∑ n ∈ Ico TT (N + 1), |Mn n| / (n : ℝ)
    have k1 : 0.033 * A1 ≤ 0.033 * ((x + 1) / (L - 2)) := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have k2 : 0.0395 * A2 ≤ 0.0395 * 1.013 * ((x + 1) / L ^ 2) := by
      have := mul_le_mul_of_nonneg_left (show A2 ≤ 1.013 * ((x + 1) / L ^ 2) by nlinarith) (by norm_num : (0 : ℝ) ≤ 0.0395)
      linarith
    have k3 : 0 ≤ 0.033 * 1.013 * ((x + 1) / L ^ 2) := by positivity
    linarith
  -- the pieces of `|m(x)| L`
  have hlogx : Real.log x / x ≤ Real.log TT / TT := by
    have he : Real.exp 1 ≤ (TT : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (1e69 : ℝ) ≤ TT := by
        have h' : ((10 ^ 69 : ℕ) : ℝ) ≤ TT := by exact_mod_cast (show 10 ^ 69 ≤ TT by decide +kernel)
        norm_num at h' ⊢; linarith
      linarith
    exact Real.log_div_self_antitoneOn he (le_trans he hx) hx
  have hSL : Sf * L / x ≤ 0.0000362 * 160.55 := by
    have hSf0 : 0 ≤ Sf := le_trans (by unfold Ssum; positivity) hS
    calc Sf * L / x = Sf * (L / x) := by ring
      _ ≤ (0.0000362 * TT) * (Real.log TT / TT) := mul_le_mul hSf hlogx (by positivity) (by positivity)
      _ = 0.0000362 * Real.log TT := by field_simp
      _ ≤ 0.0000362 * 160.55 := by linarith
  have hL2 : L ^ 2 / x ≤ 1e-30 := by
    set s4 := √(√x)
    have hs0 : 0 < s4 := Real.sqrt_pos.2 (Real.sqrt_pos.2 hx0)
    have hss : s4 ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hsv : s4 ^ 4 = x := by rw [show s4 ^ 4 = (s4 ^ 2) ^ 2 by ring, hss, Real.sq_sqrt hx0.le]
    have hLs : L ≤ 4 * s4 := by
      have : Real.log x = 4 * Real.log s4 := by rw [← hsv, Real.log_pow]; push_cast; ring
      rw [hLdef, this]; have := Real.log_le_sub_one_of_pos hs0; linarith
    have hsbig : 1e17 ≤ s4 := by
      have h4 : (1e17 : ℝ) ^ 4 ≤ s4 ^ 4 := by rw [hsv]; norm_num; linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) hs0.le h4
    rw [div_le_iff₀ hx0, ← hsv]
    nlinarith [pow_le_pow_left₀ (by linarith) hLs 2]
  have hb1 : |Mn N| / x * L ≤ 0.033 * (1 + 1e-60 / 160.54) + 0.0395 / 160.54 * (1 + 1e-60 / 160.54) := by
    have hNx' : (N : ℝ) / x ≤ 1 := by rw [div_le_one hx0]; exact hNx
    have hl0 : 0 < l := by linarith
    have hLl' : L / l ≤ 1 + 1e-60 / 160.54 := by
      rw [div_le_iff₀ hl0]
      have : 1e-60 ≤ 1e-60 / 160.54 * l := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; nlinarith
      linarith
    have hLl0 : 0 ≤ L / l := by positivity
    calc |Mn N| / x * L ≤ (0.033 / l + 0.0395 / l ^ 2) * N / x * L := by
          gcongr
      _ = (0.033 + 0.0395 / l) * (L / l) * (N / x) := by field_simp
      _ ≤ (0.033 + 0.0395 / 160.54) * (1 + 1e-60 / 160.54) * 1 := by
          apply mul_le_mul (mul_le_mul (by gcongr) hLl' hLl0 (by positivity)) hNx' (by positivity) (by positivity)
      _ = _ := by ring
  have hb2 : (0.033 * ((x + 1) / (L - 2))) / x * L ≤ 0.033 * (1 + 1e-60) * (160.54 / 158.54) := by
    have h1 : (x + 1) / x ≤ 1 + 1e-60 := by
      rw [div_le_iff₀ hx0]; nlinarith
    have h2 : L / (L - 2) ≤ 160.54 / 158.54 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    calc (0.033 * ((x + 1) / (L - 2))) / x * L = 0.033 * ((x + 1) / x) * (L / (L - 2)) := by
          field_simp
      _ ≤ 0.033 * (1 + 1e-60) * (160.54 / 158.54) := by
          have : 0 ≤ L / (L - 2) := div_nonneg (by linarith) (by linarith)
          gcongr
  have hb3 : ((0.033 * 1.013 + 0.0395 * 1.013) * ((x + 1) / L ^ 2)) / x * L ≤
      (0.033 * 1.013 + 0.0395 * 1.013) * (1 + 1e-60) / 160.54 := by
    have h1 : (x + 1) / x ≤ 1 + 1e-60 := by
      rw [div_le_iff₀ hx0]; nlinarith
    have hL0 : 0 < L := by linarith
    calc ((0.033 * 1.013 + 0.0395 * 1.013) * ((x + 1) / L ^ 2)) / x * L =
          (0.033 * 1.013 + 0.0395 * 1.013) * ((x + 1) / x) / L := by field_simp
      _ ≤ (0.033 * 1.013 + 0.0395 * 1.013) * (1 + 1e-60) / 160.54 := by
          apply div_le_div₀ (by positivity) (by gcongr) (by norm_num) hL
  have hL0 : 0 ≤ L := by linarith
  have hsplit : (Real.log x + Ssum N) / x * L ≤ L ^ 2 / x + Sf * L / x + (0.033 * ((x + 1) / (L - 2))) / x * L +
      ((0.033 * 1.013 + 0.0395 * 1.013) * ((x + 1) / L ^ 2)) / x * L := by
    rw [← hLdef]
    have : (L + Ssum N) / x * L ≤ (L + (Sf + 0.033 * ((x + 1) / (L - 2)) + 0.033 * 1.013 * ((x + 1) / L ^ 2) +
        0.0395 * 1.013 * ((x + 1) / L ^ 2))) / x * L := by gcongr
    refine le_trans this (le_of_eq ?_)
    field_simp; ring
  calc |∑ n ∈ Icc 1 N, (μ n : ℝ) / n| * L ≤ (|Mn N| / x + (Real.log x + Ssum N) / x) * L :=
        mul_le_mul_of_nonneg_right hm hL0
    _ = |Mn N| / x * L + (Real.log x + Ssum N) / x * L := by ring
    _ ≤ 0.075 := by norm_num at hb1 hb2 hb3 hSL hL2 hsplit ⊢; linarith

end TernaryGoldbach.Prelim.Sch
