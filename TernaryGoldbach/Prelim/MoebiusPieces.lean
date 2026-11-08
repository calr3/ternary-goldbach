import TernaryGoldbach.Prelim.MoebiusHead
import TernaryGoldbach.Prelim.SmallEMain

/-!
# The part `n ≤ x/Y` of the identity, range by range

The sum `∑_{n ≤ x/Y} |E(x/n)|/n`, `E(u) = E₁Λ(u) + γ`, is cut along ranges `u ≤ x/n < v`:
* `piece_le`: a range on which `|E(w)| ≤ K/√w + c + d₃/log³w + d₂/log²w`;
* `top_le`: the last range `u ≤ x/n ≤ x`;
* `tab_head`: the ranges below `10⁶`, with the constants `|E| ≤ e` of groups of the kernel table
  `SmallE.ETab` (`tabChk`, checked by the kernel), summed in `ℚ` (`gT1`, `gT2`).
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens

/-- `∑_{n ≤ N} 1/n ≤ 1 + log N`. -/
theorem sum_inv_Ioc_zero_le (N : ℕ) (hN : 1 ≤ N) : ∑ n ∈ Ioc 0 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
  induction N with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [sum_Ioc_succ_top (by omega)]
      have h1 := ih hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / k by positivity)
      rw [Real.log_div (by positivity) hk0.ne'] at h
      have e : 1 - (((k + 1 : ℕ) : ℝ) / k)⁻¹ = 1 / ((k + 1 : ℕ) : ℝ) := by
        push_cast; field_simp; ring
      linarith

/-- For `n ∈ (⌊x/v⌋, ⌊x/u⌋]`: `u ≤ x/n < v`. -/
theorem mem_piece {x u v : ℝ} (hx : 0 < x) (hu : 0 < u) (huv : u ≤ v) {n : ℕ}
    (hn : n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊) : 0 < n ∧ u ≤ x / n ∧ x / n < v := by
  obtain ⟨h1, h2⟩ := mem_Ioc.1 hn
  have hn0 : 0 < n := by omega
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hv : 0 < v := lt_of_lt_of_le hu huv
  refine ⟨hn0, ?_, ?_⟩
  · have : (n : ℝ) ≤ x / u := le_trans (by exact_mod_cast h2) (Nat.floor_le (by positivity))
    rw [le_div_iff₀ hn0']; rw [le_div_iff₀ hu] at this; linarith
  · have h3 : x / v < (n : ℝ) := by
      have := Nat.lt_floor_add_one (x / v)
      have h4 : ((⌊x / v⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h1
      linarith
    rw [div_lt_iff₀ hn0']; rw [div_lt_iff₀ hv] at h3; linarith

/-- The per-term bound. -/
theorem term_le {x w K c d3 d2 : ℝ} {n : ℕ} (hn : 0 < n) (hw : w = x / n)
    (hE : |Eg w| ≤ K / √w + c + d3 / Real.log w ^ 3 + d2 / Real.log w ^ 2) :
    |Eg (x / n)| / n ≤ K * (1 / (n * √(x / n))) + c * (1 / n) + d3 * (1 / (n * Real.log (x / n) ^ 3)) +
      d2 * (1 / (n * Real.log (x / n) ^ 2)) := by
  subst hw
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (K / √(x / n) + c + d3 / Real.log (x / n) ^ 3 + d2 / Real.log (x / n) ^ 2) / n =
      K * (1 / (n * √(x / n))) + c * (1 / n) + d3 * (1 / (n * Real.log (x / n) ^ 3)) +
        d2 * (1 / (n * Real.log (x / n) ^ 2)) := by
    simp only [div_eq_mul_inv, mul_inv, one_mul]; ring
  rw [← e]
  exact div_le_div_of_nonneg_right hE hn0.le

/-- `x/(⌊x/u⌋ + 1) ≥ u/2` for `u ≤ x`. -/
theorem div_floor_succ_ge {x u : ℝ} (hu : 0 < u) (hux : u ≤ x) :
    u / 2 ≤ x / ((⌊x / u⌋₊ : ℕ) + 1 : ℝ) := by
  have hx : 0 < x := lt_of_lt_of_le hu hux
  have hb : ((⌊x / u⌋₊ : ℕ) : ℝ) ≤ x / u := Nat.floor_le (by positivity)
  have hxu : 1 ≤ x / u := by rw [le_div_iff₀ hu]; linarith
  rw [le_div_iff₀ (by positivity)]
  have : u * (x / u) = x := by field_simp
  nlinarith

/-- The logarithmic terms: `∑_{n ≤ x/u} (d₃/log³(x/n) + d₂/log²(x/n))/n ≤ d₃/log²(u/2) + 2d₂/log(u/2)`. -/
theorem log_terms_le {x u d3 d2 : ℝ} (hu : 4 ≤ u) (hux : u ≤ x) (hd3 : 0 ≤ d3) (hd2 : 0 ≤ d2)
    {a : ℕ} (ha : a ≤ ⌊x / u⌋₊) :
    d3 * ∑ n ∈ Ioc a ⌊x / u⌋₊, (1 : ℝ) / (n * Real.log (x / n) ^ 3) +
      d2 * ∑ n ∈ Ioc a ⌊x / u⌋₊, (1 : ℝ) / (n * Real.log (x / n) ^ 2) ≤
      d3 / Real.log (u / 2) ^ 2 + 2 * d2 / Real.log (u / 2) := by
  have hu0 : 0 < u := by linarith
  have hx : 0 < x := by linarith
  have hb : ((⌊x / u⌋₊ : ℕ) : ℝ) + 1 < x := by
    have h1 : ((⌊x / u⌋₊ : ℕ) : ℝ) ≤ x / u := Nat.floor_le (by positivity)
    have h2 : x / u ≤ x / 4 := div_le_div_of_nonneg_left hx.le (by norm_num) hu
    linarith
  have hge := div_floor_succ_ge hu0 hux
  have hl2 : 0 < Real.log (u / 2) := Real.log_pos (by linarith)
  have hlb : Real.log (u / 2) ≤ Real.log (x / ((⌊x / u⌋₊ : ℕ) + 1 : ℝ)) :=
    Real.log_le_log (by linarith) hge
  have s3 := sum_log3_piece hx ha hb
  have s2 := sum_log2_piece hx ha hb
  have k3 : 1 / Real.log (x / ((⌊x / u⌋₊ : ℕ) + 1 : ℝ)) ^ 2 ≤ 1 / Real.log (u / 2) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl2.le hlb 2)
  have k2 : 2 / Real.log (x / ((⌊x / u⌋₊ : ℕ) + 1 : ℝ)) ≤ 2 / Real.log (u / 2) :=
    div_le_div_of_nonneg_left (by norm_num) hl2 hlb
  have e3 : d3 / Real.log (u / 2) ^ 2 = d3 * (1 / Real.log (u / 2) ^ 2) := by ring
  have e2 : 2 * d2 / Real.log (u / 2) = d2 * (2 / Real.log (u / 2)) := by ring
  rw [e3, e2]
  exact add_le_add (mul_le_mul_of_nonneg_left (s3.trans k3) hd3)
    (mul_le_mul_of_nonneg_left (s2.trans k2) hd2)

/-- **A range `u ≤ x/n < v`.** -/
theorem piece_le {x u v K c d3 d2 : ℝ} (hu : 4 ≤ u) (huv : u ≤ v) (hux : u ≤ x)
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hd3 : 0 ≤ d3) (hd2 : 0 ≤ d2)
    (hE : ∀ w, u ≤ w → w < v → |Eg w| ≤ K / √w + c + d3 / Real.log w ^ 3 + d2 / Real.log w ^ 2) :
    ∑ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, |Eg (x / n)| / n ≤
      K * (2 / √u - 2 / √v + 2 * √v / x) + c * (Real.log (v / u) + 2 * v / x) +
        (d3 / Real.log (u / 2) ^ 2 + 2 * d2 / Real.log (u / 2)) := by
  have hu0 : 0 < u := by linarith
  have hx : 0 < x := by linarith
  have hab : ⌊x / v⌋₊ ≤ ⌊x / u⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_left hx.le hu0 huv)
  have hterm : ∀ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, |Eg (x / n)| / n ≤
      K * (1 / (n * √(x / n))) + c * (1 / n) + d3 * (1 / (n * Real.log (x / n) ^ 3)) +
        d2 * (1 / (n * Real.log (x / n) ^ 2)) := by
    intro n hn
    obtain ⟨hn0, h1, h2⟩ := mem_piece hx hu0 huv hn
    exact term_le hn0 rfl (hE _ h1 h2)
  refine (sum_le_sum hterm).trans ?_
  simp only [sum_add_distrib, ← mul_sum]
  have s1 := mul_le_mul_of_nonneg_left (sum_sqrt_piece hx hu0 huv) hK
  have s2 := mul_le_mul_of_nonneg_left (sum_inv_piece hx (by linarith) huv) hc
  have s3 := log_terms_le hu hux hd3 hd2 hab
  linarith

/-- **The last range `u ≤ x/n ≤ x`.** -/
theorem top_le {x u K c d3 d2 : ℝ} (hu : 4 ≤ u) (hux : u ≤ x)
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hd3 : 0 ≤ d3) (hd2 : 0 ≤ d2)
    (hE : ∀ w, u ≤ w → w ≤ x → |Eg w| ≤ K / √w + c + d3 / Real.log w ^ 3 + d2 / Real.log w ^ 2) :
    ∑ n ∈ Ioc 0 ⌊x / u⌋₊, |Eg (x / n)| / n ≤
      2 * K / √u + c * (1 + Real.log (x / u)) + (d3 / Real.log (u / 2) ^ 2 + 2 * d2 / Real.log (u / 2)) := by
  have hu0 : 0 < u := by linarith
  have hx : 0 < x := by linarith
  have hN1 : 1 ≤ ⌊x / u⌋₊ := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hu0]; linarith)
  have hterm : ∀ n ∈ Ioc 0 ⌊x / u⌋₊, |Eg (x / n)| / n ≤
      K * (1 / (n * √(x / n))) + c * (1 / n) + d3 * (1 / (n * Real.log (x / n) ^ 3)) +
        d2 * (1 / (n * Real.log (x / n) ^ 2)) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hn
    have hn0' : (0 : ℝ) < n := by exact_mod_cast h1
    refine term_le h1 rfl (hE _ ?_ ?_)
    · have : (n : ℝ) ≤ x / u := le_trans (by exact_mod_cast h2) (Nat.floor_le (by positivity))
      rw [le_div_iff₀ hn0']; rw [le_div_iff₀ hu0] at this; linarith
    · rw [div_le_iff₀ hn0']
      have : (1 : ℝ) ≤ n := by exact_mod_cast h1
      nlinarith
  refine (sum_le_sum hterm).trans ?_
  simp only [sum_add_distrib, ← mul_sum]
  -- the `√` part
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have hsq : ∑ n ∈ Ioc 0 ⌊x / u⌋₊, (1 : ℝ) / (n * √(x / n)) ≤ 2 / √u := by
    have e : ∀ n ∈ Ioc 0 ⌊x / u⌋₊, (1 : ℝ) / (n * √(x / n)) = 1 / √x * (1 / √(n : ℝ)) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
      rw [Real.sqrt_div hx.le]
      have hsn := Real.mul_self_sqrt hn0.le
      have hsn0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
      field_simp
      nlinarith [hsn]
    rw [sum_congr rfl e, ← mul_sum]
    have h1 := sum_inv_sqrt_Ioc (a := 0) (b := ⌊x / u⌋₊) (Nat.zero_le _)
    have hb : √((⌊x / u⌋₊ : ℕ) : ℝ) ≤ √x / √u := by
      rw [← Real.sqrt_div' x hu0.le]; exact Real.sqrt_le_sqrt (Nat.floor_le (by positivity))
    simp only [Nat.cast_zero, Real.sqrt_zero, sub_zero] at h1
    have hsu : 0 < √u := Real.sqrt_pos.2 hu0
    calc 1 / √x * ∑ n ∈ Ioc 0 ⌊x / u⌋₊, (1 : ℝ) / √(n : ℝ) ≤ 1 / √x * (2 * (√x / √u)) :=
          mul_le_mul_of_nonneg_left (h1.trans (by linarith)) (by positivity)
      _ = 2 / √u := by field_simp
  -- the harmonic part
  have hinv : ∑ n ∈ Ioc 0 ⌊x / u⌋₊, (1 : ℝ) / n ≤ 1 + Real.log (x / u) := by
    refine (sum_inv_Ioc_zero_le _ hN1).trans ?_
    have : (0 : ℝ) < ⌊x / u⌋₊ := by exact_mod_cast hN1
    linarith [Real.log_le_log this (Nat.floor_le (show 0 ≤ x / u by positivity))]
  have s1 := mul_le_mul_of_nonneg_left hsq hK
  have s2 := mul_le_mul_of_nonneg_left hinv hc
  have s3 := log_terms_le hu hux hd3 hd2 (Nat.zero_le _)
  have e : K * (2 / √u) = 2 * K / √u := by ring
  linarith

/-! ### The table below `10⁶` -/

/-- `SmallE.E1` is `E₁Λ`. -/
theorem smallE1_eq (u : ℝ) : SmallE.E1 u = E₁Λ u := rfl

/-- A chunk `c` of the table is compatible with the bound `|E| ≤ en/S` on `[U, V)`. -/
def tabCk (U V en : ℕ) (c : ℕ × ℕ × ℤ × ℤ) : Bool :=
  !(decide (c.1 < V) && decide (U < c.2.1)) ||
    (decide (c.2.2.2 + 577219635862 ≤ (en : ℤ)) && decide (-(c.2.2.1 + 577211640885) ≤ (en : ℤ)))

/-- `|E| ≤ en/S` on `[U, V)`, as a check of all chunks of the table. -/
def tabChk (U V en : ℕ) : Bool := SmallE.ETab.all (tabCk U V en)

/-- The chunks of `L` cover `[1, b)` contiguously, from the top. -/
def Cov : ℕ → List (ℕ × ℕ × ℤ × ℤ) → Bool
  | b, [] => decide (b ≤ 1)
  | b, c :: L => decide (c.2.1 = b) && decide (c.1 < b) && Cov c.1 L

theorem cov_spec : ∀ (L : List (ℕ × ℕ × ℤ × ℤ)) (b : ℕ), Cov b L = true →
    ∀ w : ℝ, 1 ≤ w → w < b → ∃ c ∈ L, (c.1 : ℝ) ≤ w ∧ w < c.2.1
  | [], b, h, w, h1, h2 => by
    simp only [Cov, decide_eq_true_eq] at h
    have : (b : ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  | c :: L, b, h, w, h1, h2 => by
    simp only [Cov, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, _⟩, hL⟩ := h
    by_cases hw : (c.1 : ℝ) ≤ w
    · exact ⟨c, List.mem_cons_self, hw, by rw [hb]; exact h2⟩
    · obtain ⟨d, hd, h⟩ := cov_spec L c.1 hL w h1 (lt_of_not_ge hw)
      exact ⟨d, List.mem_cons_of_mem _ hd, h⟩

theorem etab_cov : Cov 1000000 SmallE.ETab = true := by decide +kernel

theorem gamma_lo_hi : (577211640885 : ℝ) / SmallE.S < Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant < (577219635862 : ℝ) / SmallE.S := by
  have h := SmallE.gamma_tab
  have hS : (SmallE.S : ℝ) = 1000000000000 := by norm_num [SmallE.S]
  rw [hS] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **A group of the table**: `tabChk U V en` gives `|E(w)| ≤ en/S` on `[U, V)`. -/
theorem tab_group {U V en : ℕ} (h : tabChk U V en = true) (hU : 1 ≤ U) (hV : V ≤ 1000000) {w : ℝ}
    (h1 : (U : ℝ) ≤ w) (h2 : w < V) : |Eg w| ≤ (en : ℝ) / SmallE.S := by
  have hw1 : (1 : ℝ) ≤ w := le_trans (by exact_mod_cast hU) h1
  have hw2 : w < ((1000000 : ℕ) : ℝ) := lt_of_lt_of_le h2 (by exact_mod_cast hV)
  obtain ⟨c, hc, hc1, hc2⟩ := cov_spec _ _ etab_cov w hw1 hw2
  have hok := SmallE.ETab_ok c hc w hc1 hc2
  have hck : tabCk U V en c = true := List.all_eq_true.1 h c hc
  have hov1 : c.1 < V := by
    have : (c.1 : ℝ) < V := lt_of_le_of_lt hc1 h2
    exact_mod_cast this
  have hov2 : U < c.2.1 := by
    have : (U : ℝ) < c.2.1 := lt_of_le_of_lt h1 hc2
    exact_mod_cast this
  simp only [tabCk, hov1, hov2, decide_true, Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨k1, k2⟩ := hck
  have k1' : ((c.2.2.2 : ℤ) : ℝ) + 577219635862 ≤ (en : ℝ) := by exact_mod_cast k1
  have k2' : -(((c.2.2.1 : ℤ) : ℝ) + 577211640885) ≤ (en : ℝ) := by exact_mod_cast k2
  have hS : (0 : ℝ) < SmallE.S := by norm_num [SmallE.S]
  have hg := gamma_lo_hi
  rw [smallE1_eq] at hok
  unfold Eg
  rw [abs_le]
  have a1 : ((c.2.2.2 : ℤ) : ℝ) / SmallE.S + 577219635862 / SmallE.S ≤ (en : ℝ) / SmallE.S := by
    rw [← add_div]; exact div_le_div_of_nonneg_right k1' hS.le
  have a2 : -((en : ℝ) / SmallE.S) ≤ ((c.2.2.1 : ℤ) : ℝ) / SmallE.S + 577211640885 / SmallE.S := by
    rw [← add_div, ← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hS.le
  constructor <;> linarith [hok.1, hok.2, hg.1, hg.2]

/-- `|E(u)| ≤ 0.5773` on `[1, 10⁶)`. -/
theorem Eg_le_F {u : ℝ} (h1 : 1 ≤ u) (h2 : u < 1000000) : |Eg u| ≤ 0.5773 := by
  have h := tab_group (U := 1) (V := 1000000) (en := 577300000000) (by decide +kernel) le_rfl le_rfl
    (by exact_mod_cast h1) (by exact_mod_cast h2)
  norm_num [SmallE.S] at h ⊢
  linarith

/-- Groups `(V, en)` from `U` on, ending at `10⁶`, each checked by `tabChk`. -/
def GOK : ℕ → List (ℕ × ℕ) → Bool
  | U, [] => decide (U = 1000000)
  | U, (V, en) :: gs => decide (1 ≤ U) && decide (U ≤ V) && tabChk U V en && GOK V gs

/-- `∑ e (V − U)/U`. -/
def gT1 : ℕ → List (ℕ × ℕ) → ℚ
  | _, [] => 0
  | U, (V, en) :: gs => (en : ℚ) * ((V : ℚ) - U) / (U * 1000000000000) + gT1 V gs

/-- `∑ 2 e V`. -/
def gT2 : List (ℕ × ℕ) → ℚ
  | [] => 0
  | (V, en) :: gs => 2 * (en : ℚ) * V / 1000000000000 + gT2 gs

theorem GOK_le : ∀ (gs : List (ℕ × ℕ)) (U : ℕ), GOK U gs = true → U ≤ 1000000
  | [], U, h => by simp only [GOK, decide_eq_true_eq] at h; omega
  | (V, en) :: gs, U, h => by
    simp only [GOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have := GOK_le gs V h.2
    omega

/-- A constant range: `∑ |E(x/n)|/n ≤ c (log(v/u) + 2v/x)`. -/
theorem piece_const {x u v c : ℝ} (hx : 0 < x) (hu : 1 ≤ u) (huv : u ≤ v) (hc : 0 ≤ c)
    (hE : ∀ w, u ≤ w → w < v → |Eg w| ≤ c) :
    ∑ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, |Eg (x / n)| / n ≤ c * (Real.log (v / u) + 2 * v / x) := by
  have hu0 : 0 < u := by linarith
  have hterm : ∀ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, |Eg (x / n)| / n ≤ c * (1 / n) := by
    intro n hn
    obtain ⟨hn0, h1, h2⟩ := mem_piece hx hu0 huv hn
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [mul_one_div]; exact div_le_div_of_nonneg_right (hE _ h1 h2) hn0'.le
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_inv_piece hx hu huv) hc

/-- **The table ranges**: `∑_{x/10⁶ < n ≤ x/U} |E(x/n)|/n ≤ gT1 + gT2/x`. -/
theorem tab_head {x : ℝ} (hx : 0 < x) : ∀ (gs : List (ℕ × ℕ)) (U : ℕ), GOK U gs = true →
    ∑ n ∈ Ioc ⌊x / 1000000⌋₊ ⌊x / U⌋₊, |Eg (x / n)| / n ≤ (gT1 U gs : ℝ) + (gT2 gs : ℝ) / x
  | [], U, h => by
    simp only [GOK, decide_eq_true_eq] at h
    subst h
    simp [gT1, gT2]
  | (V, en) :: gs, U, h => by
    have hV := GOK_le gs V (by simp only [GOK, Bool.and_eq_true] at h; exact h.2)
    simp only [GOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hU1, hUV⟩, hchk⟩, hgs⟩ := h
    have ih := tab_head hx gs V hgs
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU1
    have hUV' : (U : ℝ) ≤ V := by exact_mod_cast hUV
    have hV0 : (0 : ℝ) < V := lt_of_lt_of_le hU0 hUV'
    have m1 : ⌊x / 1000000⌋₊ ≤ ⌊x / V⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hx.le hV0 (by exact_mod_cast hV))
    have m2 : ⌊x / V⌋₊ ≤ ⌊x / U⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_left hx.le hU0 hUV')
    rw [← sum_Ioc_consecutive _ m1 m2]
    have hS : (0 : ℝ) < SmallE.S := by norm_num [SmallE.S]
    have hp := piece_const (c := (en : ℝ) / SmallE.S) hx (by exact_mod_cast hU1) hUV' (by positivity)
      fun w h1 h2 => tab_group hchk hU1 hV (by exact_mod_cast h1) (by exact_mod_cast h2)
    have hlog : Real.log ((V : ℝ) / U) ≤ ((V : ℝ) - U) / U := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < V / U by positivity)
      rw [sub_div, div_self hU0.ne']; exact this
    have hen : (0 : ℝ) ≤ (en : ℝ) / SmallE.S := by positivity
    have hp' : ∑ n ∈ Ioc ⌊x / V⌋₊ ⌊x / U⌋₊, |Eg (x / n)| / n ≤
        (en : ℝ) / SmallE.S * (((V : ℝ) - U) / U) + 2 * ((en : ℝ) / SmallE.S) * V / x := by
      refine hp.trans ?_
      have := mul_le_mul_of_nonneg_left hlog hen
      have e : (en : ℝ) / SmallE.S * (Real.log (V / U) + 2 * V / x) =
          (en : ℝ) / SmallE.S * Real.log (V / U) + 2 * ((en : ℝ) / SmallE.S) * V / x := by ring
      linarith
    have hSv : (SmallE.S : ℝ) = 1000000000000 := by norm_num [SmallE.S]
    have e1 : ((gT1 U ((V, en) :: gs) : ℚ) : ℝ) =
        (en : ℝ) / SmallE.S * (((V : ℝ) - U) / U) + (gT1 V gs : ℝ) := by
      simp only [gT1]; push_cast; rw [hSv]; field_simp
    have e2 : ((gT2 ((V, en) :: gs) : ℚ) : ℝ) / x =
        2 * ((en : ℝ) / SmallE.S) * V / x + (gT2 gs : ℝ) / x := by
      simp only [gT2]; push_cast; rw [hSv]; field_simp
    rw [e1, e2]
    linarith

end TernaryGoldbach.Prelim
