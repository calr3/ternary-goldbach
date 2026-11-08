import TernaryGoldbach.Prelim.MoebiusPieces
import TernaryGoldbach.Prelim.EOneRegions

/-!
# The ranges `x/n ≥ 10⁶` of the identity

The ranges of `u = x/n`, with the bounds of `EOneRegions.lean`:
`[10⁶, 7043²]`, `[7043², 31622²)`, `[31622², 39749²]`, `[39749², 7·10⁶²]`, `[4.9·10¹³, e^{20001})`,
`[e^{20001}, ∞)`. `an_k`: the sum `∑_{n ≤ x/10⁶} |E(x/n)|/n` when `x` lies in the `k`-th range,
in terms of a lower bound `X0 ≤ x` and an upper bound `log x ≤ L1`.
-/

open Finset

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens TernaryGoldbach.Explicit
open TernaryGoldbach.Prelim.Small (chkStep chkLow log_lt_of_chk le_log_of_chk)

theorem log_ge_cert {L cN : ℕ} (hL : 0 < L) (h : chkLow cN 10000 L = true) :
    (cN : ℝ) / 10000 ≤ Real.log L := by
  have := le_log_of_chk (by norm_num) hL h
  push_cast at this; exact this

theorem log_le_cert {L cN : ℕ} (hL : 0 < L) (h : chkStep cN 10000 1 L = true) :
    Real.log L ≤ (cN : ℝ) / 10000 := by
  have := log_lt_of_chk (by norm_num) hL h
  push_cast at this; linarith

theorem sqrt_sq_nat (a : ℕ) : √((a ^ 2 : ℕ) : ℝ) = a := by
  push_cast; exact Real.sqrt_sq (Nat.cast_nonneg _)

theorem l_r0 : 13.8154 ≤ Real.log (1000000 : ℕ) := by
  have := log_ge_cert (L := 1000000) (cN := 138154) (by norm_num) (by decide +kernel); norm_num at this ⊢; linarith
theorem l_r1 : 17.7194 ≤ Real.log (49603849 : ℕ) ∧ Real.log (49603849 : ℕ) ≤ 17.7197 := by
  have h1 := log_ge_cert (L := 49603849) (cN := 177194) (by norm_num) (by decide +kernel)
  have h2 := log_le_cert (L := 49603849) (cN := 177197) (by norm_num) (by decide +kernel)
  norm_num at h1 h2 ⊢; exact ⟨by linarith, by linarith⟩
theorem l_r2 : 20.7231 ≤ Real.log (999950884 : ℕ) ∧ Real.log (999950884 : ℕ) ≤ 20.7234 := by
  have h1 := log_ge_cert (L := 999950884) (cN := 207231) (by norm_num) (by decide +kernel)
  have h2 := log_le_cert (L := 999950884) (cN := 207234) (by norm_num) (by decide +kernel)
  norm_num at h1 h2 ⊢; exact ⟨by linarith, by linarith⟩
theorem l_r3 : 21.1805 ≤ Real.log (1579983001 : ℕ) ∧ Real.log (1579983001 : ℕ) ≤ 21.1808 := by
  have h1 := log_ge_cert (L := 1579983001) (cN := 211805) (by norm_num) (by decide +kernel)
  have h2 := log_le_cert (L := 1579983001) (cN := 211808) (by norm_num) (by decide +kernel)
  norm_num at h1 h2 ⊢; exact ⟨by linarith, by linarith⟩
theorem l_r4 : 31.5227 ≤ Real.log (49000000000000 : ℕ) ∧ Real.log (49000000000000 : ℕ) ≤ 31.523 := by
  have h1 := log_ge_cert (L := 49000000000000) (cN := 315227) (by norm_num) (by decide +kernel)
  have h2 := log_le_cert (L := 49000000000000) (cN := 315230) (by norm_num) (by decide +kernel)
  norm_num at h1 h2 ⊢; exact ⟨by linarith, by linarith⟩

theorem log_div_nat_le {u v : ℕ} (hu : 0 < u) (hv : 0 < v) {a b : ℝ} (ha : a ≤ Real.log u)
    (hb : Real.log v ≤ b) : Real.log ((v : ℝ) / u) ≤ b - a := by
  rw [Real.log_div (by positivity) (by positivity)]; linarith

variable [Fact TernaryGoldbach.PlattGRH]

/-! ### The bounds for `E` in the common form -/

theorem ER1 {w : ℝ} (h1 : ((1000000 : ℕ) : ℝ) ≤ w) (h2 : w ≤ ((49603849 : ℕ) : ℝ)) :
    |Eg w| ≤ 11.82 / √w + 1e-13 + 0 / Real.log w ^ 3 + 0 / Real.log w ^ 2 := by
  have := E_R1 (u := w) (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  simpa using this

theorem ER2 {w : ℝ} (h1 : ((49603849 : ℕ) : ℝ) ≤ w) (h2 : w < ((999950884 : ℕ) : ℝ)) :
    |Eg w| ≤ 13.6 / √w + 0.0022500000001 + 0 / Real.log w ^ 3 + 0 / Real.log w ^ 2 := by
  have := E_R2 (u := w) (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  simp only [zero_div, add_zero]; linarith

theorem ER3 {w : ℝ} (h1 : ((999950884 : ℕ) : ℝ) ≤ w) (h2 : w ≤ ((1579983001 : ℕ) : ℝ)) :
    |Eg w| ≤ 112.7 / √w + 1e-13 + 0 / Real.log w ^ 3 + 0 / Real.log w ^ 2 := by
  have := E_R3 (u := w) (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  simpa using this

theorem ER4 {w : ℝ} (h1 : ((1579983001 : ℕ) : ℝ) ≤ w) (h2 : w ≤ ((49000000000000 : ℕ) : ℝ)) :
    |Eg w| ≤ 222.6 / √w + 1e-13 + 0 / Real.log w ^ 3 + 0 / Real.log w ^ 2 := by
  have := E_R4 (u := w) (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  simpa using this

theorem ER5 {w : ℝ} (h1 : ((49000000000000 : ℕ) : ℝ) ≤ w) :
    |Eg w| ≤ 97 / √w + 1.234001e-6 + 2.51 / Real.log w ^ 3 + 0 / Real.log w ^ 2 := by
  have := E_R5 (u := w) (by norm_num at h1 ⊢; linarith)
  simp only [zero_div, add_zero]; linarith

theorem ER6 {w : ℝ} (h1 : Real.exp 20001 ≤ w) :
    |Eg w| ≤ 4100 / √w + 0 + 33 / Real.log w ^ 3 + 4.1 / Real.log w ^ 2 := by
  have hw : 0 < w := lt_of_lt_of_le (Real.exp_pos _) h1
  have hl : 20001 ≤ Real.log w := by
    rw [← Real.log_exp 20001]; exact Real.log_le_log (Real.exp_pos _) h1
  have h1' : (1 : ℝ) ≤ w := le_trans (by have := Real.add_one_le_exp (20001 : ℝ); linarith) h1
  have := E_R6 h1' hl
  simpa using this

/-! ### The full ranges -/

theorem full1 {x X0 : ℝ} (hX0 : 0 < X0) (hx : ((49603849 : ℕ) : ℝ) ≤ x) (hX0x : X0 ≤ x) :
    ∑ n ∈ Ioc ⌊x / ((49603849 : ℕ) : ℝ)⌋₊ ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      11.82 * (2 / 1000 - 2 / 7043 + 2 * 7043 / X0) + 1e-13 * (3.9043 + 2 * 49603849 / X0) := by
  have h := piece_le (x := x) (K := 11.82) (c := 1e-13) (d3 := 0) (d2 := 0) (by norm_num)
    (by norm_num) (by norm_num at hx ⊢; linarith) (by norm_num) (by norm_num) le_rfl le_rfl
    fun w h1 h2 => ER1 h1 h2.le
  have hx0 : 0 < x := by norm_num at hx; linarith
  rw [show ((1000000 : ℕ) : ℝ) = ((1000 ^ 2 : ℕ) : ℝ) by norm_num,
    show ((49603849 : ℕ) : ℝ) = ((7043 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat, sqrt_sq_nat] at h
  rw [show ((1000000 : ℕ) : ℝ) = ((1000 ^ 2 : ℕ) : ℝ) by norm_num,
    show ((49603849 : ℕ) : ℝ) = ((7043 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl := log_div_nat_le (u := 1000 ^ 2) (v := 7043 ^ 2) (by norm_num) (by norm_num)
    (by norm_num; exact l_r0) (by norm_num; exact l_r1.2)
  have k1 : 2 * ((7043 : ℕ) : ℝ) / x ≤ 2 * 7043 / X0 := by
    push_cast; exact div_le_div_of_nonneg_left (by norm_num) hX0 hX0x
  have k2 : 2 * ((7043 ^ 2 : ℕ) : ℝ) / x ≤ 2 * 49603849 / X0 := by
    push_cast; norm_num; exact div_le_div_of_nonneg_left (by norm_num) hX0 hX0x
  simp only [zero_div]
  push_cast at hl k1 k2 ⊢
  norm_num at hl k1 k2 ⊢
  nlinarith

theorem full2 {x X0 : ℝ} (hX0 : 0 < X0) (hx : ((999950884 : ℕ) : ℝ) ≤ x) (hX0x : X0 ≤ x) :
    ∑ n ∈ Ioc ⌊x / ((999950884 : ℕ) : ℝ)⌋₊ ⌊x / ((49603849 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      13.6 * (2 / 7043 - 2 / 31622 + 2 * 31622 / X0) + 0.0022500000001 * (3.004 + 2 * 999950884 / X0) := by
  have h := piece_le (x := x) (K := 13.6) (c := 0.0022500000001) (d3 := 0) (d2 := 0) (by norm_num)
    (by norm_num) (by norm_num at hx ⊢; linarith) (by norm_num) (by norm_num) le_rfl le_rfl
    fun w h1 h2 => ER2 h1 h2
  rw [show ((49603849 : ℕ) : ℝ) = ((7043 ^ 2 : ℕ) : ℝ) by norm_num,
    show ((999950884 : ℕ) : ℝ) = ((31622 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat, sqrt_sq_nat] at h
  rw [show ((49603849 : ℕ) : ℝ) = ((7043 ^ 2 : ℕ) : ℝ) by norm_num,
    show ((999950884 : ℕ) : ℝ) = ((31622 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl := log_div_nat_le (u := 7043 ^ 2) (v := 31622 ^ 2) (by norm_num) (by norm_num)
    (by norm_num; exact l_r1.1) (by norm_num; exact l_r2.2)
  have k1 : 2 * ((31622 : ℕ) : ℝ) / x ≤ 2 * 31622 / X0 := by
    push_cast; exact div_le_div_of_nonneg_left (by norm_num) hX0 hX0x
  have k2 : 2 * ((31622 ^ 2 : ℕ) : ℝ) / x ≤ 2 * 999950884 / X0 := by
    push_cast; norm_num; exact div_le_div_of_nonneg_left (by norm_num) hX0 hX0x
  simp only [zero_div]
  push_cast at hl k1 k2 ⊢
  norm_num at hl k1 k2 ⊢
  nlinarith

theorem full3 {x X0 : ℝ} (hX0 : 0 < X0) (hx : ((1579983001 : ℕ) : ℝ) ≤ x) (hX0x : X0 ≤ x) :
    ∑ n ∈ Ioc ⌊x / ((1579983001 : ℕ) : ℝ)⌋₊ ⌊x / ((999950884 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      112.7 * (2 / 31622 - 2 / 39749 + 2 * 39749 / X0) + 1e-13 * (0.4577 + 2 * 1579983001 / X0) := by
  have h := piece_le (x := x) (K := 112.7) (c := 1e-13) (d3 := 0) (d2 := 0) (by norm_num)
    (by norm_num) (by norm_num at hx ⊢; linarith) (by norm_num) (by norm_num) le_rfl le_rfl
    fun w h1 h2 => ER3 h1 h2.le
  rw [show ((999950884 : ℕ) : ℝ) = ((31622 ^ 2 : ℕ) : ℝ) by norm_num,
    show ((1579983001 : ℕ) : ℝ) = ((39749 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat, sqrt_sq_nat] at h
  rw [show ((999950884 : ℕ) : ℝ) = ((31622 ^ 2 : ℕ) : ℝ) by norm_num,
    show ((1579983001 : ℕ) : ℝ) = ((39749 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl := log_div_nat_le (u := 31622 ^ 2) (v := 39749 ^ 2) (by norm_num) (by norm_num)
    (by norm_num; exact l_r2.1) (by norm_num; exact l_r3.2)
  have k1 : 2 * ((39749 : ℕ) : ℝ) / x ≤ 2 * 39749 / X0 := by
    push_cast; exact div_le_div_of_nonneg_left (by norm_num) hX0 hX0x
  have k2 : 2 * ((39749 ^ 2 : ℕ) : ℝ) / x ≤ 2 * 1579983001 / X0 := by
    push_cast; norm_num; exact div_le_div_of_nonneg_left (by norm_num) hX0 hX0x
  simp only [zero_div]
  push_cast at hl k1 k2 ⊢
  norm_num at hl k1 k2 ⊢
  nlinarith

theorem full4 {x X0 : ℝ} (hX0 : 0 < X0) (hx : ((49000000000000 : ℕ) : ℝ) ≤ x) (hX0x : X0 ≤ x) :
    ∑ n ∈ Ioc ⌊x / ((49000000000000 : ℕ) : ℝ)⌋₊ ⌊x / ((1579983001 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      222.6 * (2 / 39749 - 2 / 7000000 + 2 * 7000000 / X0) + 1e-13 * (10.3425 + 2 * 49000000000000 / X0) := by
  have h := piece_le (x := x) (K := 222.6) (c := 1e-13) (d3 := 0) (d2 := 0) (by norm_num)
    (by norm_num) (by norm_num at hx ⊢; linarith) (by norm_num) (by norm_num) le_rfl le_rfl
    fun w h1 h2 => ER4 h1 h2.le
  rw [show ((1579983001 : ℕ) : ℝ) = ((39749 ^ 2 : ℕ) : ℝ) by norm_num,
    show ((49000000000000 : ℕ) : ℝ) = ((7000000 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat, sqrt_sq_nat] at h
  rw [show ((1579983001 : ℕ) : ℝ) = ((39749 ^ 2 : ℕ) : ℝ) by norm_num,
    show ((49000000000000 : ℕ) : ℝ) = ((7000000 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl := log_div_nat_le (u := 39749 ^ 2) (v := 7000000 ^ 2) (by norm_num) (by norm_num)
    (by norm_num; exact l_r3.1) (by norm_num; exact l_r4.2)
  have k1 : 2 * ((7000000 : ℕ) : ℝ) / x ≤ 2 * 7000000 / X0 := by
    push_cast; exact div_le_div_of_nonneg_left (by norm_num) hX0 hX0x
  have k2 : 2 * ((7000000 ^ 2 : ℕ) : ℝ) / x ≤ 2 * 49000000000000 / X0 := by
    push_cast; norm_num; exact div_le_div_of_nonneg_left (by norm_num) hX0 hX0x
  simp only [zero_div]
  push_cast at hl k1 k2 ⊢
  norm_num at hl k1 k2 ⊢
  nlinarith

theorem top1 {x L1 : ℝ} (hx : ((1000000 : ℕ) : ℝ) ≤ x) (hx1 : x ≤ ((49603849 : ℕ) : ℝ)) (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤ 2 * 11.82 / 1000 + 1e-13 * (1 + L1 - 13.8154) := by
  have h := top_le (x := x) (K := 11.82) (c := 1e-13) (d3 := 0) (d2 := 0) (by norm_num) hx
    (by norm_num) (by norm_num) le_rfl le_rfl fun w h1 h2 => ER1 h1 (h2.trans hx1)
  rw [show ((1000000 : ℕ) : ℝ) = ((1000 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat] at h
  rw [show ((1000000 : ℕ) : ℝ) = ((1000 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl : 13.8154 ≤ Real.log ((1000 ^ 2 : ℕ) : ℝ) := by
    rw [show ((1000 ^ 2 : ℕ) : ℝ) = ((1000000 : ℕ) : ℝ) by norm_num]; exact l_r0
  have hx0 : (0 : ℝ) < x := by norm_num at hx; linarith
  have e : Real.log (x / ((1000 ^ 2 : ℕ) : ℝ)) = Real.log x - Real.log ((1000 ^ 2 : ℕ) : ℝ) :=
    Real.log_div hx0.ne' (by positivity)
  rw [e]
  simp only [zero_div]
  push_cast at hl ⊢
  norm_num at hl ⊢
  nlinarith

theorem top2 {x L1 : ℝ} (hx : ((49603849 : ℕ) : ℝ) ≤ x) (hx1 : x < ((999950884 : ℕ) : ℝ)) (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((49603849 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤ 2 * 13.6 / 7043 + 0.0022500000001 * (1 + L1 - 17.7194) := by
  have h := top_le (x := x) (K := 13.6) (c := 0.0022500000001) (d3 := 0) (d2 := 0) (by norm_num) hx
    (by norm_num) (by norm_num) le_rfl le_rfl fun w h1 h2 => ER2 h1 (lt_of_le_of_lt h2 hx1)
  rw [show ((49603849 : ℕ) : ℝ) = ((7043 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat] at h
  rw [show ((49603849 : ℕ) : ℝ) = ((7043 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl : 17.7194 ≤ Real.log ((7043 ^ 2 : ℕ) : ℝ) := by
    rw [show ((7043 ^ 2 : ℕ) : ℝ) = ((49603849 : ℕ) : ℝ) by norm_num]; exact l_r1.1
  have hx0 : (0 : ℝ) < x := by norm_num at hx; linarith
  have e : Real.log (x / ((7043 ^ 2 : ℕ) : ℝ)) = Real.log x - Real.log ((7043 ^ 2 : ℕ) : ℝ) :=
    Real.log_div hx0.ne' (by positivity)
  rw [e]
  simp only [zero_div]
  push_cast at hl ⊢
  norm_num at hl ⊢
  nlinarith

theorem top3 {x L1 : ℝ} (hx : ((999950884 : ℕ) : ℝ) ≤ x) (hx1 : x ≤ ((1579983001 : ℕ) : ℝ)) (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((999950884 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤ 2 * 112.7 / 31622 + 1e-13 * (1 + L1 - 20.7231) := by
  have h := top_le (x := x) (K := 112.7) (c := 1e-13) (d3 := 0) (d2 := 0) (by norm_num) hx
    (by norm_num) (by norm_num) le_rfl le_rfl fun w h1 h2 => ER3 h1 (h2.trans hx1)
  rw [show ((999950884 : ℕ) : ℝ) = ((31622 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat] at h
  rw [show ((999950884 : ℕ) : ℝ) = ((31622 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl : 20.7231 ≤ Real.log ((31622 ^ 2 : ℕ) : ℝ) := by
    rw [show ((31622 ^ 2 : ℕ) : ℝ) = ((999950884 : ℕ) : ℝ) by norm_num]; exact l_r2.1
  have hx0 : (0 : ℝ) < x := by norm_num at hx; linarith
  have e : Real.log (x / ((31622 ^ 2 : ℕ) : ℝ)) = Real.log x - Real.log ((31622 ^ 2 : ℕ) : ℝ) :=
    Real.log_div hx0.ne' (by positivity)
  rw [e]
  simp only [zero_div]
  push_cast at hl ⊢
  norm_num at hl ⊢
  nlinarith

theorem top4 {x L1 : ℝ} (hx : ((1579983001 : ℕ) : ℝ) ≤ x) (hx1 : x ≤ ((49000000000000 : ℕ) : ℝ)) (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((1579983001 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤ 2 * 222.6 / 39749 + 1e-13 * (1 + L1 - 21.1805) := by
  have h := top_le (x := x) (K := 222.6) (c := 1e-13) (d3 := 0) (d2 := 0) (by norm_num) hx
    (by norm_num) (by norm_num) le_rfl le_rfl fun w h1 h2 => ER4 h1 (h2.trans hx1)
  rw [show ((1579983001 : ℕ) : ℝ) = ((39749 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat] at h
  rw [show ((1579983001 : ℕ) : ℝ) = ((39749 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl : 21.1805 ≤ Real.log ((39749 ^ 2 : ℕ) : ℝ) := by
    rw [show ((39749 ^ 2 : ℕ) : ℝ) = ((1579983001 : ℕ) : ℝ) by norm_num]; exact l_r3.1
  have hx0 : (0 : ℝ) < x := by norm_num at hx; linarith
  have e : Real.log (x / ((39749 ^ 2 : ℕ) : ℝ)) = Real.log x - Real.log ((39749 ^ 2 : ℕ) : ℝ) :=
    Real.log_div hx0.ne' (by positivity)
  rw [e]
  simp only [zero_div]
  push_cast at hl ⊢
  norm_num at hl ⊢
  nlinarith

omit [Fact TernaryGoldbach.PlattGRH] in
theorem log_half_r4 : 30.8295 ≤ Real.log ((49000000000000 : ℕ) / 2 : ℝ) := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  have := l_r4.1; have := Real.log_two_lt_d9; linarith

theorem top5 {x L1 : ℝ} (hx : ((49000000000000 : ℕ) : ℝ) ≤ x) (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((49000000000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      2 * 97 / 7000000 + 1.234001e-6 * (1 + L1 - 31.5227) + 2.51 / 30.8295 ^ 2 := by
  have h := top_le (x := x) (K := 97) (c := 1.234001e-6) (d3 := 2.51) (d2 := 0) (by norm_num) hx
    (by norm_num) (by norm_num) (by norm_num) le_rfl fun w h1 _ => ER5 h1
  rw [show ((49000000000000 : ℕ) : ℝ) = ((7000000 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat] at h
  rw [show ((49000000000000 : ℕ) : ℝ) = ((7000000 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hl : 31.5227 ≤ Real.log ((7000000 ^ 2 : ℕ) : ℝ) := by
    rw [show ((7000000 ^ 2 : ℕ) : ℝ) = ((49000000000000 : ℕ) : ℝ) by norm_num]; exact l_r4.1
  have hl2 : 30.8295 ≤ Real.log ((7000000 ^ 2 : ℕ) / 2 : ℝ) := by
    rw [show ((7000000 ^ 2 : ℕ) : ℝ) = ((49000000000000 : ℕ) : ℝ) by norm_num]; exact log_half_r4
  have hx0 : (0 : ℝ) < x := by norm_num at hx; linarith
  have e : Real.log (x / ((7000000 ^ 2 : ℕ) : ℝ)) = Real.log x - Real.log ((7000000 ^ 2 : ℕ) : ℝ) :=
    Real.log_div hx0.ne' (by positivity)
  rw [e]
  have k : 2.51 / Real.log ((7000000 ^ 2 : ℕ) / 2 : ℝ) ^ 2 ≤ 2.51 / 30.8295 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hl2 2)
  have k2 : 1.234001e-6 * (1 + (Real.log x - Real.log ((7000000 ^ 2 : ℕ) : ℝ))) ≤
      1.234001e-6 * (1 + L1 - 31.5227) := by nlinarith
  push_cast at k k2 ⊢
  norm_num at k k2 ⊢
  linarith

omit [Fact TernaryGoldbach.PlattGRH] in
theorem exp_20001_ge : (1e26 : ℝ) ≤ Real.exp 20001 := by
  have h1 := exp_nat_ge' 60
  push_cast at h1
  have h2 : Real.exp 60 ≤ Real.exp 20001 := Real.exp_le_exp.2 (by norm_num)
  have h3 : (1e26 : ℝ) ≤ 2.7182818283 ^ 60 := by norm_num
  linarith

omit [Fact TernaryGoldbach.PlattGRH] in
theorem sqrt_exp_20001_ge : (1e13 : ℝ) ≤ √(Real.exp 20001) := by
  rw [Real.le_sqrt (by norm_num) (Real.exp_pos _).le]; have := exp_20001_ge; norm_num at this ⊢; linarith

omit [Fact TernaryGoldbach.PlattGRH] in
theorem log_half_e : 20000 ≤ Real.log (Real.exp 20001 / 2) := by
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have := Real.log_two_lt_d9; linarith

theorem full5 {x : ℝ} (hx : Real.exp 20001 ≤ x) :
    ∑ n ∈ Ioc ⌊x / Real.exp 20001⌋₊ ⌊x / ((49000000000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      2 * 97 / 7000000 + 1.234001e-6 * (20001 - 31.5227 + 2) + 2.51 / 30.8295 ^ 2 := by
  have hv0 := Real.exp_pos 20001
  have hbig := exp_20001_ge
  have huv : ((49000000000000 : ℕ) : ℝ) ≤ Real.exp 20001 := by norm_num at hbig ⊢; linarith
  have h := piece_le (x := x) (K := 97) (c := 1.234001e-6) (d3 := 2.51) (d2 := 0) (by norm_num) huv
    (huv.trans hx) (by norm_num) (by norm_num) (by norm_num) le_rfl fun w h1 _ => ER5 h1
  rw [show ((49000000000000 : ℕ) : ℝ) = ((7000000 ^ 2 : ℕ) : ℝ) by norm_num, sqrt_sq_nat] at h
  rw [show ((49000000000000 : ℕ) : ℝ) = ((7000000 ^ 2 : ℕ) : ℝ) by norm_num]
  refine h.trans ?_
  have hx0 : 0 < x := lt_of_lt_of_le hv0 hx
  have hsv : 0 < √(Real.exp 20001) := Real.sqrt_pos.2 hv0
  have hsvv := Real.mul_self_sqrt hv0.le
  -- `√v/x ≤ 1/√v`
  have k1 : 2 * √(Real.exp 20001) / x ≤ 2 / √(Real.exp 20001) := by
    rw [div_le_div_iff₀ hx0 hsv]; nlinarith
  have hl : 31.5227 ≤ Real.log ((7000000 ^ 2 : ℕ) : ℝ) := by
    rw [show ((7000000 ^ 2 : ℕ) : ℝ) = ((49000000000000 : ℕ) : ℝ) by norm_num]; exact l_r4.1
  have hl2 : 30.8295 ≤ Real.log ((7000000 ^ 2 : ℕ) / 2 : ℝ) := by
    rw [show ((7000000 ^ 2 : ℕ) : ℝ) = ((49000000000000 : ℕ) : ℝ) by norm_num]; exact log_half_r4
  have k2 : Real.log (Real.exp 20001 / ((7000000 ^ 2 : ℕ) : ℝ)) ≤ 20001 - 31.5227 := by
    rw [Real.log_div hv0.ne' (by positivity), Real.log_exp]; linarith
  have k3 : 2 * Real.exp 20001 / x ≤ 2 := by rw [div_le_iff₀ hx0]; linarith
  have k4 : 2.51 / Real.log ((7000000 ^ 2 : ℕ) / 2 : ℝ) ^ 2 ≤ 2.51 / 30.8295 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hl2 2)
  have k5 : 1.234001e-6 * (Real.log (Real.exp 20001 / ((7000000 ^ 2 : ℕ) : ℝ)) + 2 * Real.exp 20001 / x) ≤
      1.234001e-6 * (20001 - 31.5227 + 2) := by nlinarith
  have k6 : (97 : ℝ) * (2 / ((7000000 : ℕ) : ℝ) - 2 / √(Real.exp 20001) + 2 * √(Real.exp 20001) / x) ≤
      2 * 97 / 7000000 := by
    have : 2 / ((7000000 : ℕ) : ℝ) - 2 / √(Real.exp 20001) + 2 * √(Real.exp 20001) / x ≤
        2 / 7000000 := by push_cast; linarith
    nlinarith
  simp only [mul_zero, zero_div, add_zero]
  linarith

theorem top6 {x : ℝ} (hx : Real.exp 20001 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x / Real.exp 20001⌋₊, |Eg (x / n)| / n ≤ 8200 / 1e13 + 33 / 20000 ^ 2 + 2 * 4.1 / 20000 := by
  have h := top_le (x := x) (K := 4100) (c := 0) (d3 := 33) (d2 := 4.1)
    (by have := exp_20001_ge; linarith) hx (by norm_num) le_rfl (by norm_num) (by norm_num)
    fun w h1 _ => ER6 h1
  refine h.trans ?_
  have hs := sqrt_exp_20001_ge
  have hl := log_half_e
  have k1 : 2 * 4100 / √(Real.exp 20001) ≤ 2 * 4100 / 1e13 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have k2 : 33 / Real.log (Real.exp 20001 / 2) ^ 2 ≤ 33 / 20000 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hl 2)
  have k3 : 2 * 4.1 / Real.log (Real.exp 20001 / 2) ≤ 2 * 4.1 / 20000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl
  simp only [zero_mul, add_zero]
  linarith

/-! ### The analytic part of the head, by the range containing `x` -/

omit [Fact TernaryGoldbach.PlattGRH] in
theorem split_at {x u v : ℝ} (hx : 0 < x) (hu : 0 < u) (huv : u ≤ v) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 0 ⌊x / u⌋₊, f n = ∑ n ∈ Ioc 0 ⌊x / v⌋₊, f n + ∑ n ∈ Ioc ⌊x / v⌋₊ ⌊x / u⌋₊, f n :=
  (sum_Ioc_consecutive f (Nat.zero_le _) (Nat.floor_mono (div_le_div_of_nonneg_left hx.le hu huv))).symm

theorem an1 {x : ℝ} (hx : ((1000000 : ℕ) : ℝ) ≤ x) (hx1 : x ≤ ((49603849 : ℕ) : ℝ)) {L1 : ℝ} (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      (2 * 11.82 / 1000 + 1e-13 * (1 + L1 - 13.8154)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have t := top1 hx hx1 hL1
  linarith

theorem an2 {x : ℝ} (hx : ((49603849 : ℕ) : ℝ) ≤ x) (hx1 : x < ((999950884 : ℕ) : ℝ)) {X0 : ℝ} (hX0 : 0 < X0) (hX0x : X0 ≤ x) {L1 : ℝ} (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      (11.82 * (2 / 1000 - 2 / 7043 + 2 * 7043 / X0) + 1e-13 * (3.9043 + 2 * 49603849 / X0)) +
      (2 * 13.6 / 7043 + 0.0022500000001 * (1 + L1 - 17.7194)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hm0 : ((1000000 : ℕ) : ℝ) ≤ ((49603849 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm0]
  have f0 := full1 (x := x) hX0 hx hX0x
  have t := top2 hx hx1 hL1
  linarith

theorem an3 {x : ℝ} (hx : ((999950884 : ℕ) : ℝ) ≤ x) (hx1 : x ≤ ((1579983001 : ℕ) : ℝ)) {X0 : ℝ} (hX0 : 0 < X0) (hX0x : X0 ≤ x) {L1 : ℝ} (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      (11.82 * (2 / 1000 - 2 / 7043 + 2 * 7043 / X0) + 1e-13 * (3.9043 + 2 * 49603849 / X0)) +
      (13.6 * (2 / 7043 - 2 / 31622 + 2 * 31622 / X0) + 0.0022500000001 * (3.004 + 2 * 999950884 / X0)) +
      (2 * 112.7 / 31622 + 1e-13 * (1 + L1 - 20.7231)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hm0 : ((1000000 : ℕ) : ℝ) ≤ ((49603849 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm0]
  have hm1 : ((49603849 : ℕ) : ℝ) ≤ ((999950884 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm1]
  have f0 := full1 (x := x) hX0 (by norm_num at hx ⊢; linarith) hX0x
  have f1 := full2 (x := x) hX0 hx hX0x
  have t := top3 hx hx1 hL1
  linarith

theorem an4 {x : ℝ} (hx : ((1579983001 : ℕ) : ℝ) ≤ x) (hx1 : x ≤ ((49000000000000 : ℕ) : ℝ)) {X0 : ℝ} (hX0 : 0 < X0) (hX0x : X0 ≤ x) {L1 : ℝ} (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      (11.82 * (2 / 1000 - 2 / 7043 + 2 * 7043 / X0) + 1e-13 * (3.9043 + 2 * 49603849 / X0)) +
      (13.6 * (2 / 7043 - 2 / 31622 + 2 * 31622 / X0) + 0.0022500000001 * (3.004 + 2 * 999950884 / X0)) +
      (112.7 * (2 / 31622 - 2 / 39749 + 2 * 39749 / X0) + 1e-13 * (0.4577 + 2 * 1579983001 / X0)) +
      (2 * 222.6 / 39749 + 1e-13 * (1 + L1 - 21.1805)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hm0 : ((1000000 : ℕ) : ℝ) ≤ ((49603849 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm0]
  have hm1 : ((49603849 : ℕ) : ℝ) ≤ ((999950884 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm1]
  have hm2 : ((999950884 : ℕ) : ℝ) ≤ ((1579983001 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm2]
  have f0 := full1 (x := x) hX0 (by norm_num at hx ⊢; linarith) hX0x
  have f1 := full2 (x := x) hX0 (by norm_num at hx ⊢; linarith) hX0x
  have f2 := full3 (x := x) hX0 hx hX0x
  have t := top4 hx hx1 hL1
  linarith

theorem an5 {x : ℝ} (hx : ((49000000000000 : ℕ) : ℝ) ≤ x) {X0 : ℝ} (hX0 : 0 < X0) (hX0x : X0 ≤ x) {L1 : ℝ} (hL1 : Real.log x ≤ L1) :
    ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      (11.82 * (2 / 1000 - 2 / 7043 + 2 * 7043 / X0) + 1e-13 * (3.9043 + 2 * 49603849 / X0)) +
      (13.6 * (2 / 7043 - 2 / 31622 + 2 * 31622 / X0) + 0.0022500000001 * (3.004 + 2 * 999950884 / X0)) +
      (112.7 * (2 / 31622 - 2 / 39749 + 2 * 39749 / X0) + 1e-13 * (0.4577 + 2 * 1579983001 / X0)) +
      (222.6 * (2 / 39749 - 2 / 7000000 + 2 * 7000000 / X0) + 1e-13 * (10.3425 + 2 * 49000000000000 / X0)) +
      (2 * 97 / 7000000 + 1.234001e-6 * (1 + L1 - 31.5227) + 2.51 / 30.8295 ^ 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hm0 : ((1000000 : ℕ) : ℝ) ≤ ((49603849 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm0]
  have hm1 : ((49603849 : ℕ) : ℝ) ≤ ((999950884 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm1]
  have hm2 : ((999950884 : ℕ) : ℝ) ≤ ((1579983001 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm2]
  have hm3 : ((1579983001 : ℕ) : ℝ) ≤ ((49000000000000 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm3]
  have f0 := full1 (x := x) hX0 (by norm_num at hx ⊢; linarith) hX0x
  have f1 := full2 (x := x) hX0 (by norm_num at hx ⊢; linarith) hX0x
  have f2 := full3 (x := x) hX0 (by norm_num at hx ⊢; linarith) hX0x
  have f3 := full4 (x := x) hX0 hx hX0x
  have t := top5 hx hL1
  linarith

theorem an6 {x : ℝ} (hx : Real.exp 20001 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤
      (11.82 * (2 / 1000 - 2 / 7043 + 2 * 7043 / 1e26) + 1e-13 * (3.9043 + 2 * 49603849 / 1e26)) +
      (13.6 * (2 / 7043 - 2 / 31622 + 2 * 31622 / 1e26) + 0.0022500000001 * (3.004 + 2 * 999950884 / 1e26)) +
      (112.7 * (2 / 31622 - 2 / 39749 + 2 * 39749 / 1e26) + 1e-13 * (0.4577 + 2 * 1579983001 / 1e26)) +
      (222.6 * (2 / 39749 - 2 / 7000000 + 2 * 7000000 / 1e26) + 1e-13 * (10.3425 + 2 * 49000000000000 / 1e26)) +
      (2 * 97 / 7000000 + 1.234001e-6 * (20001 - 31.5227 + 2) + 2.51 / 30.8295 ^ 2) +
      (8200 / 1e13 + 33 / 20000 ^ 2 + 2 * 4.1 / 20000) := by
  have hX0 : (0 : ℝ) < 1e26 := by norm_num
  have hX0x : (1e26 : ℝ) ≤ x := exp_20001_ge.trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hm0 : ((1000000 : ℕ) : ℝ) ≤ ((49603849 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm0]
  have hm1 : ((49603849 : ℕ) : ℝ) ≤ ((999950884 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm1]
  have hm2 : ((999950884 : ℕ) : ℝ) ≤ ((1579983001 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm2]
  have hm3 : ((1579983001 : ℕ) : ℝ) ≤ ((49000000000000 : ℕ) : ℝ) := by norm_num
  rw [split_at hx0 (by norm_num) hm3]
  have hm4 : ((49000000000000 : ℕ) : ℝ) ≤ Real.exp 20001 := by have := exp_20001_ge; norm_num at this ⊢; linarith
  rw [split_at hx0 (by norm_num) hm4]
  have f0 := full1 (x := x) hX0 (le_trans (by have := exp_20001_ge; norm_num at this ⊢; linarith) hx) hX0x
  have f1 := full2 (x := x) hX0 (le_trans (by have := exp_20001_ge; norm_num at this ⊢; linarith) hx) hX0x
  have f2 := full3 (x := x) hX0 (le_trans (by have := exp_20001_ge; norm_num at this ⊢; linarith) hx) hX0x
  have f3 := full4 (x := x) hX0 (le_trans (by have := exp_20001_ge; norm_num at this ⊢; linarith) hx) hX0x
  have f4 := full5 hx
  have t := top6 hx
  linarith

end TernaryGoldbach.Prelim
