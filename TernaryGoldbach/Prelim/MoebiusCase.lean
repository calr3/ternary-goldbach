import TernaryGoldbach.Prelim.MoebiusAnalytic
import TernaryGoldbach.Prelim.SmallMuMain

/-!
# `|m(x)| log x` on a range of `x`, from the identity

`case_gen`: for `x ≥ X0 ≥ 2 160 535` and `D = ⌊x/Y⌋`, the identity
`|m(x)| (log x − γ) ≤ ∑_{n ≤ D} |E(x/n)|/n + |∑_{D < n ≤ x} μ(n) E(x/n)/n|` with
* the table ranges `Y ≤ x/n < 10⁶` (groups `gs`, `tab_head`),
* the ranges `x/n ≥ 10⁶` (a bound `A`, from `an_k`),
* the tail by summation by parts against `M(n)` (`tail_concrete`: `|M(n)| ≤ n/4345` from
  `2 160 535` (`CDEMertens`), `|M(n)| ≤ 0.5672√n` below (`M_small`)).
`final_step` turns `|m(x)| (log x − γ) ≤ H` into `|m(x)| log x ≤ K`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens

theorem gT2_nonneg : ∀ gs : List (ℕ × ℕ), 0 ≤ gT2 gs
  | [] => by simp [gT2]
  | (V, en) :: gs => by
    simp only [gT2]
    have := gT2_nonneg gs
    positivity

theorem hsmallM : ∀ n : ℕ, 100 ≤ n → n < 2160535 → |Mt n| ≤ 0.5672 * √(n : ℝ) :=
  fun _ h1 h2 => SmallMu.M_small h1 (by omega)

theorem final_step {x H K L0 : ℝ} (h : |mx x| * (Real.log x - Real.eulerMascheroniConstant) ≤ H)
    (hL : L0 ≤ Real.log x) (hK : 0 ≤ K) (hcond : K * 0.5773 ≤ (K - H) * L0) (hHK : H ≤ K)
    (hL0 : 1 ≤ L0) : |mx x| * Real.log x ≤ K := by
  have hg := Real.eulerMascheroniConstant_lt_two_thirds
  have hg' : Real.eulerMascheroniConstant < 0.5773 := by
    have := gamma_lo_hi.2; norm_num [SmallE.S] at this ⊢; linarith
  have hg0 : 0 < Real.eulerMascheroniConstant := by
    have := gamma_lo_hi.1; norm_num [SmallE.S] at this ⊢; linarith
  have hm := abs_nonneg (mx x)
  -- `H log x ≤ K (log x − γ)`
  have hk : H * Real.log x ≤ K * (Real.log x - Real.eulerMascheroniConstant) := by
    have : (K - H) * L0 ≤ (K - H) * Real.log x := mul_le_mul_of_nonneg_left hL (by linarith)
    nlinarith
  have hpos : 0 < Real.log x - Real.eulerMascheroniConstant := by linarith
  -- `|m| (log x − γ) log x ≤ H log x ≤ K (log x − γ)`
  have h2 : |mx x| * Real.log x * (Real.log x - Real.eulerMascheroniConstant) ≤
      K * (Real.log x - Real.eulerMascheroniConstant) := by
    have := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ Real.log x)
    nlinarith
  exact le_of_mul_le_mul_right h2 hpos

variable [Fact TernaryGoldbach.PlattGRH]

/-- **The identity on a range of `x`.** -/
theorem case_gen (hCDE : CDEMertens) {x : ℝ} {X0 Y D0 s s1 : ℕ} {gs : List (ℕ × ℕ)}
    (hX0 : (X0 : ℝ) ≤ x) (hX0b : 2160535 ≤ X0) (hY2 : 2 ≤ Y) (hgs : GOK Y gs = true)
    (hD0 : D0 * Y ≤ X0) (hD0' : 101 ≤ D0) (hs : s * s ≤ D0) (hs0 : 0 < s) (hs1 : s1 * s1 ≤ D0 + 1)
    (hs10 : 0 < s1) (hYD : Y * (D0 + 1) ≤ 1000000 * D0) {lY T A : ℝ} (hlY : Real.log Y ≤ lY)
    (hT : (gT1 Y gs : ℝ) + (gT2 gs : ℝ) / X0 ≤ T)
    (hA : ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n ≤ A) :
    |mx x| * (Real.log x - Real.eulerMascheroniConstant) ≤ T + A +
      ((1 / 4345 + (1 / 4345 + 0.5672 / s)) * 0.5773 +
        (lY - 0.5772 + 0.5773 + (1 + 0.5773) * (lY + 1 / D0)) / 4345 +
        0.5672 * (2.0884 / s1 + 2 * (1 + 0.5773) / s)) := by
  have hX0r : (2160535 : ℝ) ≤ X0 := by exact_mod_cast hX0b
  have hx : (2160535 : ℝ) ≤ x := le_trans hX0r hX0
  have hx0 : 0 < x := by linarith
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hY2r : (2 : ℝ) ≤ Y := by exact_mod_cast hY2
  have hY1e6 : Y ≤ 1000000 := GOK_le gs Y hgs
  set D := ⌊x / Y⌋₊ with hDdef
  have hDD0 : D0 ≤ D := Nat.le_floor (by
    rw [le_div_iff₀ hY0]
    have : ((D0 * Y : ℕ) : ℝ) ≤ X0 := by exact_mod_cast hD0
    push_cast at this; linarith)
  have hD101 : 101 ≤ D := le_trans hD0' hDD0
  have hDr : (D : ℝ) ≤ x / Y := Nat.floor_le (by positivity)
  have hDlt : x / Y < (D : ℝ) + 1 := Nat.lt_floor_add_one _
  have hxY2 : x / Y ≤ x / 2 := div_le_div_of_nonneg_left hx0.le (by norm_num) hY2r
  have hDN : D < ⌊x⌋₊ := by
    have : D + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  have hD0r : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  -- the identity
  have hid := identity_split (x := x) (by linarith) hDN.le
  have hIcc : Icc 1 D = Ioc 0 D := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  rw [hIcc] at hid
  -- the head
  have hsplit : ∑ n ∈ Ioc 0 D, |Eg (x / n)| / n =
      ∑ n ∈ Ioc 0 ⌊x / ((1000000 : ℕ) : ℝ)⌋₊, |Eg (x / n)| / n +
        ∑ n ∈ Ioc ⌊x / ((1000000 : ℕ) : ℝ)⌋₊ D, |Eg (x / n)| / n :=
    (sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_mono (div_le_div_of_nonneg_left hx0.le hY0
      (by exact_mod_cast hY1e6)))).symm
  have htab := tab_head hx0 gs Y hgs
  have hT2 : (gT2 gs : ℝ) / x ≤ (gT2 gs : ℝ) / X0 :=
    div_le_div_of_nonneg_left (by exact_mod_cast gT2_nonneg gs) (by linarith) hX0
  have htab' : ∑ n ∈ Ioc ⌊x / ((1000000 : ℕ) : ℝ)⌋₊ D, |Eg (x / n)| / n ≤ T := by
    have e : ((1000000 : ℕ) : ℝ) = 1000000 := by norm_num
    rw [e]; linarith
  -- the tail
  have hxD : x / D < Y * (D0 + 1) / D0 := by
    have hD0p : (0 : ℝ) < D0 := by exact_mod_cast (by omega : 0 < D0)
    have hDD0r : (D0 : ℝ) ≤ D := by exact_mod_cast hDD0
    rw [div_lt_div_iff₀ hD0r hD0p]
    have h1 : x < Y * ((D : ℝ) + 1) := by rw [div_lt_iff₀ hY0] at hDlt; linarith
    nlinarith
  have hYD' : (Y : ℝ) * (D0 + 1) / D0 ≤ 1000000 := by
    have hD0p : (0 : ℝ) < D0 := by exact_mod_cast (by omega : 0 < D0)
    rw [div_le_iff₀ hD0p]
    have : ((Y * (D0 + 1) : ℕ) : ℝ) ≤ ((1000000 * D0 : ℕ) : ℝ) := by exact_mod_cast hYD
    push_cast at this; linarith
  have hF : ∀ u : ℝ, 1 ≤ u → u ≤ x / D → |Eg u| ≤ 0.5773 :=
    fun u h1 h2 => Eg_le_F h1 (by linarith)
  have htail := tail_concrete hCDE hsmallM (by linarith) hD101 hDN hF
  -- the terms of the tail
  have hbN : betaM ⌊x⌋₊ = 1 / 4345 := by
    unfold betaM; rw [if_pos (Nat.le_floor (by exact_mod_cast hx))]
  have hsD : (s : ℝ) ≤ √(D : ℝ) := by
    rw [Real.le_sqrt (by positivity) hD0r.le]
    have : ((s * s : ℕ) : ℝ) ≤ D := by exact_mod_cast le_trans hs hDD0
    push_cast at this; nlinarith
  have hs1D : (s1 : ℝ) ≤ √((D : ℝ) + 1) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : ((s1 * s1 : ℕ) : ℝ) ≤ D0 + 1 := by exact_mod_cast hs1
    have hDD0r : (D0 : ℝ) ≤ D := by exact_mod_cast hDD0
    push_cast at this; nlinarith
  have hs0r : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs10r : (0 : ℝ) < s1 := by exact_mod_cast hs10
  have hbD : betaM D ≤ 1 / 4345 + 0.5672 / s := by
    refine (betaM_le D).trans ?_
    have : 0.5672 / √(D : ℝ) ≤ 0.5672 / s := div_le_div_of_nonneg_left (by norm_num) hs0r hsD
    linarith
  have hl1 : Real.log (x / (D + 1)) ≤ lY := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hlY
    rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ hY0] at hDlt; linarith
  have hl2 : Real.log x - Real.log D ≤ lY + 1 / D0 := by
    have hD0p : (0 : ℝ) < D0 := by exact_mod_cast (by omega : 0 < D0)
    rw [← Real.log_div hx0.ne' hD0r.ne']
    have h1 : Real.log (x / D) ≤ Real.log (Y * (D0 + 1) / D0) := Real.log_le_log (by positivity) hxD.le
    have e : Real.log ((Y : ℝ) * (D0 + 1) / D0) = Real.log Y + Real.log (1 + 1 / D0) := by
      rw [← Real.log_mul hY0.ne' (by positivity)]; congr 1; field_simp
    have h2 : Real.log (1 + 1 / (D0 : ℝ)) ≤ 1 / D0 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / D0 by positivity); linarith
    linarith
  have hg : 0.5772 < Real.eulerMascheroniConstant := by
    have := gamma_lo_hi.1; norm_num [SmallE.S] at this ⊢; linarith
  have k3 : 2.0884 / √((D : ℝ) + 1) ≤ 2.0884 / s1 := div_le_div_of_nonneg_left (by norm_num) hs10r hs1D
  have k4 : 2 * (1 + 0.5773) / √(D : ℝ) ≤ 2 * (1 + 0.5773) / s :=
    div_le_div_of_nonneg_left (by norm_num) hs0r hsD
  rw [hbN] at htail
  have hbD' := mul_le_mul_of_nonneg_right hbD (by norm_num : (0 : ℝ) ≤ 0.5773)
  have hlY0 : 0 ≤ lY := le_trans (Real.log_nonneg (by linarith)) hlY
  have k5 : (1 + 0.5773) * (Real.log x - Real.log D) ≤ (1 + 0.5773) * (lY + 1 / D0) :=
    mul_le_mul_of_nonneg_left hl2 (by norm_num)
  linarith

end TernaryGoldbach.Prelim
