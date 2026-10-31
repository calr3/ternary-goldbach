import TernaryGoldbach.Prelim.MertensProduct
import TernaryGoldbach.MinorArcs.EtaStarBound

/-!
# Theorem 3.1.1 as a function of `r = max(1, |δ|/8) q` [B, (11.11)–(11.13)]

[B, §11.2] restates the first case of Theorem 3.1.1 as `|S_{η₂}(α, x)| ≤ g_x(r) x` with
`r = max(1, |δ|/8) q` (so `δ₀q = 2r`), bounding `q/φ(q)` by `Ϝ(r)` (Lemma C.2.2, trusted):

`g_x(r) = ((R_{x,2r} log 2r + 0.8103) √Ϝ(r) + 2.5)/√(2r) + L_{2r}/r + 3.8 x^{-1/6}`,
`L_t = Ϝ(t/2)(13/4 log t + 7.82) + 13.66 log t + 37.55`.

The constants `0.8103`, `3.8` are those of our corrected Theorem 3.1.1 ([B]: `0.5`, `3.36`).

Proved, modulo the trusted inputs of `theorem_3_1_1` and Lemma C.2.2.
-/

open Real

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 S)

/-- `Ϝ(r) = e^γ log log r + 2.50637 / log log r` [B, Lemma C.2.2]. -/
noncomputable def Fr (r : ℝ) : ℝ :=
  rexp eulerMascheroniConstant * Real.log (Real.log r) + 2.50637 / Real.log (Real.log r)

/-- `L_t = Ϝ(t/2)(13/4 log t + 7.82) + 13.66 log t + 37.55` [B, (11.13)]. -/
noncomputable def Lg (t : ℝ) : ℝ :=
  Fr (t / 2) * (13 / 4 * Real.log t + 7.82) + 13.66 * Real.log t + 37.55

/-- `g_x(r)` [B, (11.12)], with our constants `0.8103` and `3.8`. -/
noncomputable def gx (x r : ℝ) : ℝ :=
  ((R x (2 * r) * Real.log (2 * r) + 0.8103) * √(Fr r) + 2.5) / √(2 * r) + Lg (2 * r) / r +
    3.8 * x ^ (-1 / 6 : ℝ)

/-- `R_{x,t} ≥ 0` for `1 ≤ t ≤ x^{1/3}/3` (both logarithms in (11.13) are positive). -/
theorem R_nonneg {x t : ℝ} (ht1 : 1 ≤ t) (ht : t ≤ x ^ (1 / 3 : ℝ) / 3) : 0 ≤ R x t := by
  unfold R
  have h4 : 0 < Real.log (4 * t) := Real.log_pos (by linarith)
  have hb : 1 < 9 * x ^ (1 / 3 : ℝ) / (2.004 * t) := by
    rw [one_lt_div (by positivity)]; linarith
  have hl : 0 < Real.log (9 * x ^ (1 / 3 : ℝ) / (2.004 * t)) := Real.log_pos hb
  have : 0 ≤ Real.log (1 + Real.log (4 * t) / (2 * Real.log (9 * x ^ (1 / 3 : ℝ) / (2.004 * t)))) :=
    Real.log_nonneg (by
      have := div_pos h4 (by positivity : (0:ℝ) < 2 * Real.log (9 * x ^ (1 / 3 : ℝ) / (2.004 * t)))
      linarith)
  linarith

/-- **[B, (11.11)]** (first case of Theorem 3.1.1, in terms of `r = max(1, |δ|/8) q`). -/
theorem norm_S_eta2_le_gx {α x δ : ℝ} {a : ℤ} {q : ℕ} (hx : 2.16e20 ≤ x)
    (h : Approx2 α x δ a q (3 / 4 * x ^ (2 / 3 : ℝ))) (hq : (q : ℝ) ≤ x ^ (1 / 3 : ℝ) / 6)
    (hr3 : 3 ≤ max 1 (|δ| / 8) * q) :
    ‖S eta2 x α‖ ≤ gx x (max 1 (|δ| / 8) * q) * x := by
  have key := (theorem_3_1_1 hx h).1 hq
  set r := max 1 (|δ| / 8) * q with hr
  obtain ⟨hT, hT3, hT23, hT56⟩ := cube_root_facts hx
  set T := x ^ (1 / 3 : ℝ) with hTdef
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h.1
  have hq0 : (0 : ℝ) < q := by linarith
  have hδ₀ : max 2 (|δ| / 4) * q = 2 * r := by
    rw [hr, ← mul_assoc, mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]; ring_nf
  rw [hδ₀] at key
  have hr0 : 0 < r := by linarith
  have hqr : (q : ℝ) ≤ r := by
    rw [hr]; exact le_mul_of_one_le_left hq0.le (le_max_left _ _)
  -- `2r = δ₀q ≤ T/3`
  have h2r : 2 * r ≤ T / 3 := by
    rw [← hδ₀]
    have hd := h.2.2.2.1
    rw [abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 (by rw [hT23]; positivity), one_mul] at hd
    rcases le_total 2 (|δ| / 4) with hm | hm
    · rw [max_eq_right hm]
      have : |δ| * q * (3 / 4 * T ^ 2) ≤ x := by
        calc |δ| * q * (3 / 4 * T ^ 2) = |δ| * (q * (3 / 4 * x ^ (2 / 3 : ℝ))) := by rw [hT23]; ring
          _ ≤ x := hd
      rw [← hT3] at this
      have : |δ| * q ≤ 4 / 3 * T := by nlinarith
      linarith
    · rw [max_eq_left hm]; linarith
  have hR := R_nonneg (x := x) (t := 2 * r) (by linarith) h2r
  have hlog : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hA : 0 ≤ R x (2 * r) * Real.log (2 * r) + 0.8103 := by positivity
  -- `q/φ(q) < Ϝ(r)`
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by exact_mod_cast hq0)
  have hF := TernaryGoldbach.Prelim.div_totient_lt h.1 hr3 hqr
  rw [div_lt_iff₀ hφ0] at hF
  set F := Fr r with hFdef
  have hF' : (q : ℝ) < F * Nat.totient q := by simpa only [hFdef, Fr] using hF
  have hF0 : 0 < F := by
    by_contra hc; push Not at hc; nlinarith
  -- term 1
  have hδ₀' : max 2 (|δ| / 4) = 2 * r / q := by rw [← hδ₀]; field_simp
  have t1 : (R x (2 * r) * Real.log (2 * r) + 0.8103) / √(max 2 (|δ| / 4) * Nat.totient q) * x ≤
      (R x (2 * r) * Real.log (2 * r) + 0.8103) * √F / √(2 * r) * x := by
    gcongr ?_ * x
    rw [div_le_div_iff₀ (by rw [hδ₀']; positivity) (by positivity), mul_assoc, ← Real.sqrt_mul hF0.le]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hA
    rw [hδ₀', div_mul_eq_mul_div, mul_div_assoc', le_div_iff₀ hq0]
    have := mul_lt_mul_of_pos_left hF' (by linarith : (0:ℝ) < 2 * r)
    nlinarith
  -- term 3
  have t3 : 2 * x / (2 * r) * L (2 * r) q ≤ Lg (2 * r) / r * x := by
    have hL : L (2 * r) q ≤ Lg (2 * r) := by
      unfold L Lg
      rw [show 2 * r / 2 = r by ring]
      have : (q : ℝ) / Nat.totient q ≤ F := by rw [div_le_iff₀ hφ0]; linarith
      have : 0 ≤ 13 / 4 * Real.log (2 * r) + 7.82 := by positivity
      nlinarith
    rw [show 2 * x / (2 * r) = x / r by field_simp, div_mul_eq_mul_div, div_mul_eq_mul_div,
      mul_comm (Lg _) x]
    gcongr
  -- term 4
  have t4 : x ^ (5 / 6 : ℝ) = x ^ (-1 / 6 : ℝ) * x := by
    conv_lhs => rw [show (5 / 6 : ℝ) = -1 / 6 + 1 by norm_num]
    rw [Real.rpow_add hx0, Real.rpow_one]
  refine key.trans ?_
  unfold gx
  rw [t4, ← hFdef]
  have e2 : 2.5 * x / √(2 * r) = 2.5 / √(2 * r) * x := by ring
  rw [e2]
  have : (R x (2 * r) * Real.log (2 * r) + 0.8103) * √F / √(2 * r) * x + 2.5 / √(2 * r) * x =
      ((R x (2 * r) * Real.log (2 * r) + 0.8103) * √F + 2.5) / √(2 * r) * x := by ring
  nlinarith [t1, t3]

end TernaryGoldbach.MinorArcs
