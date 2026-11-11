/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import RSBounds.LambdaCert.Defs

/-!
# Soundness of the logarithm bounds `logRatio`

For `0 < q < k` with `3 (k - q) ≤ k + q`, `logRatio (k - q) (k + q)` encloses
`S (log k - log q)`, by the series `log (1 + x) - log (1 - x) = 2 ∑ x^(2i+1)/(2i+1)` with
`x = (k - q)/(k + q) ≤ 1/3`, whose tail from `i ≥ 1` is at most `x^(2i+1)`.
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

open Real

/-- The `i`-th term of the series for `log (1 + x) - log (1 - x)`. -/
noncomputable def lterm (x : ℝ) (i : ℕ) : ℝ := 2 * (1 / (2 * i + 1)) * x ^ (2 * i + 1)

/-- The tail of that series from `i` on. -/
noncomputable def ltail (x : ℝ) (i : ℕ) : ℝ := ∑' t, lterm x (t + i)

theorem lterm_nonneg {x : ℝ} (hx : 0 ≤ x) (i : ℕ) : 0 ≤ lterm x i := by
  unfold lterm; positivity

theorem lterm_hasSum {x : ℝ} (hx : |x| < 1) : HasSum (lterm x) (log (1 + x) - log (1 - x)) :=
  hasSum_log_sub_log_of_abs_lt_one hx

theorem lterm_summable_shift {x : ℝ} (hx : |x| < 1) (i : ℕ) :
    Summable (fun t => lterm x (t + i)) :=
  (summable_nat_add_iff i).2 (lterm_hasSum hx).summable

theorem ltail_zero {x : ℝ} (hx : |x| < 1) : ltail x 0 = log (1 + x) - log (1 - x) := by
  simp only [ltail, add_zero]
  exact (lterm_hasSum hx).tsum_eq

theorem ltail_succ {x : ℝ} (hx : |x| < 1) (i : ℕ) : ltail x i = lterm x i + ltail x (i + 1) := by
  unfold ltail
  rw [(lterm_summable_shift hx i).tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  apply tsum_congr
  intro t
  congr 1
  ring

theorem ltail_nonneg {x : ℝ} (hx0 : 0 ≤ x) (i : ℕ) : 0 ≤ ltail x i :=
  tsum_nonneg (fun _ => lterm_nonneg hx0 _)

theorem ltail_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 3) {i : ℕ} (hi : 1 ≤ i) :
    ltail x i ≤ x ^ (2 * i + 1) := by
  have hxabs : |x| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hx2' : 0 ≤ x ^ 2 := by positivity
  set c : ℝ := 2 * (1 / (2 * (i : ℝ) + 1)) * x ^ (2 * i + 1) with hc
  have hterm : ∀ t : ℕ, lterm x (t + i) ≤ c * (x ^ 2) ^ t := by
    intro t
    unfold lterm
    have h1 : 1 / (2 * ((t + i : ℕ) : ℝ) + 1) ≤ 1 / (2 * (i : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have h2 : x ^ (2 * (t + i) + 1) = x ^ (2 * i + 1) * (x ^ 2) ^ t := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [h2, hc]
    have : 0 ≤ x ^ (2 * i + 1) * (x ^ 2) ^ t := by positivity
    calc 2 * (1 / (2 * ((t + i : ℕ) : ℝ) + 1)) * (x ^ (2 * i + 1) * (x ^ 2) ^ t)
        ≤ 2 * (1 / (2 * (i : ℝ) + 1)) * (x ^ (2 * i + 1) * (x ^ 2) ^ t) := by gcongr
      _ = 2 * (1 / (2 * (i : ℝ) + 1)) * x ^ (2 * i + 1) * (x ^ 2) ^ t := by ring
  have hsum : Summable (fun t : ℕ => c * (x ^ 2) ^ t) :=
    (summable_geometric_of_lt_one hx2' hx2).mul_left c
  calc ltail x i ≤ ∑' t : ℕ, c * (x ^ 2) ^ t :=
        Summable.tsum_le_tsum hterm (lterm_summable_shift hxabs i) hsum
    _ = c * (1 - x ^ 2)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hx2' hx2]
    _ ≤ x ^ (2 * i + 1) := by
        have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
        have hxp : 0 ≤ x ^ (2 * i + 1) := by positivity
        have h1x : 8 / 9 ≤ 1 - x ^ 2 := by nlinarith
        have hinv : (1 - x ^ 2)⁻¹ ≤ 9 / 8 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        have hfrac : 2 * (1 / (2 * (i : ℝ) + 1)) ≤ 2 / 3 := by
          rw [mul_one_div]
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        rw [hc]
        calc 2 * (1 / (2 * (i : ℝ) + 1)) * x ^ (2 * i + 1) * (1 - x ^ 2)⁻¹
            ≤ 2 / 3 * x ^ (2 * i + 1) * (9 / 8) := by
              gcongr
          _ ≤ x ^ (2 * i + 1) := by nlinarith

/-! ## Fixed-point bounds -/

theorem cast_div_le' (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

theorem le_cast_div_add_one (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((a / b + 1 : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := a) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have : (a : ℝ) < ((a / b) * b + b : ℕ) := by exact_mod_cast h
  push_cast at this ⊢
  nlinarith

theorem le_cast_ceil_div (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (((a + b - 1) / b : ℕ) : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ b * ((a + b - 1) / b) := by
    generalize (a + b - 1) / b = Q at h1 h2 ⊢
    generalize b * Q = M at h1 h2 ⊢
    omega
  have : (a : ℝ) ≤ (b * ((a + b - 1) / b) : ℕ) := by exact_mod_cast h3
  push_cast at this
  linarith

theorem serTail_zero (g2 D2 i pn pd : ℕ) :
    serTail g2 D2 0 i pn pd = (0, (S * pn + pd - 1) / pd) := rfl

theorem serTail_succ (g2 D2 f i pn pd : ℕ) :
    serTail g2 D2 (f + 1) i pn pd =
      cond (Nat.blt (S * pn) pd) (0, 1)
        (S2 * pn / ((2 * i + 1) * pd) + (serTail g2 D2 f (i + 1) (pn * g2) (pd * D2)).1,
          S2 * pn / ((2 * i + 1) * pd) + 1 + (serTail g2 D2 f (i + 1) (pn * g2) (pd * D2)).2) :=
  rfl

theorem S_pos : (0 : ℝ) < (S : ℕ) := by norm_num [S]

theorem S2_eq : (S2 : ℕ) = 2 * S := by norm_num [S, S2]

/-- The real value of the `i`-th term, scaled by `S`. -/
theorem S_mul_lterm (g D : ℕ) (hD : 0 < D) (i : ℕ) :
    (S : ℝ) * lterm ((g : ℝ) / D) i = ((S2 * g ^ (2 * i + 1) : ℕ) : ℝ) / (((2 * i + 1) * D ^ (2 * i + 1) : ℕ) : ℝ) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold lterm
  rw [S2_eq]
  push_cast
  rw [div_pow]
  field_simp

theorem serTail_sound (g D : ℕ) (hD : 0 < D) (hg3 : 3 * g ≤ D) :
    ∀ fuel i, 1 ≤ i →
      ((serTail (g * g) (D * D) fuel i (g ^ (2 * i + 1)) (D ^ (2 * i + 1))).1 : ℝ) ≤
          (S : ℝ) * ltail ((g : ℝ) / D) i ∧
        (S : ℝ) * ltail ((g : ℝ) / D) i ≤
          (serTail (g * g) (D * D) fuel i (g ^ (2 * i + 1)) (D ^ (2 * i + 1))).2 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hx0 : (0 : ℝ) ≤ (g : ℝ) / D := by positivity
  have hx3 : (g : ℝ) / D ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hD' (by norm_num)]
    have : ((3 * g : ℕ) : ℝ) ≤ D := by exact_mod_cast hg3
    push_cast at this; linarith
  have hxabs : |(g : ℝ) / D| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have hpow : ∀ i : ℕ, ((g : ℝ) / D) ^ (2 * i + 1) =
      ((g ^ (2 * i + 1) : ℕ) : ℝ) / ((D ^ (2 * i + 1) : ℕ) : ℝ) := by
    intro i; push_cast; rw [div_pow]
  have htail_le : ∀ i, 1 ≤ i → (S : ℝ) * ltail ((g : ℝ) / D) i ≤
      ((S * g ^ (2 * i + 1) : ℕ) : ℝ) / ((D ^ (2 * i + 1) : ℕ) : ℝ) := by
    intro i hi
    have h := ltail_le hx0 hx3 hi
    rw [hpow] at h
    have hS := S_pos
    calc (S : ℝ) * ltail ((g : ℝ) / D) i ≤ (S : ℝ) * (((g ^ (2 * i + 1) : ℕ) : ℝ) /
          ((D ^ (2 * i + 1) : ℕ) : ℝ)) := by gcongr
      _ = ((S * g ^ (2 * i + 1) : ℕ) : ℝ) / ((D ^ (2 * i + 1) : ℕ) : ℝ) := by
          push_cast; ring
  intro fuel
  induction fuel with
  | zero =>
    intro i hi
    rw [serTail_zero]
    refine ⟨?_, ?_⟩
    · simp only [Nat.cast_zero]
      exact mul_nonneg S_pos.le (ltail_nonneg hx0 i)
    · refine (htail_le i hi).trans ?_
      exact le_cast_ceil_div _ _ (by positivity)
  | succ f ih =>
    intro i hi
    rw [serTail_succ]
    have hpd : 0 < D ^ (2 * i + 1) := by positivity
    cases hb : Nat.blt (S * g ^ (2 * i + 1)) (D ^ (2 * i + 1)) with
    | true =>
      simp only [Bool.cond_true, Nat.cast_zero, Nat.cast_one]
      refine ⟨mul_nonneg S_pos.le (ltail_nonneg hx0 i), ?_⟩
      have hlt : S * g ^ (2 * i + 1) < D ^ (2 * i + 1) := by simpa [Nat.blt_eq] using hb
      refine (htail_le i hi).trans ?_
      rw [div_le_one (by exact_mod_cast hpd)]
      exact_mod_cast hlt.le
    | false =>
      simp only [Bool.cond_false]
      have hrec := ih (i + 1) (by omega)
      have e1 : g ^ (2 * i + 1) * (g * g) = g ^ (2 * (i + 1) + 1) := by ring
      have e2 : D ^ (2 * i + 1) * (D * D) = D ^ (2 * (i + 1) + 1) := by ring
      rw [e1, e2]
      have hsplit : (S : ℝ) * ltail ((g : ℝ) / D) i =
          (S : ℝ) * lterm ((g : ℝ) / D) i + (S : ℝ) * ltail ((g : ℝ) / D) (i + 1) := by
        rw [ltail_succ hxabs i]; ring
      have hterm := S_mul_lterm g D hD i
      have hden : 0 < (2 * i + 1) * D ^ (2 * i + 1) := by positivity
      have hlo := cast_div_le' (S2 * g ^ (2 * i + 1)) ((2 * i + 1) * D ^ (2 * i + 1))
      have hhi := le_cast_div_add_one (S2 * g ^ (2 * i + 1)) ((2 * i + 1) * D ^ (2 * i + 1)) hden
      rw [hsplit, hterm]
      constructor
      · push_cast at hlo hrec ⊢
        linarith [hrec.1]
      · push_cast at hhi hrec ⊢
        linarith [hrec.2]

theorem logRatio_eq (g D : ℕ) :
    logRatio g D = (S2 * g / D + (serTail (g * g) (D * D) 30 1 (g * g * g) (D * D * D)).1,
      S2 * g / D + 1 + (serTail (g * g) (D * D) 30 1 (g * g * g) (D * D * D)).2) := rfl

theorem logRatio_sound (k q : ℕ) (hq : 0 < q) (hqk : q < k) (h3 : 3 * (k - q) ≤ k + q) :
    ((logRatio (k - q) (k + q)).1 : ℝ) ≤ (S : ℝ) * (log k - log q) ∧
      (S : ℝ) * (log k - log q) ≤ (logRatio (k - q) (k + q)).2 := by
  obtain ⟨g, hg⟩ : ∃ g, g = k - q := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = k + q := ⟨_, rfl⟩
  rw [← hg, ← hDdef]
  rw [← hg, ← hDdef] at h3
  have hD : 0 < D := by omega
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx0 : (0 : ℝ) ≤ (g : ℝ) / D := by positivity
  have hx3 : (g : ℝ) / D ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hD' (by norm_num)]
    have : ((3 * g : ℕ) : ℝ) ≤ D := by exact_mod_cast h3
    push_cast at this; linarith
  have hxabs : |(g : ℝ) / D| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have hgk : (g : ℝ) = k - q := by rw [hg]; push_cast [hqk.le]; ring
  have hDk : (D : ℝ) = k + q := by rw [hDdef]; push_cast; ring
  have h1 : 1 + (g : ℝ) / D = 2 * k / D := by
    field_simp; rw [hgk, hDk]; ring
  have h2 : 1 - (g : ℝ) / D = 2 * q / D := by
    field_simp; rw [hgk, hDk]; ring
  have hlog : log k - log q = ltail ((g : ℝ) / D) 0 := by
    rw [ltail_zero hxabs, h1, h2, log_div (by positivity) hD'.ne', log_div (by positivity) hD'.ne',
      log_mul (by norm_num) hk'.ne', log_mul (by norm_num) hq'.ne']
    ring
  rw [hlog, ltail_succ hxabs 0, logRatio_eq]
  have hrec := serTail_sound g D hD h3 30 1 le_rfl
  have e1 : g ^ (2 * 1 + 1) = g * g * g := by ring
  have e2 : D ^ (2 * 1 + 1) = D * D * D := by ring
  rw [e1, e2] at hrec
  have hterm := S_mul_lterm g D hD 0
  simp only [mul_zero, zero_add, pow_one, one_mul] at hterm
  have hlo := cast_div_le' (S2 * g) D
  have hhi := le_cast_div_add_one (S2 * g) D hD
  dsimp only
  rw [mul_add, hterm]
  constructor
  · push_cast at hlo hrec ⊢
    linarith [hrec.1]
  · push_cast at hhi hrec ⊢
    linarith [hrec.2]

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
