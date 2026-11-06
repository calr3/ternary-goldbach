import TernaryGoldbach.MinorArcs.TypeI2Sum

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# Type I totals [H, §6.2.2]: the case `|δ| ≥ 1/2c₂` ((6.8), (6.14))
-/

open Real Finset
open ArithmeticFunction (vonMangoldt)
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

/-- [H, p. 106]: `∑_{v ≤ V} Λ(v) min(⌊x/v/|δ|q_v⌋ + 1, 2U)`
`≤ (x/|δ|q)(1.03883 + log q + log⁺(6UV|δ|q/√2x)) + 1.0064 V`. -/
theorem sum_min_floor_le {x δ U V : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x) (hδ : 0 < |δ|)
    (hU : 0 < U) (hV : 2.5e7 ≤ V) :
    ∑ v ∈ Icc 1 ⌊V⌋₊, (Λ v : ℝ) *
        min ((⌊x / v / (|δ| * ((q / Nat.gcd q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * U) ≤
      x / (|δ| * q) * (1.03883 + Real.log q + logPlus (6 * U * V * |δ| * q / (√2 * x))) +
        1.0064 * V := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hV0 : 0 < V := by linarith
  set N := ⌊V⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNV : (N : ℝ) ≤ V := Nat.floor_le hV0.le
  set v₀ := x / (2 * U * |δ| * q) with hv₀
  have hv₀0 : 0 < v₀ := by positivity
  set M := ⌊v₀⌋₊ with hM
  set B := x / (|δ| * q) with hB
  have hB0 : 0 < B := by positivity
  have hΛ : ∀ v, (0 : ℝ) ≤ Λ v := fun v => ArithmeticFunction.vonMangoldt_nonneg
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun v => v ≤ M)]
  -- Small `v`: the minimum is at most `2U`.
  have p1 : ∑ v ∈ (Icc 1 N).filter (fun v => v ≤ M), (Λ v : ℝ) *
      min ((⌊x / v / (|δ| * ((q / Nat.gcd q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * U) ≤ 1.03883 * B := by
    calc _ ≤ ∑ v ∈ Icc 1 M, (Λ v : ℝ) * (2 * U) := by
          refine (sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (min_le_right _ _) (hΛ v)).trans
            (sum_le_sum_of_subset_of_nonneg ?_ fun v _ _ => mul_nonneg (hΛ v) (by positivity))
          intro v hv; simp only [mem_filter, mem_Icc] at hv ⊢; omega
      _ = 2 * U * ∑ v ∈ Icc 1 M, (Λ v : ℝ) := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ 2 * U * (1.03883 * v₀) :=
          mul_le_mul_of_nonneg_left (Prelim.sum_vonMangoldt_lt hv₀0).le (by positivity)
      _ = 1.03883 * B := by simp only [hv₀, hB]; field_simp
  -- Large `v`: the minimum is at most `x(q,v)/(v|δ|q) + 1`.
  set S := (Icc 1 N).filter (fun v => ¬v ≤ M) with hS
  have hSsub : S ⊆ Icc 1 N := filter_subset _ _
  have p2a : ∑ v ∈ S, (Λ v : ℝ) *
      min ((⌊x / v / (|δ| * ((q / Nat.gcd q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * U) ≤
      B * ∑ v ∈ S, (Λ v : ℝ) * (1 / v) * Nat.gcd q v + ∑ v ∈ S, (Λ v : ℝ) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun v hv => ?_
    have hv1 : 1 ≤ v := (mem_Icc.1 (hSsub hv)).1
    have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
    have hg : (0 : ℝ) < Nat.gcd q v := by exact_mod_cast Nat.gcd_pos_of_pos_left v hq
    have hy : x / v / (|δ| * ((q / Nat.gcd q v : ℕ) : ℝ)) = B * (1 / v * Nat.gcd q v) := by
      rw [cast_div_gcd q v hq, hB]; field_simp
    have h1 : min ((⌊x / v / (|δ| * ((q / Nat.gcd q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * U) ≤
        B * (1 / v * Nat.gcd q v) + 1 := by
      refine (min_le_left _ _).trans ?_
      rw [hy]
      have := Nat.floor_le (show 0 ≤ B * (1 / v * Nat.gcd q v) by positivity)
      linarith
    calc (Λ v : ℝ) * min _ _ ≤ (Λ v : ℝ) * (B * (1 / v * Nat.gcd q v) + 1) :=
          mul_le_mul_of_nonneg_left h1 (hΛ v)
      _ = _ := by ring
  have p2b := sum_vonMangoldt_gcd_div_subset_le hq hSsub
  have p2c : ∑ v ∈ S, (Λ v : ℝ) ≤ 1.0064 * V := by
    refine (sum_le_sum_of_subset_of_nonneg hSsub fun v _ _ => hΛ v).trans ?_
    have := Prelim.sum_vonMangoldt_le_a14 (y := V) (by linarith)
    rwa [← hN] at this
  -- `∑_{v ∈ S} Λ(v)/v ≤ log⁺(6UV|δ|q/√2x)`.
  have p2d : ∑ v ∈ S, (Λ v : ℝ) * (1 / v) ≤ logPlus (6 * U * V * |δ| * q / (√2 * x)) := by
    by_cases hMN : M ≤ N
    · have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) (fun v => v ≤ M)
        (fun v => (Λ v : ℝ) * (1 / v))
      have hfilt : (Icc 1 N).filter (fun v => v ≤ M) = Icc 1 M := by
        ext v; simp only [mem_filter, mem_Icc]; omega
      rw [hfilt] at hsplit
      have hall : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * (1 / v) ≤ Real.log V := by
        have := Prelim.sum_vonMangoldt_div_le_log (x := V) (by linarith)
        rw [← hN] at this
        simpa [div_eq_mul_inv] using this
      have hsmall : Real.log v₀ - Real.log (3 / √2) ≤ ∑ v ∈ Icc 1 M, (Λ v : ℝ) * (1 / v) := by
        by_cases hv1 : 1 ≤ v₀
        · have := Prelim.log_sub_le_sum_vonMangoldt_div hv1
          rw [← hM] at this
          simpa [div_eq_mul_inv] using this
        · push Not at hv1
          have h1 : Real.log v₀ < 0 := Real.log_neg hv₀0 hv1
          have h2 : 0 < Real.log (3 / √2) := Real.log_pos (by
            rw [one_lt_div (by positivity)]
            have : √2 < 2 := by
              rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                Real.sqrt_sq (by norm_num)]]
              exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
            linarith)
          have : 0 ≤ ∑ v ∈ Icc 1 M, (Λ v : ℝ) * (1 / v) :=
            sum_nonneg fun v _ => mul_nonneg (hΛ v) (by positivity)
          linarith
      have heq : Real.log V - (Real.log v₀ - Real.log (3 / √2)) =
          Real.log (6 * U * V * |δ| * q / (√2 * x)) := by
        rw [sub_sub_eq_add_sub, ← Real.log_mul hV0.ne' (by positivity),
          ← Real.log_div (by positivity) hv₀0.ne']
        congr 1
        simp only [hv₀]
        field_simp
        ring
      have : ∑ v ∈ S, (Λ v : ℝ) * (1 / v) ≤ Real.log (6 * U * V * |δ| * q / (√2 * x)) := by
        rw [← heq]; linarith
      exact this.trans (le_max_left _ _)
    · have hSe : S = ∅ := by
        ext v; simp only [hS, mem_filter, mem_Icc, notMem_empty, iff_false]; omega
      rw [hSe, sum_empty]; exact logPlus_nonneg _
  have := mul_le_mul_of_nonneg_left (p2b.trans (add_le_add_left p2d _)) hB0.le
  nlinarith

omit [Fact TernaryGoldbach.RHUpTo] in
theorem logPlus_le_logPlus {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : logPlus a ≤ logPlus b :=
  max_le_max (Real.log_le_log ha hab) le_rfl

omit [Fact TernaryGoldbach.RHUpTo] in
/-- [H, (6.8)], per `v`: (4.32) for `x/v`, `q_v = q/(q,v)`, `Q/v`, keeping
`m_v = min(⌊x/v/|δ|q_v⌋ + 1, 2U)` (summed in `sum_min_floor_le`). -/
theorem bound_4_32_v_le {x δ Q U V ε : ℝ} {q v : ℕ} (hq : 1 ≤ q) (hx : 0 < x) (hδ : 0 < |δ|)
    (hδQ : |δ| * q * Q ≤ x) (hU : 0 < U) (hQ : 0 < Q) (hv : 1 ≤ v) (hvV : (v : ℝ) ≤ V)
    (hε : 0 < ε) :
    bound_4_32 (x / v) δ (q / Nat.gcd q v) U (Q / v) ε ≤
      2 * √(c₀ * cPlus x U V) / π * (1 + ε) * √(3 + 2 * ε) *
          min ((⌊x / v / (|δ| * ((q / Nat.gcd q v : ℕ) : ℝ))⌋₊ : ℝ) + 1) (2 * U) +
        (2 * √(c₀ * cPlus x U V) / π * (1 + (1 + ε) * (1 + V / Q) / rexp 1) * U +
          3 / 2 * cPlus x U V * (2 + (1 + ε) / ε * logPlus (2 * U * V * |δ| * q / x)) * (x / Q) +
          35 * c₀ * c₂ / (3 * π ^ 2) * q) := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hV : 0 < V := lt_of_lt_of_le hv0 hvV
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hg1 : (1 : ℝ) ≤ Nat.gcd q v := by exact_mod_cast Nat.gcd_pos_of_pos_left v hq
  have hqv := cast_div_gcd q v hq
  have hqv1 : (1 : ℝ) ≤ ((q / Nat.gcd q v : ℕ) : ℝ) := by exact_mod_cast one_le_div_gcd q v hq
  have hqvq : ((q / Nat.gcd q v : ℕ) : ℝ) ≤ q := by rw [hqv]; exact div_le_self hq0.le hg1
  have hL := eta2'L1_pos
  have hc0 : (0 : ℝ) < c₀ := by norm_num [c₀]
  have hc2 := c₂_pos
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  set c := cPlus x U V with hc
  have hcc : 1 + eta2'L1 / (x / v / U) ≤ c := by
    simp only [hc, cPlus]
    have e1 : eta2'L1 / (x / v / U) = eta2'L1 * U * v / x := by field_simp
    have e2 : eta2'L1 / (x / (U * V)) = eta2'L1 * U * V / x := by field_simp
    rw [e1, e2]; gcongr
  have hc1 : 1 ≤ 1 + eta2'L1 / (x / v / U) := by
    have : 0 ≤ eta2'L1 / (x / v / U) := by positivity
    linarith
  set s := ((q / Nat.gcd q v : ℕ) : ℝ) with hs
  have hs0 : 0 < s := by linarith
  set y := x / v / (|δ| * s) with hy
  have hy0 : 0 < y := by positivity
  have hyQ : Q / V ≤ y := by
    rw [hy, div_le_div_iff₀ hV (by positivity)]
    calc Q * (|δ| * s) ≤ Q * (|δ| * q) := by gcongr
      _ = |δ| * q * Q := by ring
      _ ≤ x := hδQ
      _ = x / v * v := by field_simp
      _ ≤ x / v * V := by gcongr
  set m := min ((⌊y⌋₊ : ℝ) + 1) (2 * U) with hm
  have hm0 : 0 ≤ m := le_min (by positivity) (by positivity)
  have hmy : m ≤ (1 + V / Q) * y := by
    refine (min_le_left _ _).trans ?_
    have h1 := Nat.floor_le hy0.le
    have h2 : 1 ≤ V / Q * y := by
      rw [show V / Q * y = y / (Q / V) by field_simp, le_div_iff₀ (by positivity)]; linarith
    nlinarith
  set Lg := logPlus (2 * U / y) with hLg
  have hLg0 : 0 ≤ Lg := logPlus_nonneg _
  have hyL : y * Lg ≤ 2 * U / rexp 1 := mul_logPlus_div_le hy0 (by positivity)
  have hLL : Lg ≤ logPlus (2 * U * V * |δ| * q / x) := by
    refine logPlus_le_logPlus (by positivity) ?_
    rw [hy, show 2 * U / (x / v / (|δ| * s)) = 2 * U * v * |δ| * s / x by field_simp]
    gcongr
  have hsq : √(c₀ * (1 + eta2'L1 / (x / v / U))) ≤ √(c₀ * c) := Real.sqrt_le_sqrt (by gcongr)
  unfold bound_4_32
  simp only []
  rw [← hs, ← hy, ← hm, ← hLg]
  have hxQ : x / v / (Q / v) = x / Q := by field_simp
  rw [hxQ]
  have hmL : m * (1 / 2 * Lg) ≤ (1 + V / Q) * U / rexp 1 := by
    calc m * (1 / 2 * Lg) ≤ (1 + V / Q) * y * (1 / 2 * Lg) := by gcongr
      _ = (1 + V / Q) / 2 * (y * Lg) := by ring
      _ ≤ (1 + V / Q) / 2 * (2 * U / rexp 1) := by gcongr
      _ = (1 + V / Q) * U / rexp 1 := by ring
  have hA : 0 ≤ 2 * √(c₀ * c) / π := by positivity
  have t1 : 2 * √(c₀ * (1 + eta2'L1 / (x / v / U))) / π *
      (U + (1 + ε) * m * (√(3 + 2 * ε) + 1 / 2 * Lg)) ≤
      2 * √(c₀ * c) / π * (U + (1 + ε) * m * (√(3 + 2 * ε) + 1 / 2 * Lg)) := by
    gcongr
  have t1' : 2 * √(c₀ * c) / π * (U + (1 + ε) * m * (√(3 + 2 * ε) + 1 / 2 * Lg)) ≤
      2 * √(c₀ * c) / π * (1 + ε) * √(3 + 2 * ε) * m +
        2 * √(c₀ * c) / π * (1 + (1 + ε) * (1 + V / Q) / rexp 1) * U := by
    have : (1 + ε) * (m * (1 / 2 * Lg)) ≤ (1 + ε) * ((1 + V / Q) * U / rexp 1) := by gcongr
    have e1 : U + (1 + ε) * m * (√(3 + 2 * ε) + 1 / 2 * Lg) =
        (1 + ε) * √(3 + 2 * ε) * m + U + (1 + ε) * (m * (1 / 2 * Lg)) := by ring
    have e2 : 2 * √(c₀ * c) / π * (1 + ε) * √(3 + 2 * ε) * m +
        2 * √(c₀ * c) / π * (1 + (1 + ε) * (1 + V / Q) / rexp 1) * U =
        2 * √(c₀ * c) / π * ((1 + ε) * √(3 + 2 * ε) * m + U + (1 + ε) * ((1 + V / Q) * U / rexp 1))
        := by ring
    rw [e1, e2]; gcongr
  have t2 : 3 / 2 * (1 + eta2'L1 / (x / v / U)) * (2 + (1 + ε) / ε * Lg) * (x / Q) ≤
      3 / 2 * c * (2 + (1 + ε) / ε * logPlus (2 * U * V * |δ| * q / x)) * (x / Q) := by
    have : 0 ≤ 3 / 2 * c := by linarith
    gcongr
  have t3 : 35 * c₀ * c₂ / (3 * π ^ 2) * s ≤ 35 * c₀ * c₂ / (3 * π ^ 2) * q := by gcongr
  linarith

variable [Fact TernaryGoldbach.RamareMoebius] in
/-- **[H, (6.12) + (6.14)]**, our version, for `|δ| ≥ 1/2c₂`, `qV ≤ Q` and `0 < ε ≤ 1`:
`|S_{I,2}|` is at most the first two lines of `typeI2_le_small` ((6.12)) plus
`1.0064 (2√(c₀c₊)/π)(1 + (1+ε)(1+V/Q)/e) UV`
`+ 1.0064 (3c₊/2)(2 + ((1+ε)/ε) log⁺(2UV|δ|q/x)) xV/Q + 1.0064 (35c₀c₂/3π²) Q`
`+ (2√(c₀c₊)/π)(1+ε)√(3+2ε) ((x/|δ|q)(1.03883 + log q + log⁺(6UV|δ|q/√2x)) + 1.0064 V)`.
Compared with [H]: the `U/e` term carries a factor `1 + V/Q` (since (4.32) has
`log⁺(2D/y)` rather than `log⁺(2D/(⌊y⌋+1))`). -/
theorem typeI2_le_large {α x δ Q U V ε : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q)
    (hx : 0 < x) (hqV : q * V ≤ Q) (hQV : 16 * V ≤ Q) (hU : 1 ≤ U) (hV : 2.5e7 ≤ V)
    (hUV : U * V ≤ x) (hδ : 1 / (2 * c₂) ≤ |δ|) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖typeI2 α x U V‖ ≤
      x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q * Real.log (V * q) +
        c₀ * (1 / 8 - 1 / (2 * π ^ 2)) / x *
          (U ^ 2 / q * (0.511 * V ^ 2 + V * q * Real.log q) + (2 * U + q) * (0.511 * V ^ 2)) +
        1.0064 * (2 * √(c₀ * cPlus x U V) / π * (1 + (1 + ε) * (1 + V / Q) / rexp 1)) * (U * V) +
        1.0064 * (3 / 2 * cPlus x U V * (2 + (1 + ε) / ε * logPlus (2 * U * V * |δ| * q / x))) *
          (x * V / Q) +
        1.0064 * (35 * c₀ * c₂ / (3 * π ^ 2)) * Q +
        2 * √(c₀ * cPlus x U V) / π * (1 + ε) * √(3 + 2 * ε) *
          (x / (|δ| * q) * (1.03883 + Real.log q + logPlus (6 * U * V * |δ| * q / (√2 * x))) +
            1.0064 * V) := by
  have hsum := (typeI2_le_sum h hx hqV hQV hU (by linarith) hUV).2 hδ ε hε hε1
  refine hsum.trans ?_
  obtain ⟨hq, -, -, hδQ', -⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hV0 : 0 < V := by linarith
  have hQ : 0 < Q := by linarith
  have hU0 : 0 < U := by linarith
  have hδ0 : 0 < |δ| := lt_of_lt_of_le (by have := c₂_pos; positivity) hδ
  have hδQ : |δ| * q * Q ≤ x := by
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity), one_mul] at hδQ'
    linarith
  set N := ⌊V⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNV : (N : ℝ) ≤ V := Nat.floor_le hV0.le
  set A := x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q with hA
  set K := c₀ * (1 / 8 - 1 / (2 * π ^ 2)) / x with hK
  set c := cPlus x U V with hc
  set C := 2 * √(c₀ * c) / π * (1 + (1 + ε) * (1 + V / Q) / rexp 1) * U +
    3 / 2 * c * (2 + (1 + ε) / ε * logPlus (2 * U * V * |δ| * q / x)) * (x / Q) +
    35 * c₀ * c₂ / (3 * π ^ 2) * q with hC
  set D := 2 * √(c₀ * c) / π * (1 + ε) * √(3 + 2 * ε) with hD
  set m : ℕ → ℝ := fun v => min ((⌊x / v / (|δ| * ((q / Nat.gcd q v : ℕ) : ℝ))⌋₊ : ℝ) + 1)
    (2 * U) with hm
  have hc0 : 0 ≤ c := by
    simp only [hc, cPlus]; have := eta2'L1_pos; positivity
  have hpi := Real.pi_pos
  have hc2 := c₂_pos
  have hc00 : (0 : ℝ) < c₀ := by norm_num [c₀]
  have hmi : 0 ≤ minInv c₀ (π * δ) := by
    unfold minInv; split_ifs
    · norm_num
    · exact le_min zero_le_one (div_nonneg (by norm_num [c₀]) (sq_nonneg _))
  have hA0 : 0 ≤ A := by
    have := muBound_nonneg (min (Q / (2 * V)) U) hq; positivity
  have hK0 : 0 ≤ K := by
    have := Real.pi_gt_three
    have : 0 ≤ 1 / 8 - 1 / (2 * π ^ 2) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    positivity
  have hC0 : 0 ≤ C := by
    have := logPlus_nonneg (2 * U * V * |δ| * q / x)
    have := Real.exp_pos 1
    positivity
  have hD0 : 0 ≤ D := by positivity
  have hm0 : ∀ v, 0 ≤ m v := fun v => le_min (by positivity) (by positivity)
  set F : ℕ → ℝ := fun v => A * (1 / v * Nat.gcd q v) +
    K * (U ^ 2 / q * (v * Nat.gcd q v) + (2 * U + q) * v) + C + D * m v with hF
  have hF0 : ∀ v, 0 ≤ F v := fun v => by
    simp only [hF]; have := hm0 v; positivity
  have step1 : (∑ v ∈ Icc 1 N, if Odd v then (Λ v : ℝ) * (bound_4_30 (x / v) δ (q / Nat.gcd q v) U +
      bound_4_32 (x / v) δ (q / Nat.gcd q v) U (Q / v) ε) else 0) ≤
      ∑ v ∈ Icc 1 N, (Λ v : ℝ) * F v := by
    refine sum_le_sum fun v hv => ?_
    have hv1 := (mem_Icc.1 hv).1
    have hvV : (v : ℝ) ≤ V := (Nat.cast_le.2 (mem_Icc.1 hv).2).trans hNV
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := v)
    split_ifs
    · refine mul_le_mul_of_nonneg_left ?_ hΛ
      have h30 := bound_4_30_v_le (δ := δ) hq hx hδQ hU0 hQ hv1 hvV
      have h32 := bound_4_32_v_le hq hx hδ0 hδQ hU0 hQ hv1 hvV hε
      simp only [hF, hA, hK, hC, hc, hD, hm]
      have : x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q *
          (Nat.gcd q v / v) = x / (2 * q) * minInv c₀ (π * δ) * muBound (min (Q / (2 * V)) U) q *
          (1 / v * Nat.gcd q v) := by ring
      have : U ^ 2 / q * v * Nat.gcd q v = U ^ 2 / q * (v * Nat.gcd q v) := by ring
      linarith
    · exact mul_nonneg hΛ (hF0 v)
  have e : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * F v =
      A * ∑ v ∈ Icc 1 N, (Λ v : ℝ) * (1 / v) * Nat.gcd q v +
        K * U ^ 2 / q * ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v * Nat.gcd q v +
        K * (2 * U + q) * ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v + C * ∑ v ∈ Icc 1 N, (Λ v : ℝ) +
        D * ∑ v ∈ Icc 1 N, (Λ v : ℝ) * m v := by
    rw [mul_sum, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib,
      ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    simp only [hF]; ring
  rw [e] at step1
  refine step1.trans ?_
  have s1 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * (1 / v) * Nat.gcd q v ≤ Real.log (V * q) := by
    refine (sum_vonMangoldt_gcd_div_le hq hN1).trans ?_
    rw [Real.log_mul hV0.ne' hq0.ne']
    have : Real.log N ≤ Real.log V :=
      Real.log_le_log (by exact_mod_cast hN1) hNV
    linarith
  have s3 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v ≤ 0.511 * V ^ 2 := by
    have := Prelim.sum_vonMangoldt_mul_lt_a17 (y := V) (by norm_num; linarith)
    rw [← hN] at this; linarith
  have s2 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) * v * Nat.gcd q v ≤ 0.511 * V ^ 2 + V * q * Real.log q := by
    refine (sum_vonMangoldt_mul_gcd_le hq (N := N)).trans ?_
    have : (N : ℝ) * q * Real.log q ≤ V * q * Real.log q := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
      gcongr
    linarith
  have s4 : ∑ v ∈ Icc 1 N, (Λ v : ℝ) ≤ 1.0064 * V := by
    have := Prelim.sum_vonMangoldt_le_a14 (y := V) (by linarith)
    rwa [← hN] at this
  have s5 := sum_min_floor_le (δ := δ) hq hx hδ0 hU0 hV (x := x)
  have hKU : 0 ≤ K * U ^ 2 / q := by positivity
  have hK2 : 0 ≤ K * (2 * U + q) := by positivity
  have b1 := mul_le_mul_of_nonneg_left s1 hA0
  have b2 := mul_le_mul_of_nonneg_left s2 hKU
  have b3 := mul_le_mul_of_nonneg_left s3 hK2
  have b4 := mul_le_mul_of_nonneg_left s4 hC0
  have b5 := mul_le_mul_of_nonneg_left s5 hD0
  have hqQ : 35 * c₀ * c₂ / (3 * π ^ 2) * q * V ≤ 35 * c₀ * c₂ / (3 * π ^ 2) * Q := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hqV (by positivity)
  have hlast : C * (1.0064 * V) ≤
      1.0064 * (2 * √(c₀ * c) / π * (1 + (1 + ε) * (1 + V / Q) / rexp 1)) * (U * V) +
      1.0064 * (3 / 2 * c * (2 + (1 + ε) / ε * logPlus (2 * U * V * |δ| * q / x))) * (x * V / Q) +
      1.0064 * (35 * c₀ * c₂ / (3 * π ^ 2)) * Q := by
    have e2 : C * (1.0064 * V) =
        1.0064 * (2 * √(c₀ * c) / π * (1 + (1 + ε) * (1 + V / Q) / rexp 1)) * (U * V) +
        1.0064 * (3 / 2 * c * (2 + (1 + ε) / ε * logPlus (2 * U * V * |δ| * q / x))) *
          (x * V / Q) + 1.0064 * (35 * c₀ * c₂ / (3 * π ^ 2) * q * V) := by
      simp only [hC]; ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hqQ (by norm_num : (0 : ℝ) ≤ 1.0064)
    linarith
  have hfin : K * U ^ 2 / q * (0.511 * V ^ 2 + V * q * Real.log q) +
      K * (2 * U + q) * (0.511 * V ^ 2) = K * (U ^ 2 / q * (0.511 * V ^ 2 + V * q * Real.log q) +
        (2 * U + q) * (0.511 * V ^ 2)) := by ring
  linarith

end TernaryGoldbach.MinorArcs
