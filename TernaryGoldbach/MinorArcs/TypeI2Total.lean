import TernaryGoldbach.MinorArcs.TypeITotal
import TernaryGoldbach.MinorArcs.TypeIProof

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# Type I totals [H, §6.2.2]: `S_{I,2}` for `q ≤ Q/V`
-/

open Real Finset
open ArithmeticFunction (vonMangoldt moebius)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

open Classical in
/-- [H, (6.5)]: `S_{I,2}(α, x) = ∑_{v ≤ V odd} Λ(v) S_I(vα, x/v)`. -/
theorem typeI2_eq_sum (α : ℝ) {x : ℝ} (hx : 0 < x) (U V : ℝ) :
    typeI2 α x U V = ∑ v ∈ Icc 1 ⌊V⌋₊, if Odd v then (Λ v : ℂ) * typeI (v * α) (x / v) U else 0 := by
  unfold typeI2 typeI
  refine sum_congr rfl fun v hv => ?_
  have hv1 : 1 ≤ v := (mem_Icc.1 hv).1
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
  split_ifs with hvo
  · congr 1
    refine sum_congr rfl fun u hu => ?_
    have hu1 : 1 ≤ u := (mem_Icc.1 hu).1
    split_ifs with huo
    · congr 1
      have hsub : Icc 1 ⌊x / v⌋₊ ⊆ Icc 1 ⌊x⌋₊ :=
        Icc_subset_Icc le_rfl (Nat.floor_le_floor (div_le_self hx.le (by exact_mod_cast hv1)))
      rw [← sum_subset hsub]
      · refine sum_congr rfl fun n _ => ?_
        split_ifs
        · congr 2
          · ring_nf
          · congr 1; field_simp
        · rfl
      · intro n hn hn'
        have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
        have : x / v < n := by
          by_contra h; push Not at h
          exact hn' (mem_Icc.2 ⟨hn1, Nat.le_floor h⟩)
        have hvn : x < v * u * n := by
          rw [div_lt_iff₀ hv0] at this
          have : (1 : ℝ) ≤ u := by exact_mod_cast hu1
          nlinarith
        rw [Helfgott.eta2_eq_zero (fun h => by
          have := h.2; rw [div_lt_one hx] at this; push_cast at hvn; linarith)]
        simp
    · rfl
  · rfl

/-- The approximation of `2vα` induced by `2α = a/q + δ/x`: `2vα = a_v/q_v + δ/(x/v)` with
`q_v = q/(q,v)`, `a_v = a·v/(q,v)`, valid with `Q_v = Q/v` when `qv ≤ Q`. -/
theorem approx2_mul {α x δ Q : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q) (hx : 0 < x) {v : ℕ}
    (hv : 1 ≤ v) (hqv : (q : ℝ) * v ≤ Q) :
    Approx2 (v * α) (x / v) δ (a * (v / Nat.gcd q v : ℕ)) (q / Nat.gcd q v) (Q / v) := by
  obtain ⟨hq, hcop, ⟨k, h2α⟩, hδQ, hqQ⟩ := h
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set g := Nat.gcd q v
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hq
  obtain ⟨q', hq'⟩ : g ∣ q := Nat.gcd_dvd_left q v
  obtain ⟨v', hv'⟩ : g ∣ v := Nat.gcd_dvd_right q v
  have hqd : q / g = q' := by rw [hq', Nat.mul_div_cancel_left _ hg]
  have hvd : v / g = v' := by rw [hv', Nat.mul_div_cancel_left _ hg]
  have hcop' : Nat.Coprime q' v' := by
    have := Nat.coprime_div_gcd_div_gcd (m := q) (n := v) hg
    rwa [hqd, hvd] at this
  rw [hqd, hvd]
  have hq'1 : 1 ≤ q' := Nat.pos_of_ne_zero (by rintro rfl; simp at hq'; omega)
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hq'0 : (0 : ℝ) < q' := by exact_mod_cast hq'1
  have hq'q : (q' : ℝ) ≤ q := by
    rw [hq']; push_cast; nlinarith [show (1 : ℝ) ≤ g by exact_mod_cast hg]
  refine ⟨hq'1, ?_, ⟨v * k, ?_⟩, ?_, ?_⟩
  · -- `(a v', q') = 1`.
    have h1 : IsCoprime a (q' : ℤ) := by
      have : (q' : ℤ) ∣ q := ⟨g, by rw [hq']; push_cast; ring⟩
      exact hcop.of_isCoprime_of_dvd_right this
    have h2 : IsCoprime ((v' : ℕ) : ℤ) (q' : ℤ) :=
      Nat.isCoprime_iff_coprime.2 hcop'.symm
    exact h1.mul_left h2
  · -- `2vα = a v'/q' + δ/(x/v) + vk`.
    have : (a : ℝ) * v' / q' = a * v / q := by
      rw [hq', hv']; push_cast; field_simp
    push_cast
    rw [this]
    have h2 := congrArg (fun t => (v : ℝ) * t) h2α
    rw [div_div_eq_mul_div]
    field_simp at h2 ⊢
    linarith
  · have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hqv
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity), one_mul] at hδQ
    rw [abs_div, abs_of_pos (div_pos hx hv0), div_le_div_iff₀ (div_pos hx hv0) (by positivity),
      one_mul]
    have : |δ| * (q' * (Q / v)) ≤ |δ| * (q * Q) / v := by
      rw [show |δ| * (q' * (Q / v)) = |δ| * (q' * Q) / v by ring]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq'q hQ0.le) (abs_nonneg _)) hv0.le
    calc |δ| * (q' * (Q / v)) ≤ |δ| * (q * Q) / v := this
      _ ≤ x / v := div_le_div_of_nonneg_right hδQ hv0.le
  · rw [le_div_iff₀ hv0]; nlinarith


open Classical in
/-- [H, (6.6)–(6.8)]: for `qV ≤ Q`, applying Lemma 4.2.2 to each `S_I(vα, x/v)`:
`|S_{I,2}| ≤ ∑_{v ≤ V odd} Λ(v) B_v`, where `B_v` is (4.30) + (4.31) (if `|δ| ≤ 1/2c₂`) or
(4.30) + (4.32) (if `|δ| ≥ 1/2c₂`) for `x/v`, `q_v = q/(q,v)`, `Q/v`. -/
theorem typeI2_le_sum {α x δ Q U V : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q) (hx : 0 < x)
    (hqV : q * V ≤ Q) (hQV : 16 * V ≤ Q) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U * V ≤ x) :
    (|δ| ≤ 1 / (2 * c₂) → ‖typeI2 α x U V‖ ≤ ∑ v ∈ Icc 1 ⌊V⌋₊, if Odd v then
        (Λ v : ℝ) * (bound_4_30 (x / v) δ (q / Nat.gcd q v) U +
          bound_4_31 (x / v) (q / Nat.gcd q v) U) else 0) ∧
    (1 / (2 * c₂) ≤ |δ| → ∀ ε, 0 < ε → ε ≤ 1 → ‖typeI2 α x U V‖ ≤ ∑ v ∈ Icc 1 ⌊V⌋₊, if Odd v then
        (Λ v : ℝ) * (bound_4_30 (x / v) δ (q / Nat.gcd q v) U +
          bound_4_32 (x / v) δ (q / Nat.gcd q v) U (Q / v) ε) else 0) := by
  have hper : ∀ v ∈ Icc 1 ⌊V⌋₊, Approx2 (v * α) (x / v) δ (a * (v / Nat.gcd q v : ℕ))
      (q / Nat.gcd q v) (Q / v) ∧ 16 ≤ Q / v ∧ U ≤ x / v := by
    intro v hv
    have hv1 := (mem_Icc.1 hv).1
    have hv0 : (0 : ℝ) < v := by exact_mod_cast hv1
    have hvV : (v : ℝ) ≤ V := (Nat.cast_le.2 (mem_Icc.1 hv).2).trans (Nat.floor_le (by linarith))
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    refine ⟨approx2_mul h hx hv1 (le_trans (mul_le_mul_of_nonneg_left hvV hq0) hqV), ?_, ?_⟩
    · rw [le_div_iff₀ hv0]; nlinarith
    · rw [le_div_iff₀ hv0]; nlinarith
  have key : ∀ (B : ℕ → ℝ), (∀ v ∈ Icc 1 ⌊V⌋₊, ‖typeI (v * α) (x / v) U‖ ≤ B v) →
      ‖typeI2 α x U V‖ ≤ ∑ v ∈ Icc 1 ⌊V⌋₊, if Odd v then (Λ v : ℝ) * B v else 0 := by
    intro B hB
    rw [typeI2_eq_sum α hx]
    refine (norm_sum_le _ _).trans (sum_le_sum fun v hv => ?_)
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (hB v hv) ArithmeticFunction.vonMangoldt_nonneg
    · simp
  refine ⟨fun hδ => key _ fun v hv => ?_, fun hδ ε hε hε1 => key _ fun v hv => ?_⟩
  · obtain ⟨hA, hQ, hUx⟩ := hper v hv
    exact ((lemma_4_2_2 hA hQ hU hUx).1 (Or.inl hδ))
  · obtain ⟨hA, hQ, hUx⟩ := hper v hv
    exact ((lemma_4_2_2 hA hQ hU hUx).2 hδ ε hε hε1)

end TernaryGoldbach.MinorArcs
