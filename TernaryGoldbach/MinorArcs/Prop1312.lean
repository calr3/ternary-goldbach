import Mathlib

/-!
# Combining ℓ² bounds over arcs with ℓ∞ bounds [B, Lemma 13.1.1, Prop. 13.1.2]

Abstract form, over any measure space.  `u = |S₁|²`, `v = |S₂|`, `M n` a non-decreasing family of
measurable sets ("the major arcs `𝔐_{δ₀,n}`"), `v ≤ g n` off `M n`, `∫_{M(n+1)} u ≤ H n`.  Then
(`prop_13_1_2`)

`∫_{(M r₀)ᶜ} u v ≤ g(r₀)(H(r₀) − I₀) + Σ_{r₀ < n ≤ r₁} g(n)(H(n) − H(n−1))`, `I₀ = ∫_{M r₀} u`,

the discrete form of [B, (13.6)] (`∫ g H'` becomes `Σ g(n)(H(n) − H(n−1))`, which is at most
`∫_{r₀}^{r₁} g H'` for non-increasing `g` and non-decreasing `H`).  The levels are integers, as in
[B]'s proof.  The discrete Abel summation step is `abel_le` (the core of Lemma 13.1.1).

Proved, with no `sorry`.
-/

open MeasureTheory Set Finset

namespace TernaryGoldbach.MinorArcs

/-- Abel summation, inequality form: if `g` is non-increasing and `≥ 0` on `[a, b]` and the
partial sums `S(n) = Σ_{a ≤ m ≤ n} f(m)` satisfy `S(n) ≤ F(n)`, then
`Σ_{a ≤ n ≤ b} f(n) g(n) ≤ g(a) F(a) + Σ_{a < n ≤ b} g(n)(F(n) − F(n−1))`. -/
theorem abel_le {f g F : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b)
    (hg : ∀ n, a ≤ n → n < b → g (n + 1) ≤ g n) (hg0 : 0 ≤ g b)
    (hS : ∀ n, a ≤ n → n ≤ b → ∑ m ∈ Icc a n, f m ≤ F n) :
    ∑ n ∈ Icc a b, f n * g n ≤ g a * F a + ∑ n ∈ Ioc a b, g n * (F n - F (n - 1)) := by
  -- stronger statement by induction: the defect `g(k)(F(k) − S(k))` is kept
  have key : ∀ k, a ≤ k → k ≤ b →
      ∑ n ∈ Icc a k, f n * g n ≤ g a * F a + ∑ n ∈ Ioc a k, g n * (F n - F (n - 1)) -
        g k * (F k - ∑ m ∈ Icc a k, f m) := by
    intro k hak hkb
    induction k, hak using Nat.le_induction with
    | base => simp; linarith [mul_comm (f a) (g a)]
    | succ k hak ih =>
      have ih := ih (by omega)
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), sum_Ioc_succ_top hak,
        Nat.add_sub_cancel]
      have hgk := hg k hak (by omega)
      have hSk := hS k hak (by omega)
      nlinarith [mul_le_mul_of_nonneg_right hgk (sub_nonneg.2 hSk)]
  have := key b hab le_rfl
  have : 0 ≤ g b * (F b - ∑ m ∈ Icc a b, f m) := mul_nonneg hg0 (sub_nonneg.2 (hS b hab le_rfl))
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Peeling off one level: `∫_{(M r₀)ᶜ} u v ≤ Σ_{r₀ ≤ n < k} g(n)(I(n+1) − I(n)) + ∫_{(M k)ᶜ} u v`
with `I(n) = ∫_{M n} u`. -/
theorem layer_le {u v : Ω → ℝ} (hu : Integrable u μ) (huv : Integrable (fun ω => u ω * v ω) μ)
    (hu0 : ∀ ω, 0 ≤ u ω) {M : ℕ → Set Ω} (hM : ∀ n, MeasurableSet (M n)) (hmono : Monotone M)
    {g : ℕ → ℝ} {r₀ K : ℕ} (hv : ∀ n, r₀ ≤ n → n < K → ∀ ω ∉ M n, v ω ≤ g n) :
    ∀ k, r₀ ≤ k → k ≤ K → ∫ ω in (M r₀)ᶜ, u ω * v ω ∂μ ≤
      ∑ n ∈ Ico r₀ k, g n * ((∫ ω in M (n + 1), u ω ∂μ) - ∫ ω in M n, u ω ∂μ) +
        ∫ ω in (M k)ᶜ, u ω * v ω ∂μ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    intro hkK
    have ih := ih (by omega)
    rw [sum_Ico_succ_top hk]
    have hsplit : (M k)ᶜ = (M (k + 1) \ M k) ∪ (M (k + 1))ᶜ := by
      ext ω; simp only [mem_compl_iff, mem_union, mem_sdiff]
      have : ω ∈ M k → ω ∈ M (k + 1) := fun h => hmono (show k ≤ k + 1 by omega) h
      tauto
    have hdisj : Disjoint (M (k + 1) \ M k) (M (k + 1))ᶜ :=
      disjoint_compl_right.mono_left sdiff_subset
    have e1 : ∫ ω in (M k)ᶜ, u ω * v ω ∂μ = (∫ ω in M (k + 1) \ M k, u ω * v ω ∂μ) +
        ∫ ω in (M (k + 1))ᶜ, u ω * v ω ∂μ := by
      rw [hsplit, setIntegral_union hdisj (hM _).compl huv.integrableOn huv.integrableOn]
    have e2 : ∫ ω in M (k + 1), u ω ∂μ = (∫ ω in M k, u ω ∂μ) + ∫ ω in M (k + 1) \ M k, u ω ∂μ := by
      have : M (k + 1) = M k ∪ (M (k + 1) \ M k) := (union_sdiff_cancel (hmono (by omega))).symm
      conv_lhs => rw [this]
      rw [setIntegral_union disjoint_sdiff_right ((hM _).diff (hM _)) hu.integrableOn hu.integrableOn]
    have h3 : ∫ ω in M (k + 1) \ M k, u ω * v ω ∂μ ≤ ∫ ω in M (k + 1) \ M k, g k * u ω ∂μ := by
      refine setIntegral_mono_on huv.integrableOn (hu.integrableOn.const_mul _)
        ((hM _).diff (hM _)) fun ω hω => ?_
      rw [mul_comm (g k)]
      exact mul_le_mul_of_nonneg_left (hv k hk (by omega) ω hω.2) (hu0 ω)
    rw [integral_const_mul] at h3
    have e4 : g k * ((∫ ω in M (k + 1), u ω ∂μ) - ∫ ω in M k, u ω ∂μ) =
        g k * ∫ ω in M (k + 1) \ M k, u ω ∂μ := by rw [e2]; ring
    linarith

/-- **[B, Prop. 13.1.2]**, discrete form (see the module docstring). -/
theorem prop_13_1_2 {u v : Ω → ℝ} (hu : Integrable u μ) (huv : Integrable (fun ω => u ω * v ω) μ)
    (hu0 : ∀ ω, 0 ≤ u ω) {M : ℕ → Set Ω} (hM : ∀ n, MeasurableSet (M n)) (hmono : Monotone M)
    {g H : ℕ → ℝ} {r₀ r₁ : ℕ} (h01 : r₀ ≤ r₁)
    (hg : ∀ n, r₀ ≤ n → n < r₁ → g (n + 1) ≤ g n) (hg0 : 0 ≤ g r₁)
    (hv : ∀ n, r₀ ≤ n → n ≤ r₁ → ∀ ω ∉ M n, v ω ≤ g n)
    (hH : ∀ n, r₀ ≤ n → n < r₁ → ∫ ω in M (n + 1), u ω ∂μ ≤ H n) (hH₁ : ∫ ω, u ω ∂μ ≤ H r₁) :
    ∫ ω in (M r₀)ᶜ, u ω * v ω ∂μ ≤
      g r₀ * (H r₀ - ∫ ω in M r₀, u ω ∂μ) + ∑ n ∈ Ioc r₀ r₁, g n * (H n - H (n - 1)) := by
  set I : ℕ → ℝ := fun n => ∫ ω in M n, u ω ∂μ with hI
  -- the last layer
  have hlast : ∫ ω in (M r₁)ᶜ, u ω * v ω ∂μ ≤ g r₁ * ((∫ ω, u ω ∂μ) - I r₁) := by
    have h1 : ∫ ω in (M r₁)ᶜ, u ω * v ω ∂μ ≤ ∫ ω in (M r₁)ᶜ, g r₁ * u ω ∂μ := by
      refine setIntegral_mono_on huv.integrableOn (hu.integrableOn.const_mul _)
        (hM _).compl fun ω hω => ?_
      rw [mul_comm (g r₁)]
      exact mul_le_mul_of_nonneg_left (hv r₁ h01 le_rfl ω hω) (hu0 ω)
    rw [integral_const_mul] at h1
    have h2 : ∫ ω in (M r₁)ᶜ, u ω ∂μ = (∫ ω, u ω ∂μ) - I r₁ := by
      have := integral_add_compl (hM r₁) hu
      simp only [hI]; linarith
    rwa [h2] at h1
  have hl := layer_le hu huv hu0 hM hmono (K := r₁) (fun n h1 h2 => hv n h1 h2.le) r₁ h01 le_rfl
  -- write it as `Σ_{n ∈ [r₀, r₁]} f(n) g(n)`
  set f : ℕ → ℝ := fun n => if n < r₁ then I (n + 1) - I n else (∫ ω, u ω ∂μ) - I r₁ with hf
  have hsum : ∑ n ∈ Ico r₀ r₁, g n * (I (n + 1) - I n) + g r₁ * ((∫ ω, u ω ∂μ) - I r₁) =
      ∑ n ∈ Icc r₀ r₁, f n * g n := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_succ_top (by omega)]
    congr 1
    · refine sum_congr rfl fun n hn => ?_
      have : n < r₁ := (mem_Ico.1 hn).2
      simp only [hf, ite_eq_left this]; ring
    · simp only [hf, lt_irrefl, ite_false]; ring
  -- partial sums telescope
  have hS : ∀ n, r₀ ≤ n → n ≤ r₁ → ∑ m ∈ Icc r₀ n, f m ≤ H n - I r₀ := by
    intro n hn hn1
    have tele : ∀ k, r₀ ≤ k → k ≤ r₁ → ∑ m ∈ Ico r₀ k, f m = I k - I r₀ := by
      intro k hk hk1
      induction k, hk using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [sum_Ico_succ_top hk, ih (by omega)]
        simp only [hf, ite_eq_left (show k < r₁ by omega)]; ring
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_succ_top hn, tele n hn hn1]
    rcases lt_or_eq_of_le hn1 with h | h
    · simp only [hf, ite_eq_left h]; linarith [hH n hn h]
    · subst h; simp only [hf, lt_irrefl, ite_false]; linarith
  have habel := abel_le (F := fun n => H n - I r₀) h01 hg hg0 hS
  have e3 : ∑ n ∈ Ioc r₀ r₁, g n * ((H n - I r₀) - (H (n - 1) - I r₀)) =
      ∑ n ∈ Ioc r₀ r₁, g n * (H n - H (n - 1)) := sum_congr rfl fun n _ => by ring
  rw [e3] at habel
  linarith

end TernaryGoldbach.MinorArcs
