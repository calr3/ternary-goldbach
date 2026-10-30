import TernaryGoldbach.MinorArcs.TypeIProof
import TernaryGoldbach.MinorArcs.Eta2Log
import TernaryGoldbach.MinorArcs.SumTools

/-!
# Proof of [B, Lemma 4.2.3] (Type I sums with `log n`; `η = η₂`)
-/

open Real Finset
open ArithmeticFunction (moebius)
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- The inner sum of `typeILog`, for `m ≥ 1`, is `T_{m,∘}` with smoothing `η_(x/m)`. -/
theorem innerLog_eq_ToddG {α x : ℝ} (hx : 0 < x) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Icc 1 ⌊x⌋₊,
        (if Odd n then (Real.log n : ℂ) * e (α * m * n) * (eta2 (m * n / x) : ℂ) else 0) =
      ToddG (eta2log (x / m)) α x m := by
  set N := ⌊x⌋₊
  set K := (N + 1) / 2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpt : ∀ n : ℕ, (Real.log n : ℂ) * e (α * m * n) * (eta2 (m * n / x) : ℂ) =
      e (α * m * n) * (eta2log (x / m) (m * n / x) : ℂ) := by
    intro n
    rw [eta2log, show x / m * (m * n / x) = (n : ℝ) by field_simp]
    push_cast; ring
  simp_rw [hpt]
  rw [sum_Icc_odd_eq N (fun n => e (α * m * n) * (eta2log (x / m) (m * n / x) : ℂ)), ToddG]
  rw [tsum_eq_sum (s := (range K).map Nat.castEmbedding)]
  · rw [sum_map]; refine sum_congr rfl fun r _ => ?_; simp
  · intro r hr
    simp only [mem_map, mem_range, Nat.castEmbedding_apply, not_exists, not_and] at hr
    rw [eta2log, Helfgott.eta2_eq_zero, mul_zero, Complex.ofReal_zero, mul_zero]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    rcases lt_or_ge r 0 with h | h
    · left
      have : (2 * (r : ℝ) + 1) ≤ 0 := by
        have : r ≤ -1 := by omega
        have : (r : ℝ) ≤ -1 := by exact_mod_cast this
        linarith
      have : m * (2 * (r : ℝ) + 1) / x ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) this) hx.le
      linarith
    · right
      have hrK : K ≤ r.toNat := by
        by_contra hlt; push Not at hlt
        exact hr r.toNat hlt (Int.toNat_of_nonneg h)
      have hr' : ((N : ℝ) + 1) ≤ 2 * r + 1 := by
        have : (N + 1 : ℤ) ≤ 2 * r + 1 := by
          have : (K : ℤ) ≤ r := by
            have := Int.toNat_of_nonneg h; omega
          omega
        exact_mod_cast this
      have hxN : x < N + 1 := Nat.lt_floor_add_one x
      rw [le_div_iff₀ hx]
      nlinarith

theorem typeILog_eq_sum {α x : ℝ} (hx : 0 < x) (D : ℝ) :
    typeILog α x D = ∑ m ∈ Icc 1 ⌊D⌋₊,
      if Odd m then (μ m : ℂ) * ToddG (eta2log (x / m)) α x m else 0 := by
  rw [typeILog]
  refine sum_congr rfl fun m hm => ?_
  split_ifs
  · rw [innerLog_eq_ToddG hx (mem_Icc.1 hm).1]
  · rfl

/-- `‖T_{m,∘}‖` for the smoothing `η_(x/m)`, indexed by integers. -/
noncomputable def TLn (α x : ℝ) (n : ℤ) : ℝ := ‖ToddG (eta2log (x / n.toNat)) α x n.toNat‖

theorem TLn_nonneg (α x : ℝ) (n : ℤ) : 0 ≤ TLn α x n := norm_nonneg _

/-- [B, p. 67]: `|T_{m,∘}| ≤ log(x/m) · minA(x/2m + |η'|₁/2, (m/x)(c₀/2), sin²)` for `x/m ≥ 4`. -/
theorem norm_ToddL_le_minA {α x δ : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x)
    (h2α : 2 * α = a / q + δ / x + k) {m : ℕ} (hm : 1 ≤ m) (hmx : 4 * m ≤ x) {A C : ℝ}
    (hA : x / (2 * m) + eta2'L1 / 2 ≤ A) (hC : m / x * (c₀ / 2) ≤ C) :
    ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * minA A C (Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 4 ≤ x / m := by rw [le_div_iff₀ (by linarith)]; linarith
  have hL : 0 ≤ Real.log (x / m) := Real.log_nonneg (by linarith)
  have hsd := smoothData_eta2log hρ
  have hs := sin_sq_two_pi_mul h2α (m : ℝ) ⟨m, by simp⟩
  obtain ⟨h1, h2⟩ := hsd.norm_ToddG_le hx hm α
  push_cast at hs ⊢
  have h1' : ‖ToddG (eta2log (x / m)) α x m‖ ≤ Real.log (x / m) * A := by
    refine h1.trans ?_
    have : x / (2 * m) * Real.log (x / m) + eta2'L1 * Real.log (x / m) / 2 =
        Real.log (x / m) * (x / (2 * m) + eta2'L1 / 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hA hL
  unfold minA
  split_ifs with h0
  · exact h1'
  · have hne : Real.sin (2 * π * m * α) ≠ 0 := by
      intro h; apply h0; rw [← hs, h]; ring
    rw [mul_min_of_nonneg _ _ hL]
    refine le_min h1' ?_
    refine (h2 hne).2.trans ?_
    rw [hs]
    have : m / x * (c₀ * Real.log (x / m) / 2) / Real.sin (π * (a / q + δ / x) * m) ^ 2 =
        Real.log (x / m) * (m / x * (c₀ / 2) / Real.sin (π * (a / q + δ / x) * m) ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC (sq_nonneg _)) hL

/-- The second and third bounds, with the factor `log(x/m)`. -/
theorem norm_ToddL_le_min_sin {α x δ : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x)
    (h2α : 2 * α = a / q + δ / x + k) {m : ℕ} (hm : 1 ≤ m) (hmx : 4 * m ≤ x)
    (hne : Real.sin (π * (a / q + δ / x) * (m : ℤ)) ≠ 0) {A B C : ℝ}
    (hA : x / (2 * m) + eta2'L1 / 2 ≤ A) (hB : eta2'L1 / 2 ≤ B) (hC : m / x * (c₀ / 2) ≤ C) :
    ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * min A (C / Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) ∧
    ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * min (B / |Real.sin (π * (a / q + δ / x) * (m : ℤ))|)
        (C / Real.sin (π * (a / q + δ / x) * (m : ℤ)) ^ 2) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 4 ≤ x / m := by rw [le_div_iff₀ (by linarith)]; linarith
  have hL : 0 ≤ Real.log (x / m) := Real.log_nonneg (by linarith)
  have hsd := smoothData_eta2log hρ
  have hs := sin_sq_two_pi_mul h2α (m : ℝ) ⟨m, by simp⟩
  push_cast at hs hne ⊢
  have habs : |Real.sin (2 * π * m * α)| = |Real.sin (π * (a / q + δ / x) * m)| := by
    rw [← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs, hs]
  have hne' : Real.sin (2 * π * m * α) ≠ 0 := by
    intro h; apply hne; rw [← abs_eq_zero, ← habs, h, abs_zero]
  obtain ⟨h1, h2⟩ := hsd.norm_ToddG_le hx hm α
  obtain ⟨h2a, h2b⟩ := h2 hne'
  have hA' : ‖ToddG (eta2log (x / m)) α x m‖ ≤ Real.log (x / m) * A := by
    refine h1.trans ?_
    have : x / (2 * m) * Real.log (x / m) + eta2'L1 * Real.log (x / m) / 2 =
        Real.log (x / m) * (x / (2 * m) + eta2'L1 / 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hA hL
  have hC' : ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * (C / Real.sin (π * (a / q + δ / x) * m) ^ 2) := by
    refine h2b.trans ?_; rw [hs]
    have : m / x * (c₀ * Real.log (x / m) / 2) / Real.sin (π * (a / q + δ / x) * m) ^ 2 =
        Real.log (x / m) * (m / x * (c₀ / 2) / Real.sin (π * (a / q + δ / x) * m) ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC (sq_nonneg _)) hL
  have hB' : ‖ToddG (eta2log (x / m)) α x m‖ ≤
      Real.log (x / m) * (B / |Real.sin (π * (a / q + δ / x) * m)|) := by
    refine h2a.trans ?_; rw [habs]
    have : eta2'L1 * Real.log (x / m) / 2 / |Real.sin (π * (a / q + δ / x) * m)| =
        Real.log (x / m) * (eta2'L1 / 2 / |Real.sin (π * (a / q + δ / x) * m)|) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hB (abs_nonneg _)) hL
  rw [mul_min_of_nonneg _ _ hL, mul_min_of_nonneg _ _ hL]
  exact ⟨le_min hA' hC', le_min hB' hC'⟩


/-- `[m odd] μ(qm)/m · w(m) = μ(q) [(m, 2q) = 1] μ(m)/m · w(m)` for `q` odd. -/
theorem moebius_odd_term_w {q : ℕ} (hq : Odd q) (m : ℕ) (w : ℝ) :
    (if Odd m then ((μ (q * m) : ℤ) : ℝ) / m * w else 0) =
      (μ q : ℝ) * (if Nat.Coprime m (2 * q) then (μ m : ℝ) / m * w else 0) := by
  have h := moebius_odd_term hq m
  by_cases hm : Odd m
  · rw [if_pos hm] at h ⊢
    by_cases hc : Nat.Coprime m (2 * q)
    · rw [if_pos hc] at h ⊢
      rw [h]; ring
    · rw [if_neg hc] at h ⊢
      rw [h]; ring
  · rw [if_neg hm]
    have hc : ¬ Nat.Coprime m (2 * q) := fun hc =>
      hm (Nat.coprime_two_right.1 (Nat.Coprime.coprime_mul_right_right hc))
    rw [if_neg hc, mul_zero]

theorem mul_log_le_inv_e {u : ℝ} (hu : 0 < u) : u * (-Real.log u) ≤ 1 / rexp 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (rexp 1 * u) by positivity)
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul (by positivity)
    hu.ne', Real.log_exp] at h
  have : u * (1 / (rexp 1 * u)) = 1 / rexp 1 := by field_simp
  nlinarith

/-- The main part of `typeILog`: `∑_{m ≤ M, m odd, q | m} μ(m) T_{m,∘}`, indexed by `m = qm'`. -/
noncomputable def mainPartL (α x M : ℝ) (q : ℕ) : ℂ :=
  ∑ m' ∈ Icc 1 ⌊M / q⌋₊, if Odd (q * m') then
    (μ (q * m') : ℂ) * ToddG (eta2log (x / (q * m' : ℕ))) α x (q * m') else 0

/-- **[B, (4.40)], corrected** (see `bound_4_40`): the terms with `q ∣ m ≤ M` of (4.39). -/
theorem norm_mainPartL_le {α x δ M D : ℝ} {a k : ℤ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q)
    (h2α : 2 * α = a / q + δ / x + k) (hM0 : 0 ≤ M) (hMδ : |δ| * M ≤ x / 2) (hMD : M ≤ D)
    (hD4 : D ≤ x / 4) (hDe : D ≤ x / rexp 1) :
    ‖mainPartL α x M q‖ ≤
      x / (2 * q) * minInv c₀ (π * δ) * |muSum M q (2 * q) fun m => Real.log (x / (m * q))| +
        x / (2 * q) * ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ *
          |muSum M q (2 * q) fun _ => 1| +
        c₀ * (1 / 2 - 2 / π ^ 2) *
          (D ^ 2 / (4 * q * x) * Real.log (rexp (1 / 2) * x / D) + 1 / rexp 1) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c₀_pos
  have hpi4 : (0 : ℝ) ≤ 1 / 2 - 2 / π ^ 2 := by
    have := Real.pi_gt_three
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have he1 : (1 : ℝ) < rexp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); have := Real.exp_pos 1
    linarith [Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num)]
  have hD0' : 0 ≤ D := hM0.trans hMD
  have hlogD : 0 ≤ Real.log (rexp (1 / 2) * x / D) ∨ D = 0 := by
    rcases eq_or_lt_of_le hD0' with h | h
    · right; exact h.symm
    · left; apply Real.log_nonneg
      rw [le_div_iff₀ h, one_mul]
      have : D ≤ x := hDe.trans (div_le_self hx.le he1.le)
      have : 1 ≤ rexp (1 / 2) := Real.one_le_exp (by norm_num)
      nlinarith
  have hRHS3 : 0 ≤ c₀ * (1 / 2 - 2 / π ^ 2) *
      (D ^ 2 / (4 * q * x) * Real.log (rexp (1 / 2) * x / D) + 1 / rexp 1) := by
    apply mul_nonneg (mul_nonneg hc0.le hpi4)
    rcases hlogD with h | h
    · exact add_nonneg (mul_nonneg (by positivity) h) (by positivity)
    · rw [h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
        zero_mul, zero_add]; positivity
  have hRHS1 : 0 ≤ x / (2 * q) * minInv c₀ (π * δ) *
      |muSum M q (2 * q) fun m => Real.log (x / (m * q))| :=
    mul_nonneg (mul_nonneg (by positivity) (minInv_nonneg _ _ hc0.le)) (abs_nonneg _)
  have hRHS2 : 0 ≤ x / (2 * q) * ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ *
      |muSum M q (2 * q) fun _ => 1| := by positivity
  rcases Nat.even_or_odd q with hqe | hqo
  · have : mainPartL α x M q = 0 := by
      refine sum_eq_zero fun m' _ => ?_
      rw [if_neg]; rw [Nat.not_odd_iff_even]; exact hqe.mul_right m'
    rw [this, norm_zero]; linarith
  set N := ⌊M / q⌋₊
  have hNM : (N : ℝ) ≤ M / q := Nat.floor_le (by positivity)
  have hqN : (q : ℝ) * N ≤ M := by rw [le_div_iff₀ hq0] at hNM; linarith
  -- Per-term data.
  have hT : ∀ m' : ℕ, ∃ E : ℂ, Odd m' → 1 ≤ m' → m' ≤ N →
      ToddG (eta2log (x / (q * m' : ℕ))) α x (q * m') = e ((a + k * q) / 2) *
        ((x / (2 * (q * m' : ℕ)) : ℝ) * ghat (eta2log (x / (q * m' : ℕ))) (-(δ / 2)) + E) ∧
      ‖E‖ ≤ (q * m' : ℕ) / x * (c₀ * Real.log (x / (q * m' : ℕ)) / (2 * π ^ 2)) * (π ^ 2 - 4) := by
    intro m'
    by_cases h : Odd m' ∧ 1 ≤ m' ∧ m' ≤ N
    · have hm'N : (m' : ℝ) ≤ N := by exact_mod_cast h.2.2
      have hqm : ((q * m' : ℕ) : ℝ) ≤ M := by push_cast; nlinarith
      have hρ : 4 ≤ x / (q * m' : ℕ) := by
        have : (0 : ℝ) < (q * m' : ℕ) := by
          have : 1 ≤ q * m' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
          exact_mod_cast this
        rw [le_div_iff₀ this]; linarith
      have hr : |δ * (q * m' : ℕ) / x| ≤ 1 / 2 := by
        rw [abs_div, abs_mul, abs_of_pos hx, Nat.abs_cast, div_le_iff₀ hx]
        nlinarith [abs_nonneg δ]
      obtain ⟨E, hE1, hE2⟩ := ToddG_main (smoothData_eta2log hρ) hx hq h.1 h2α hr
      exact ⟨E, fun _ _ _ => ⟨hE1, hE2⟩⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose E hE using hT
  set κ := e ((a + k * q) / 2)
  set η0 := eta2hat (-(δ / 2))
  set ηL := ghat (fun t => Real.log t * eta2 t) (-(δ / 2))
  have hsplit : mainPartL α x M q = κ * (((x / (2 * q) : ℝ) : ℂ) * ηL *
        ((∑ m' ∈ Icc 1 N, (if Odd m' then ((μ (q * m') : ℤ) : ℝ) / m' * 1 else 0) : ℝ) : ℂ) +
      ((x / (2 * q) : ℝ) : ℂ) * η0 *
        ((∑ m' ∈ Icc 1 N, (if Odd m' then ((μ (q * m') : ℤ) : ℝ) / m' *
          Real.log (x / (m' * q)) else 0) : ℝ) : ℂ) +
      ∑ m' ∈ Icc 1 N, (if Odd m' then (μ (q * m') : ℂ) * E m' else 0)) := by
    rw [mainPartL, Complex.ofReal_sum, Complex.ofReal_sum, mul_sum, mul_sum, ← sum_add_distrib,
      ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun m' hm' => ?_
    have hm'N : m' ≤ N := (mem_Icc.1 hm').2
    have hm'1 : 1 ≤ m' := (mem_Icc.1 hm').1
    have hodd : Odd (q * m') ↔ Odd m' := by
      rw [Nat.odd_mul]; exact ⟨fun h => h.2, fun h => ⟨hqo, h⟩⟩
    by_cases ho : Odd m'
    · rw [if_pos (hodd.2 ho), if_pos ho, if_pos ho, if_pos ho, (hE m' ho hm'1 hm'N).1]
      have hm'R : (0 : ℝ) < m' := by exact_mod_cast hm'1
      have hqm : ((q * m' : ℕ) : ℝ) = q * m' := by push_cast; ring
      have hρ : 4 ≤ x / (q * m' : ℕ) := by
        have hqmR : ((q * m' : ℕ) : ℝ) ≤ M := by
          push_cast; have : (m' : ℝ) ≤ N := by exact_mod_cast hm'N
          nlinarith
        rw [le_div_iff₀ (by rw [hqm]; positivity)]; linarith
      rw [ghat_eta2log hρ, hqm, show x / (m' * q) = x / (q * m') by ring]
      push_cast
      field_simp
      ring
    · rw [if_neg (fun h => ho (hodd.1 h)), if_neg ho, if_neg ho, if_neg ho]; simp
  rw [hsplit, norm_mul, norm_e, one_mul]
  set XL : ℂ := ((x / (2 * q) : ℝ) : ℂ) * ηL *
        ((∑ m' ∈ Icc 1 N, (if Odd m' then ((μ (q * m') : ℤ) : ℝ) / m' * 1 else 0) : ℝ) : ℂ)
  set X0 : ℂ := ((x / (2 * q) : ℝ) : ℂ) * η0 *
        ((∑ m' ∈ Icc 1 N, (if Odd m' then ((μ (q * m') : ℤ) : ℝ) / m' *
          Real.log (x / (m' * q)) else 0) : ℝ) : ℂ)
  set XE : ℂ := ∑ m' ∈ Icc 1 N, (if Odd m' then (μ (q * m') : ℂ) * E m' else 0)
  have hBL : ‖XL‖ ≤ x / (2 * q) * ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ *
      |muSum M q (2 * q) fun _ => 1| := by
    simp only [XL]
    have hmu : (∑ m' ∈ Icc 1 N, (if Odd m' then ((μ (q * m') : ℤ) : ℝ) / m' * 1 else 0)) =
        (μ q : ℝ) * muSum M q (2 * q) fun _ => 1 := by
      rw [muSum, mul_sum]
      exact sum_congr rfl fun m' _ => moebius_odd_term_w hqo m' 1
    have hηL : ηL = fourier (fun t => Real.log t * eta2 t) (-(δ / 2)) := by
      simp only [ηL, ghat]; rw [fourier_eq_integral_e]; rfl
    rw [hmu, hηL, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity), abs_mul]
    have hmuq : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc x / (2 * q) * ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ *
          (|(μ q : ℝ)| * |muSum M q (2 * q) fun _ => 1|)
        ≤ x / (2 * q) * ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ *
          (1 * |muSum M q (2 * q) fun _ => 1|) := by gcongr
      _ = _ := by ring
  have hA0 : ‖X0‖ ≤ x / (2 * q) * minInv c₀ (π * δ) *
      |muSum M q (2 * q) fun m => Real.log (x / (m * q))| := by
    simp only [X0]
    have hmu : (∑ m' ∈ Icc 1 N, (if Odd m' then ((μ (q * m') : ℤ) : ℝ) / m' *
          Real.log (x / (m' * q)) else 0)) =
        (μ q : ℝ) * muSum M q (2 * q) fun m => Real.log (x / (m * q)) := by
      rw [muSum, mul_sum]
      exact sum_congr rfl fun m' _ => moebius_odd_term_w hqo m' _
    rw [hmu, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity), abs_mul]
    have hmuq : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h1 := norm_eta2hat_le_minInv δ
    have := minInv_nonneg c₀ (π * δ) hc0.le
    calc x / (2 * q) * ‖η0‖ * (|(μ q : ℝ)| * |muSum M q (2 * q) fun m => Real.log (x / (m * q))|)
        ≤ x / (2 * q) * minInv c₀ (π * δ) *
          (1 * |muSum M q (2 * q) fun m => Real.log (x / (m * q))|) := by gcongr
      _ = _ := by ring
  have hCE : ‖XE‖ ≤ c₀ * (1 / 2 - 2 / π ^ 2) *
      (D ^ 2 / (4 * q * x) * Real.log (rexp (1 / 2) * x / D) + 1 / rexp 1) := by
    simp only [XE]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ m' ∈ Icc 1 N, ‖(if Odd m' then (μ (q * m') : ℂ) * E m' else 0)‖ ≤
        c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) *
          (if Odd m' then ((q : ℝ) * m') * (Real.log x - Real.log (q * m')) else 0) := by
      intro m' hm'
      by_cases ho : Odd m'
      · rw [if_pos ho, if_pos ho, norm_mul]
        have hmu : ‖(μ (q * m') : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hE2 := (hE m' ho (mem_Icc.1 hm').1 (mem_Icc.1 hm').2).2
        have hm'R : (0 : ℝ) < m' := by exact_mod_cast (mem_Icc.1 hm').1
        calc ‖(μ (q * m') : ℂ)‖ * ‖E m'‖ ≤ 1 * ‖E m'‖ := by gcongr
          _ ≤ _ := by
            rw [one_mul]; refine hE2.trans (le_of_eq ?_)
            push_cast
            rw [Real.log_div hx.ne' (by positivity : (0:ℝ) < q * m').ne']; field_simp
      · rw [if_neg ho, if_neg ho, norm_zero, mul_zero]
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hpi2 : (0 : ℝ) ≤ π ^ 2 - 4 := by have := Real.pi_gt_three; nlinarith
    have hk : 0 ≤ c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) := by positivity
    rcases eq_or_lt_of_le hM0 with hM | hM
    · -- `M = 0`: no terms.
      have hN : N = 0 := by simp [N, ← hM]
      rw [hN, Finset.Icc_eq_empty (by norm_num), sum_empty, mul_zero]; exact hRHS3
    have hsum := sum_odd_mul_log_le hx hq hM hqN (hMD.trans hDe)
    have hDx : D ≤ x := hDe.trans (div_le_self hx.le he1.le)
    have h1 : M / x * (Real.log x - Real.log M) ≤ 1 / rexp 1 := by
      have := mul_log_le_inv_e (show 0 < M / x by positivity)
      rw [Real.log_div hM.ne' hx.ne'] at this; linarith
    have h2 : M ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log M) ≤
        D ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log D) := by
      have := F₂_mono hx hM hMD hDx
      have e : ∀ t : ℝ, t ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log t) =
          (t ^ 2 / 2 * (1 / 2 + Real.log x - Real.log t)) / (2 * q) := fun t => by field_simp; ring
      rw [e, e]; gcongr
    have hD0 : 0 < D := hM.trans_le hMD
    have hlogeq : Real.log (rexp (1 / 2) * x / D) = 1 / 2 + Real.log x - Real.log D := by
      rw [Real.log_div (by positivity) hD0.ne', Real.log_mul (by positivity) hx.ne', Real.log_exp]
    rw [hlogeq]
    calc c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) *
          ∑ m' ∈ Icc 1 N, (if Odd m' then ((q : ℝ) * m') * (Real.log x - Real.log (q * m')) else 0)
        ≤ c₀ * (π ^ 2 - 4) / (2 * π ^ 2 * x) *
          (M * (Real.log x - Real.log M) + M ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log M)) := by
          gcongr
      _ = c₀ * (π ^ 2 - 4) / (2 * π ^ 2) *
          (M / x * (Real.log x - Real.log M) + M ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log M) / x) := by
          field_simp
      _ ≤ c₀ * (π ^ 2 - 4) / (2 * π ^ 2) *
          (1 / rexp 1 + D ^ 2 / (4 * q) * (1 / 2 + Real.log x - Real.log D) / x) := by
          gcongr
      _ = _ := by field_simp; ring

  calc ‖XL + X0 + XE‖ ≤ ‖XL‖ + ‖X0‖ + ‖XE‖ := norm_add₃_le
    _ ≤ _ := by linarith

end TernaryGoldbach.MinorArcs
