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


/-- **Range (R1)** of [B, Lemma 4.2.3], i.e. [B, (4.46)]:
`∑_{m ≤ min(q/2, D)} |T_{m,∘}| ≤ (2|η'|₁/π) q max(1, log(c₀e³q²/(4π|η'|₁x))) log x`. -/
theorem sum_R1L {α x δ Q D : ℝ} {a k : ℤ} {q : ℕ} (hx : 1 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) (hD4 : D ≤ x / 4) :
    ∑ n ∈ Ioc 0 ⌊min ((q : ℝ) / 2) D⌋, TLn α x n ≤
      2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) *
        Real.log x := by
  have hx0 : 0 < x := by linarith
  have happ := approx_of hq hcop hqQ hδ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hV := eta2'L1_pos
  have hc0 := c₀_pos
  have hlx : 0 < Real.log x := Real.log_pos hx
  set B := eta2'L1 / 2
  set C := c₀ * q / (4 * x)
  have h13 := (lemma_4_1_3 happ (y₁ := 0) (y₂ := q / 2) le_rfl (by positivity) (by linarith)
    (by linarith) (B := Real.log x * B) (C := Real.log x * C) (by positivity) (by positivity)).1
  rw [Int.floor_zero] at h13
  have hsub : Ioc 0 ⌊min ((q : ℝ) / 2) D⌋ ⊆ Ioc 0 ⌊(q : ℝ) / 2⌋ :=
    Ioc_subset_Ioc le_rfl (Int.floor_mono (min_le_left _ _))
  have hterm : ∀ n ∈ Ioc 0 ⌊min ((q : ℝ) / 2) D⌋, TLn α x n ≤ (if (q : ℤ) ∣ n then 0 else
      min (Real.log x * B / |Real.sin (π * (a / q + δ / x) * n)|)
        (Real.log x * C / Real.sin (π * (a / q + δ / x) * n) ^ 2)) := by
    intro n hn
    rw [mem_Ioc] at hn
    have hnmin : (n : ℝ) ≤ min ((q : ℝ) / 2) D := (Int.cast_le.2 hn.2).trans (Int.floor_le _)
    have hnq : (n : ℝ) ≤ q / 2 := hnmin.trans (min_le_left _ _)
    have hnD : (n : ℝ) ≤ D := hnmin.trans (min_le_right _ _)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hndvd : ¬ (q : ℤ) ∣ n := by
      intro ⟨t, ht⟩
      have : (n : ℝ) = q * t := by exact_mod_cast ht
      have ht1 : (1 : ℤ) ≤ t := by
        by_contra h; push Not at h
        have : (t : ℝ) ≤ 0 := by exact_mod_cast (by omega : t ≤ 0)
        nlinarith
      have : (q : ℝ) ≤ n := by rw [this]; nlinarith [show (1 : ℝ) ≤ t by exact_mod_cast ht1]
      linarith
    rw [ite_eq_right hndvd]
    have hm : 1 ≤ n.toNat := by omega
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
    have hmR : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast hcast
    have hmx : 4 * ((n.toNat : ℕ) : ℝ) ≤ x := by rw [hmR]; linarith
    have hne : Real.sin (π * (a / q + δ / x) * ((n.toNat : ℕ) : ℤ)) ≠ 0 := by
      rw [hcast]
      exact sin_ne_zero_of_approx happ hndvd (by rw [abs_of_pos (by linarith)]; linarith)
    have := (norm_ToddL_le_min_sin hx0 h2α hm hmx hne (A := x / (2 * n.toNat) + eta2'L1 / 2)
      (B := B) (C := C) le_rfl le_rfl (by
        rw [hmR]; simp only [C]
        rw [show c₀ * q / (4 * x) = q / 2 / x * (c₀ / 2) by ring]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnq hx0.le) (by positivity))).2
    rw [hcast] at this
    have hL : Real.log (x / ((n.toNat : ℕ) : ℝ)) ≤ Real.log x := by
      rw [hmR]; exact Real.log_le_log (by positivity) (div_le_self hx0.le hn1)
    refine (le_trans (show TLn α x n = ‖ToddG (eta2log (x / (n.toNat : ℕ))) α x n.toNat‖ from rfl).le
      this).trans ?_
    rw [mul_div_assoc, mul_div_assoc, ← mul_min_of_nonneg _ _ hlx.le]
    exact mul_le_mul_of_nonneg_right hL (le_min (by positivity) (by positivity))
  refine (sum_le_sum hterm).trans ((sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by
    split_ifs; exacts [le_rfl, le_min (by positivity) (by positivity)]).trans (h13.trans ?_))
  have hX : 0 < c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x) := by positivity
  have harg : Real.log x * C * rexp 3 * q / (Real.log x * B * π) =
      2 * (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x)) := by
    simp only [B, C]; field_simp
  rw [harg]
  calc 2 * (Real.log x * B) * q / π * max 2 (Real.log (2 * (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))))
      ≤ 2 * (Real.log x * B) * q / π * (2 * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x)))) :=
        mul_le_mul_of_nonneg_left (max_log_two_mul_le hX) (by positivity)
    _ = _ := by simp only [B]; ring


theorem c₂_lt_one : c₂ < 1 := by
  unfold c₂
  have hc0 : (5.6 : ℝ) < √c₀ := by
    rw [Real.lt_sqrt (by norm_num)]; unfold c₀; norm_num
  have hpi := Real.pi_lt_d2
  rw [div_lt_one (by positivity)]
  linarith

set_option maxHeartbeats 1000000 in
/-- **Range (R2)** of [B, Lemma 4.2.3], i.e. [B, (4.47)] (with `log(2ex/c₂)` in the last term,
see `bound_4_41`): for `q/2 < D' ≤ min(Q/2, c₂x/q, x/4, x/e)`,
`∑_{q/2 < m ≤ D', q ∤ m} |T_{m,∘}| ≤ (5c₀c₂/3π²)(D' log(√e x/D') + 4√(2c₂x) log(2ex/c₂))`. -/
theorem sum_R2L {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 1 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) {D' : ℝ} (hD'q : (q : ℝ) / 2 < D') (hD'Q : D' ≤ Q / 2)
    (hD'c : D' ≤ c₂ * x / q) (hD'4 : D' ≤ x / 4) (hD'e : D' ≤ x / rexp 1) :
    ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, (if (q : ℤ) ∣ n then 0 else TLn α x n) ≤
      5 * c₀ * c₂ / (3 * π ^ 2) * (D' * Real.log (rexp (1 / 2) * x / D') +
        4 * √(2 * c₂ * x) * Real.log (2 * rexp 1 * x / c₂)) := by
  have hx0 : 0 < x := by linarith
  have happ := approx_of hq hcop hqQ hδ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hV := eta2'L1_pos
  have hc0 := c₀_pos
  have hc2 := c₂_pos
  have hD'0 : 0 < D' := by linarith
  have he1 : (1 : ℝ) < rexp 1 := by
    linarith [Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num)]
  have hD'x : D' ≤ x := hD'e.trans (div_le_self hx0.le he1.le)
  set J := ⌈(D' - q / 2) / q⌉₊
  have hblocks := sum_Ioc_le_blocks (G := fun n => if (q : ℤ) ∣ n then 0 else TLn α x n)
    (fun n => by split_ifs; exacts [le_rfl, TLn_nonneg _ _ _]) hq J (q / 2) D' (nblocks_spec hq0)
  refine hblocks.trans ?_
  set A := x / 2 + eta2'L1 / 2
  -- Each block, with the weight `log(x/((j+½)q))`.
  have hblock : ∀ j ∈ range J,
      ∑ n ∈ Ioc ⌊(q : ℝ) / 2 + j * q⌋ ⌊min ((q : ℝ) / 2 + (j + 1) * q) D'⌋,
          (if (q : ℤ) ∣ n then 0 else TLn α x n) ≤
        10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) *
          (((j : ℝ) + 3 / 2) * (Real.log x - Real.log ((j + 1 / 2) * q))) := by
    intro j hj
    set y₁ := (q : ℝ) / 2 + j * q
    set y₂ := min ((q : ℝ) / 2 + (j + 1) * q) D'
    set w := Real.log x - Real.log ((j + 1 / 2) * q)
    have hy1 : y₁ = (j + 1 / 2) * q := by simp only [y₁]; ring
    have hy1D : y₁ < D' := lt_of_lt_nblocks hq0 (mem_range.1 hj)
    have hy10 : 0 < y₁ := by positivity
    have hw : 0 ≤ w := by
      simp only [w]; rw [← hy1]; linarith [Real.log_le_log hy10 (hy1D.le.trans hD'x)]
    set C := c₀ / 2 * ((q : ℝ) / 2 + (j + 1) * q) / x
    have hbound : 0 ≤ 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (((j : ℝ) + 3 / 2) * w) := by positivity
    rcases le_or_gt y₂ y₁ with h12 | h12
    · rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono h12))]; simpa using hbound
    have hy₂ : y₂ ≤ Q / 2 := (min_le_right _ _).trans hD'Q
    have h12' := (lemma_4_1_2 happ (y₁ := y₁) (y₂ := y₂) hy10.le h12
      (by simp only [y₁, y₂]; have := min_le_left ((q : ℝ) / 2 + (j + 1) * q) D'; linarith)
      hy₂ (A := w * A) (C := w * C) (by positivity) (by positivity))
    have hterm : ∀ n ∈ Ioc ⌊y₁⌋ ⌊y₂⌋, (if (q : ℤ) ∣ n then 0 else TLn α x n) ≤
        (if (q : ℤ) ∣ n then 0 else min (w * A) (w * C / Real.sin (π * (a / q + δ / x) * n) ^ 2)) := by
      intro n hn
      split_ifs with hdvd
      · exact le_rfl
      rw [mem_Ioc] at hn
      have hyn : y₁ < n := by
        have := Int.lt_floor_add_one y₁
        have : ((⌊y₁⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
        linarith
      have hn1 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
      have hnR : (n : ℝ) ≤ y₂ := (Int.cast_le.2 hn.2).trans (Int.floor_le _)
      have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn1.le
      have hmR : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast hcast
      have hm : 1 ≤ n.toNat := by omega
      have hmx : 4 * ((n.toNat : ℕ) : ℝ) ≤ x := by
        rw [hmR]; linarith [hnR.trans (min_le_right _ _)]
      have hne : Real.sin (π * (a / q + δ / x) * ((n.toNat : ℕ) : ℤ)) ≠ 0 := by
        rw [hcast]
        exact sin_ne_zero_of_approx happ hdvd (by
          rw [abs_of_pos (by exact_mod_cast hn1)]; linarith [hnR.trans hy₂])
      have := (norm_ToddL_le_min_sin hx0 h2α hm hmx hne (A := A) (B := eta2'L1 / 2) (C := C)
        (by
          rw [hmR]; simp only [A]
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          have : x / (2 * n) ≤ x / 2 := div_le_div_of_nonneg_left hx0.le (by norm_num) (by linarith)
          linarith) le_rfl
        (by
          rw [hmR]; simp only [C]
          have : (n : ℝ) ≤ (q : ℝ) / 2 + (j + 1) * q := hnR.trans (min_le_left _ _)
          rw [show c₀ / 2 * ((q : ℝ) / 2 + (j + 1) * q) / x = ((q : ℝ) / 2 + (j + 1) * q) / x * (c₀ / 2)
            by ring]
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this hx0.le) (by positivity))).1
      rw [hcast] at this
      have hL : Real.log (x / ((n.toNat : ℕ) : ℝ)) ≤ w := by
        rw [hmR, Real.log_div hx0.ne' (by linarith)]
        simp only [w]; rw [← hy1]; linarith [Real.log_le_log hy10 hyn.le]
      refine (le_trans (show TLn α x n = ‖ToddG (eta2log (x / (n.toNat : ℕ))) α x n.toNat‖ from
        rfl).le this).trans ?_
      rw [mul_div_assoc, ← mul_min_of_nonneg _ _ hw]
      exact mul_le_mul_of_nonneg_right hL (le_min (by positivity) (by positivity))
    refine (sum_le_sum hterm).trans (h12'.trans ((min_le_left _ _).trans (le_of_eq ?_)))
    simp only [C]; field_simp; ring
  refine (sum_le_sum hblock).trans ?_
  rw [← mul_sum]
  have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.2 (by
    simp only [J, ne_eq, Nat.ceil_eq_zero, not_le]; exact div_pos (by linarith) hq0)
  have hJD : ((J : ℝ) - 1 / 2) * q ≤ D' := by
    have := lt_of_lt_nblocks hq0 (a := q / 2) (b := D') (j := J - 1) (by omega)
    rw [Nat.cast_sub hJ1] at this; push_cast at this; nlinarith
  have hS2 := S2_le hx0 hq0 hJ1 hJD hD'e
  -- The final simplification.
  set s := q * D' / x
  have hs0 : 0 < s := by positivity
  have hsc : s ≤ c₂ := by simp only [s]; rw [div_le_iff₀ hx0]; rw [le_div_iff₀ hq0] at hD'c; linarith
  have hq2 : (q : ℝ) ^ 2 ≤ 2 * c₂ * x := by
    have : (q : ℝ) / 2 < c₂ * x / q := hD'q.trans_le hD'c
    rw [lt_div_iff₀ hq0] at this
    have e : (q : ℝ) ^ 2 = 2 * (q / 2 * q) := by ring
    rw [e]; linarith
  have hΛ : 0 ≤ 1 / 2 + Real.log x - Real.log D' := by linarith [Real.log_le_log hD'0 hD'x]
  have hlog2 : Real.log x - Real.log (q / 2) = Real.log (2 * x / q) := by
    rw [Real.log_div (by positivity) hq0.ne', Real.log_div hq0.ne' (by norm_num), Real.log_mul
      (by norm_num) hx0.ne']; ring
  have hlog2pos : 0 ≤ Real.log (2 * x / q) := Real.log_nonneg (by
    rw [le_div_iff₀ hq0]; nlinarith)
  -- `s Λ ≤ c₂ log(e q/c₂)`.
  have hsΛ : s * (1 / 2 + Real.log x - Real.log D') ≤ c₂ * (1 + Real.log q - Real.log c₂) := by
    have e1 : Real.log x - Real.log D' = Real.log q - Real.log s := by
      simp only [s]; rw [Real.log_div (by positivity) hx0.ne', Real.log_mul hq0.ne' hD'0.ne']; ring
    have hmono := F₁_mono hq0 hs0 hsc (c₂_lt_one.le.trans hq1)
    have : s * (1 / 2 + Real.log x - Real.log D') ≤ s * (1 + Real.log q - Real.log s) := by
      rw [show 1 / 2 + Real.log x - Real.log D' = 1 / 2 + (Real.log q - Real.log s) by linarith]
      exact mul_le_mul_of_nonneg_left (by linarith) hs0.le
    linarith
  have hk : 0 ≤ 5 * c₀ * c₂ / (3 * π ^ 2) := by positivity
  have ha : 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * Real.log (2 * x / q) ≤
      5 * c₀ * c₂ / (3 * π ^ 2) * (4 * q * Real.log (2 * x / q)) := by
    have : 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) ≤ 5 * c₀ * c₂ / (3 * π ^ 2) * (4 * q) := by
      rw [div_le_iff₀ (by positivity)]
      have : (5 * c₀ * c₂ / (3 * π ^ 2) * (4 * q)) * (3 * π ^ 2 * x) = 20 * c₀ * c₂ * q * x := by
        field_simp; ring
      rw [this]
      calc 10 * c₀ * q ^ 3 = 10 * c₀ * q * q ^ 2 := by ring
        _ ≤ 10 * c₀ * q * (2 * c₂ * x) := by gcongr
        _ = 20 * c₀ * c₂ * q * x := by ring
    calc _ ≤ 5 * c₀ * c₂ / (3 * π ^ 2) * (4 * q) * Real.log (2 * x / q) :=
          mul_le_mul_of_nonneg_right this hlog2pos
      _ = _ := by ring
  have hb : 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (2 * D' / q * (1 / 2 + Real.log x - Real.log D')) ≤
      5 * c₀ * c₂ / (3 * π ^ 2) * (4 * q * (1 + Real.log q - Real.log c₂)) := by
    have e : 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (2 * D' / q * (1 / 2 + Real.log x - Real.log D')) =
        20 * c₀ / (3 * π ^ 2) * q * (s * (1 / 2 + Real.log x - Real.log D')) := by
      simp only [s]; field_simp; ring
    rw [e]
    calc 20 * c₀ / (3 * π ^ 2) * q * (s * (1 / 2 + Real.log x - Real.log D'))
        ≤ 20 * c₀ / (3 * π ^ 2) * q * (c₂ * (1 + Real.log q - Real.log c₂)) := by gcongr
      _ = _ := by ring
  have hc : 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (D' ^ 2 / (2 * q ^ 2) * (1 / 2 + Real.log x - Real.log D')) ≤
      5 * c₀ * c₂ / (3 * π ^ 2) * (D' * (1 / 2 + Real.log x - Real.log D')) := by
    have e : 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (D' ^ 2 / (2 * q ^ 2) * (1 / 2 + Real.log x - Real.log D')) =
        5 * c₀ / (3 * π ^ 2) * s * (D' * (1 / 2 + Real.log x - Real.log D')) := by
      simp only [s]; field_simp; ring
    rw [e]
    calc 5 * c₀ / (3 * π ^ 2) * s * (D' * (1 / 2 + Real.log x - Real.log D'))
        ≤ 5 * c₀ / (3 * π ^ 2) * c₂ * (D' * (1 / 2 + Real.log x - Real.log D')) := by gcongr
      _ = _ := by ring
  have hsum2 : Real.log (2 * x / q) + (1 + Real.log q - Real.log c₂) = Real.log (2 * rexp 1 * x / c₂) := by
    rw [Real.log_div (by positivity) hq0.ne', Real.log_div (by positivity) hc2.ne',
      Real.log_mul (by positivity) hx0.ne', Real.log_mul (by positivity) hx0.ne',
      Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]; ring
  have hqsqrt : (q : ℝ) ≤ √(2 * c₂ * x) := Real.le_sqrt_of_sq_le hq2
  have hL2 : 0 ≤ Real.log (2 * rexp 1 * x / c₂) := by
    rw [← hsum2]
    have : 0 ≤ 1 + Real.log q - Real.log c₂ := by
      have := Real.log_nonneg hq1
      have := Real.log_neg hc2 c₂_lt_one
      linarith
    linarith
  have hlogD' : Real.log (rexp (1 / 2) * x / D') = 1 / 2 + Real.log x - Real.log D' := by
    rw [Real.log_div (by positivity) hD'0.ne', Real.log_mul (by positivity) hx0.ne', Real.log_exp]
  rw [hlogD', ← hlog2] at *
  calc 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) *
        ∑ j ∈ range J, ((j : ℝ) + 3 / 2) * (Real.log x - Real.log ((j + 1 / 2) * q))
      ≤ 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (Real.log x - Real.log (q / 2) +
          (2 * D' / q + D' ^ 2 / (2 * q ^ 2)) * (1 / 2 + Real.log x - Real.log D')) := by gcongr
    _ = 10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (Real.log x - Real.log (q / 2)) +
        10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (2 * D' / q * (1 / 2 + Real.log x - Real.log D')) +
        10 * c₀ * q ^ 3 / (3 * π ^ 2 * x) * (D' ^ 2 / (2 * q ^ 2) * (1 / 2 + Real.log x - Real.log D')) := by
        ring
    _ ≤ 5 * c₀ * c₂ / (3 * π ^ 2) * (4 * q * (Real.log x - Real.log (q / 2))) +
        5 * c₀ * c₂ / (3 * π ^ 2) * (4 * q * (1 + Real.log q - Real.log c₂)) +
        5 * c₀ * c₂ / (3 * π ^ 2) * (D' * (1 / 2 + Real.log x - Real.log D')) := by
        gcongr
    _ = 5 * c₀ * c₂ / (3 * π ^ 2) * (D' * (1 / 2 + Real.log x - Real.log D') +
        4 * q * Real.log (2 * rexp 1 * x / c₂)) := by rw [← hsum2, hlog2]; ring
    _ ≤ _ := by gcongr


set_option maxHeartbeats 1000000 in
/-- **Range (R3)** of [B, Lemma 4.2.3], i.e. [B, (4.25), (4.26), (4.48)] with log weights: for
`max(c₂x/q, q/2) ≤ R < D ≤ min(x/4, x/e)`, with `c₁ = 1 + |η'|₁/(x/D)`,
`∑_{R < m ≤ D} |T_{m,∘}| ≤ (3c₁/2)(√(2x/c₂) log(2x/c₂) + (x/q) log(q/c₂) log⁺(D/(c₂x/q)))
+ (2√(c₀c₁)/π)(√3 q log(q/c₂) + D log(ex/D) - R log(ex/R) + (q/2) log(q/c₂) log⁺(D/(q/2)))`. -/
theorem sum_R3L {α x δ Q : ℝ} {a k : ℤ} {q : ℕ} (hx : 1 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) {R D : ℝ} (hRq : (q : ℝ) / 2 ≤ R) (hRc : c₂ * x / q ≤ R)
    (hRD : R < D) (hD4 : D ≤ x / 4) (hDe : D ≤ x / rexp 1) :
    ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, TLn α x n ≤
      3 * (1 + eta2'L1 / (x / D)) / 2 * (√(2 * x / c₂) * Real.log (2 * x / c₂) +
          x / q * Real.log (q / c₂) * logPlus (D / (c₂ * x / q))) +
        2 * √(c₀ * (1 + eta2'L1 / (x / D))) / π * (√3 * q * Real.log (q / c₂) +
          (D * (1 + Real.log x - Real.log D) - R * (1 + Real.log x - Real.log R)) +
          q / 2 * Real.log (q / c₂) * logPlus (D / (q / 2))) := by
  have hx0 : 0 < x := by linarith
  have happ := approx_of hq hcop hqQ hδ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hR0 : 0 < R := by linarith
  have hD0 : 0 < D := by linarith
  have hV := eta2'L1_pos
  have hc0 := c₀_pos
  have hc2 := c₂_pos
  have he1 : (1 : ℝ) < rexp 1 := by
    linarith [Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num)]
  have hDx : D ≤ x := hDe.trans (div_le_self hx0.le he1.le)
  set c₁ := 1 + eta2'L1 / (x / D) with hc₁def
  have hc₁ : 1 ≤ c₁ := by
    simp only [c₁]; have : 0 ≤ eta2'L1 / (x / D) := by positivity
    linarith
  set J := ⌈(D - R) / q⌉₊
  have hblocks := sum_Ioc_le_blocks (G := TLn α x) (TLn_nonneg α x) hq J R D (nblocks_spec hq0)
  refine hblocks.trans ?_
  set lx := Real.log x
  have hblock : ∀ j ∈ range J,
      ∑ n ∈ Ioc ⌊R + j * q⌋ ⌊min (R + (j + 1) * q) D⌋, TLn α x n ≤
        3 * c₁ / 2 * x * ((lx - Real.log (R + j * q)) / (R + j * q)) +
          2 * q * √(c₀ * c₁) / π * (√(1 + q / (R + j * q)) * (lx - Real.log (R + j * q))) := by
    intro j hj
    set y := R + j * q
    have hy0 : 0 < y := by positivity
    have hyD : y < D := lt_of_lt_nblocks hq0 (mem_range.1 hj)
    set w := lx - Real.log y
    have hw : 0 ≤ w := by simp only [w, lx]; linarith [Real.log_le_log hy0 (hyD.le.trans hDx)]
    set A := c₁ * x / (2 * y)
    set C := c₀ / 2 * (y + q) / x
    have h11 := (lemma_4_1_1' happ y (A := A) (C := C) (by positivity) (by positivity))
    have hsub : Ioc ⌊y⌋ ⌊min (R + (j + 1) * q) D⌋ ⊆ Ioc ⌊y⌋ ⌊y + q⌋ := by
      apply Ioc_subset_Ioc le_rfl (Int.floor_mono ?_)
      have := min_le_left (R + (j + 1) * q) D; simp only [y]; linarith
    have hterm : ∀ n ∈ Ioc ⌊y⌋ ⌊min (R + (j + 1) * q) D⌋,
        TLn α x n ≤ w * minA A C (Real.sin (π * (a / q + δ / x) * n) ^ 2) := by
      intro n hn
      rw [mem_Ioc] at hn
      have hyn : y < n := by
        have := Int.lt_floor_add_one y
        have : ((⌊y⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
        linarith
      have hnD : (n : ℝ) ≤ D := (Int.cast_le.2 hn.2).trans ((Int.floor_le _).trans (min_le_right _ _))
      have hnR : (n : ℝ) ≤ y + q := by
        have := (Int.cast_le.2 hn.2).trans (Int.floor_le (min (R + (j + 1) * q) D))
        have := min_le_left (R + (j + 1) * q) D
        simp only [y] at *; push_cast at *; linarith
      have hn1 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
      have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn1.le
      have hmR : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast hcast
      have hm : 1 ≤ n.toNat := by omega
      have hmx : 4 * ((n.toNat : ℕ) : ℝ) ≤ x := by rw [hmR]; linarith
      have := norm_ToddL_le_minA hx0 h2α hm hmx (A := A) (C := C)
        (by
          rw [hmR]; simp only [A, c₁]
          have e : (1 + eta2'L1 / (x / D)) * x / (2 * y) = x / (2 * y) + eta2'L1 * D / (2 * y) := by
            field_simp
          rw [e]
          have h1 : x / (2 * n) ≤ x / (2 * y) := div_le_div_of_nonneg_left hx0.le (by positivity)
            (by linarith)
          have h2 : eta2'L1 / 2 ≤ eta2'L1 * D / (2 * y) := by
            rw [le_div_iff₀ (by positivity)]; nlinarith
          linarith)
        (by
          rw [hmR]; simp only [C]
          rw [show c₀ / 2 * (y + q) / x = (y + q) / x * (c₀ / 2) by ring]
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnR hx0.le) (by positivity))
      rw [hcast] at this
      have hL : Real.log (x / ((n.toNat : ℕ) : ℝ)) ≤ w := by
        rw [hmR, Real.log_div hx0.ne' (by linarith)]
        simp only [w, lx]; linarith [Real.log_le_log hy0 hyn.le]
      refine (le_trans (show TLn α x n = ‖ToddG (eta2log (x / (n.toNat : ℕ))) α x n.toNat‖ from
        rfl).le this).trans ?_
      exact mul_le_mul_of_nonneg_right hL (minA_nonneg (by positivity) (by positivity) (sq_nonneg _))
    have hAC : √(A * C) = √(c₀ * c₁) / 2 * √(1 + q / y) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      have e1 : √(c₀ * c₁) / 2 * √(1 + q / y) * (√(c₀ * c₁) / 2 * √(1 + q / y)) =
          (√(c₀ * c₁) * √(c₀ * c₁)) / 4 * (√(1 + q / y) * √(1 + q / y)) := by ring
      rw [e1, Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by positivity)]
      simp only [A, C]; field_simp; norm_num
    calc ∑ n ∈ Ioc ⌊y⌋ ⌊min (R + (j + 1) * q) D⌋, TLn α x n
        ≤ ∑ n ∈ Ioc ⌊y⌋ ⌊min (R + (j + 1) * q) D⌋,
            w * minA A C (Real.sin (π * (a / q + δ / x) * n) ^ 2) := sum_le_sum hterm
      _ ≤ ∑ n ∈ Ioc ⌊y⌋ ⌊y + q⌋, w * minA A C (Real.sin (π * (a / q + δ / x) * n) ^ 2) :=
          sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
            mul_nonneg hw (minA_nonneg (by positivity) (by positivity) (sq_nonneg _))
      _ = w * ∑ n ∈ Ioc ⌊y⌋ ⌊y + q⌋, minA A C (Real.sin (π * (a / q + δ / x) * n) ^ 2) := by
          rw [mul_sum]
      _ ≤ w * (3 * A + 4 * q / π * √(A * C)) :=
          mul_le_mul_of_nonneg_left (h11.trans (min_le_right _ _)) hw
      _ = _ := by rw [hAC]; simp only [A, w]; field_simp; ring
  refine (sum_le_sum hblock).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.2 (by
    simp only [J, ne_eq, Nat.ceil_eq_zero, not_le]; exact div_pos (by linarith) hq0)
  have hJD : R + ((J : ℝ) - 1) * q ≤ D := by
    have := lt_of_lt_nblocks hq0 (a := R) (b := D) (j := J - 1) (by omega)
    rw [Nat.cast_sub hJ1] at this; push_cast at this; linarith
  obtain ⟨K, hK⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  rw [hK] at hJD ⊢
  push_cast at hJD; simp only [add_sub_cancel_right] at hJD
  set yK := R + K * q
  have hyK0 : 0 < yK := by positivity
  have hyKD : yK ≤ D := hJD
  have hsub3 : Set.Icc R (R + K * q) ⊆ Set.Ioc 0 (rexp 1 * x) := fun t ht =>
    ⟨lt_of_lt_of_le hR0 ht.1, ht.2.trans (hyKD.trans (hDx.trans (by nlinarith)))⟩
  -- (i) `∑ log(x/y)/y`.
  have hF3 := sum_le_of_antitone (F := fun t => -(lx - Real.log t) ^ 2 / 2)
    (f := fun t => (lx - Real.log t) / t) (a := R) hq0 K
    (fun t ht => hasDerivAt_F₃ x (lt_of_lt_of_le hR0 ht.1)) ((antitoneOn_f₃ x hx0).mono hsub3)
  have hlD : 0 ≤ lx - Real.log D := by simp only [lx]; linarith [Real.log_le_log hD0 hDx]
  have hlyK : lx - Real.log yK ≥ lx - Real.log D := by linarith [Real.log_le_log hyK0 hyKD]
  have hlR : lx - Real.log D ≤ lx - Real.log R := by linarith [Real.log_le_log hR0 hRD.le]
  have hF3' : -(lx - Real.log yK) ^ 2 / 2 - -(lx - Real.log R) ^ 2 / 2 ≤
      (Real.log D - Real.log R) * (lx - Real.log R) := by
    nlinarith
  have hi : ∑ j ∈ range (K + 1), (lx - Real.log (R + j * q)) / (R + j * q) ≤
      (lx - Real.log R) / R + (Real.log D - Real.log R) * (lx - Real.log R) / q := by
    rw [sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
    have : ∑ i ∈ range K, (lx - Real.log (R + (i + 1) * q)) / (R + (i + 1) * q) ≤
        (Real.log D - Real.log R) * (lx - Real.log R) / q := by
      rw [le_div_iff₀ hq0, mul_comm]; linarith
    linarith
  -- (ii) `∑ √(1 + q/y) log(x/y)`.
  have hF1 := sum_le_of_antitone (F := fun t => t * (1 + lx - Real.log t))
    (f := fun t => lx - Real.log t) (a := R) hq0 K
    (fun t ht => hasDerivAt_F₁ x (lt_of_lt_of_le hR0 ht.1))
    ((antitoneOn_f₁ x).mono fun t ht => lt_of_lt_of_le hR0 ht.1)
  have hF1mono := F₁_mono hx0 hyK0 hyKD hDx
  have hii : ∑ j ∈ range (K + 1), √(1 + q / (R + j * q)) * (lx - Real.log (R + j * q)) ≤
      √(1 + q / R) * (lx - Real.log R) +
        (D * (1 + lx - Real.log D) - R * (1 + lx - Real.log R)) / q +
        1 / 2 * ((Real.log D - Real.log R) * (lx - Real.log R)) := by
    rw [sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
    have hterm : ∀ i ∈ range K, √(1 + q / (R + (i + 1) * q)) * (lx - Real.log (R + (i + 1) * q)) ≤
        (lx - Real.log (R + (i + 1) * q)) + q / 2 * ((lx - Real.log (R + (i + 1) * q)) / (R + (i + 1) * q)) := by
      intro i _
      have hy : 0 < R + ((i : ℝ) + 1) * q := by positivity
      have hyD : R + ((i : ℝ) + 1) * q ≤ D := by
        have : (i : ℝ) + 1 ≤ K := by
          have := mem_range.1 ‹i ∈ range K›; exact_mod_cast this
        nlinarith
      have hl : 0 ≤ lx - Real.log (R + (i + 1) * q) := by
        simp only [lx]; linarith [Real.log_le_log hy (hyD.trans hDx)]
      have hs : √(1 + q / (R + (i + 1) * q)) ≤ 1 + q / (2 * (R + (i + 1) * q)) := by
        rw [Real.sqrt_le_left (by positivity)]
        have : 0 ≤ q / (R + (i + 1) * q) := by positivity
        have e : q / (2 * (R + (i + 1) * q)) = q / (R + (i + 1) * q) / 2 := by field_simp
        rw [e]; nlinarith [sq_nonneg (q / (R + (i + 1) * q))]
      calc √(1 + q / (R + (i + 1) * q)) * (lx - Real.log (R + (i + 1) * q))
          ≤ (1 + q / (2 * (R + (i + 1) * q))) * (lx - Real.log (R + (i + 1) * q)) :=
            mul_le_mul_of_nonneg_right hs hl
        _ = _ := by field_simp
    refine (add_le_add_left (sum_le_sum hterm) _).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    have h1 : ∑ i ∈ range K, (lx - Real.log (R + (i + 1) * q)) ≤
        (D * (1 + lx - Real.log D) - R * (1 + lx - Real.log R)) / q := by
      rw [le_div_iff₀ hq0, mul_comm]; linarith
    have h2 : q / 2 * ∑ i ∈ range K, (lx - Real.log (R + (i + 1) * q)) / (R + (i + 1) * q) ≤
        1 / 2 * ((Real.log D - Real.log R) * (lx - Real.log R)) := by
      have : q * ∑ i ∈ range K, (lx - Real.log (R + (i + 1) * q)) / (R + (i + 1) * q) ≤
          (Real.log D - Real.log R) * (lx - Real.log R) := by linarith
      linarith
    linarith
  -- Simplify.
  have hlxR : lx - Real.log R ≤ Real.log (q / c₂) := by
    rw [Real.log_div hq0.ne' hc2.ne']
    have := Real.log_le_log (by positivity) hRc
    rw [Real.log_div (by positivity) hq0.ne', Real.log_mul hc2.ne' hx0.ne'] at this
    simp only [lx]; linarith
  have hlxR0 : 0 ≤ lx - Real.log R := by linarith
  have hlDR0 : 0 ≤ Real.log D - Real.log R := by linarith [Real.log_le_log hR0 hRD.le]
  have hlDR1 : Real.log D - Real.log R ≤ logPlus (D / (c₂ * x / q)) := by
    rw [← Real.log_div hD0.ne' hR0.ne']
    exact log_le_logPlus (by positivity) (div_le_div_of_nonneg_left hD0.le (by positivity) hRc)
  have hlDR2 : Real.log D - Real.log R ≤ logPlus (D / (q / 2)) := by
    rw [← Real.log_div hD0.ne' hR0.ne']
    exact log_le_logPlus (by positivity) (div_le_div_of_nonneg_left hD0.le (by positivity) hRq)
  have hxR : x / R ≤ √(2 * x / c₂) := by
    rw [Real.le_sqrt (by positivity) (by positivity), div_pow, div_le_div_iff₀ (by positivity) hc2]
    have h1 : x / R ≤ q / c₂ := by
      rw [div_le_div_iff₀ hR0 hc2]; rw [div_le_iff₀ hq0] at hRc; linarith
    have h2 : x / R ≤ 2 * x / q := by
      rw [div_le_div_iff₀ hR0 hq0]; nlinarith
    have h3 : (x / R) ^ 2 ≤ (q / c₂) * (2 * x / q) := by
      rw [sq]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
    rw [div_pow] at h3
    have e : (q / c₂) * (2 * x / q) = 2 * x / c₂ := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) hc2] at h3; linarith
  have hlogxR : lx - Real.log R ≤ Real.log (2 * x / c₂) := by
    rw [Real.log_div (by positivity) hc2.ne', Real.log_mul (by norm_num) hx0.ne']
    have : Real.log (c₂ / 2) ≤ Real.log R := Real.log_le_log (by positivity) (by
      have := c₂_lt_one; linarith)
    rw [Real.log_div hc2.ne' (by norm_num)] at this
    simp only [lx]; linarith
  have hsqrt3 : √(1 + q / R) ≤ √3 := Real.sqrt_le_sqrt (by
    have : q / R ≤ 2 := by rw [div_le_iff₀ hR0]; linarith
    linarith)
  have hk1 : 0 ≤ 3 * c₁ / 2 := by positivity
  have hk2 : 0 ≤ 2 * √(c₀ * c₁) / π := by positivity
  have hpart1 : 3 * c₁ / 2 * x * ∑ j ∈ range (K + 1), (lx - Real.log (R + j * q)) / (R + j * q) ≤
      3 * c₁ / 2 * (√(2 * x / c₂) * Real.log (2 * x / c₂) +
        x / q * Real.log (q / c₂) * logPlus (D / (c₂ * x / q))) := by
    have e : 3 * c₁ / 2 * x * ((lx - Real.log R) / R + (Real.log D - Real.log R) * (lx - Real.log R) / q) =
        3 * c₁ / 2 * (x / R * (lx - Real.log R) + x / q * (lx - Real.log R) * (Real.log D - Real.log R)) := by
      field_simp
    calc _ ≤ 3 * c₁ / 2 * x * ((lx - Real.log R) / R + (Real.log D - Real.log R) * (lx - Real.log R) / q) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := e
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul hxR hlogxR hlxR0 (Real.sqrt_nonneg _))
          (mul_le_mul (mul_le_mul_of_nonneg_left hlxR (by positivity)) hlDR1 hlDR0 (by
            have := Real.log_nonneg (show (1:ℝ) ≤ q / c₂ by
              rw [le_div_iff₀ hc2]; linarith [c₂_lt_one])
            positivity))) hk1
  have hpart2 : 2 * q * √(c₀ * c₁) / π *
        ∑ j ∈ range (K + 1), √(1 + q / (R + j * q)) * (lx - Real.log (R + j * q)) ≤
      2 * √(c₀ * c₁) / π * (√3 * q * Real.log (q / c₂) +
        (D * (1 + lx - Real.log D) - R * (1 + lx - Real.log R)) +
        q / 2 * Real.log (q / c₂) * logPlus (D / (q / 2))) := by
    have e : 2 * q * √(c₀ * c₁) / π * (√(1 + q / R) * (lx - Real.log R) +
        (D * (1 + lx - Real.log D) - R * (1 + lx - Real.log R)) / q +
        1 / 2 * ((Real.log D - Real.log R) * (lx - Real.log R))) =
        2 * √(c₀ * c₁) / π * (√(1 + q / R) * q * (lx - Real.log R) +
        (D * (1 + lx - Real.log D) - R * (1 + lx - Real.log R)) +
        q / 2 * (lx - Real.log R) * (Real.log D - Real.log R)) := by field_simp
    calc _ ≤ 2 * q * √(c₀ * c₁) / π * (√(1 + q / R) * (lx - Real.log R) +
          (D * (1 + lx - Real.log D) - R * (1 + lx - Real.log R)) / q +
          1 / 2 * ((Real.log D - Real.log R) * (lx - Real.log R))) :=
          mul_le_mul_of_nonneg_left hii (by positivity)
      _ = _ := e
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (mul_le_mul
          (mul_le_mul_of_nonneg_right hsqrt3 hq0.le) hlxR hlxR0 (by positivity)) le_rfl)
          (mul_le_mul (mul_le_mul_of_nonneg_left hlxR (by positivity)) hlDR2 hlDR0 (by
            have := Real.log_nonneg (show (1:ℝ) ≤ q / c₂ by
              rw [le_div_iff₀ hc2]; linarith [c₂_lt_one])
            positivity))) hk2
  linarith

/-- The terms of `typeILog` not in `mainPartL`. -/
noncomputable def restPartL (α x D M : ℝ) (q : ℕ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊D⌋₊, if Odd m ∧ ¬ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M) then (μ m : ℂ) * ToddG (eta2log (x / m)) α x m else 0

theorem typeILog_eq_main_add_rest {α x M D : ℝ} {q : ℕ} (hx : 0 < x) (hq : 1 ≤ q) (hM0 : 0 ≤ M)
    (hMD : M ≤ D) : typeILog α x D = mainPartL α x M q + restPartL α x D M q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [typeILog_eq_sum hx, restPartL, mainPartL]
  have hsplit : ∀ m ∈ Icc 1 ⌊D⌋₊, (if Odd m then (μ m : ℂ) * ToddG (eta2log (x / m)) α x m else 0) =
      (if Odd m ∧ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M) then (μ m : ℂ) * ToddG (eta2log (x / m)) α x m else 0) +
      (if Odd m ∧ ¬ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M) then (μ m : ℂ) * ToddG (eta2log (x / m)) α x m else 0) := by
    intro m _
    by_cases h1 : Odd m <;> by_cases h2 : ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M) <;> simp [h1, h2]
  rw [sum_congr rfl hsplit, sum_add_distrib]
  congr 1
  rw [← sum_filter, ← sum_filter]
  refine (sum_nbij' (fun m => m / q) (fun m' => q * m') ?_ ?_ ?_ ?_ ?_)
  · intro m hm
    simp only [mem_filter, mem_Icc] at hm
    obtain ⟨⟨h1, h2⟩, hodd, ⟨t, rfl⟩, hle⟩ := hm
    simp only [mem_filter, mem_Icc]
    have ht : q * t / q = t := Nat.mul_div_cancel_left t (by omega)
    rw [ht]
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at h1
      · exact h
    refine ⟨⟨ht1, ?_⟩, hodd⟩
    apply Nat.le_floor
    rw [le_div_iff₀ hq0]; push_cast at hle ⊢; linarith
  · intro m' hm'
    simp only [mem_filter, mem_Icc] at hm' ⊢
    obtain ⟨⟨h1, h2⟩, hodd⟩ := hm'
    have hle : ((q * m' : ℕ) : ℝ) ≤ M := by
      have := Nat.floor_le (show 0 ≤ M / q by positivity)
      have h2' : (m' : ℝ) ≤ M / q := le_trans (by exact_mod_cast h2) this
      push_cast; rw [le_div_iff₀ hq0] at h2'; linarith
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩, hodd,
      ⟨m', rfl⟩, hle⟩
    exact Nat.le_floor (hle.trans hMD)
  · intro m hm
    simp only [mem_filter] at hm
    obtain ⟨_, _, hdvd, _⟩ := hm
    exact Nat.mul_div_cancel' hdvd
  · intro m' _; exact Nat.mul_div_cancel_left m' (by omega)
  · intro m hm
    simp only [mem_filter] at hm
    obtain ⟨_, hodd, hdvd, _⟩ := hm
    rw [Nat.mul_div_cancel' hdvd]



theorem c₂_rpow : 5 * c₀ * c₂ / (3 * π ^ 2) * (4 * √(2 * c₂ * x)) =
    20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) * √(2 * x) := by
  have hc2 := c₂_pos
  have e1 : c₂ ^ (3 / 2 : ℝ) = c₂ * √c₂ := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hc2, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [e1, show 2 * c₂ * x = c₂ * (2 * x) by ring, Real.sqrt_mul hc2.le]
  ring

set_option maxHeartbeats 2000000 in
/-- **[B, Lemma 4.2.3], case (b), terms other than the main term**: they contribute at most (4.41)
(in the form `bound_4_41`). -/
theorem norm_restPartL_le_caseB {α x δ Q M D : ℝ} {a k : ℤ} {q : ℕ} (hx : 1 < x) (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hqQ : (q : ℝ) ≤ Q)
    (hδ : |δ / x| * (q * Q) ≤ 1) (hD1 : 1 ≤ D) (hD4 : D ≤ x / 4) (hDe : D ≤ x / rexp 1)
    (hD'Q : min (c₂ * x / q) D ≤ Q / 2) (hMD' : min (c₂ * x / q) D ≤ M) :
    ‖restPartL α x D M q‖ ≤ bound_4_41 x q D := by
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hV := eta2'L1_pos
  have hc0 := c₀_pos
  have hc2 := c₂_pos
  have he1 : (1 : ℝ) < rexp 1 := by
    linarith [Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num)]
  have hDx : D ≤ x := hDe.trans (div_le_self hx0.le he1.le)
  set D' := min (c₂ * x / q) D with hD'def
  have hD'0 : 0 ≤ D' := le_min (by positivity) (by linarith)
  have hD'D : D' ≤ D := min_le_right _ _
  set R := max D' ((q : ℝ) / 2)
  set c₁ := 1 + eta2'L1 / (x / D) with hc₁def
  have hc₁ : 1 ≤ c₁ := by
    simp only [c₁]; have : 0 ≤ eta2'L1 / (x / D) := by positivity
    linarith
  have hsq : √c₀ ≤ √(c₀ * c₁) := Real.sqrt_le_sqrt (by nlinarith)
  -- Step 1.
  set g : ℤ → ℝ := fun n => if ¬ ((q : ℤ) ∣ n ∧ (n : ℝ) ≤ M) then TLn α x n else 0
  have h1 : ‖restPartL α x D M q‖ ≤ ∑ n ∈ Ioc (0 : ℤ) ⌊D⌋, g n := by
    rw [restPartL]
    refine (norm_sum_le _ _).trans ?_
    have hfl : ((⌊D⌋₊ : ℕ) : ℤ) = ⌊D⌋ := Int.natCast_floor_eq_floor (by linarith)
    rw [← hfl, ← sum_Icc_eq_Ioc_int]
    refine sum_le_sum fun m hm => ?_
    simp only [g, TLn, Int.toNat_natCast]
    by_cases h : Odd m ∧ ¬ ((q : ℕ) ∣ m ∧ (m : ℝ) ≤ M)
    · rw [if_pos h, if_pos (by
        intro ⟨hd, hle⟩; exact h.2 ⟨by exact_mod_cast hd, by exact_mod_cast hle⟩), norm_mul]
      have : ‖(μ m : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc ‖(μ m : ℂ)‖ * ‖ToddG (eta2log (x / m)) α x m‖ ≤ 1 * ‖ToddG (eta2log (x / m)) α x m‖ := by
            gcongr
        _ = _ := one_mul _
    · rw [if_neg h, norm_zero]; split_ifs <;> simp [norm_nonneg]
  -- Step 2: split the range.
  have h2 : ∑ n ∈ Ioc (0 : ℤ) ⌊D⌋, g n ≤
      ∑ n ∈ Ioc 0 ⌊min ((q : ℝ) / 2) D⌋, TLn α x n +
      ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, (if (q : ℤ) ∣ n then 0 else TLn α x n) +
      ∑ n ∈ Ioc ⌊R⌋ ⌊D⌋, TLn α x n := by
    have hpt : ∀ n ∈ Ioc (0 : ℤ) ⌊D⌋, g n ≤
        (if n ∈ Ioc 0 ⌊min ((q : ℝ) / 2) D⌋ then TLn α x n else 0) +
        (if n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋ then (if (q : ℤ) ∣ n then 0 else TLn α x n) else 0) +
        (if n ∈ Ioc ⌊R⌋ ⌊D⌋ then TLn α x n else 0) := by
      intro n hn
      have hT := TLn_nonneg α x n
      have hgT : g n ≤ TLn α x n := by simp only [g]; split_ifs <;> linarith
      rw [mem_Ioc] at hn
      by_cases hA : n ≤ ⌊(q : ℝ) / 2⌋
      · have hmin : n ≤ ⌊min ((q : ℝ) / 2) D⌋ := by
          rw [Int.le_floor]
          exact le_min ((Int.cast_le.2 hA).trans (Int.floor_le _))
            ((Int.cast_le.2 hn.2).trans (Int.floor_le _))
        rw [if_pos (mem_Ioc.2 ⟨hn.1, hmin⟩)]
        have : 0 ≤ (if n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋ then (if (q : ℤ) ∣ n then 0 else TLn α x n) else 0) := by
          split_ifs <;> linarith
        have : 0 ≤ (if n ∈ Ioc ⌊R⌋ ⌊D⌋ then TLn α x n else 0) := by split_ifs <;> linarith
        linarith
      push Not at hA
      have hnotA : n ∉ Ioc 0 ⌊min ((q : ℝ) / 2) D⌋ := by
        rw [mem_Ioc]; intro h
        have : ⌊min ((q : ℝ) / 2) D⌋ ≤ ⌊(q : ℝ) / 2⌋ := Int.floor_mono (min_le_left _ _)
        omega
      by_cases hB : n ≤ ⌊D'⌋
      · have hRR : ⌊D'⌋ ≤ ⌊R⌋ := Int.floor_mono (le_max_left _ _)
        rw [if_neg hnotA, if_pos (mem_Ioc.2 ⟨hA, hB⟩),
          if_neg (show n ∉ Ioc ⌊R⌋ ⌊D⌋ by rw [mem_Ioc]; omega)]
        by_cases hd : (q : ℤ) ∣ n
        · rw [if_pos hd]
          have hnD' : (n : ℝ) ≤ D' := (Int.cast_le.2 hB).trans (Int.floor_le _)
          have : g n = 0 := by
            simp only [g]; rw [if_neg (not_not.2 ⟨hd, hnD'.trans hMD'⟩)]
          linarith
        · rw [if_neg hd]; linarith
      push Not at hB
      have hnR : ⌊R⌋ < n := by
        have h1 : D' < n := by
          have := Int.lt_floor_add_one D'
          have : ((⌊D'⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast hB
          linarith
        have h2 : (q : ℝ) / 2 < n := by
          have := Int.lt_floor_add_one ((q : ℝ) / 2)
          have : ((⌊(q : ℝ) / 2⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast hA
          linarith
        exact Int.floor_lt.2 (max_lt h1 h2)
      rw [if_neg hnotA, if_neg (by rw [mem_Ioc]; omega), if_pos (mem_Ioc.2 ⟨hnR, hn.2⟩)]
      linarith
    refine (sum_le_sum hpt).trans ?_
    rw [sum_add_distrib, sum_add_distrib, sum_ite_mem, sum_ite_mem, sum_ite_mem]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => TLn_nonneg _ _ _
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => by
        split_ifs <;> first | exact le_rfl | exact TLn_nonneg _ _ _
    · exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => TLn_nonneg _ _ _
  -- Step 3: the bounds.
  have hR1 := sum_R1L hx hq hcop h2α hqQ hδ hD4 (α := α)
  have hR1pos : 0 ≤ 2 * eta2'L1 / π * q *
      max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) * Real.log x := by
    have : (0 : ℝ) ≤ max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * x))) :=
      le_trans zero_le_one (le_max_left _ _)
    have := Real.log_nonneg hx.le
    positivity
  set T20 := 20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) * √(2 * x) * Real.log (2 * rexp 1 * x / c₂)
  have hT20 : 0 ≤ T20 := by
    have : 0 ≤ Real.log (2 * rexp 1 * x / c₂) := Real.log_nonneg (by
      rw [le_div_iff₀ hc2]; have := c₂_lt_one; nlinarith [Real.exp_pos 1])
    positivity
  have hF1 : ∀ t, 0 < t → t ≤ x → t * (1 / 2 + Real.log x - Real.log t) ≤ t * (1 + Real.log x - Real.log t) :=
    fun t ht _ => by nlinarith
  have hB2 : ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, (if (q : ℤ) ∣ n then 0 else TLn α x n) ≤
      2 * √c₀ / π * (D' * (1 + Real.log x - Real.log D')) + T20 ∧
      (D' ≤ (q : ℝ) / 2 → ∑ n ∈ Ioc ⌊(q : ℝ) / 2⌋ ⌊D'⌋, (if (q : ℤ) ∣ n then 0 else TLn α x n) = 0) := by
    refine ⟨?_, fun hle => by rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hle)), sum_empty]⟩
    rcases le_or_gt D' ((q : ℝ) / 2) with hle | hlt
    · rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hle)), sum_empty]
      have : 0 ≤ D' * (1 + Real.log x - Real.log D') := by
        rcases eq_or_lt_of_le hD'0 with h | h
        · rw [← h]; simp
        · exact mul_nonneg hD'0 (by linarith [Real.log_le_log h (hD'D.trans hDx)])
      positivity
    have h := sum_R2L hx hq hcop h2α hqQ hδ hlt hD'Q (min_le_left _ _) (hD'D.trans hD4)
      (hD'D.trans hDe) (α := α)
    refine h.trans ?_
    have hD'pos : 0 < D' := by linarith
    have hlog : Real.log (rexp (1 / 2) * x / D') = 1 / 2 + Real.log x - Real.log D' := by
      rw [Real.log_div (by positivity) hD'pos.ne', Real.log_mul (by positivity) hx0.ne', Real.log_exp]
    have e20 : 5 * c₀ * c₂ / (3 * π ^ 2) * (4 * √(2 * c₂ * x) * Real.log (2 * rexp 1 * x / c₂)) = T20 := by
      rw [show 5 * c₀ * c₂ / (3 * π ^ 2) * (4 * √(2 * c₂ * x) * Real.log (2 * rexp 1 * x / c₂)) =
        5 * c₀ * c₂ / (3 * π ^ 2) * (4 * √(2 * c₂ * x)) * Real.log (2 * rexp 1 * x / c₂) by ring,
        c₂_rpow]
    rw [hlog, mul_add, e20, c₂_identity]
    have := hF1 D' hD'pos (hD'D.trans hDx)
    have hk : 0 ≤ 2 * √c₀ / π := by positivity
    have := mul_le_mul_of_nonneg_left this hk
    linarith
  have hlog1 := logPlus_nonneg (D / (c₂ * x / q))
  have hlog2 := logPlus_nonneg (D / (q / 2))
  have hlq : 0 ≤ Real.log (q / c₂) := Real.log_nonneg (by
    rw [le_div_iff₀ hc2]; linarith [c₂_lt_one])
  have hl2x : 0 ≤ Real.log (2 * x / c₂) := Real.log_nonneg (by
    rw [le_div_iff₀ hc2]; linarith [c₂_lt_one])
  have hD'R : D' ≤ R := le_max_left _ _
  have hqR : (q : ℝ) / 2 ≤ R := le_max_right _ _
  have hlogexD : Real.log (rexp 1 * x / D) = 1 + Real.log x - Real.log D := by
    rw [Real.log_div (by positivity) (by linarith), Real.log_mul (by positivity) hx0.ne', Real.log_exp]
  -- Step 4: combine.
  refine h1.trans (h2.trans ?_)
  unfold bound_4_41
  simp only []
  rw [← hc₁def, hlogexD]
  have hFD : D' * (1 + Real.log x - Real.log D') ≤ D * (1 + Real.log x - Real.log D) := by
    rcases eq_or_lt_of_le hD'0 with h | h
    · rw [← h]; simp
      exact mul_nonneg (by linarith) (by linarith [Real.log_le_log (by linarith) hDx])
    · exact F₁_mono hx0 h hD'D hDx
  have hpos5 : 0 ≤ 3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) * Real.log (q / c₂) := by
    positivity
  have hpos6 : 0 ≤ 2 * √(c₀ * c₁) / π * (√3 + 1 / 2 * logPlus (D / (q / 2))) * Real.log (q / c₂) * q := by
    positivity
  have hpos7 : 0 ≤ 3 * c₁ / 2 * √(2 * x / c₂) * Real.log (2 * x / c₂) := by positivity
  rcases lt_or_ge R D with hRD | hRD
  · have hD'eq : D' = c₂ * x / q := by
      rcases min_choice (c₂ * x / q) D with h | h
      · exact h
      · exfalso; have : D' = D := h; linarith
    have hB3 := sum_R3L hx hq hcop h2α hqQ hδ hqR (hD'eq ▸ hD'R) hRD hD4 hDe (α := α)
    rw [← hc₁def] at hB3
    have hcancel : 2 * √c₀ / π * (D' * (1 + Real.log x - Real.log D')) ≤
        2 * √(c₀ * c₁) / π * (R * (1 + Real.log x - Real.log R)) := by
      have hR0 : 0 < R := by
        have : (0 : ℝ) < q / 2 := by positivity
        linarith
      have h1 : D' * (1 + Real.log x - Real.log D') ≤ R * (1 + Real.log x - Real.log R) := by
        rcases eq_or_lt_of_le hD'0 with h | h
        · rw [← h]; simp
          exact mul_nonneg hR0.le (by linarith [Real.log_le_log hR0 (hRD.le.trans hDx)])
        · exact F₁_mono hx0 h hD'R (hRD.le.trans hDx)
      have h2 : 0 ≤ R * (1 + Real.log x - Real.log R) :=
        mul_nonneg hR0.le (by linarith [Real.log_le_log hR0 (hRD.le.trans hDx)])
      have := Real.pi_pos
      calc 2 * √c₀ / π * (D' * (1 + Real.log x - Real.log D'))
          ≤ 2 * √c₀ / π * (R * (1 + Real.log x - Real.log R)) := by gcongr
        _ ≤ _ := by gcongr
    have e3 : 3 * c₁ / 2 * (√(2 * x / c₂) * Real.log (2 * x / c₂) +
        x / q * Real.log (q / c₂) * logPlus (D / (c₂ * x / q))) =
        3 * c₁ / 2 * √(2 * x / c₂) * Real.log (2 * x / c₂) +
        3 * c₁ / 2 * (x / q) * logPlus (D / (c₂ * x / q)) * Real.log (q / c₂) := by ring
    have e4 : 2 * √(c₀ * c₁) / π * (√3 * q * Real.log (q / c₂) +
        (D * (1 + Real.log x - Real.log D) - R * (1 + Real.log x - Real.log R)) +
        q / 2 * Real.log (q / c₂) * logPlus (D / (q / 2))) =
        2 * √(c₀ * c₁) / π * (√3 + 1 / 2 * logPlus (D / (q / 2))) * Real.log (q / c₂) * q +
        2 * √(c₀ * c₁) / π * (D * (1 + Real.log x - Real.log D)) -
        2 * √(c₀ * c₁) / π * (R * (1 + Real.log x - Real.log R)) := by ring
    rw [e3, e4] at hB3
    have hB2' := hB2.1
    nlinarith
  · rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hRD)), sum_empty, add_zero]
    have hcancel : 2 * √c₀ / π * (D' * (1 + Real.log x - Real.log D')) ≤
        2 * √(c₀ * c₁) / π * (D * (1 + Real.log x - Real.log D)) := by
      have := Real.pi_pos
      have h2 : 0 ≤ D * (1 + Real.log x - Real.log D) :=
        mul_nonneg (by linarith) (by linarith [Real.log_le_log (by linarith) hDx])
      calc 2 * √c₀ / π * (D' * (1 + Real.log x - Real.log D'))
          ≤ 2 * √c₀ / π * (D * (1 + Real.log x - Real.log D)) := by gcongr
        _ ≤ _ := by gcongr
    have hB2' := hB2.1
    nlinarith

/-- **[B, Lemma 4.2.3], case (b)** (`|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`), for `η = η₂`: (4.40) + (4.41)
in the forms `bound_4_40` (corrected) and `bound_4_41` (slightly weakened). Proved; it depends
only on the trusted bounds `eta2_fourier_bound'` and `eta2log_fourier_bound`. -/
theorem lemma_4_2_3_caseB {α x δ Q₀ D : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hD : √3 ≤ D) (hDx : D ≤ min (x / 4) (x / rexp 1))
    (hcase : |δ| ≤ 1 / (2 * c₂) ∨ D ≤ Q₀ / 2) :
    ‖typeILog α x D‖ ≤ bound_4_40 x δ q D + bound_4_41 x q D := by
  obtain ⟨hq, hcop, ⟨k, h2α⟩, hδQ₀, hqQ₀⟩ := h
  have hD4 : D ≤ x / 4 := hDx.trans (min_le_left _ _)
  have hDe : D ≤ x / rexp 1 := hDx.trans (min_le_right _ _)
  have hD1 : 1 ≤ D := le_trans (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) hD
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc2 := c₂_pos
  have hQ₀0 : 0 < Q₀ := lt_of_lt_of_le hq0 hqQ₀
  obtain ⟨Q, hqQ, hδ, hD'Q, hMQ⟩ : ∃ Q : ℝ, (q : ℝ) ≤ Q ∧ |δ / x| * (q * Q) ≤ 1 ∧
      min (c₂ * x / q) D ≤ Q / 2 ∧ Mof x δ q D = min (Q / 2) D := by
    by_cases hδ0 : δ = 0
    · refine ⟨max Q₀ (2 * D), hqQ₀.trans (le_max_left _ _), by simp [hδ0], ?_, ?_⟩
      · have := le_max_right Q₀ (2 * D)
        exact (min_le_right _ _).trans (by linarith)
      · rw [Mof, if_pos hδ0, min_eq_right]
        have := le_max_right Q₀ (2 * D); linarith
    · have hδpos : 0 < |δ| := abs_pos.2 hδ0
      have hQ₀le : Q₀ ≤ x / (|δ| * q) := by
        rw [abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 (by positivity)] at hδQ₀
        rw [le_div_iff₀ (by positivity)]; nlinarith
      refine ⟨x / (|δ| * q), hqQ₀.trans hQ₀le, ?_, ?_, by rw [Mof, if_neg hδ0]⟩
      · rw [abs_div, abs_of_pos hx0]; field_simp; rfl
      · rcases hcase with hc | hc
        · refine (min_le_left _ _).trans ?_
          have h1 : 2 * c₂ * |δ| ≤ 1 := by
            rw [le_div_iff₀ (by positivity)] at hc; linarith
          have e : c₂ * x / q = (2 * c₂ * |δ|) * (x / (|δ| * q) / 2) := by field_simp
          rw [e]; exact mul_le_of_le_one_left (by positivity) h1
        · exact (min_le_right _ _).trans (hc.trans (by linarith))
  set M := Mof x δ q D
  have hMD : M ≤ D := by rw [hMQ]; exact min_le_right _ _
  have hM0 : 0 ≤ M := by rw [hMQ]; exact le_min (by linarith) (by linarith)
  have hMD' : min (c₂ * x / q) D ≤ M := by rw [hMQ]; exact le_min hD'Q (min_le_right _ _)
  have hMδ : |δ| * M ≤ x / 2 := by
    have h1 : |δ| * M ≤ |δ| * (Q / 2) := by
      rw [hMQ]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)
    have h2 : |δ| * (q * Q) ≤ x := by
      have e : |δ / x| * (q * Q) = |δ| * (q * Q) / x := by rw [abs_div, abs_of_pos hx0]; ring
      rw [e, div_le_one hx0] at hδ; exact hδ
    have h3 : |δ| * Q ≤ x := by
      have : |δ| * Q ≤ |δ| * (q * Q) := by
        have hQ0 : 0 ≤ Q := by linarith
        have : Q ≤ q * Q := by
          nlinarith [mul_nonneg (sub_nonneg.2 (show (1 : ℝ) ≤ q by exact_mod_cast hq)) hQ0]
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      linarith
    linarith
  rw [typeILog_eq_main_add_rest hx0 hq hM0 hMD]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_mainPartL_le hx0 hq h2α hM0 hMδ hMD hD4 hDe
  · exact norm_restPartL_le_caseB hx hq hcop h2α hqQ hδ hD1 hD4 hDe hD'Q hMD'

/-- **[B, Lemma 4.2.3]** for `η = η₂` (and `ρ₀ = 4`, by [B, (6.2)]), in the form used by [B, §6.2.1]:
if `|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`, (4.39) is at most (4.40) + (4.41).

[B]'s second statement, the bound (4.42) for `|δ| ≥ 1/2c₂`, is not formalized: it is never used
(§6.2.1 takes `D = U ≤ Q₀/2`), and as printed it omits the main term (4.40), which the proof
(p. 67) separates in both cases. -/
theorem lemma_4_2_3 {α x δ Q₀ D : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hD : √3 ≤ D) (hDx : D ≤ min (x / 4) (x / rexp 1)) (hcase : |δ| ≤ 1 / (2 * c₂) ∨ D ≤ Q₀ / 2) :
    ‖typeILog α x D‖ ≤ bound_4_40 x δ q D + bound_4_41 x q D :=
  lemma_4_2_3_caseB h hD hDx hcase

end TernaryGoldbach.MinorArcs
