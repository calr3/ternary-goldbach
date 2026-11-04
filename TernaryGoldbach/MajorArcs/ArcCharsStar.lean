import TernaryGoldbach.MajorArcs.ArcChars
import TernaryGoldbach.MinorArcs.BaseGap2

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.ButhePsi] [Fact TernaryGoldbach.RamareMoebius]

/-!
# `S_{η_*}` on the arcs of modulus `q`, via characters ([H, Cor 7.1.3])

The analogue of `ArcChars.lean` for `η_*(t) = η(κt)` (`η = η₂ *_M φ`, our `etaU`), at scale `y = x/κ`:
for `q ∈ Qset r₀` and `|βx| ≤ 1.2·10⁶/q̃`, with `S'_q` the part over `(n, q) = 1`,
* `μ²(q)/φ(q) |S'_q(β)|² ≤ Σ_b |S'_q(b/q + β)|² ≤ μ²(q)/φ(q) |S'_q(β)|² + (1.35·10⁻⁷ y)²`;
* `|S'_q(β) − η̂(−βy) y| ≤ 1.21·10⁻⁷ y`;
* `|S_{η_*}(α, x) − S'_q(α)| ≤ 10⁻¹² y`.
-/

open Real MeasureTheory FourierTransform Set Finset
open scoped ArithmeticFunction.vonMangoldt
open TernaryGoldbach (e expTsum Schar)
open TernaryGoldbach.MinorArcs (coprimePart norm_coprimePart_le Schar_primitive Schar_sub norm_Schar_le
  Qset Bset qt sum_Bset_eq_units etaU etaStar_eq_etaU sum_noncoprime_le S_etaStar_eq_expTsum)
open TernaryGoldbach.Helfgott (etaStar S r₀ κ)

namespace TernaryGoldbach.MajorArcs

theorem kappa_pos : (0 : ℝ) < κ := by rw [TernaryGoldbach.Helfgott.κ]; norm_num

/-- The coefficients `Λ(n) η(n/y)`. -/
noncomputable def cU (y : ℝ) (n : ℕ) : ℂ := ((Λ n * etaU (n / y) : ℝ) : ℂ)

theorem summable_cU {y : ℝ} (hy : 0 < y) : Summable fun n => ‖cU y n‖ := by
  have hx0 : 0 < κ * y := by have := kappa_pos; positivity
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (TernaryGoldbach.Helfgott.summable_etaStar hx0)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [cU]
  · rw [etaStar_eq_etaU (by positivity)]
    simp only [cU, Complex.norm_real]
    apply le_of_eq; congr 3; have := kappa_pos; field_simp

theorem S_etaStar_eq_cU {x : ℝ} (hx : 0 < x) (α : ℝ) : S etaStar x α = expTsum (cU (x / κ)) α :=
  S_etaStar_eq_expTsum hx α

/-- A `K` with `y² ≤ 2^K` and `6.2 K log(3·10⁵) + 1 ≤ 10⁻¹² y`. -/
theorem exists_K_star {y : ℝ} (hy : 1e25 ≤ y) :
    ∃ K : ℕ, y ^ 2 ≤ 2 ^ K ∧ 6.2 * K * Real.log 300000 + 1 ≤ 1e-12 * y := by
  have hy0 : 0 < y := by linarith
  set s := √(√y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs4 : s ^ 4 = y := by
    rw [hs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hy0.le]
  have hsge : 1.7e6 ≤ s := by
    by_contra h; push Not at h
    have : s ^ 4 < (1.7e6) ^ 4 := pow_lt_pow_left₀ h hs0 (by norm_num)
    rw [hs4] at this; norm_num at this; linarith
  have hlogy : Real.log y ≤ 4 * s := by
    rw [← hs4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
    push_cast; linarith
  have hlog2 : 0.693 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog3 := log_3e5_le
  have hlogynn : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  set L := Real.logb 2 (y ^ 2)
  have hL : L = 2 * Real.log y / Real.log 2 := by
    simp only [L, Real.logb, Real.log_pow]; push_cast; ring
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  refine ⟨⌈L⌉₊, ?_, ?_⟩
  · have h1 : (2 : ℝ) ^ L = y ^ 2 := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    calc y ^ 2 = (2 : ℝ) ^ L := h1.symm
      _ ≤ (2 : ℝ) ^ (⌈L⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil L)
      _ = 2 ^ ⌈L⌉₊ := Real.rpow_natCast 2 _
  · have hK : (⌈L⌉₊ : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL0).le
    have hL' : L ≤ 11.55 * s := by
      rw [hL, div_le_iff₀ (by linarith)]; nlinarith
    have hK0 : (0 : ℝ) ≤ ⌈L⌉₊ := Nat.cast_nonneg _
    have hl3 : 0 ≤ Real.log 300000 := Real.log_nonneg (by norm_num)
    have h1 : 6.2 * (⌈L⌉₊ : ℝ) * Real.log 300000 ≤ 6.2 * (11.55 * s + 1) * 12.62 := by
      have := mul_le_mul (show 6.2 * (⌈L⌉₊ : ℝ) ≤ 6.2 * (11.55 * s + 1) by linarith) hlog3 hl3
        (by positivity)
      linarith
    have hs3 : (1.7e6 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hsge 3
    have : 1e-12 * y = 1e-12 * (s * s ^ 3) := by rw [← hs4]; ring
    rw [this]
    nlinarith

/-- `|S_{η_*} − S'_q| ≤ 10⁻¹² y`. -/
theorem coprime_split_star {y : ℝ} (hy : 1e25 ≤ y) {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ 300000) :
    ∑' n, ‖cU y n - coprimePart q (cU y) n‖ ≤ 1e-12 * y := by
  obtain ⟨K, hK, hD⟩ := exists_K_star hy
  refine (sum_noncoprime_le hy hq1 hK).trans ?_
  have h1 : Real.log q ≤ Real.log 300000 :=
    Real.log_le_log (by exact_mod_cast hq1) (by exact_mod_cast hq)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  nlinarith

theorem summable_sub_coprimePart_star {y : ℝ} (hy : 0 < y) (q : ℕ) :
    Summable fun n => ‖(cU y - coprimePart q (cU y)) n‖ :=
  ((summable_cU hy).add ((summable_cU hy).of_nonneg_of_le (fun n => norm_nonneg _)
    (norm_coprimePart_le q (cU y)))).of_nonneg_of_le (fun n => norm_nonneg _)
    fun n => norm_sub_le _ _

theorem norm_S_star_sub_coprime_le {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (α : ℝ) : ‖S etaStar x α - expTsum (coprimePart q (cU (x / κ))) α‖ ≤ 1e-12 * (x / κ) := by
  have hx0 : 0 < x := by linarith
  have hy : 1e25 ≤ x / κ := by
    rw [TernaryGoldbach.Helfgott.κ, le_div_iff₀ (by norm_num)]; linarith
  have hy0 : 0 < x / κ := by linarith
  have hc := summable_cU hy0
  have ha : Summable fun n => ‖coprimePart q (cU (x / κ)) n‖ :=
    hc.of_nonneg_of_le (fun n => norm_nonneg _) (norm_coprimePart_le q _)
  rw [S_etaStar_eq_cU hx0, ← expTsum_sub hc ha]
  exact (norm_expTsum_le_tsum (summable_sub_coprimePart_star hy0 q) α).trans (coprime_split_star hy hq1 hq)

/-- `√c (err_{7.1.3}(c) y + 10⁻¹² y) ≤ 1.49·10⁻⁶ y` for `1 ≤ c ≤ 3·10⁵`, `y ≥ 10²⁵`. -/
theorem err_scaled_le_star {y c : ℝ} (hy : 1e25 ≤ y) (hc1 : 1 ≤ c) (hc3 : c ≤ 300000) :
    √c * ((1e-17 + 4.7e6 / √c / √y) * y + 1e-12 * y) ≤ 1.49e-6 * y := by
  have hy0 : 0 < y := by linarith
  set s := √c with hs
  set r := √y with hr
  have hs2 : s ^ 2 = c := Real.sq_sqrt (by linarith)
  have hr2 : r ^ 2 = y := Real.sq_sqrt hy0.le
  have hs1 : 1 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs548 : s ≤ 548 := by
    rw [hs, Real.sqrt_le_left (by norm_num)]; linarith
  have hr1 : 3.16e12 ≤ r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < s := by linarith
  have hr0 : 0 < r := by linarith
  have e : s * ((1e-17 + 4.7e6 / s / r) * y + 1e-12 * y) = r ^ 2 * (s * (1e-17 + 1e-12)) + 4.7e6 * r := by
    rw [← hr2]; field_simp; ring
  rw [e, ← hr2]
  have h1 : 4.7e6 * r ≤ r ^ 2 * (4.7e6 / 3.16e12) := by
    rw [mul_div_assoc', le_div_iff₀ (by norm_num)]; nlinarith
  have h2 : r ^ 2 * (s * (1e-17 + 1e-12)) ≤ r ^ 2 * (548 * (1e-17 + 1e-12)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  have h3 : (548 * (1e-17 + 1e-12) : ℝ) + 4.7e6 / 3.16e12 ≤ 1.49e-6 := by norm_num
  nlinarith [sq_nonneg r]

set_option maxHeartbeats 1000000 in
/-- **[H, §10.4] for `η_*` and one modulus `q`**: Bombieri's identity and [H, Cor 7.1.3]. -/
theorem arc_chars_star {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq1 : 1 ≤ q) (hqt : (qt q : ℝ) ≤ 300000)
    {β : ℝ} (hβ : |β * x| ≤ 1200000 / qt q) :
    ((if Squarefree q then (1:ℝ) else 0) / q.totient * ‖expTsum (coprimePart q (cU (x / κ))) β‖ ^ 2 ≤
        ∑ b ∈ Bset q, ‖expTsum (coprimePart q (cU (x / κ))) ((b : ℝ) / q + β)‖ ^ 2 ∧
      ∑ b ∈ Bset q, ‖expTsum (coprimePart q (cU (x / κ))) ((b : ℝ) / q + β)‖ ^ 2 ≤
        (if Squarefree q then (1:ℝ) else 0) / q.totient * ‖expTsum (coprimePart q (cU (x / κ))) β‖ ^ 2 +
          (1.49e-6 * (x / κ)) ^ 2) ∧
      ‖expTsum (coprimePart q (cU (x / κ))) β -
        𝓕 (fun u => (etaU u : ℂ)) (-(β * (x / κ))) * ((x / κ : ℝ) : ℂ)‖ ≤ 1.49e-6 * (x / κ) := by
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
  set y := x / κ with hy_def
  have hy : 1e25 ≤ y := by
    rw [hy_def, TernaryGoldbach.Helfgott.κ, le_div_iff₀ (by norm_num)]; linarith
  have hy0 : 0 < y := by linarith
  set a := coprimePart q (cU y) with ha_def
  have hc := summable_cU hy0
  have ha : Summable fun n => ‖a n‖ :=
    hc.of_nonneg_of_le (fun n => norm_nonneg _) (norm_coprimePart_le q (cU y))
  have hca := summable_sub_coprimePart_star hy0 q
  have hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q := fun n hn => by
    by_contra h; exact hn (by simp [ha_def, coprimePart, h])
  have hqq : q ≤ qt q := by unfold qt; split_ifs <;> omega
  have hq3 : q ≤ 300000 := by
    have : (q : ℝ) ≤ 300000 := le_trans (by exact_mod_cast hqq) hqt
    exact_mod_cast this
  have hD := coprime_split_star hy hq1 hq3
  have hDa : ∑' n, ‖(cU y - a) n‖ ≤ 1e-12 * y := by
    refine le_trans (le_of_eq ?_) hD; rfl
  have hqt0 : (0 : ℝ) < qt q := by
    have : 1 ≤ qt q := hq1.trans hqq
    exact_mod_cast this
  have hκ49 : (κ : ℝ) = 49 := rfl
  have hβy : |β * y| ≤ 1200000 / qt q := by
    have : |β * y| = |β * x| / κ := by rw [hy_def, mul_div_assoc', abs_div, abs_of_pos kappa_pos]
    rw [this, div_le_iff₀ kappa_pos]
    have h0 : 0 ≤ 1200000 / (qt q : ℝ) := by positivity
    rw [hκ49]
    nlinarith
  have hδy : β * y / y = β := by field_simp
  -- the non-principal characters
  have hE : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖ ≤ 1.49e-6 * y := by
    intro ψ hψ
    set c' := ψ⁻¹.conductor with hc'
    haveI : NeZero c' := ⟨DirichletCharacter.conductor_ne_zero _⟩
    have hc'0 : 1 ≤ c' := Nat.pos_of_ne_zero (NeZero.ne c')
    have hc'q : c' ∣ q := DirichletCharacter.conductor_dvd_level _
    have hc'le : c' ≤ q := Nat.le_of_dvd (by omega) hc'q
    have hτ : ‖gaussSum ψ ZMod.stdAddChar‖ ≤ √(c' : ℝ) := by
      have := norm_gaussSum_le_sqrt_conductor ψ
      rwa [← DirichletCharacter.conductor_inv] at this
    set χ := ψ⁻¹.primitiveCharacter
    have hχ : χ.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive _
    have hS : ‖Schar ψ⁻¹ a β‖ ≤ ‖Schar χ (cU y) β‖ + 1e-12 * y := by
      rw [ha_def, Schar_primitive, ← ha_def]
      have h1 : Schar χ a β = Schar χ (cU y) β - Schar χ (cU y - a) β := by
        rw [Schar_sub _ hc ha]; ring
      rw [h1]
      have h2 := norm_Schar_le χ hca β
      have := norm_sub_le (Schar χ (cU y) β) (Schar χ (cU y - a) β)
      linarith
    have hc'1 : c' ≠ 1 := fun h =>
      hψ (inv_eq_one.1 ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := ψ⁻¹)).2 h))
    have hcr : (c' : ℝ) ≤ q := by exact_mod_cast hc'le
    have hc'pos : (0 : ℝ) < c' := by exact_mod_cast hc'0
    have hδ : |β * y| ≤ 4 * 300000 / c' := by
      refine hβy.trans ?_
      rw [div_le_div_iff₀ hqt0 hc'pos]
      have : (c' : ℝ) ≤ qt q := hcr.trans (by exact_mod_cast hqq)
      nlinarith
    have hT := cor_7_1_3' (y := y) hy (le_trans hc'le hq3) χ hχ hδ
    rw [if_neg hc'1, sub_zero, hδy] at hT
    have hT' : ‖Schar χ (cU y) β‖ ≤ (1e-17 + 4.7e6 / √(c' : ℝ) / √y) * y := hT
    have hc'3r : (c' : ℝ) ≤ 300000 := hcr.trans (by exact_mod_cast hq3)
    calc ‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖
        ≤ √(c' : ℝ) * ((1e-17 + 4.7e6 / √(c' : ℝ) / √y) * y + 1e-12 * y) :=
          mul_le_mul hτ (hS.trans (by linarith)) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ 1.49e-6 * y := err_scaled_le_star hy (by exact_mod_cast hc'0) hc'3r
  refine ⟨?_, ?_⟩
  · have hsplit := sum_units_sq_bounds ha hcop β hE
    rw [sum_Bset_eq_units (fun t => ‖expTsum a t‖ ^ 2) β]
    exact hsplit
  · have hqt1 : (1 : ℝ) ≤ qt q := by exact_mod_cast hq1.trans hqq
    have hδ1 : |β * y| ≤ 4 * 300000 / (1 : ℕ) := by
      refine hβy.trans ?_
      rw [div_le_iff₀ hqt0]; push_cast; nlinarith
    have h1 := cor_7_1_3' (y := y) hy (q := 1) (by norm_num) (1 : DirichletCharacter ℂ 1)
      DirichletCharacter.isPrimitive_one_level_one hδ1
    rw [if_pos rfl, hδy, Schar_level_one] at h1
    have h2 : expTsum a β = expTsum (cU y) β - expTsum (cU y - a) β := by
      rw [expTsum_sub hc ha]; ring
    have h3 := (norm_expTsum_le_tsum hca β).trans hDa
    have hsy : 3.16e12 ≤ √y := Real.le_sqrt_of_sq_le (by nlinarith)
    have h4 : 4.7e6 / √((1 : ℕ) : ℝ) / √y ≤ 4.7e6 / 3.16e12 := by
      rw [Nat.cast_one, Real.sqrt_one, div_one, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    rw [h2]
    calc ‖expTsum (cU y) β - expTsum (cU y - a) β - 𝓕 (fun u => (etaU u : ℂ)) (-(β * y)) * y‖
        ≤ ‖expTsum (cU y) β - 𝓕 (fun u => (etaU u : ℂ)) (-(β * y)) * y‖ + ‖expTsum (cU y - a) β‖ := by
          have := norm_sub_le (expTsum (cU y) β - 𝓕 (fun u => (etaU u : ℂ)) (-(β * y)) * y)
            (expTsum (cU y - a) β)
          calc _ = ‖expTsum (cU y) β - 𝓕 (fun u => (etaU u : ℂ)) (-(β * y)) * y - expTsum (cU y - a) β‖ := by
                congr 1; ring
            _ ≤ _ := this
      _ ≤ (1e-17 + 4.7e6 / √((1 : ℕ) : ℝ) / √y) * y + 1e-12 * y := add_le_add h1 h3
      _ ≤ 1.49e-6 * y := by nlinarith

end TernaryGoldbach.MajorArcs
