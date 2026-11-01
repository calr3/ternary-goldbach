import TernaryGoldbach.MajorArcs.EtaPlusL2
import TernaryGoldbach.MajorArcs.Thm714
import TernaryGoldbach.MajorArcs.ArcsEq
import TernaryGoldbach.MinorArcs.BaseGap

/-!
# `S_{η₊}` on the arcs of modulus `q`, via characters

For `q` and `β` on the arc `|β| < w_q`, with `S'_q` the part of `S_{η₊}` over `(n, q) = 1`:
* `|S − S'_q| ≤ D` everywhere, `D = 1.94 K log q + 1` (`x² ≤ 2^K`): only prime powers `p^k`, `p ∣ q`;
* (Bombieri's identity, `|τ(ψ)|² ≤ cond ψ`) `μ²(q)/φ(q) |S'_q(β)|² ≤ Σ_b |S'_q(b/q + β)|²
  ≤ μ²(q)/φ(q) |S'_q(β)|² + E²`, with `E = max_{ψ ≠ 1} |τ(ψ)| |S'_{q,ψ⁻¹}(β)|`;
* [B, Thm 7.1.4] for the primitive characters inducing `ψ⁻¹`: `E ≤ 2.41·10⁻⁸ x` and
  `|S'_q(β) − η̂₊(−βx) x| ≤ 1.141·10⁻⁸ x` for `x ≥ 4.9·10²⁶`.
-/

open Real MeasureTheory FourierTransform Set Finset
open scoped ArithmeticFunction.vonMangoldt
open TernaryGoldbach (e expTsum Schar)
open TernaryGoldbach.MinorArcs (coprimePart norm_coprimePart_le Schar_primitive Schar_sub norm_Schar_le
  Qset Bset qt sum_Bset_eq_units)
open TernaryGoldbach.Helfgott (etaPlus S r₀)

namespace TernaryGoldbach.MajorArcs

/-- The coefficients `Λ(n) η₊(n/x)`. -/
noncomputable def cP (x : ℝ) (n : ℕ) : ℂ := ((Λ n * etaPlus (n / x) : ℝ) : ℂ)

theorem summable_cP {x : ℝ} (hx : 0 < x) : Summable fun n => ‖cP x n‖ :=
  Helfgott.summable_etaPlus hx

theorem S_etaPlus_eq_expTsum (x α : ℝ) : S etaPlus x α = expTsum (cP x) α := rfl

/-! ## The terms with `(n, q) > 1` -/

theorem cube_mul_exp_le' (t : ℝ) (ht : 0 ≤ t) :
    t ^ 3 * Real.exp (-t / 2) ≤ 384 * Real.exp (-t / 4) := by
  have h := Real.pow_div_factorial_le_exp (x := t / 4) (by positivity) 3
  norm_num [Nat.factorial] at h
  have e1 : Real.exp (-t / 4) = Real.exp (t / 4) * Real.exp (-t / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1]
  have := Real.exp_pos (-t / 2)
  nlinarith

theorem tsum_exp_neg_quarter_le : ∑' n : ℕ, Real.exp (-(n : ℝ) / 4) ≤ 5 := by
  have h := tsum_geometric_of_lt_one (r := Real.exp (-1 / 4)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.2 (by norm_num))
  have e : ∀ n : ℕ, Real.exp (-(n : ℝ) / 4) = Real.exp (-1 / 4) ^ n := fun n => by
    rw [← Real.exp_nat_mul]; ring_nf
  simp_rw [e, h]
  have : Real.exp (-1 / 4) ≤ 0.8 := by
    have := Real.add_one_le_exp (1 / 4)
    have h2 : Real.exp (-1 / 4) = (Real.exp (1 / 4))⁻¹ := by rw [← Real.exp_neg]; ring_nf
    rw [h2, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
  rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith

theorem summable_exp_neg_quarter : Summable fun n : ℕ => Real.exp (-(n : ℝ) / 4) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 0 (show (0:ℝ) < 1 / 4 by norm_num)
  refine h.congr fun n => ?_
  simp only [pow_zero, one_mul]; ring_nf

/-- **The terms with `(n, q) > 1`**: for `x ≥ 10⁴` and `x² ≤ 2^K`,
`Σ_{(n,q)>1} Λ(n) |η₊(n/x)| ≤ 1.94 K log q + 1`. -/
theorem sum_noncoprime_etaPlus_le {x : ℝ} (hx : 1e4 ≤ x) {q K : ℕ} (hq : 1 ≤ q)
    (hK : x ^ 2 ≤ 2 ^ K) :
    ∑' n, ‖cP x n - coprimePart q (cP x) n‖ ≤ 1.94 * K * Real.log q + 1 := by
  have hx0 : 0 < x := by linarith
  set g : ℕ → ℝ := fun n => ‖cP x n - coprimePart q (cP x) n‖ with hg
  set g₁ : ℕ → ℝ := fun n => if n ∈ (q ^ K).divisors then 1.94 * Λ n else 0
  set g₂ : ℕ → ℝ := fun n => 3.15 * 384 / x * Real.exp (-(n : ℝ) / 4)
  have hs₁ : Summable g₁ := summable_of_ne_finset_zero (s := (q ^ K).divisors)
    (fun n hn => by simp only [g₁, hn, ite_false])
  have hs₂ : Summable g₂ := summable_exp_neg_quarter.mul_left _
  have hpt : ∀ n, g n ≤ g₁ n + g₂ n := by
    intro n
    have hg2 : 0 ≤ g₂ n := by positivity
    have hg1 : 0 ≤ g₁ n := by
      simp only [g₁]; split_ifs
      · exact mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl
    by_cases hc : Nat.Coprime n q
    · have : g n = 0 := by
        simp only [hg, coprimePart]; rw [ite_eq_left (c := Nat.Coprime n q) hc, sub_self, norm_zero]
      rw [this]; linarith
    have hgn : g n = Λ n * |etaPlus (n / x)| := by
      simp only [hg, coprimePart, hc, ite_false, sub_zero, cP, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [hgn]
    by_cases hΛ : Λ n = 0
    · rw [hΛ, zero_mul]; linarith
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hΛ
      · exact h
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    by_cases hny : (n : ℝ) ≤ x ^ 2
    · obtain ⟨p, k, hp, hk, rfl⟩ :=
        (isPrimePow_nat_iff _).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
      have hpq : p ∣ q := by
        by_contra h
        exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
      have hkK : k ≤ K := by
        have h1 : (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := pow_le_pow_left₀ (by norm_num)
          (by exact_mod_cast hp.two_le) k
        have h2 : (2 : ℝ) ^ k ≤ 2 ^ K := by push_cast at hny; linarith
        exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).1 h2
      have hdvd : p ^ k ∣ q ^ K := (pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK)
      have hmem : p ^ k ∈ (q ^ K).divisors :=
        Nat.mem_divisors.2 ⟨hdvd, pow_ne_zero _ (by omega)⟩
      have : g₁ (p ^ k) = 1.94 * Λ (p ^ k) := by simp only [g₁, hmem, ite_true]
      rw [this]
      have := Helfgott.abs_etaPlus_le_A (t := ((p ^ k : ℕ) : ℝ) / x) (by positivity)
      nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := p ^ k)]
    · push Not at hny
      have hu : 0 ≤ (n : ℝ) / x := by positivity
      have h1 : |etaPlus (n / x)| ≤ 3.15 * ((n / x) * Real.exp (-((n : ℝ) / x) ^ 2 / 2)) := by
        have := abs_etaPlus_le_gauss ((n : ℝ) / x)
        have hnn : 0 ≤ (n : ℝ) / x * Real.exp (-(1 / 2) * ((n : ℝ) / x) ^ 2) := by positivity
        rw [abs_of_nonneg hnn, show -(1 / 2) * ((n : ℝ) / x) ^ 2 = -((n : ℝ) / x) ^ 2 / 2
          by ring] at this
        exact this
      have hsq : (n : ℝ) ≤ ((n : ℝ) / x) ^ 2 := by
        rw [div_pow, le_div_iff₀ (by positivity)]; nlinarith
      have h2 : Real.exp (-((n : ℝ) / x) ^ 2 / 2) ≤ Real.exp (-(n : ℝ) / 2) :=
        Real.exp_le_exp.2 (by linarith)
      have hΛn : Λ n ≤ n := ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn0.le)
      have h3 := cube_mul_exp_le' n hn0.le
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      calc Λ n * |etaPlus (n / x)| ≤ n * (3.15 * ((n / x) * Real.exp (-(n : ℝ) / 2))) := by
            refine mul_le_mul hΛn (h1.trans ?_) (abs_nonneg _) hn0.le
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hu) (by norm_num)
        _ = 3.15 / x * ((n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / 2)) := by field_simp
        _ ≤ 3.15 / x * ((n : ℝ) ^ 3 * Real.exp (-(n : ℝ) / 2)) := by
            gcongr
            nlinarith
        _ ≤ 3.15 / x * (384 * Real.exp (-(n : ℝ) / 4)) := by gcongr
        _ = g₂ n := by simp only [g₂]; ring
        _ ≤ g₁ n + g₂ n := by linarith
  have hs : Summable g := (hs₁.add hs₂).of_nonneg_of_le (fun n => norm_nonneg _) hpt
  calc ∑' n, g n ≤ ∑' n, (g₁ n + g₂ n) := Summable.tsum_le_tsum hpt hs (hs₁.add hs₂)
    _ = ∑' n, g₁ n + ∑' n, g₂ n := hs₁.tsum_add hs₂
    _ ≤ 1.94 * K * Real.log q + 1 := by
        have e1 : ∑' n, g₁ n = 1.94 * (K * Real.log q) := by
          rw [tsum_eq_sum (s := (q ^ K).divisors) (fun n hn => by simp only [g₁, hn, ite_false])]
          rw [Finset.sum_congr rfl (g := fun n => 1.94 * Λ n) (fun n hn => by simp only [g₁, hn, ite_true]),
            ← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
          push_cast; rw [Real.log_pow]
        have e2 : ∑' n, g₂ n ≤ 1 := by
          simp only [g₂]
          rw [tsum_mul_left]
          have hsum := tsum_exp_neg_quarter_le
          have h0 : 0 ≤ ∑' n : ℕ, Real.exp (-(n : ℝ) / 4) := tsum_nonneg fun n => (Real.exp_pos _).le
          have : 3.15 * 384 / x ≤ 3.15 * 384 / 1e4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
          nlinarith
        linarith

/-! ## Bombieri's identity: the principal and non-principal parts -/

theorem Schar_one_eq_expTsum {q : ℕ} [NeZero q] {a : ℕ → ℂ}
    (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q) (β : ℝ) :
    Schar (1 : DirichletCharacter ℂ q) a β = expTsum a β := by
  unfold Schar expTsum
  congr 1; ext n
  by_cases h : a n = 0
  · simp [h]
  · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).2 (hcop n h)
    rw [MulChar.one_apply hu, mul_one]

theorem Schar_level_one (χ : DirichletCharacter ℂ 1) (a : ℕ → ℂ) (β : ℝ) :
    Schar χ a β = expTsum a β := by
  unfold Schar expTsum
  congr 1; ext n
  rw [Subsingleton.elim (n : ZMod 1) 1, map_one, mul_one]

theorem norm_sq_gaussSum_one {q : ℕ} [NeZero q] :
    ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ ^ 2 = if Squarefree q then 1 else 0 := by
  rw [norm_sq_gaussSum, DirichletCharacter.conductor_one]
  simp

theorem norm_gaussSum_le_sqrt_conductor {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) :
    ‖gaussSum ψ ZMod.stdAddChar‖ ≤ √(ψ.conductor : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg (gaussSum ψ ZMod.stdAddChar)), norm_sq_gaussSum]
  split_ifs
  · exact le_rfl
  · exact Real.sqrt_le_sqrt (by positivity)

/-- **Principal and non-principal parts** of `Σ_b |S(b/q + β)|²` for `aₙ` supported on `(n, q) = 1`:
`μ²(q)/φ(q) |S(β)|² ≤ Σ_b |S(b/q + β)|² ≤ μ²(q)/φ(q) |S(β)|² + E²` when
`|τ(ψ)| |S_{ψ⁻¹}(β)| ≤ E` for all `ψ ≠ 1`. -/
theorem sum_units_sq_bounds {q : ℕ} [NeZero q] {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q) (β : ℝ) {E : ℝ}
    (hE : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖ ≤ E) :
    (if Squarefree q then (1 : ℝ) else 0) / q.totient * ‖expTsum a β‖ ^ 2 ≤
        ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖expTsum a ((b.val : ℝ) / q + β)‖ ^ 2 ∧
      ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖expTsum a ((b.val : ℝ) / q + β)‖ ^ 2 ≤
        (if Squarefree q then (1 : ℝ) else 0) / q.totient * ‖expTsum a β‖ ^ 2 + E ^ 2 := by
  classical
  set F := ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖expTsum a ((b.val : ℝ) / q + β)‖ ^ 2
  have key := totient_mul_sum_units ha hcop β
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)), inv_one,
    Schar_one_eq_expTsum hcop, norm_sq_gaussSum_one] at key
  set R := ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
    ‖gaussSum ψ ZMod.stdAddChar‖ ^ 2 * ‖Schar ψ⁻¹ a β‖ ^ 2
  set m : ℝ := if Squarefree q then (1 : ℝ) else 0
  have hR0 : 0 ≤ R := sum_nonneg fun _ _ => by positivity
  have hcard : (univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hR : R ≤ q.totient * E ^ 2 := by
    calc R ≤ ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, E ^ 2 := by
          refine sum_le_sum fun ψ hψ => ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (hE ψ (Finset.ne_of_mem_erase hψ)) 2
      _ = (((univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) * E ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ q.totient * E ^ 2 := by
          gcongr
          rw [← hcard]; exact_mod_cast Finset.card_erase_le
  have hF : F = (m * ‖expTsum a β‖ ^ 2 + R) / q.totient := by
    rw [eq_div_iff hφ.ne']; linarith
  rw [hF]
  constructor
  · rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) hφ.le
  · rw [div_mul_eq_mul_div, div_add' _ _ _ hφ.ne']
    exact div_le_div_of_nonneg_right (by nlinarith) hφ.le

/-! ## Numerics -/

theorem sqrt_x_ge {x : ℝ} (hx : 4.9e26 ≤ x) : 2.2135e13 ≤ √x :=
  Real.le_sqrt_of_sq_le (by nlinarith)

/-- A `K` with `x² ≤ 2^K` and `1.94 K log(3·10⁵) + 1 ≤ 10⁻¹⁵ x`. -/
theorem exists_K {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∃ K : ℕ, x ^ 2 ≤ 2 ^ K ∧ 1.94 * K * Real.log 300000 + 1 ≤ 1e-15 * x := by
  have hx0 : 0 < x := by linarith
  set s := √(√x) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs4 : s ^ 4 = x := by
    rw [hs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hx0.le]
  have hsge : 4.7e6 ≤ s := by
    by_contra h; push Not at h
    have : s ^ 4 < (4.7e6) ^ 4 := pow_lt_pow_left₀ h hs0 (by norm_num)
    rw [hs4] at this; norm_num at this; linarith
  have hlogx : Real.log x ≤ 4 * s := by
    rw [← hs4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
    push_cast; linarith
  have hlog2 : 0.693 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog3 := log_3e5_le
  have hlogxnn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set L := Real.logb 2 (x ^ 2)
  have hL : L = 2 * Real.log x / Real.log 2 := by
    simp only [L, Real.logb, Real.log_pow]; push_cast; ring
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  refine ⟨⌈L⌉₊, ?_, ?_⟩
  · have h1 : (2 : ℝ) ^ L = x ^ 2 := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    calc x ^ 2 = (2 : ℝ) ^ L := h1.symm
      _ ≤ (2 : ℝ) ^ (⌈L⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil L)
      _ = 2 ^ ⌈L⌉₊ := Real.rpow_natCast 2 _
  · have hK : (⌈L⌉₊ : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL0).le
    have hL' : L ≤ 11.55 * s := by
      rw [hL, div_le_iff₀ (by linarith)]; nlinarith
    have hK0 : (0 : ℝ) ≤ ⌈L⌉₊ := Nat.cast_nonneg _
    have hl3 : 0 ≤ Real.log 300000 := Real.log_nonneg (by norm_num)
    have h1 : 1.94 * (⌈L⌉₊ : ℝ) * Real.log 300000 ≤ 1.94 * (11.55 * s + 1) * 12.62 := by
      have := mul_le_mul (show 1.94 * (⌈L⌉₊ : ℝ) ≤ 1.94 * (11.55 * s + 1) by linarith) hlog3 hl3
        (by positivity)
      linarith
    have hs3 : (4.7e6 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hsge 3
    have : 1e-15 * x = 1e-15 * (s * s ^ 3) := by rw [← hs4]; ring
    rw [this]
    nlinarith

theorem norm_expTsum_le_tsum {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) (α : ℝ) :
    ‖expTsum a α‖ ≤ ∑' n, ‖a n‖ := by
  unfold expTsum
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact ha.congr fun n => by rw [norm_mul_e]
  · congr 1; ext n; rw [norm_mul_e]

theorem expTsum_sub {a b : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (α : ℝ) : expTsum (a - b) α = expTsum a α - expTsum b α := by
  unfold expTsum
  have s1 : Summable fun n : ℕ => a n * e (n * α) :=
    Summable.of_norm (ha.congr fun n => by rw [norm_mul_e])
  have s2 : Summable fun n : ℕ => b n * e (n * α) :=
    Summable.of_norm (hb.congr fun n => by rw [norm_mul_e])
  rw [← s1.tsum_sub s2]; congr 1; ext n; simp only [Pi.sub_apply]; ring

/-- **The coprime split**: `Σ_{(n,q)>1} Λ(n)|η₊(n/x)| ≤ 10⁻¹⁵ x` for `q ≤ 3·10⁵`, `x ≥ 4.9·10²⁶`. -/
theorem coprime_split {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ 300000) :
    ∑' n, ‖cP x n - coprimePart q (cP x) n‖ ≤ 1e-15 * x := by
  obtain ⟨K, hK, hD⟩ := exists_K hx
  refine (sum_noncoprime_etaPlus_le (by linarith) hq1 hK).trans ?_
  have h1 : Real.log q ≤ Real.log 300000 :=
    Real.log_le_log (by exact_mod_cast hq1) (by exact_mod_cast hq)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  nlinarith

theorem summable_sub_coprimePart {x : ℝ} (hx : 0 < x) (q : ℕ) :
    Summable fun n => ‖(cP x - coprimePart q (cP x)) n‖ :=
  ((summable_cP hx).add ((summable_cP hx).of_nonneg_of_le (fun n => norm_nonneg _)
    (norm_coprimePart_le q (cP x)))).of_nonneg_of_le (fun n => norm_nonneg _)
    fun n => norm_sub_le _ _

/-- `|S_{η₊}(α) − S'_q(α)| ≤ 10⁻¹⁵ x`. -/
theorem norm_S_sub_coprime_le {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (α : ℝ) : ‖S etaPlus x α - expTsum (coprimePart q (cP x)) α‖ ≤ 1e-15 * x := by
  have hx0 : 0 < x := by linarith
  have hc := summable_cP hx0
  have ha : Summable fun n => ‖coprimePart q (cP x) n‖ :=
    hc.of_nonneg_of_le (fun n => norm_nonneg _) (norm_coprimePart_le q (cP x))
  rw [S_etaPlus_eq_expTsum, ← expTsum_sub hc ha]
  exact (norm_expTsum_le_tsum (summable_sub_coprimePart hx0 q) α).trans (coprime_split hx hq1 hq)

/-- `√c (err_{7.1.4}(c) x + 10⁻¹⁵ x) ≤ 4.25·10⁻⁷ x` for `2 ≤ c ≤ 3·10⁵`. -/
theorem err_scaled_le {x c : ℝ} (hx : 4.9e26 ≤ x) (hc2 : 2 ≤ c) (hc3 : c ≤ 300000) :
    √c * (((7.5e-8 + 7.7e6 / √x) / √c) * x + 1e-15 * x) ≤ 4.25e-7 * x := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < √c := Real.sqrt_pos.2 (by linarith)
  have hs548 : √c ≤ 548 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hr1 : 2.2135e13 ≤ √x := sqrt_x_ge hx
  have e : √c * (((7.5e-8 + 7.7e6 / √x) / √c) * x + 1e-15 * x) =
      (7.5e-8 + 7.7e6 / √x + 1e-15 * √c) * x := by
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_right _ hx0.le
  have h1 : 7.7e6 / √x ≤ 7.7e6 / 2.2135e13 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr1
  have h2 : (7.5e-8 + 7.7e6 / 2.2135e13 + 1e-15 * 548 : ℝ) ≤ 4.25e-7 := by norm_num
  nlinarith

/-! ## The arcs of modulus `q` -/

set_option maxHeartbeats 1000000 in
/-- **[B, §10.3] for one modulus `q`** (`q̃ ≤ 3·10⁵`, `|βx| ≤ 1.2·10⁶/q̃`, `x ≥ 4.9·10²⁶`), with
`S'_q = Σ_{(n,q)=1} Λ(n) η₊(n/x) e(nα)`:
`μ²(q)/φ(q) |S'_q(β)|² ≤ Σ_b |S'_q(b/q + β)|² ≤ μ²(q)/φ(q) |S'_q(β)|² + (4.25·10⁻⁷ x)²` and
`|S'_q(β) − η̂₊(−βx) x| ≤ 2.83·10⁻⁷ x`. -/
theorem arc_chars {x : ℝ} (hx : 4.9e26 ≤ x) {q : ℕ} (hq1 : 1 ≤ q) (hqt : (qt q : ℝ) ≤ 300000)
    {β : ℝ} (hβ : |β * x| ≤ 1200000 / qt q) :
    ((if Squarefree q then (1:ℝ) else 0) / q.totient * ‖expTsum (coprimePart q (cP x)) β‖ ^ 2 ≤
        ∑ b ∈ Bset q, ‖expTsum (coprimePart q (cP x)) ((b : ℝ) / q + β)‖ ^ 2 ∧
      ∑ b ∈ Bset q, ‖expTsum (coprimePart q (cP x)) ((b : ℝ) / q + β)‖ ^ 2 ≤
        (if Squarefree q then (1:ℝ) else 0) / q.totient * ‖expTsum (coprimePart q (cP x)) β‖ ^ 2 +
          (4.25e-7 * x) ^ 2) ∧
      ‖expTsum (coprimePart q (cP x)) β - 𝓕 etaPC (-(β * x)) * x‖ ≤ 2.83e-7 * x := by
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
  set a := coprimePart q (cP x) with ha_def
  have hc := summable_cP hx0
  have ha : Summable fun n => ‖a n‖ :=
    hc.of_nonneg_of_le (fun n => norm_nonneg _) (norm_coprimePart_le q (cP x))
  have hca := summable_sub_coprimePart hx0 q
  have hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q := fun n hn => by
    by_contra h; exact hn (by simp [ha_def, coprimePart, h])
  have hqq : q ≤ qt q := by unfold qt; split_ifs <;> omega
  have hq3 : q ≤ 300000 := by
    have : (q : ℝ) ≤ 300000 := le_trans (by exact_mod_cast hqq) hqt
    exact_mod_cast this
  have hD := coprime_split hx hq1 hq3
  have hDa : ∑' n, ‖(cP x - a) n‖ ≤ 1e-15 * x := by
    refine le_trans (le_of_eq ?_) hD; rfl
  have hqt2 : (2 : ℝ) ≤ qt q := by
    have : 2 ≤ qt q := by unfold qt; split_ifs with h
                          · obtain ⟨k, hk⟩ := h; omega
                          · omega
    exact_mod_cast this
  have hqt0 : (0 : ℝ) < qt q := by linarith
  have hδx : β * x / x = β := by field_simp
  -- the non-principal characters
  have hE : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖ ≤ 4.25e-7 * x := by
    intro ψ hψ
    set c' := ψ⁻¹.conductor with hc'
    haveI : NeZero c' := ⟨DirichletCharacter.conductor_ne_zero _⟩
    have hc'1 : c' ≠ 1 := fun h =>
      hψ (inv_eq_one.1 ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := ψ⁻¹)).2 h))
    have hc'2 : 2 ≤ c' := by have := NeZero.ne c'; omega
    have hc'q : c' ∣ q := DirichletCharacter.conductor_dvd_level _
    have hc'le : c' ≤ q := Nat.le_of_dvd (by omega) hc'q
    have hτ : ‖gaussSum ψ ZMod.stdAddChar‖ ≤ √(c' : ℝ) := by
      have := norm_gaussSum_le_sqrt_conductor ψ
      rwa [← DirichletCharacter.conductor_inv] at this
    set χ := ψ⁻¹.primitiveCharacter
    have hχ : χ.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive _
    have hS : ‖Schar ψ⁻¹ a β‖ ≤ ‖Schar χ (cP x) β‖ + 1e-15 * x := by
      rw [ha_def, Schar_primitive, ← ha_def]
      have h1 : Schar χ a β = Schar χ (cP x) β - Schar χ (cP x - a) β := by
        rw [Schar_sub _ hc ha]; ring
      rw [h1]
      have h2 := norm_Schar_le χ hca β
      have := norm_sub_le (Schar χ (cP x) β) (Schar χ (cP x - a) β)
      linarith
    have hcr : (c' : ℝ) ≤ q := by exact_mod_cast hc'le
    have hT : ‖Schar χ (cP x) β‖ ≤
        ((7.5e-8 + 7.7e6 / √x) / √(c' : ℝ)) * x := by
      rcases Nat.even_or_odd c' with hev | hod
      · have hqev : Even q := (even_iff_two_dvd.1 hev).trans hc'q |> even_iff_two_dvd.2
        have hqtq : qt q = q := by unfold qt; rw [if_pos hqev]
        have hc'3 : c' ≤ 300000 := le_trans hc'le hq3
        have hδ : |β * x| ≤ 1200000 / c' := by
          refine hβ.trans ?_
          rw [hqtq]
          exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast (by omega : 0 < c')) hcr
        have := thm_7_1_4_even hx hev hc'3 χ hχ hδ
        rw [if_neg hc'1, sub_zero, hδx] at this
        exact this
      · have hc'pos : (0 : ℝ) < c' := by exact_mod_cast (by omega : 0 < c')
        have key : 2 * c' ≤ qt q := by
          unfold qt
          split_ifs with hqe
          · have h2 : 2 ∣ q := even_iff_two_dvd.1 hqe
            have hcop2 : Nat.Coprime 2 c' := (Nat.coprime_two_left).2 hod
            exact Nat.le_of_dvd (by omega) (hcop2.mul_dvd_of_dvd_of_dvd h2 hc'q)
          · omega
        have hkey : (2 * c' : ℝ) ≤ qt q := by exact_mod_cast key
        have hc'3 : c' ≤ 150000 := by
          have : (2 * c' : ℝ) ≤ 300000 := hkey.trans hqt
          have : (c' : ℝ) ≤ 150000 := by linarith
          exact_mod_cast this
        have hδ : |β * x| ≤ 600000 / c' := by
          refine hβ.trans ?_
          rw [div_le_div_iff₀ hqt0 hc'pos]; nlinarith
        have := thm_7_1_4_odd hx hod hc'3 χ hχ hδ
        rw [if_neg hc'1, sub_zero, hδx] at this
        exact this
    have hc'3r : (c' : ℝ) ≤ 300000 := hcr.trans (by exact_mod_cast hq3)
    have hc'2r : (2 : ℝ) ≤ c' := by exact_mod_cast hc'2
    calc ‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖
        ≤ √(c' : ℝ) * (((7.5e-8 + 7.7e6 / √x) / √(c' : ℝ)) * x + 1e-15 * x) :=
          mul_le_mul hτ (hS.trans (by linarith)) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ 4.25e-7 * x := err_scaled_le hx hc'2r hc'3r
  refine ⟨?_, ?_⟩
  · have hsplit := sum_units_sq_bounds ha hcop β hE
    rw [sum_Bset_eq_units (fun t => ‖expTsum a t‖ ^ 2) β]
    exact hsplit
  · -- the principal character: [B, Thm 7.1.4] for `q = 1`
    have hδ1 : |β * x| ≤ 600000 := by
      refine hβ.trans ?_
      rw [div_le_iff₀ hqt0]; nlinarith
    have h1 := thm_7_1_4_one hx (1 : DirichletCharacter ℂ 1) hδ1
    rw [hδx, Schar_level_one] at h1
    have h2 : expTsum a β = expTsum (cP x) β - expTsum (cP x - a) β := by
      rw [expTsum_sub hc ha]; ring
    have h3 := (norm_expTsum_le_tsum hca β).trans hDa
    have hsx := sqrt_x_ge hx
    have h4 : 6.24e6 / √x ≤ 6.24e6 / 2.2135e13 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsx
    rw [h2]
    calc ‖expTsum (cP x) β - expTsum (cP x - a) β - 𝓕 etaPC (-(β * x)) * x‖
        ≤ ‖expTsum (cP x) β - 𝓕 etaPC (-(β * x)) * x‖ + ‖expTsum (cP x - a) β‖ := by
          have := norm_sub_le (expTsum (cP x) β - 𝓕 etaPC (-(β * x)) * x) (expTsum (cP x - a) β)
          calc _ = ‖expTsum (cP x) β - 𝓕 etaPC (-(β * x)) * x - expTsum (cP x - a) β‖ := by
                congr 1; ring
            _ ≤ _ := this
      _ ≤ (1e-18 + 6.24e6 / √x) * x + 1e-15 * x := add_le_add h1 h3
      _ ≤ 2.83e-7 * x := by nlinarith

end TernaryGoldbach.MajorArcs
