import TernaryGoldbach.MinorArcs.Bombieri
import TernaryGoldbach.MinorArcs.LargeSieveProof

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# The base gap of repair 3: `𝔐_{8,r₀}(y) \ 𝔐_{8,r₀}(x)`, via [H, Cor 7.1.3]

* `totient_mul_norm_le`: the character expansion
  `φ(q) |S(b/q + β)| ≤ Σ_ψ |τ(ψ)| |S_{ψ⁻¹}(β)|` for coefficients supported on `(n, q) = 1`.
-/

open Finset
open TernaryGoldbach (expTsum e)

namespace TernaryGoldbach.MinorArcs

/-- **Character expansion**: for `aₙ` supported on `n` coprime to `q` and a unit `b`,
`φ(q) S(b/q + β) = Σ_ψ ψ(b⁻¹) τ(ψ) S_{ψ⁻¹}(β)`, hence
`φ(q) |S(b/q + β)| ≤ Σ_ψ |τ(ψ)| |S_{ψ⁻¹}(β)|`. -/
theorem totient_mul_norm_le {q : ℕ} [NeZero q] {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q) (β : ℝ)
    {b : ZMod q} (hb : IsUnit b) :
    q.totient * ‖expTsum a ((b.val : ℝ) / q + β)‖ ≤
      ∑ ψ : DirichletCharacter ℂ q, ‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖ := by
  have hid : ∑ ψ : DirichletCharacter ℂ q, ψ b⁻¹ * (gaussSum ψ ZMod.stdAddChar * Schar ψ⁻¹ a β) =
      (q.totient : ℂ) * expTsum a ((b.val : ℝ) / q + β) := by
    simp_rw [← sum_char_mul_S _ ha hcop β, mul_sum]
    rw [sum_comm]
    have : ∀ c : ZMod q, ∑ ψ : DirichletCharacter ℂ q, ψ b⁻¹ * (ψ c * expTsum a (c.val / q + β)) =
        if b = c then (q.totient : ℂ) * expTsum a (c.val / q + β) else 0 := by
      intro c
      simp_rw [← mul_assoc, ← sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb c]
      split_ifs <;> simp
    rw [sum_congr rfl fun c _ => this c, sum_ite_eq]
    simp
  have h1 : ‖(q.totient : ℂ) * expTsum a ((b.val : ℝ) / q + β)‖ =
      q.totient * ‖expTsum a ((b.val : ℝ) / q + β)‖ := by
    rw [norm_mul, Complex.norm_natCast]
  rw [← h1, ← hid]
  refine (norm_sum_le _ _).trans (sum_le_sum fun ψ _ => ?_)
  rw [norm_mul, norm_mul]
  have : ‖ψ b⁻¹‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
  calc ‖ψ b⁻¹‖ * (‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖)
      ≤ 1 * (‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := one_mul _

theorem norm_Schar_le {d : ℕ} (χ : DirichletCharacter ℂ d) {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) (β : ℝ) : ‖Schar χ a β‖ ≤ ∑' n, ‖a n‖ := by
  have hle : ∀ n : ℕ, ‖a n * χ (n : ZMod d) * e (n * β)‖ ≤ ‖a n‖ := fun n => by
    rw [norm_mul, norm_mul, norm_e, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hs : Summable fun n : ℕ => ‖a n * χ (n : ZMod d) * e (n * β)‖ :=
    ha.of_nonneg_of_le (fun n => norm_nonneg _) hle
  exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hle hs ha)

theorem summable_Schar {d : ℕ} (χ : DirichletCharacter ℂ d) {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) (β : ℝ) :
    Summable fun n : ℕ => a n * χ (n : ZMod d) * e (n * β) := by
  refine Summable.of_norm (ha.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_)
  rw [norm_mul, norm_mul, norm_e, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

theorem Schar_sub {d : ℕ} (χ : DirichletCharacter ℂ d) {a b : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) (β : ℝ) :
    Schar χ (a - b) β = Schar χ a β - Schar χ b β := by
  unfold Schar
  rw [← (summable_Schar χ ha β).tsum_sub (summable_Schar χ hb β)]
  congr 1; ext n; simp only [Pi.sub_apply]; ring

/-- The restriction to `(n, q) = 1`. -/
noncomputable def coprimePart (q : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ := if Nat.Coprime n q then c n else 0

theorem norm_coprimePart_le (q : ℕ) (c : ℕ → ℂ) (n : ℕ) : ‖coprimePart q c n‖ ≤ ‖c n‖ := by
  unfold coprimePart; split_ifs <;> simp

/-- For `ψ` mod `q` and `aₙ` supported on `(n, q) = 1`, `S_ψ = S_{χ}` with `χ` the primitive
character inducing `ψ`. -/
theorem Schar_primitive {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (c : ℕ → ℂ) (β : ℝ) :
    Schar ψ (coprimePart q c) β = Schar ψ.primitiveCharacter (coprimePart q c) β := by
  unfold Schar
  congr 1; ext n
  have h := changeLevel_apply_natCast (DirichletCharacter.conductor_dvd_level ψ)
    ψ.primitiveCharacter n
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  rw [h]
  unfold coprimePart
  split_ifs <;> simp

/-- **The major-arc bound from character sums.** Let `D ≥ Σ_{(n,q) > 1} |cₙ|`. Suppose that for
every `ψ` mod `q`, the sum over the primitive character `χ` inducing `ψ⁻¹` satisfies
`|S_χ(β) - [ψ = 1] M| ≤ E`. Then for a unit `b`,
`|S(b/q + β)| ≤ D + |M|/φ(q) + √q (E + D)`. -/
theorem norm_expTsum_le_of_chars {q : ℕ} [NeZero q] {c : ℕ → ℂ}
    (hc : Summable fun n => ‖c n‖) (β : ℝ) {b : ZMod q} (hb : IsUnit b) {M : ℂ} {E D : ℝ}
    (hD : ∑' n, ‖c n - coprimePart q c n‖ ≤ D)
    (hchar : ∀ ψ : DirichletCharacter ℂ q,
      ‖Schar ψ⁻¹.primitiveCharacter c β - (if ψ = 1 then M else 0)‖ ≤ E) :
    ‖expTsum c ((b.val : ℝ) / q + β)‖ ≤ D + ‖M‖ / q.totient + √q * (E + D) := by
  classical
  set a := coprimePart q c with ha_def
  have ha : Summable fun n => ‖a n‖ :=
    hc.of_nonneg_of_le (fun n => norm_nonneg _) (norm_coprimePart_le q c)
  have hca : Summable fun n => ‖c n - a n‖ := (hc.add ha).of_nonneg_of_le (fun n => norm_nonneg _)
    fun n => norm_sub_le _ _
  have hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q := fun n hn => by
    by_contra h; exact hn (by simp [ha_def, coprimePart, h])
  have hD0 : 0 ≤ D := (tsum_nonneg fun n => norm_nonneg _).trans hD
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hchar 1)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  -- split `c = a + (c - a)`
  have hsplit : expTsum c ((b.val : ℝ) / q + β) =
      expTsum a ((b.val : ℝ) / q + β) + expTsum (c - a) ((b.val : ℝ) / q + β) := by
    unfold expTsum
    have s1 : Summable fun n : ℕ => a n * e (n * ((b.val : ℝ) / q + β)) :=
      Summable.of_norm (ha.congr fun n => by rw [norm_mul_e])
    have s2 : Summable fun n : ℕ => (c - a) n * e (n * ((b.val : ℝ) / q + β)) :=
      Summable.of_norm (hca.congr fun n => by rw [norm_mul_e]; rfl)
    rw [← s1.tsum_add s2]
    congr 1; ext n; simp only [Pi.sub_apply]; ring
  have hrest : ‖expTsum (c - a) ((b.val : ℝ) / q + β)‖ ≤ D := by
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact hca.congr fun n => by rw [norm_mul_e]; rfl
    · refine le_trans (le_of_eq ?_) hD
      congr 1; ext n; rw [norm_mul_e]; rfl
  -- the coprime part
  have hmain := totient_mul_norm_le ha hcop β hb
  have hψ : ∀ ψ : DirichletCharacter ℂ q, ‖Schar ψ⁻¹ a β‖ ≤ (if ψ = 1 then ‖M‖ else 0) + E + D := by
    intro ψ
    rw [ha_def, Schar_primitive, ← ha_def]
    have h1 : Schar ψ⁻¹.primitiveCharacter a β =
        Schar ψ⁻¹.primitiveCharacter c β - Schar ψ⁻¹.primitiveCharacter (c - a) β := by
      rw [Schar_sub _ hc ha]; ring
    rw [h1]
    have h2 := norm_Schar_le ψ⁻¹.primitiveCharacter hca β
    have h3 := hchar ψ
    have h4 : ‖(if ψ = 1 then M else 0)‖ ≤ if ψ = 1 then ‖M‖ else 0 := by
      split_ifs <;> simp
    calc ‖Schar ψ⁻¹.primitiveCharacter c β - Schar ψ⁻¹.primitiveCharacter (c - a) β‖
        ≤ ‖Schar ψ⁻¹.primitiveCharacter c β - (if ψ = 1 then M else 0)‖ +
          ‖(if ψ = 1 then M else 0)‖ + ‖Schar ψ⁻¹.primitiveCharacter (c - a) β‖ := by
          have := norm_sub_le (Schar ψ⁻¹.primitiveCharacter c β) (Schar ψ⁻¹.primitiveCharacter (c - a) β)
          have := norm_le_norm_sub_add (Schar ψ⁻¹.primitiveCharacter c β) (if ψ = 1 then M else 0)
          linarith
      _ ≤ E + (if ψ = 1 then ‖M‖ else 0) + D := by
          gcongr
          exact h2.trans hD
      _ = _ := by ring
  have hτ : ∀ ψ : DirichletCharacter ℂ q, ‖gaussSum ψ ZMod.stdAddChar‖ ≤ √q := by
    intro ψ
    have h := norm_sq_gaussSum ψ
    rw [← Real.sqrt_sq (norm_nonneg (gaussSum ψ ZMod.stdAddChar)), h]
    have hle : ψ.conductor ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (DirichletCharacter.conductor_dvd_level ψ)
    split_ifs
    · exact Real.sqrt_le_sqrt (by exact_mod_cast hle)
    · exact Real.sqrt_le_sqrt (by positivity)
  have hτ1 : ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ ≤ 1 := by
    have h := norm_sq_gaussSum (1 : DirichletCharacter ℂ q)
    rw [DirichletCharacter.conductor_one] at h
    have : ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ ^ 2 ≤ 1 := by
      rw [h]; split_ifs <;> norm_num
    nlinarith [norm_nonneg (gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar)]
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hsum : ∑ ψ : DirichletCharacter ℂ q, ‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖ ≤
      ‖M‖ + q.totient * (√q * (E + D)) := by
    calc ∑ ψ : DirichletCharacter ℂ q, ‖gaussSum ψ ZMod.stdAddChar‖ * ‖Schar ψ⁻¹ a β‖
        ≤ ∑ ψ : DirichletCharacter ℂ q, ((if ψ = 1 then ‖M‖ else 0) + √q * (E + D)) := by
          refine sum_le_sum fun ψ _ => ?_
          have h1 := hψ ψ
          by_cases h : ψ = 1
          · subst h
            simp only [ite_true] at h1 ⊢
            have h2 : ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ * ‖M‖ ≤ ‖M‖ :=
              mul_le_of_le_one_left (norm_nonneg M) hτ1
            have h3 : ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ * (E + D) ≤ √q * (E + D) :=
              mul_le_mul_of_nonneg_right (hτ 1) (by positivity)
            nlinarith [norm_nonneg (gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar)]
          · simp only [h, ite_false, zero_add] at h1 ⊢
            exact mul_le_mul (hτ ψ) h1 (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = ‖M‖ + q.totient * (√q * (E + D)) := by
          rw [sum_add_distrib, sum_ite_eq' univ (1 : DirichletCharacter ℂ q), sum_const, hcard]
          simp
  have hcop_bound : ‖expTsum a ((b.val : ℝ) / q + β)‖ ≤ ‖M‖ / q.totient + √q * (E + D) := by
    have := hmain.trans hsum
    rw [div_add' _ _ _ hφ.ne', le_div_iff₀ hφ]
    nlinarith
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith

end TernaryGoldbach.MinorArcs
