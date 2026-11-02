import TernaryGoldbach.Prelim.GaussInduced

/-!
# Bombieri's identity for prime-supported exponential sums [H, §12.1], [Bom74, pp. 24–25]

For `aₙ` (in `ℓ¹`) supported on `n` coprime to `q`, `S(α) = Σ aₙ e(αn)`, `S_χ(β) = Σ aₙ χ(n) e(βn)`:

* `parseval_chars`: `Σ_ψ |Σ_b ψ(b) F(b)|² = φ(q) Σ_{b unit} |F(b)|²` (orthogonality);
* `sum_char_mul_S`: `Σ_b ψ(b) S(b/q + β) = τ(ψ) S_{ψ⁻¹}(β)`;
* hence `φ(q) Σ_{b unit} |S(b/q + β)|² = Σ_ψ |τ(ψ)|² |S_{ψ⁻¹}(β)|²` (`totient_mul_sum_units`).

Proved, with no `sorry`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach

/-- For a unit `b` of `ZMod q`, `ψ⁻¹(b) = ψ(b⁻¹)`. -/
theorem dirichlet_inv_apply_unit {q : ℕ} (ψ : DirichletCharacter ℂ q) {b : ZMod q} (hb : IsUnit b) :
    ψ⁻¹ b = ψ b⁻¹ := by
  obtain ⟨u, rfl⟩ := hb
  rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

/-- **Parseval for the characters mod `q`**: `Σ_ψ |Σ_b ψ(b) F(b)|² = φ(q) Σ_{b unit} |F(b)|²`. -/
theorem parseval_chars {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    ∑ ψ : DirichletCharacter ℂ q, ‖∑ b, ψ b * F b‖ ^ 2 =
      q.totient * ∑ b ∈ univ.filter IsUnit, ‖F b‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  have hs : ∀ (ψ : DirichletCharacter ℂ q) (b : ZMod q), (starRingEnd ℂ) (ψ b) = ψ⁻¹ b :=
    fun ψ b => MulChar.star_apply' ψ b
  simp_rw [← Complex.mul_conj', map_sum, map_mul, hs, sum_mul, mul_sum]
  -- `Σ_ψ Σ_b Σ_b' ψ(b) F(b) ψ⁻¹(b') F̄(b')`
  rw [sum_comm]
  have hinner : ∀ b : ZMod q, ∑ ψ : DirichletCharacter ℂ q, ∑ b' : ZMod q,
      ψ b * F b * (ψ⁻¹ b' * (starRingEnd ℂ) (F b')) =
      if IsUnit b then (q.totient : ℂ) * (F b * (starRingEnd ℂ) (F b)) else 0 := by
    intro b
    rw [sum_comm]
    have h1 : ∀ b' : ZMod q, ∑ ψ : DirichletCharacter ℂ q,
        ψ b * F b * (ψ⁻¹ b' * (starRingEnd ℂ) (F b')) =
        if IsUnit b' ∧ b' = b then (q.totient : ℂ) * (F b * (starRingEnd ℂ) (F b')) else 0 := by
      intro b'
      by_cases hb' : IsUnit b'
      · have h2 := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb' b
        have h3 : ∑ ψ : DirichletCharacter ℂ q, ψ b * F b * (ψ⁻¹ b' * (starRingEnd ℂ) (F b')) =
            (∑ ψ : DirichletCharacter ℂ q, ψ b'⁻¹ * ψ b) * (F b * (starRingEnd ℂ) (F b')) := by
          rw [sum_mul]
          refine sum_congr rfl fun ψ _ => ?_
          rw [dirichlet_inv_apply_unit ψ hb']; ring
        rw [h3, h2]
        by_cases hbb : b' = b
        · rw [ite_eq_left hbb, ite_eq_left ⟨hb', hbb⟩]
        · rw [ite_eq_right hbb, ite_eq_right (fun h => hbb h.2), zero_mul]
      · rw [ite_eq_right (fun h => hb' h.1)]
        refine sum_eq_zero fun ψ _ => ?_
        rw [MulChar.map_nonunit _ hb']; ring
    rw [sum_congr rfl fun b' _ => h1 b']
    by_cases hb : IsUnit b
    · rw [ite_eq_left hb, Finset.sum_eq_single b]
      · rw [ite_eq_left ⟨hb, rfl⟩]
      · intro b' _ hne; rw [ite_eq_right (fun h => hne h.2)]
      · intro h; exact absurd (mem_univ b) h
    · rw [ite_eq_right hb]
      refine sum_eq_zero fun b' _ => ?_
      rw [ite_eq_right]; rintro ⟨hu, rfl⟩; exact hb hu
  rw [sum_congr rfl fun b _ => hinner b, ← sum_filter, ← mul_sum]

/-- `S_ψ(β) = Σ aₙ ψ(n) e(nβ)`. -/
noncomputable def Schar {q : ℕ} (ψ : DirichletCharacter ℂ q) (a : ℕ → ℂ) (β : ℝ) : ℂ :=
  ∑' n : ℕ, a n * ψ (n : ZMod q) * e (n * β)

/-- **Twisting by a character**: for `aₙ` supported on `n` coprime to `q`,
`Σ_b ψ(b) S(b/q + β) = τ(ψ) S_{ψ⁻¹}(β)`. -/
theorem sum_char_mul_S {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q) (β : ℝ) :
    ∑ b : ZMod q, ψ b * expTsum a (b.val / q + β) =
      gaussSum ψ ZMod.stdAddChar * Schar ψ⁻¹ a β := by
  have hsum : ∀ b : ZMod q, Summable fun n : ℕ => ψ b * (a n * e (n * (b.val / q + β))) := by
    intro b
    have h1 : Summable fun n : ℕ => ‖a n * e (n * (b.val / q + β))‖ := by
      refine ha.congr fun n => ?_
      rw [norm_mul_e]
    exact (Summable.of_norm h1).mul_left (ψ b)
  have e1 : ∀ b : ZMod q, ψ b * expTsum a (b.val / q + β) =
      ∑' n : ℕ, ψ b * (a n * e (n * (b.val / q + β))) := fun b => by
    rw [expTsum, tsum_mul_left]
  rw [Finset.sum_congr rfl fun b _ => e1 b, ← Summable.tsum_finsetSum fun b _ => hsum b, Schar,
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  by_cases han : a n = 0
  · simp [han]
  have hu : IsUnit (n : ZMod q) := (ZMod.unitOfCoprime n (hcop n han)).isUnit
  have hterm : ∀ b : ZMod q, ψ b * (a n * e (n * (b.val / q + β))) =
      a n * e (n * β) * (ψ b * ZMod.stdAddChar ((n : ZMod q) * b)) := by
    intro b
    have h2 : ((n : ZMod q) * b) = ((n * b.val : ℕ) : ZMod q) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [h2, stdAddChar_natCast_eq_e, mul_add, e_add]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun b _ => hterm b, ← Finset.mul_sum]
  have hg : ∑ b : ZMod q, ψ b * ZMod.stdAddChar ((n : ZMod q) * b) =
      gaussSum ψ (ZMod.stdAddChar.mulShift (hu.unit : ZMod q)) := by
    rw [gaussSum, IsUnit.unit_spec]
    rfl
  rw [hg, gaussSum_mulShift_eq ψ ZMod.stdAddChar hu.unit, IsUnit.unit_spec]
  ring

/-- `φ(q) Σ_{b unit} |S(b/q + β)|² = Σ_ψ |τ(ψ)|² |S_{ψ⁻¹}(β)|²`. -/
theorem totient_mul_sum_units {q : ℕ} [NeZero q] {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n q) (β : ℝ) :
    q.totient * ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖expTsum a ((b.val : ℝ) / q + β)‖ ^ 2 =
      ∑ ψ : DirichletCharacter ℂ q, ‖gaussSum ψ ZMod.stdAddChar‖ ^ 2 * ‖Schar ψ⁻¹ a β‖ ^ 2 := by
  rw [← parseval_chars]
  refine sum_congr rfl fun ψ _ => ?_
  rw [sum_char_mul_S ψ ha hcop, norm_mul, mul_pow]

/-- `(χ↑q)(b) = [(b, q) = 1] χ(b)` for `χ` mod `d ∣ q`. -/
theorem changeLevel_apply_natCast {d q : ℕ} [NeZero q] (h : d ∣ q) (χ : DirichletCharacter ℂ d)
    (b : ℕ) :
    DirichletCharacter.changeLevel h χ (b : ZMod q) = if Nat.Coprime b q then χ (b : ZMod d) else 0 := by
  split_ifs with hb
  · have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h (ZMod.unitOfCoprime b hb)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast h] at this
    exact this
  · apply MulChar.map_nonunit
    rwa [ZMod.isUnit_iff_coprime]

/-- **`|τ(ψ)|²` for any `ψ` mod `q`**, with `c` the conductor:
`|τ(ψ)|² = c` if `q/c` is squarefree and coprime to `c`, and `0` otherwise. -/
theorem norm_sq_gaussSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) :
    ‖gaussSum ψ ZMod.stdAddChar‖ ^ 2 =
      if Squarefree (q / ψ.conductor) ∧ Nat.Coprime (q / ψ.conductor) ψ.conductor
      then (ψ.conductor : ℝ) else 0 := by
  set c := ψ.conductor with hc
  have hc0 : c ≠ 0 := DirichletCharacter.conductor_ne_zero ψ
  have : NeZero c := ⟨hc0⟩
  have hcq : c ∣ q := DirichletCharacter.conductor_dvd_level ψ
  set χ := ψ.primitiveCharacter
  have hψ : DirichletCharacter.changeLevel hcq χ = ψ := DirichletCharacter.changeLevel_primitiveCharacter ψ
  set r := q / c with hr
  have hqr : q = c * r := (Nat.mul_div_cancel' hcq).symm
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero (by
    intro h0; rw [h0, mul_zero] at hqr; exact NeZero.ne q hqr)
  set f : ℕ → ℂ := fun b => χ (b : ZMod c)
  have hτ : gaussSum ψ ZMod.stdAddChar = (μ r : ℂ) * f r * gaussSum χ ZMod.stdAddChar := by
    rw [gaussSum_eq_sum_range, gaussSum_eq_sum_range]
    have h1 : ∑ b ∈ range q, ψ (b : ZMod q) * e (b / q) =
        ∑ b ∈ (range (c * r)).filter (fun b => Nat.Coprime b (c * r)), f b * e (b / (c * r)) := by
      have hqR : (c : ℝ) * r = q := by rw [hqr]; push_cast; ring
      rw [sum_filter, ← hqr, hqR]
      refine sum_congr rfl fun b _ => ?_
      rw [← hψ, changeLevel_apply_natCast]
      split_ifs <;> simp [f]
    rw [h1, gauss_induced (Nat.pos_of_ne_zero hc0) hr1 f]
    · intro b; simp [f]
    · intro a b; simp [f, map_mul]
    · intro b hb; simp only [f]
      apply MulChar.map_nonunit; rwa [ZMod.isUnit_iff_coprime]
  rw [hτ, norm_mul, norm_mul, mul_pow, mul_pow,
    norm_sq_gaussSum_of_isPrimitive (DirichletCharacter.primitiveCharacter_isPrimitive ψ)]
  have hμ : ‖(μ r : ℂ)‖ ^ 2 = if Squarefree r then 1 else 0 := by
    split_ifs with hs
    · have := ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs
      rw [Complex.norm_intCast, ← Int.cast_abs, this]; norm_num
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; simp
  have hχ : ‖f r‖ ^ 2 = if Nat.Coprime r c then 1 else 0 := by
    split_ifs with hcop
    · have := DirichletCharacter.unit_norm_eq_one χ (ZMod.unitOfCoprime r hcop)
      rw [ZMod.coe_unitOfCoprime] at this
      simp only [f, this, one_pow]
    · simp only [f]
      rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]; simp
  rw [hμ, hχ]
  split_ifs <;> simp_all

/-- The weight `w(q, c) = c [q/c squarefree and coprime to c]` (`= |τ(ψ)|²` for `ψ` mod `q` of
conductor `c`). -/
noncomputable def wq (q c : ℕ) : ℝ :=
  if Squarefree (q / c) ∧ Nat.Coprime (q / c) c then (c : ℝ) else 0

/-- **Bombieri's identity, lifted to a common modulus `L`**: for `q ∣ L` and `aₙ` supported on
`n` coprime to `L`,
`φ(q) Σ_{b unit mod q} |S(b/q + β)|² = Σ_{Ψ mod L, cond Ψ ∣ q} w(q, cond Ψ) |S_{Ψ⁻¹}(β)|²`. -/
theorem totient_mul_sum_units_lift {q L : ℕ} [NeZero q] [NeZero L] (hqL : q ∣ L) {a : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n L) (β : ℝ) :
    q.totient * ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖expTsum a ((b.val : ℝ) / q + β)‖ ^ 2 =
      ∑ Ψ : DirichletCharacter ℂ L,
        (if Ψ.conductor ∣ q then wq q Ψ.conductor else 0) * ‖Schar Ψ⁻¹ a β‖ ^ 2 := by
  classical
  have hcopq : ∀ n, a n ≠ 0 → Nat.Coprime n q := fun n hn => (hcop n hn).coprime_dvd_right hqL
  rw [totient_mul_sum_units ha hcopq]
  -- the right side as a sum over the image of `changeLevel`
  have himg : (univ : Finset (DirichletCharacter ℂ q)).image (DirichletCharacter.changeLevel hqL) =
      univ.filter (fun Ψ : DirichletCharacter ℂ L => Ψ.conductor ∣ q) := by
    ext Ψ
    simp only [mem_image, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨ψ, rfl⟩
      rw [DirichletCharacter.conductor_changeLevel]
      exact DirichletCharacter.conductor_dvd_level ψ
    · intro h
      have hm := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd Ψ hqL).2 h
      rw [DirichletCharacter.mem_conductorSet_iff] at hm
      obtain ⟨_, ψ, hψ⟩ := hm
      exact ⟨ψ, hψ.symm⟩
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter, ← himg, sum_image fun ψ₁ _ ψ₂ _ h => DirichletCharacter.changeLevel_injective hqL h]
  refine sum_congr rfl fun ψ _ => ?_
  have hS : Schar (DirichletCharacter.changeLevel hqL ψ)⁻¹ a β = Schar ψ⁻¹ a β := by
    unfold Schar
    refine tsum_congr fun n => ?_
    by_cases han : a n = 0
    · simp [han]
    rw [← map_inv, changeLevel_apply_natCast, if_pos (hcop n han)]
  rw [DirichletCharacter.conductor_changeLevel, norm_sq_gaussSum, hS, wq]

end TernaryGoldbach
