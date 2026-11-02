import TernaryGoldbach.Prelim.Liouville
import TernaryGoldbach.Prelim.RamareGq

/-!
# The convolution behind Ramaré's (12.12)

With `v(n) = [n odd]/n`, `g_d(n) = [(n,d)=1] μ²(n)/φ(n)` and `h_d = g_d ∗ μv` (so `g_d = h_d ∗ v`):
* `h_d(p) = 1/(p(p−1))`, `h_d(p²) = −1/(p(p−1))` for odd `p ∤ d`; `h_d(p) = −1/p` for odd `p ∣ d`;
  `h_d(2) = 1` if `2 ∤ d`; all other prime-power values vanish (`hD_p`, `hD_p2`, `hD_pk`);
* `G_d(R) = ∑_{a ≤ R} h_d(a) V(R/a)` with `V(x) = ∑_{b ≤ x, b odd} 1/b` (`GqP_eq`).

Compared with [Ram95, Lemma 3.4], which convolves with `1/n`, the odd harmonic sums have a smaller
error constant (`½(γ + log 2) ≈ 0.635` against `0.9105`).
-/

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.Prelim.RamPf

open TernaryGoldbach.Prelim (conv_pp GqP)

/-- `g_d(n) = [(n,d)=1] μ²(n)/φ(n)`. -/
noncomputable def gD (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n d then ((μ n : ℝ) ^ 2) / (Nat.totient n : ℝ) else 0, by simp⟩

/-- `v(n) = [n odd]/n`. -/
noncomputable def vO : ArithmeticFunction ℝ := ⟨fun n => if Odd n then ((n : ℝ))⁻¹ else 0, by simp⟩

/-- `w(n) = μ(n) v(n)`. -/
noncomputable def wO : ArithmeticFunction ℝ := pmul (μ : ArithmeticFunction ℝ) vO

/-- `h_d = g_d ∗ w`. -/
noncomputable def hD (d : ℕ) : ArithmeticFunction ℝ := gD d * wO

theorem gD_apply (d n : ℕ) :
    gD d n = if Nat.Coprime n d then ((μ n : ℝ) ^ 2) / (Nat.totient n : ℝ) else 0 := rfl

theorem vO_apply (n : ℕ) : vO n = if Odd n then ((n : ℝ))⁻¹ else 0 := rfl

theorem wO_apply (n : ℕ) : wO n = (μ n : ℝ) * vO n := by
  simp [wO, pmul_apply, intCoe_apply]

theorem vO_mul (m n : ℕ) : vO (m * n) = vO m * vO n := by
  simp only [vO_apply, Nat.odd_mul]
  by_cases hm : Odd m <;> by_cases hn : Odd n <;> simp [hm, hn] <;> ring

theorem isMult_vO : IsMultiplicative vO :=
  ⟨by simp [vO_apply], fun {m n} _ => vO_mul m n⟩

theorem isMult_gD (d : ℕ) : IsMultiplicative (gD d) := by
  refine ⟨by simp [gD_apply], fun {m n} hmn => ?_⟩
  simp only [gD_apply, Nat.coprime_mul_iff_left,
    isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  by_cases hm : Nat.Coprime m d
  · by_cases hn : Nat.Coprime n d
    · rw [if_pos ⟨hm, hn⟩, if_pos hm, if_pos hn]; push_cast; ring
    · rw [if_neg (fun h => hn h.2), if_neg hn, mul_zero]
  · rw [if_neg (fun h => hm h.1), if_neg hm, zero_mul]

theorem isMult_wO : IsMultiplicative wO := isMultiplicative_moebius.intCast.pmul isMult_vO

theorem isMult_hD (d : ℕ) : IsMultiplicative (hD d) := (isMult_gD d).mul isMult_wO

/-- Pointwise multiplication by a completely multiplicative function commutes with `∗`. -/
theorem pmul_mul_pmul (F G c : ArithmeticFunction ℝ) (hc : ∀ m n, c (m * n) = c m * c n) :
    pmul F c * pmul G c = pmul (F * G) c := by
  ext n
  simp only [pmul_apply, mul_apply, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.1 hx).1, hc]; ring

theorem wO_mul_vO : wO * vO = 1 := by
  have hz : pmul ((ζ : ArithmeticFunction ℝ)) vO = vO := by
    ext n
    rw [pmul_apply, natCoe_apply, zeta_apply]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · simp [Nat.pos_iff_ne_zero.1 h]
  have e : wO * vO = pmul (μ : ArithmeticFunction ℝ) vO * pmul ((ζ : ArithmeticFunction ℝ)) vO := by
    rw [hz]; rfl
  rw [e, pmul_mul_pmul _ _ _ vO_mul, coe_moebius_mul_coe_zeta]
  ext n
  rw [pmul_apply, one_apply]
  split_ifs with h
  · subst h; simp [vO_apply]
  · simp

theorem gD_eq (d : ℕ) : gD d = hD d * vO := by
  rw [hD, mul_assoc, wO_mul_vO, mul_one]

/-! ### Values at prime powers -/

theorem gD_p {d p : ℕ} (hp : p.Prime) : gD d p = if p ∣ d then 0 else 1 / ((p : ℝ) - 1) := by
  rw [gD_apply]
  have hcop : Nat.Coprime p d ↔ ¬ p ∣ d := hp.coprime_iff_not_dvd
  by_cases h : p ∣ d
  · rw [if_neg (by rw [hcop]; exact not_not.2 h), if_pos h]
  · rw [if_pos (hcop.2 h), if_neg h, moebius_apply_prime hp, Nat.totient_prime hp]
    push_cast [Nat.cast_sub hp.one_le]; ring

theorem gD_pk {d p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : gD d (p ^ k) = 0 := by
  rw [gD_apply, moebius_apply_prime_pow hp (by omega)]; simp [show k ≠ 1 by omega]

theorem vO_p {p : ℕ} (hp : p.Prime) : vO p = if p = 2 then 0 else 1 / (p : ℝ) := by
  rw [vO_apply]
  by_cases h2 : p = 2
  · subst h2; simp
  · rw [if_pos (hp.odd_of_ne_two h2), if_neg h2, one_div]

theorem wO_p {p : ℕ} (hp : p.Prime) : wO p = if p = 2 then 0 else -1 / (p : ℝ) := by
  rw [wO_apply, vO_p hp, moebius_apply_prime hp]
  split_ifs <;> push_cast <;> ring

theorem wO_pk {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : wO (p ^ k) = 0 := by
  rw [wO_apply, moebius_apply_prime_pow hp (by omega)]; simp [show k ≠ 1 by omega]

theorem hD_p {d p : ℕ} (hp : p.Prime) : hD d p = gD d p + wO p := by
  have h := conv_pp (gD d) wO hp 1
  rw [pow_one] at h
  rw [hD, h, sum_range_succ, sum_range_one]
  simp [(isMult_gD d).map_one, isMult_wO.map_one]
  ring

theorem hD_p2 {d p : ℕ} (hp : p.Prime) : hD d (p ^ 2) = gD d p * wO p := by
  rw [hD, conv_pp _ _ hp, sum_range_succ, sum_range_succ, sum_range_one]
  simp [(isMult_gD d).map_one, isMult_wO.map_one, gD_pk hp (le_refl 2), wO_pk hp (le_refl 2)]

theorem hD_pk {d p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) : hD d (p ^ k) = 0 := by
  rw [hD, conv_pp _ _ hp]
  refine sum_eq_zero fun i hi => ?_
  have hi' := mem_range.1 hi
  rcases Nat.lt_or_ge i 2 with h | h
  · rw [wO_pk hp (by omega), mul_zero]
  · rw [gD_pk hp h, zero_mul]

/-! ### `G_d(R) = ∑_{a ≤ R} h_d(a) V(R/a)` -/

/-- `V(x) = ∑_{b ≤ x, b odd} 1/b`. -/
noncomputable def V (x : ℝ) : ℝ := ∑ b ∈ Icc 1 ⌊x⌋₊, vO b

theorem GqP_eq (d : ℕ) (R : ℝ) : GqP d R = ∑ a ∈ Icc 1 ⌊R⌋₊, hD d a * V (R / a) := by
  have h1 : GqP d R = ∑ n ∈ Icc 1 ⌊R⌋₊, gD d n := by
    rw [GqP, sum_filter]; rfl
  rw [h1, gD_eq, show Icc 1 ⌊R⌋₊ = Ioc 0 ⌊R⌋₊ from rfl, sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [V, Nat.floor_div_natCast]; rfl

end TernaryGoldbach.Prelim.RamPf
