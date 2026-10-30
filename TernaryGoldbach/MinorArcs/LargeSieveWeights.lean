import TernaryGoldbach.MinorArcs.Bombieri
import TernaryGoldbach.MinorArcs.LargeSievePrimes

/-!
# The weights in [B, Prop. 12.1.2]

The major arcs `𝔐_{δ₀,Q₀}` have, around `b/q`, radius `δ₀Q₀/(q̃x)` with `q̃ = q` for even `q`
(`q ≤ 2Q₀`) and `q̃ = 2q` for odd `q` (`q ≤ Q₀`); so `q` contributes iff `q̃ ≤ min(2Q₀, …)`.
After Bombieri's identity (`totient_mul_sum_units_lift`), a character of conductor `c` gets the
weight `Σ_{q̃ ≤ X} [c ∣ q] w(q, c)/φ(q)`, which we evaluate (`weight_sum`):

`Σ_{q ≥ 1, q̃ ≤ X} [c ∣ q] w(q, c)/φ(q) = (c/φ(c)) κ_c G_{c̃}(X/c̃)`,

`c̃ = c` and `κ_c = 1` for even `c`, `c̃ = 2c` and `κ_c = 2` for odd `c` (the odd and even `r` in
`q = cr` give equal sums).  This is the identity behind [B, (12.6)].

Proved, with no `sorry`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

/-- `q̃ = q` for even `q`, `2q` for odd `q`. -/
def qt (q : ℕ) : ℕ := if Even q then q else 2 * q

/-- `κ_c = 1` for even `c`, `2` for odd `c`. -/
noncomputable def kap (c : ℕ) : ℝ := if Even c then 1 else 2

/-- `(μ r)² = [r squarefree]`, in `ℝ`. -/
theorem moebius_sq_real (r : ℕ) : ((μ r : ℝ)) ^ 2 = if Squarefree r then 1 else 0 := by
  have := ArithmeticFunction.moebius_sq (n := r)
  split_ifs at this ⊢ <;> exact_mod_cast this

/-- Step 1: the sum over `q = cr`. -/
theorem weight_sum_r (c : ℕ) (hc : 1 ≤ c) (X : ℝ) :
    ∑ q ∈ (Icc 1 ⌊X⌋₊).filter (fun q => (qt q : ℝ) ≤ X),
        (if c ∣ q then TernaryGoldbach.wq q c else 0) / q.totient =
      c / c.totient * ∑ r ∈ (Icc 1 ⌊X⌋₊).filter (fun r => (qt (c * r) : ℝ) ≤ X ∧ Nat.Coprime r c),
        (μ r : ℝ) ^ 2 / r.totient := by
  have hc0 : 0 < c := hc
  set R := (Icc 1 ⌊X⌋₊).filter (fun r => (qt (c * r) : ℝ) ≤ X)
  -- both sides as sums over `R` of `[r sqfree, (r,c)=1] c/(φ(c)φ(r))`
  have hR : (Icc 1 ⌊X⌋₊).filter (fun r => (qt (c * r) : ℝ) ≤ X ∧ Nat.Coprime r c) =
      R.filter (fun r => Nat.Coprime r c) := by
    rw [filter_filter]
  have hL : ∑ q ∈ (Icc 1 ⌊X⌋₊).filter (fun q => (qt q : ℝ) ≤ X),
        (if c ∣ q then TernaryGoldbach.wq q c else 0) / q.totient =
      ∑ q ∈ ((Icc 1 ⌊X⌋₊).filter (fun q => (qt q : ℝ) ≤ X)).filter (c ∣ ·),
        TernaryGoldbach.wq q c / q.totient := by
    rw [Finset.sum_filter (p := (c ∣ ·))]; refine sum_congr rfl fun q _ => ?_; split_ifs <;> simp
  have hRR : c / c.totient * ∑ r ∈ R.filter (fun r => Nat.Coprime r c), (μ r : ℝ) ^ 2 / r.totient =
      ∑ r ∈ R, if Nat.Coprime r c then c / c.totient * ((μ r : ℝ) ^ 2 / r.totient) else 0 := by
    rw [Finset.sum_filter (p := fun r => Nat.Coprime r c), mul_sum]
    refine sum_congr rfl fun r _ => ?_; split_ifs <;> simp
  rw [hR, hL, hRR]
  refine Finset.sum_nbij' (fun q => q / c) (fun r => c * r) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [mem_filter, mem_filter, mem_Icc] at hq
    obtain ⟨⟨⟨hq1, hqX⟩, hqt⟩, hdvd⟩ := hq
    obtain ⟨k, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left _ hc0]
    have hk : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; simp at hq1)
    simp only [R, mem_filter, mem_Icc]
    exact ⟨⟨hk, le_trans (Nat.le_mul_of_pos_left k hc0) hqX⟩, hqt⟩
  · intro r hr
    simp only [R, mem_filter, mem_Icc] at hr
    obtain ⟨⟨hr1, -⟩, hrt⟩ := hr
    rw [mem_filter, mem_filter, mem_Icc]
    refine ⟨⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩, hrt⟩, dvd_mul_right _ _⟩
    have h1 : ((c * r : ℕ) : ℝ) ≤ qt (c * r) := by
      unfold qt; split_ifs <;> push_cast <;> nlinarith [show (0:ℝ) ≤ c * r by positivity]
    exact Nat.le_floor (h1.trans hrt)
  · intro q hq
    rw [mem_filter] at hq
    exact Nat.mul_div_cancel' hq.2
  · intro r _
    exact Nat.mul_div_cancel_left _ hc0
  · intro q hq
    rw [mem_filter] at hq
    obtain ⟨k, rfl⟩ := hq.2
    rw [Nat.mul_div_cancel_left _ hc0, TernaryGoldbach.wq, Nat.mul_div_cancel_left _ hc0,
      moebius_sq_real]
    by_cases hcop : Nat.Coprime k c
    · rw [if_pos hcop, Nat.totient_mul (Nat.coprime_comm.1 hcop)]
      by_cases hs : Squarefree k
      · rw [if_pos ⟨hs, hcop⟩, if_pos hs]; push_cast; field_simp
      · rw [if_neg (fun h => hs h.1), if_neg hs]; simp
    · rw [if_neg hcop, if_neg (fun h => hcop h.2), zero_div]

/-- `r ≤ ⌊X/d⌋₊ ↔ d r ≤ X` for `r ≥ 1`, `d ≥ 1`. -/
theorem le_floor_div_iff {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) (X : ℝ) :
    r ≤ ⌊X / d⌋₊ ↔ ((d * r : ℕ) : ℝ) ≤ X := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · intro h
    have hX : (1 : ℝ) ≤ X / d := by
      have : (1 : ℕ) ≤ ⌊X / d⌋₊ := hr.trans h
      exact_mod_cast (Nat.one_le_floor_iff _).1 this
    have := (Nat.le_floor_iff (by linarith)).1 h
    push_cast
    rw [le_div_iff₀ hd0] at this; linarith
  · intro h
    apply Nat.le_floor
    rw [le_div_iff₀ hd0]; push_cast at h; linarith

/-- `μ(2r)² / φ(2r) = [r odd] μ(r)² / φ(r)`. -/
theorem moebius_sq_div_totient_two_mul (r : ℕ) :
    ((μ (2 * r) : ℝ)) ^ 2 / (2 * r).totient =
      if Nat.Coprime r 2 then (μ r : ℝ) ^ 2 / r.totient else 0 := by
  split_ifs with h
  · have h2 : Nat.Coprime 2 r := Nat.coprime_comm.1 h
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h2, Nat.totient_mul h2,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    simp
  · have : ¬ Squarefree (2 * r) := by
      intro hs
      apply h
      rw [Nat.coprime_two_right]  -- r odd
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨k, rfl⟩ := hev
      have := hs 2 ⟨k, by ring⟩
      simp at this
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree this]; simp

/-- **The weight of a character of conductor `c`**:
`Σ_{q ≥ 1, q̃ ≤ X} [c ∣ q] w(q, c)/φ(q) = (c/φ(c)) κ_c G_{c̃}(X/c̃)`. -/
theorem weight_sum (c : ℕ) (hc : 1 ≤ c) (X : ℝ) :
    ∑ q ∈ (Icc 1 ⌊X⌋₊).filter (fun q => (qt q : ℝ) ≤ X),
        (if c ∣ q then TernaryGoldbach.wq q c else 0) / q.totient =
      c / c.totient * (kap c * Gq (qt c) (X / qt c)) := by
  rw [weight_sum_r c hc X]
  congr 1
  unfold Gq
  rcases Nat.even_or_odd c with hce | hco
  · -- even conductor
    have hqt : ∀ r, qt (c * r) = c * r := fun r => by
      unfold qt; rw [if_pos (hce.mul_right r)]
    rw [kap, if_pos hce, one_mul, show qt c = c by unfold qt; rw [if_pos hce]]
    refine sum_congr ?_ fun _ _ => rfl
    ext r
    simp only [mem_filter, mem_Icc, hqt]
    constructor
    · rintro ⟨⟨hr1, -⟩, hrX, hcop⟩
      exact ⟨⟨hr1, (le_floor_div_iff hr1 hc X).2 hrX⟩, hcop⟩
    · rintro ⟨⟨hr1, hrX⟩, hcop⟩
      have h := (le_floor_div_iff hr1 hc X).1 hrX
      refine ⟨⟨hr1, Nat.le_floor (le_trans ?_ h)⟩, h, hcop⟩
      exact_mod_cast Nat.le_mul_of_pos_left r hc
  · -- odd conductor: odd and even `r` contribute equally
    have hc2 : ¬ Even c := Nat.not_even_iff_odd.2 hco
    rw [kap, if_neg hc2, show qt c = 2 * c by unfold qt; rw [if_neg hc2]]
    set A := (Icc 1 ⌊X⌋₊).filter (fun r => (qt (c * r) : ℝ) ≤ X ∧ Nat.Coprime r c)
    set B := (Icc 1 ⌊X / ((2 * c : ℕ) : ℝ)⌋₊).filter (fun r => Nat.Coprime r (2 * c))
    rw [← sum_filter_add_sum_filter_not A (fun r => Odd r), two_mul]
    congr 1
    · -- odd `r`
      refine sum_congr ?_ fun _ _ => rfl
      ext r
      simp only [A, B, mem_filter, mem_Icc, Nat.coprime_mul_iff_right, Nat.coprime_two_right]
      constructor
      · rintro ⟨⟨⟨hr1, -⟩, hrX, hcop⟩, hodd⟩
        have hq : qt (c * r) = 2 * c * r := by
          unfold qt; rw [if_neg (Nat.not_even_iff_odd.2 (hco.mul hodd))]; ring
        rw [hq] at hrX
        exact ⟨⟨hr1, (le_floor_div_iff hr1 (by omega) X).2 hrX⟩, hodd, hcop⟩
      · rintro ⟨⟨hr1, hrX⟩, hodd, hcop⟩
        have hq : qt (c * r) = 2 * c * r := by
          unfold qt; rw [if_neg (Nat.not_even_iff_odd.2 (hco.mul hodd))]; ring
        have h := (le_floor_div_iff hr1 (by omega) X).1 hrX
        refine ⟨⟨⟨hr1, Nat.le_floor (le_trans ?_ h)⟩, by rw [hq]; exact h, hcop⟩, hodd⟩
        exact_mod_cast Nat.le_mul_of_pos_left r (by omega)
    · -- even `r = 2r'`
      have hB : ∑ r ∈ B, (μ r : ℝ) ^ 2 / r.totient =
          ∑ r' ∈ (Icc 1 ⌊X / ((2 * c : ℕ) : ℝ)⌋₊).filter (fun r => Nat.Coprime r c),
            ((μ (2 * r') : ℝ)) ^ 2 / (2 * r').totient := by
        simp_rw [moebius_sq_div_totient_two_mul]
        rw [← sum_filter, filter_filter]
        refine sum_congr ?_ fun _ _ => rfl
        ext r
        simp only [B, mem_filter, Nat.coprime_mul_iff_right]
        tauto
      rw [hB]
      refine Finset.sum_nbij' (fun r => r / 2) (fun r' => 2 * r') ?_ ?_ ?_ ?_ ?_
      · intro r hr
        simp only [A, mem_filter, mem_Icc, Nat.not_odd_iff_even] at hr ⊢
        obtain ⟨⟨⟨hr1, -⟩, hrX, hcop⟩, hev⟩ := hr
        obtain ⟨k, rfl⟩ := hev
        have hk : k + k = 2 * k := by ring
        rw [hk] at hr1 hrX hcop ⊢
        rw [Nat.mul_div_cancel_left _ (by norm_num)]
        have hk1 : 1 ≤ k := by omega
        have hq : qt (c * (2 * k)) = 2 * c * k := by
          unfold qt; rw [if_pos ((even_two_mul k).mul_left c)]; ring
        rw [hq] at hrX
        exact ⟨⟨hk1, (le_floor_div_iff hk1 (by omega) X).2 hrX⟩,
          Nat.Coprime.coprime_mul_left hcop⟩
      · intro r' hr'
        simp only [A, mem_filter, mem_Icc, Nat.not_odd_iff_even] at hr' ⊢
        obtain ⟨⟨hr1, hrX⟩, hcop⟩ := hr'
        have hq : qt (c * (2 * r')) = 2 * c * r' := by
          unfold qt; rw [if_pos ((even_two_mul r').mul_left c)]; ring
        have h := (le_floor_div_iff hr1 (by omega) X).1 hrX
        refine ⟨⟨⟨by omega, Nat.le_floor (le_trans ?_ h)⟩, by rw [hq]; exact h, ?_⟩, even_two_mul r'⟩
        · push_cast; nlinarith [show (1:ℝ) ≤ c by exact_mod_cast hc, show (0:ℝ) ≤ r' by positivity]
        · exact Nat.Coprime.mul_left ((Nat.coprime_two_left).2 hco) hcop
      · intro r hr
        simp only [A, mem_filter, Nat.not_odd_iff_even] at hr
        obtain ⟨k, rfl⟩ := hr.2
        omega
      · intro r' _; omega
      · intro r hr
        simp only [A, mem_filter, Nat.not_odd_iff_even] at hr
        obtain ⟨k, rfl⟩ := hr.2
        rw [show k + k = 2 * k by ring, Nat.mul_div_cancel_left _ (by norm_num)]

end TernaryGoldbach.MinorArcs
