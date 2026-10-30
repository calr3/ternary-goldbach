import TernaryGoldbach.MinorArcs.TypeIProof
import TernaryGoldbach.Prelim.LargeSieveMV

/-!
# Type II sums [B, Ch. 5]: the sum `S₂` via the large sieve [B, §5.2]

`S(β) = ∑_{W' < p ≤ W} (log p) e(βp)` (`primeExpSum`), `∑_{W' < p ≤ W} (log p)²` (`logSqSum`).
The large sieve inequalities used are the trusted sharp forms in `Prelim/LargeSieveMV.lean`.
-/

open Real Finset

namespace TernaryGoldbach.MinorArcs

/-- `S(β) = ∑_{W' < p ≤ W} (log p) e(βp)`. -/
noncomputable def primeExpSum (W' W β : ℝ) : ℂ :=
  ∑ p ∈ (Ioc ⌊W'⌋₊ ⌊W⌋₊).filter Nat.Prime, (Real.log p : ℂ) * e (β * p)

/-- `∑_{W' < p ≤ W} (log p)²`. -/
noncomputable def logSqSum (W' W : ℝ) : ℝ :=
  ∑ p ∈ (Ioc ⌊W'⌋₊ ⌊W⌋₊).filter Nat.Prime, Real.log p ^ 2

theorem logSqSum_nonneg (W' W : ℝ) : 0 ≤ logSqSum W' W :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- The large sieve (optimal form) for `S(β)`: for `δ`-separated points (`0 < δ ≤ 1`),
`∑_r |S(β_r)|² ≤ (W - W' + δ⁻¹) ∑ (log p)²`. -/
theorem large_sieve_primes {ι : Type*} (s : Finset ι) (β : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ ≤ |(β r - β r') - round (β r - β r')|)
    {W' W : ℝ} (hW' : 0 ≤ W') :
    ∑ r ∈ s, ‖primeExpSum W' W (β r)‖ ^ 2 ≤ (W - W' + δ⁻¹) * logSqSum W' W := by
  rcases lt_or_ge ⌊W'⌋₊ ⌊W⌋₊ with hlt | hge
  · set M := ⌊W'⌋₊
    set N := ⌊W⌋₊ - M
    have hMN : M + N = ⌊W⌋₊ := by omega
    set a : ℕ → ℂ := fun n => if n.Prime then (Real.log n : ℂ) else 0
    have hS : ∀ t, primeExpSum W' W t = ∑ n ∈ Ioc M (M + N), a n * e (t * n) := by
      intro t
      rw [primeExpSum, hMN, sum_filter]
      refine sum_congr rfl fun n _ => ?_
      simp only [a]; split_ifs <;> simp
    have hL : logSqSum W' W = ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
      rw [logSqSum, hMN, sum_filter]
      refine sum_congr rfl fun n _ => ?_
      simp only [a]; split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · simp
    simp_rw [hS]
    rw [hL]
    refine (Prelim.large_sieve_opt s β hδ hδ1 hsep M N a).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _)
    have hW0 : 0 ≤ W := by
      by_contra h; push Not at h
      have : ⌊W⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
      omega
    have h1 : (⌊W⌋₊ : ℝ) ≤ W := Nat.floor_le hW0
    have h2 : W' < (⌊W'⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one W'
    have hN : (N : ℝ) = ⌊W⌋₊ - ⌊W'⌋₊ := by
      simp only [N, M]; rw [Nat.cast_sub hlt.le]
    rw [hN]; linarith
  · have hempty : Ioc ⌊W'⌋₊ ⌊W⌋₊ = ∅ := Ioc_eq_empty (not_lt.2 hge)
    simp [primeExpSum, logSqSum, hempty]

/-- If `|t - b/q| ≤ η` with `q ∤ b`, then `‖t‖ ≥ 1/q - η`. -/
theorem dist_round_ge {q : ℕ} (hq : 1 ≤ q) {b : ℤ} (hb : ¬ (q : ℤ) ∣ b) {t η : ℝ}
    (ht : |t - b / q| ≤ η) : 1 / q - η ≤ |t - round t| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set n := round t
  have hne : b - n * q ≠ 0 := by
    intro h; exact hb ⟨n, by linarith⟩
  have h1 : (1 : ℝ) ≤ |((b - n * q : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
  have h2 : |(b : ℝ) / q - n| = |((b - n * q : ℤ) : ℝ)| / q := by
    rw [← abs_of_pos hq0, ← abs_div, abs_of_pos hq0]; congr 1; push_cast; field_simp
  have h3 : 1 / q ≤ |(b : ℝ) / q - n| := by
    rw [h2]; exact div_le_div_of_nonneg_right h1 hq0.le
  have h4 := abs_sub_abs_le_abs_sub ((b : ℝ) / q - n) (t - n)
  rw [show (b : ℝ) / q - n - (t - n) = -(t - b / q) by ring, abs_neg] at h4
  linarith

/-- The separation of `2αj` for `0 < |j| < q`, `2α = a/q + O*(1/qQ)` (mod 1). -/
theorem dist_two_alpha_mul {α Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hQ : 0 < Q) {j : ℤ} (hj0 : j ≠ 0)
    (hjq : |j| < q) : 1 / q - |j| / (q * Q) ≤ |2 * α * j - round (2 * α * j)| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  refine dist_round_ge hq (b := a * j + k * q * j) ?_ ?_
  · intro hd
    have : (q : ℤ) ∣ a * j := by
      have h2 : (q : ℤ) ∣ k * q * j := ⟨k * j, by ring⟩
      exact (Int.dvd_add_left h2).1 hd
    have hqj : (q : ℤ) ∣ j := hcop.symm.dvd_of_dvd_mul_left this
    have := Int.le_of_dvd (abs_pos.2 hj0) ((dvd_abs _ _).2 hqj)
    omega
  · have e : 2 * α * j - ((a * j + k * q * j : ℤ) : ℝ) / q = j * (2 * α - a / q - k) := by
      push_cast; field_simp; ring
    rw [e, abs_mul]
    calc |(j : ℝ)| * |2 * α - a / q - k| ≤ |(j : ℝ)| * (1 / (q * Q)) :=
          mul_le_mul_of_nonneg_left hα (abs_nonneg _)
      _ = |j| / (q * Q) := by push_cast; ring

/-- `∑_{A₀ < m ≤ A₁, m odd} |S(αm)|²` (over integers `m`). -/
noncomputable def oddSqSum (α W' W A₀ A₁ : ℝ) : ℝ :=
  ∑ m ∈ Ioc ⌊A₀⌋ ⌊A₁⌋, if Odd m then ‖primeExpSum W' W (α * m)‖ ^ 2 else 0

/-- Odd `m ≠ m'` with `|m - m'| ≤ 2K - 1` are separated by `≥ 1/q - (K-1)/(qQ)`: `m - m' = 2j`,
`0 < |j| ≤ K - 1`. -/
theorem sep_odd {α Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hQ : 0 < Q) {m m' : ℤ} (hm : Odd m) (hm' : Odd m')
    (hne : m ≠ m') {K : ℝ} (hK : |((m - m' : ℤ) : ℝ)| / 2 ≤ K) (hKq : K < q) :
    1 / q - K / (q * Q) ≤ |(α * m - α * m') - round (α * m - α * m')| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨j, hj⟩ : ∃ j : ℤ, m - m' = 2 * j := by
    obtain ⟨u, hu⟩ := hm; obtain ⟨u', hu'⟩ := hm'; exact ⟨u - u', by omega⟩
  have hj0 : j ≠ 0 := by omega
  have hjK : (|j| : ℝ) ≤ K := by
    rw [hj] at hK; push_cast at hK; rw [abs_mul] at hK; norm_num at hK; exact_mod_cast hK
  have hjq : |j| < q := by exact_mod_cast hjK.trans_lt hKq
  have e : α * m - α * m' = 2 * α * j := by
    have : (m : ℝ) - m' = 2 * j := by exact_mod_cast hj
    linear_combination α * this
  rw [e]
  refine le_trans ?_ (dist_two_alpha_mul hq hcop hα hQ hj0 hjq)
  have : (|j| : ℝ) / (q * Q) ≤ K / (q * Q) := div_le_div_of_nonneg_right hjK (by positivity)
  push_cast at this ⊢; linarith

set_option maxHeartbeats 1000000 in
/-- **[B, Lemma 5.2.3], (5.50)**: if `2α = a/q + O*(1/qQ)`, `q ≤ Q`, then
`∑_{A₀ < m ≤ A₁, m odd} |S(αm)|² ≤ ⌈(A₁ - A₀)/min(2q, Q)⌉ (W - W' + 2q) ∑ (log p)²`. -/
theorem lemma_5_2_3_a {α Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hqQ : (q : ℝ) ≤ Q) {W' W : ℝ} (hW' : 0 ≤ W')
    (hWW : W' ≤ W) (A₀ A₁ : ℝ) :
    oddSqSum α W' W A₀ A₁ ≤
      ⌈(A₁ - A₀) / min (2 * (q : ℝ)) Q⌉₊ * ((W - W' + 2 * q) * logSqSum W' W) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ : 0 < Q := hq0.trans_le hqQ
  set K := min q ⌈Q / 2⌉₊ with hKdef
  have hK1 : 1 ≤ K := le_min hq (Nat.one_le_iff_ne_zero.2 (by
    rw [ne_eq, Nat.ceil_eq_zero, not_le]; positivity))
  have hKq : K ≤ q := min_le_left _ _
  have hKQ : (K : ℝ) - 1 < Q / 2 := by
    have : (K : ℝ) ≤ ⌈Q / 2⌉₊ := by exact_mod_cast min_le_right _ _
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ Q / 2 by positivity)
    linarith
  have h2K : 1 ≤ 2 * K := by omega
  set J := ⌈(A₁ - A₀) / ((2 * K : ℕ) : ℝ)⌉₊
  have hP := logSqSum_nonneg W' W
  have hB0 : 0 ≤ (W - W' + 2 * q) * logSqSum W' W := mul_nonneg (by linarith) hP
  have hblocks := sum_Ioc_le_blocks (G := fun m : ℤ => if Odd m then ‖primeExpSum W' W (α * m)‖ ^ 2 else 0)
    (fun m => by split_ifs; exacts [sq_nonneg _, le_rfl]) h2K J A₀ A₁ (nblocks_spec (by positivity))
  rw [oddSqSum]
  refine hblocks.trans ?_
  -- Each block.
  have hblock : ∀ j ∈ range J,
      ∑ m ∈ Ioc ⌊A₀ + j * ((2 * K : ℕ) : ℝ)⌋ ⌊min (A₀ + (j + 1) * ((2 * K : ℕ) : ℝ)) A₁⌋,
        (if Odd m then ‖primeExpSum W' W (α * m)‖ ^ 2 else 0) ≤
        (W - W' + 2 * q) * logSqSum W' W := by
    intro j _
    set y := A₀ + j * ((2 * K : ℕ) : ℝ)
    set B := Ioc ⌊y⌋ ⌊min (A₀ + (j + 1) * ((2 * K : ℕ) : ℝ)) A₁⌋
    have hBsub : ∀ m ∈ B, ⌊y⌋ < m ∧ m ≤ ⌊y⌋ + 2 * K := by
      intro m hm
      rw [mem_Ioc] at hm
      refine ⟨hm.1, hm.2.trans ?_⟩
      have h1 : min (A₀ + (j + 1) * ((2 * K : ℕ) : ℝ)) A₁ ≤ y + ((2 * K : ℕ) : ℤ) := by
        have := min_le_left (A₀ + (j + 1) * ((2 * K : ℕ) : ℝ)) A₁
        simp only [y]; push_cast at this ⊢; linarith
      have := Int.floor_mono h1
      rw [Int.floor_add_intCast] at this
      push_cast at this ⊢; exact this
    rw [← sum_filter]
    have hls := large_sieve_primes (B.filter Odd) (fun m : ℤ => α * m) (δ := 1 / (2 * q))
      (W' := W') (W := W)
      (by positivity) (by rw [div_le_one (by positivity)]; linarith) (by
        intro m hm m' hm' hne
        rw [mem_filter] at hm hm'
        have h1 := hBsub m hm.1
        have h2 := hBsub m' hm'.1
        have hdiff : |((m - m' : ℤ) : ℝ)| / 2 ≤ (K : ℝ) - 1 := by
          obtain ⟨u, hu⟩ := hm.2
          obtain ⟨u', hu'⟩ := hm'.2
          have h3 : |m - m'| ≤ 2 * (K : ℤ) - 2 := by rw [abs_le]; constructor <;> omega
          have h4 : ((|m - m'| : ℤ) : ℝ) ≤ 2 * (K : ℝ) - 2 := by exact_mod_cast h3
          rw [← Int.cast_abs]; push_cast at h4 ⊢; linarith
        have hsep := sep_odd hq hcop hα hQ hm.2 hm'.2 hne hdiff (by
          have : (K : ℝ) ≤ q := by exact_mod_cast hKq
          linarith)
        refine le_trans ?_ hsep
        have : ((K : ℝ) - 1) / (q * Q) ≤ (Q / 2) / (q * Q) :=
          div_le_div_of_nonneg_right hKQ.le (by positivity)
        have e : (Q / 2) / (q * Q) = 1 / (2 * q) := by field_simp
        have e2 : 1 / (q : ℝ) - 1 / (2 * q) = 1 / (2 * q) := by field_simp; ring
        linarith) hW'
    rw [one_div, inv_inv] at hls
    exact hls
  refine (sum_le_sum hblock).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hB0
  rcases le_or_gt (A₁ - A₀) 0 with h | h
  · have : J = 0 := Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg h (by positivity))
    rw [this]; simp
  · exact_mod_cast Nat.ceil_mono (div_le_div_of_nonneg_left h.le (lt_min (by positivity) hQ) (by
      push_cast
      have : (K : ℝ) = min (q : ℝ) (⌈Q / 2⌉₊ : ℝ) := by simp [hKdef]
      rw [this, mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      exact min_le_min le_rfl (by linarith [Nat.le_ceil (Q / 2)])))

/-- **[B, Lemma 5.2.3], (5.52)** (with `m` odd, as the proof requires; [B]'s display omits it):
if `A₁ - A₀ ≤ 2ϱq` and `q ≤ ρQ`, `0 ≤ ϱ ≤ 1`, `ϱρ < 1`, then
`∑_{A₀ < m ≤ A₁, m odd} |S(αm)|² ≤ (W - W' + q/(1 - ϱρ)) ∑ (log p)²`. -/
theorem lemma_5_2_3_c {α Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) {ϱ ρ : ℝ} (hϱ : 0 ≤ ϱ) (hϱ1 : ϱ ≤ 1) (hρ : 0 ≤ ρ)
    (hϱρ : ϱ * ρ < 1) (hqρ : (q : ℝ) ≤ ρ * Q) {W' W : ℝ} (hW' : 0 ≤ W') {A₀ A₁ : ℝ}
    (hA : A₁ - A₀ ≤ 2 * ϱ * q) :
    oddSqSum α W' W A₀ A₁ ≤ (W - W' + q / (1 - ϱ * ρ)) * logSqSum W' W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := by
    rcases eq_or_lt_of_le hρ with h | h
    · rw [← h] at hqρ; linarith
    · nlinarith
  rw [oddSqSum, ← sum_filter]
  have h1ϱρ : 0 < 1 - ϱ * ρ := by linarith
  have hls := large_sieve_primes ((Ioc ⌊A₀⌋ ⌊A₁⌋).filter Odd) (fun m : ℤ => α * m)
    (δ := (1 - ϱ * ρ) / q) (W' := W') (W := W) (by positivity) (by
      rw [div_le_one hq0]; have : 0 ≤ ϱ * ρ := by positivity
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith) (by
      intro m hm m' hm' hne
      rw [mem_filter, mem_Ioc] at hm hm'
      have hlt : ((|m - m'| : ℤ) : ℝ) < A₁ - A₀ := by
        have h1 : (⌊A₁⌋ : ℝ) ≤ A₁ := Int.floor_le _
        have h2 : A₀ < (⌊A₀⌋ : ℝ) + 1 := Int.lt_floor_add_one _
        have : |m - m'| ≤ ⌊A₁⌋ - ⌊A₀⌋ - 1 := by rw [abs_le]; omega
        have : ((|m - m'| : ℤ) : ℝ) ≤ ⌊A₁⌋ - ⌊A₀⌋ - 1 := by exact_mod_cast this
        linarith
      have hdiff : |((m - m' : ℤ) : ℝ)| / 2 ≤ ϱ * q := by
        rw [← Int.cast_abs]; linarith
      have hsep := sep_odd hq hcop hα hQ hm.2 hm'.2 hne (K := |((m - m' : ℤ) : ℝ)| / 2) le_rfl (by
        have : ϱ * q ≤ q := by nlinarith
        rw [← Int.cast_abs]; linarith)
      refine le_trans ?_ hsep
      have h5 : |((m - m' : ℤ) : ℝ)| / 2 / (q * Q) ≤ ϱ * q / (q * Q) :=
        div_le_div_of_nonneg_right hdiff (by positivity)
      have : ϱ * q / (q * Q) ≤ ϱ * ρ / q := by
        rw [div_le_div_iff₀ (by positivity) hq0]
        have := mul_le_mul_of_nonneg_left hqρ (show 0 ≤ ϱ * q by positivity)
        nlinarith
      have e : (1 - ϱ * ρ) / q = 1 / q - ϱ * ρ / q := by ring
      linarith) hW'
  rwa [inv_div] at hls

end TernaryGoldbach.MinorArcs
