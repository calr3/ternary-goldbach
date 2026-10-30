import TernaryGoldbach.MinorArcs.TypeIProof
import TernaryGoldbach.Prelim.LargeSieveMV
import TernaryGoldbach.Prelim.SumMuSqPhi
import TernaryGoldbach.MinorArcs.Montgomery

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

/-! ### [B, Lemma 5.2.1] -/

/-- Distance to the nearest integer is at least `ν` if it is so for every integer. -/
theorem le_dist_round_of_forall {t ν : ℝ} (h : ∀ n : ℤ, ν ≤ |t - n|) : ν ≤ |t - round t| :=
  h (round t)

/-- The separation of the angles `a/q + b/r + u` of [B, (5.40)–(5.41)]: for `r, r' ≤ R` coprime
to `q`, `(b, r) = (b', r') = 1`, `|u| ≤ υ`, `qR²(ν + υ) ≤ 1`, `ν + υ ≤ 1/q`, the difference
`t = A/q + b/r - b'/r' + u` has `‖t‖ ≥ ν`, unless `q | A`, `r = r'`, `b = b'` (where we assume
`|u| ≥ ν`). -/
theorem sep_triples {q r r' b b' : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (hrq : Nat.Coprime r q) (hr'q : Nat.Coprime r' q) (hb : b < r) (hb' : b' < r')
    (hbr : Nat.Coprime r b) (hb'r : Nat.Coprime r' b') {A : ℤ} {u ν υ R : ℝ} (hν : 0 < ν)
    (hu : |u| ≤ υ) (hRr : (r : ℝ) ≤ R) (hRr' : (r' : ℝ) ≤ R) (hR : q * R ^ 2 * (ν + υ) ≤ 1)
    (hνυ : ν + υ ≤ 1 / q) (hcase : (q : ℤ) ∣ A → r = r' → b = b' → ν ≤ |u|) :
    ν ≤ |(A / q + b / r - b' / r' + u : ℝ) - round (A / q + b / r - b' / r' + u : ℝ)| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr'0 : (0 : ℝ) < r' := by exact_mod_cast hr'
  set M : ℤ := A * r * r' + q * (b * r' - b' * r)
  have hM : (A / q + b / r - b' / r' : ℝ) = M / (q * r * r') := by
    simp only [M]; push_cast; field_simp; ring
  apply le_dist_round_of_forall
  intro n
  by_cases hdiv : ((q * r * r' : ℕ) : ℤ) ∣ M
  · -- Then `r = r'`, `b = b'`, `q ∣ A`.
    have hrq' : IsCoprime (r : ℤ) q := Nat.isCoprime_iff_coprime.2 hrq
    have hr'q' : IsCoprime (r' : ℤ) q := Nat.isCoprime_iff_coprime.2 hr'q
    have hbr' : IsCoprime (r : ℤ) b := Nat.isCoprime_iff_coprime.2 hbr
    have hb'r' : IsCoprime (r' : ℤ) b' := Nat.isCoprime_iff_coprime.2 hb'r
    have h1 : (r : ℤ) ∣ r' := by
      have : (r : ℤ) ∣ M := dvd_trans (⟨(q : ℤ) * r', by push_cast; ring⟩ : (r : ℤ) ∣ ((q * r * r' : ℕ) : ℤ)) hdiv
      have h2 : (r : ℤ) ∣ q * (b * r') := by
        have e : (q : ℤ) * (b * r') = M - r * (A * r' - q * b') := by simp only [M]; ring
        rw [e]; exact dvd_sub this (dvd_mul_right _ _)
      exact hbr'.dvd_of_dvd_mul_left (hrq'.dvd_of_dvd_mul_left h2)
    have h1' : (r' : ℤ) ∣ r := by
      have : (r' : ℤ) ∣ M := dvd_trans (⟨(q : ℤ) * r, by push_cast; ring⟩ : (r' : ℤ) ∣ ((q * r * r' : ℕ) : ℤ)) hdiv
      have h2 : (r' : ℤ) ∣ q * (b' * r) := by
        have e : (q : ℤ) * (b' * r) = r' * (A * r + q * b) - M := by simp only [M]; ring
        rw [e]; exact dvd_sub (dvd_mul_right _ _) this
      exact hb'r'.dvd_of_dvd_mul_left (hr'q'.dvd_of_dvd_mul_left h2)
    have hrr : r = r' := by
      have := Int.dvd_antisymm (by positivity) (by positivity) h1 h1'
      exact_mod_cast this
    subst hrr
    have h3 : ((q * r : ℕ) : ℤ) ∣ A * r + q * (b - b') := by
      have e : M = r * (A * r + q * (b - b')) := by simp only [M]; ring
      rw [e] at hdiv
      have : ((q * r * r : ℕ) : ℤ) = r * ((q * r : ℕ) : ℤ) := by push_cast; ring
      rw [this] at hdiv
      exact (Int.dvd_of_mul_dvd_mul_left (by positivity) hdiv)
    have h4 : (r : ℤ) ∣ b - b' := by
      have : (r : ℤ) ∣ q * (b - b') := by
        have hr3 : (r : ℤ) ∣ A * r + q * (b - b') :=
          dvd_trans (⟨(q : ℤ), by push_cast; ring⟩ : (r : ℤ) ∣ ((q * r : ℕ) : ℤ)) h3
        have e : (q : ℤ) * (b - b') = (A * r + q * (b - b')) - A * r := by ring
        rw [e]; exact dvd_sub hr3 (dvd_mul_left _ _)
      exact hrq'.dvd_of_dvd_mul_left this
    have hbb : b = b' := by
      obtain ⟨c, hc⟩ := h4
      have : c = 0 := by
        by_contra hc0
        have : (r : ℤ) ≤ |(b : ℤ) - b'| := by
          rw [hc, abs_mul]; nlinarith [abs_nonneg (r : ℤ), Int.one_le_abs hc0, abs_of_pos (show (0:ℤ) < r by positivity)]
        have : |(b : ℤ) - b'| < r := by rw [abs_lt]; constructor <;> omega
        omega
      rw [this, mul_zero] at hc; omega
    subst hbb
    have h5 : (q : ℤ) ∣ A := by
      have e : A * r + q * (b - b) = A * r := by ring
      rw [e] at h3
      have : ((q * r : ℕ) : ℤ) = q * r := by push_cast; ring
      rw [this] at h3
      exact Int.dvd_of_mul_dvd_mul_right (by positivity) h3
    have hνu := hcase h5 rfl rfl
    obtain ⟨k, hk⟩ := h5
    have ht : (A / q + b / r - b / r + u : ℝ) - n = u - (n - k) := by
      rw [hk]; push_cast; field_simp; ring
    rw [ht]
    by_cases hnk : n - k = 0
    · have : ((n : ℝ) - k) = 0 := by exact_mod_cast hnk
      rw [this, sub_zero]; exact hνu
    · have h6 : (1 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hnk
      push_cast at h6
      have h7 := abs_sub_abs_le_abs_sub ((n : ℝ) - k) u
      rw [abs_sub_comm ((n : ℝ) - k) u] at h7
      have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hq0]; exact_mod_cast hq
      linarith
  · -- `‖M/(qrr')‖ ≥ 1/(qrr') ≥ 1/(qR²) ≥ ν + υ`.
    have hne : M - n * (q * r * r' : ℕ) ≠ 0 := by
      intro h; exact hdiv ⟨n, by linarith⟩
    have hqrr : (0 : ℝ) < q * r * r' := by positivity
    have h1 : 1 / ((q : ℝ) * r * r') ≤ |(M : ℝ) / (q * r * r') - n| := by
      have e : (M : ℝ) / (q * r * r') - n = ((M - n * (q * r * r' : ℕ) : ℤ) : ℝ) / (q * r * r') := by
        push_cast; field_simp
      rw [e, abs_div, abs_of_pos hqrr]
      refine div_le_div_of_nonneg_right ?_ hqrr.le
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
    have h2 : ν + υ ≤ 1 / ((q : ℝ) * r * r') := by
      rw [le_div_iff₀ hqrr]
      calc (ν + υ) * (q * r * r') ≤ (ν + υ) * (q * R ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith [abs_nonneg u])
            rw [sq]
            have := mul_le_mul hRr hRr' hr'0.le (hr0.le.trans hRr)
            nlinarith
        _ ≤ 1 := by linarith
    have h3 := abs_sub_abs_le_abs_sub ((M : ℝ) / (q * r * r') - n) (-u)
    have e2 : (A / q + b / r - b' / r' + u : ℝ) - n = ((M : ℝ) / (q * r * r') - n) - (-u) := by
      rw [← hM]; ring
    rw [e2]
    rw [abs_neg] at h3
    linarith

set_option maxHeartbeats 2000000 in
/-- **[B, Lemma 5.2.1]**: let `α_i = a_i/q + u_i` (`i ∈ s`), with `|u_i - u_j| ≤ υ` (the `u_i` in
an interval of length `υ`), and `|u_i - u_j| ≥ ν > 0` whenever `i ≠ j`, `a_i ≡ a_j mod q`; let `ν + υ ≤ 1/q`. Then
(i) `∑_i |S(α_i)|² ≤ (W - W' + ν⁻¹) ∑ (log p)²`, and
(ii) for `1 ≤ R ≤ W'` with `qR²(ν + υ) ≤ 1`,
`(φ(q)/q) log R · ∑_i |S(α_i)|² ≤ (W - W' + ν⁻¹) ∑ (log p)²`.
With `R = (q(ν+υ))^{-1/2}`, (ii) is [B]'s gain `min(1, 2q/(φ(q) log((q(ν+υ))⁻¹)))`. **Note**: the
condition `R ≤ W'` (so that the primes `p > W'` are coprime to all `r ≤ R`, as Montgomery's
inequality requires) is missing in [B]; it is harmless in the applications. -/
theorem lemma_5_2_1 {ι : Type*} (s : Finset ι) {q : ℕ} (hq : 1 ≤ q) (a : ι → ℤ) (u : ι → ℝ)
    {ν υ : ℝ} (hν : 0 < ν) (hυ : 0 ≤ υ) (hνυ : ν + υ ≤ 1 / q)
    (hdiff : ∀ i ∈ s, ∀ j ∈ s, |u i - u j| ≤ υ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (q : ℤ) ∣ a i - a j → ν ≤ |u i - u j|)
    {W' W : ℝ} (hW' : 0 ≤ W') :
    (∑ i ∈ s, ‖primeExpSum W' W (a i / q + u i)‖ ^ 2 ≤ (W - W' + ν⁻¹) * logSqSum W' W) ∧
    (∀ R : ℝ, 1 ≤ R → R ≤ W' → q * R ^ 2 * (ν + υ) ≤ 1 →
      Nat.totient q / q * Real.log R * ∑ i ∈ s, ‖primeExpSum W' W (a i / q + u i)‖ ^ 2 ≤
        (W - W' + ν⁻¹) * logSqSum W' W) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hν1 : ν ≤ 1 := by
    have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hq0]; exact hq1
    linarith
  -- The general separation of `α_i + b/r`.
  have hsep3 : ∀ R : ℝ, 1 ≤ R → q * R ^ 2 * (ν + υ) ≤ 1 →
      ∀ i ∈ s, ∀ j ∈ s, ∀ r r' b b' : ℕ, 1 ≤ r → 1 ≤ r' → (r : ℝ) ≤ R → (r' : ℝ) ≤ R →
        Nat.Coprime r q → Nat.Coprime r' q → b < r → b' < r' → Nat.Coprime r b →
        Nat.Coprime r' b' → (i, r, b) ≠ (j, r', b') →
        ν ≤ |((a i / q + u i + b / r) - (a j / q + u j + b' / r')) -
          round ((a i / q + u i + b / r) - (a j / q + u j + b' / r'))| := by
    intro R hR hRq i hi j hj r r' b b' hr hr' hrR hr'R hrq hr'q hb hb' hbr hb'r hne
    have e : (a i / q + u i + b / r) - (a j / q + u j + b' / r') =
        ((a i - a j : ℤ) : ℝ) / q + b / r - b' / r' + (u i - u j) := by push_cast; ring
    rw [e]
    refine sep_triples hq hr hr' hrq hr'q hb hb' hbr hb'r hν (hdiff i hi j hj) hrR hr'R hRq hνυ ?_
    intro hA hrr hbb
    refine hsep i hi j hj (fun hij => hne ?_) hA
    rw [hij, hrr, hbb]
  constructor
  · -- (i): the large sieve with `δ = ν`.
    refine large_sieve_primes s (fun i => a i / q + u i) hν hν1 ?_ hW'
    intro i hi j hj hij
    have := hsep3 1 le_rfl (by have := (le_div_iff₀ hq0).1 hνυ; nlinarith) i hi j hj 1 1 0 0 le_rfl le_rfl (by simp) (by simp)
      (Nat.coprime_one_left q) (Nat.coprime_one_left q) one_pos one_pos (Nat.coprime_one_left 0)
      (Nat.coprime_one_left 0) (fun h => hij (Prod.ext_iff.1 h).1)
    simpa using this
  · -- (ii): Montgomery's inequality for each `r ≤ R`, then the large sieve for all `α_i + b/r`.
    intro R hR hRW hRq
    set N := ⌊R⌋₊
    set C := (Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r q)
    set T := (s ×ˢ (C ×ˢ range N)).filter (fun t => t.2.2 < t.2.1 ∧ Nat.Coprime t.2.1 t.2.2)
    set β : ι × ℕ × ℕ → ℝ := fun t => a t.1 / q + u t.1 + t.2.2 / t.2.1
    have hCmem : ∀ r ∈ C, 1 ≤ r ∧ (r : ℝ) ≤ R ∧ Squarefree r ∧ Nat.Coprime r q := by
      intro r hr
      rw [mem_filter, mem_Icc] at hr
      exact ⟨hr.1.1, (Nat.cast_le.2 hr.1.2).trans (Nat.floor_le (by linarith)), hr.2.1, hr.2.2⟩
    have hLS := large_sieve_primes T β hν hν1 (W' := W') (W := W) (by
      intro t ht t' ht' hne
      rw [mem_filter, mem_product, mem_product] at ht ht'
      obtain ⟨⟨hi, hr, _⟩, hb, hbr⟩ := ht
      obtain ⟨⟨hj, hr', _⟩, hb', hb'r⟩ := ht'
      have h1 := hCmem _ hr
      have h2 := hCmem _ hr'
      exact hsep3 R hR hRq _ hi _ hj _ _ _ _ h1.1 h2.1 h1.2.1 h2.2.1 h1.2.2.2 h2.2.2.2 hb hb'
        hbr hb'r (by simpa using hne)) hW'
    -- Rewrite the sum over `T`.
    have hT : ∑ t ∈ T, ‖primeExpSum W' W (β t)‖ ^ 2 = ∑ i ∈ s, ∑ r ∈ C,
        ∑ b ∈ (range r).filter r.Coprime, ‖primeExpSum W' W (a i / q + u i + b / r)‖ ^ 2 := by
      rw [sum_filter, sum_product]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_product]
      refine sum_congr rfl fun r hr => ?_
      have hrN : r ≤ N := (mem_Icc.1 (mem_filter.1 hr).1).2
      have hset : (range r).filter r.Coprime = (range N).filter (fun b => b < r ∧ r.Coprime b) := by
        ext b; simp only [mem_filter, mem_range]; constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1.trans_le hrN, h1, h2⟩
        · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      rw [hset, sum_filter]
    rw [hT] at hLS
    -- Montgomery.
    have hMont : ∀ i ∈ s, ∀ r ∈ C, (1 / Nat.totient r : ℝ) *
        ‖primeExpSum W' W (a i / q + u i)‖ ^ 2 ≤
        ∑ b ∈ (range r).filter r.Coprime, ‖primeExpSum W' W (a i / q + u i + b / r)‖ ^ 2 := by
      intro i _ r hr
      obtain ⟨hr1, hrR, hrsq, _⟩ := hCmem r hr
      have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 hr1
      have hM := montgomery_ineq hrsq ((Ioc ⌊W'⌋₊ ⌊W⌋₊).filter Nat.Prime)
        (fun n => (Real.log n : ℂ)) (by
          intro p hp
          rw [mem_filter, mem_Ioc] at hp
          refine (Nat.Prime.coprime_iff_not_dvd hp.2).2 fun hpr => ?_
          have : p ≤ r := Nat.le_of_dvd hr1 hpr
          have h1 : (⌊W'⌋₊ : ℝ) < p := by exact_mod_cast hp.1.1
          have h2 : W' < (⌊W'⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one W'
          have h3 : (p : ℝ) ≤ r := by exact_mod_cast this
          have h4 : (⌊W'⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
          have : W' < p := by linarith
          linarith) (a i / q + u i)
      simp only [primeExpSum] at hM ⊢
      rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hφ, mul_comm]
      exact hM
    have hsum : (∑ r ∈ C, (1 / Nat.totient r : ℝ)) * ∑ i ∈ s, ‖primeExpSum W' W (a i / q + u i)‖ ^ 2 ≤
        ∑ i ∈ s, ∑ r ∈ C, ∑ b ∈ (range r).filter r.Coprime,
          ‖primeExpSum W' W (a i / q + u i + b / r)‖ ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun i hi => ?_
      rw [sum_mul]
      exact sum_le_sum fun r hr => hMont i hi r hr
    have hlog := Prelim.log_le_sum_coprime hq (show (0 : ℝ) ≤ R by linarith)
    have hS0 : 0 ≤ ∑ i ∈ s, ‖primeExpSum W' W (a i / q + u i)‖ ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    calc Nat.totient q / q * Real.log R * ∑ i ∈ s, ‖primeExpSum W' W (a i / q + u i)‖ ^ 2
        ≤ (∑ r ∈ C, (1 / Nat.totient r : ℝ)) * ∑ i ∈ s, ‖primeExpSum W' W (a i / q + u i)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hlog hS0
      _ ≤ _ := hsum.trans hLS

end TernaryGoldbach.MinorArcs
