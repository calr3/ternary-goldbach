import TernaryGoldbach.MinorArcs.TypeIProof
import TernaryGoldbach.Prelim.LargeSieveMV
import TernaryGoldbach.Prelim.SumMuSqPhi
import TernaryGoldbach.MinorArcs.Montgomery
import TernaryGoldbach.MinorArcs.TypeIINumerics

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

/-! ### [B, Proposition 5.2.4] -/

/-- `S₂(U', W', W) = ∑_{U' < m ≤ x/W, m odd} |∑_{W' < p ≤ W} (log p) e(αmp)|²` [B, (5.38)], `v = 2`. -/
noncomputable def S2 (α x U' W' W : ℝ) : ℝ := oddSqSum α W' W U' (x / W)

theorem primeExpSum_add_int (W' W β : ℝ) (n : ℤ) :
    primeExpSum W' W (β + n) = primeExpSum W' W β := by
  unfold primeExpSum
  refine sum_congr rfl fun p _ => ?_
  rw [add_mul, e_add]
  have : e ((n : ℝ) * p) = 1 := (e_eq_one_iff _).2 ⟨n * p, by push_cast; ring⟩
  rw [this, mul_one]

/-- Lemma 5.2.1 for a set of odd `m` of width `≤ 2Δ`, with `2α = a/q + δ/x + k`, `δ ≠ 0`:
`ν = |δ|q/x`, `υ = Δ|δ|/x`, provided `(q + Δ)|δ|/x ≤ 1/q`. -/
theorem odd_block_bound {α x δ : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (h2α : 2 * α = a / q + δ / x + k) (hx : 0 < x) (hδ0 : δ ≠ 0) (s : Finset ℤ)
    (hodd : ∀ m ∈ s, Odd m) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hwidth : ∀ m ∈ s, ∀ m' ∈ s, |((m - m' : ℤ) : ℝ)| ≤ 2 * Δ)
    (hcond : (q + Δ) * |δ| / x ≤ 1 / q) {W' W : ℝ} (hW' : 0 ≤ W') :
    (∑ m ∈ s, ‖primeExpSum W' W (α * m)‖ ^ 2 ≤ (W - W' + x / (|δ| * q)) * logSqSum W' W) ∧
    (∀ R : ℝ, 1 ≤ R → R ≤ W' → q * R ^ 2 * ((q + Δ) * |δ| / x) ≤ 1 →
      Nat.totient q / q * Real.log R * ∑ m ∈ s, ‖primeExpSum W' W (α * m)‖ ^ 2 ≤
        (W - W' + x / (|δ| * q)) * logSqSum W' W) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hδpos : 0 < |δ| := abs_pos.2 hδ0
  set j : ℤ → ℤ := fun m => (m - 1) / 2
  have hj : ∀ m ∈ s, (m : ℝ) = 2 * j m + 1 := by
    intro m hm
    obtain ⟨t, ht⟩ := hodd m hm
    have : j m = t := by simp only [j]; omega
    rw [this, ht]; push_cast; ring
  set aa : ℤ → ℤ := fun m => j m * a
  set u : ℤ → ℝ := fun m => α + j m * (δ / x)
  have hS : ∀ m ∈ s, primeExpSum W' W (α * m) = primeExpSum W' W (aa m / q + u m) := by
    intro m hm
    have e : α * m = (aa m / q + u m) + (j m * k : ℤ) := by
      rw [hj m hm]; simp only [aa, u]; push_cast
      have : α * (2 * j m + 1) = α + j m * (2 * α) := by ring
      rw [this, h2α]; ring
    rw [e, primeExpSum_add_int]
  have hsum : ∑ m ∈ s, ‖primeExpSum W' W (α * m)‖ ^ 2 =
      ∑ m ∈ s, ‖primeExpSum W' W (aa m / q + u m)‖ ^ 2 :=
    sum_congr rfl fun m hm => by rw [hS m hm]
  have hjdiff : ∀ m ∈ s, ∀ m' ∈ s, ((j m - j m' : ℤ) : ℝ) = ((m - m' : ℤ) : ℝ) / 2 := by
    intro m hm m' hm'
    push_cast; rw [hj m hm, hj m' hm']; ring
  have hres := lemma_5_2_1 s hq aa u (ν := |δ| * q / x) (υ := Δ * |δ| / x) (W' := W') (W := W)
    (by positivity)
    (by positivity) (by
      have : |δ| * q / x + Δ * |δ| / x = (q + Δ) * |δ| / x := by ring
      rw [this]; exact hcond)
    (by
      intro m hm m' hm'
      have e : u m - u m' = ((j m - j m' : ℤ) : ℝ) * (δ / x) := by simp only [u]; push_cast; ring
      rw [e, abs_mul, hjdiff m hm m' hm', abs_div, abs_div, abs_of_pos hx]
      have := hwidth m hm m' hm'
      rw [abs_two]
      have h1 : |((m - m' : ℤ) : ℝ)| / 2 ≤ Δ := by linarith
      calc |((m - m' : ℤ) : ℝ)| / 2 * (|δ| / x) ≤ Δ * (|δ| / x) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = Δ * |δ| / x := by ring)
    (by
      intro m hm m' hm' hne hdvd
      have hdvd' : (q : ℤ) ∣ j m - j m' := by
        have : aa m - aa m' = (j m - j m') * a := by simp only [aa]; ring
        rw [this] at hdvd
        exact hcop.symm.dvd_of_dvd_mul_right hdvd
      have hjne : j m - j m' ≠ 0 := by
        intro h
        have := hjdiff m hm m' hm'
        rw [h] at this
        push_cast at this
        exact hne (by have : ((m : ℝ) - m') = 0 := by linarith
                      exact_mod_cast sub_eq_zero.1 this)
      have hq' : (q : ℝ) ≤ |((j m - j m' : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.le_of_dvd (abs_pos.2 hjne) ((dvd_abs _ _).2 hdvd')
      have e : u m - u m' = ((j m - j m' : ℤ) : ℝ) * (δ / x) := by simp only [u]; push_cast; ring
      rw [e, abs_mul, abs_div, abs_of_pos hx]
      calc |δ| * q / x = q * (|δ| / x) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hq' (by positivity)) hW'
  have hinv : (|δ| * q / x)⁻¹ = x / (|δ| * q) := by rw [inv_div]
  rw [hinv] at hres
  refine ⟨hsum ▸ hres.1, fun R hR hRW hRq => hsum ▸ hres.2 R hR hRW (by
    have : |δ| * q / x + Δ * |δ| / x = (q + Δ) * |δ| / x := by ring
    rw [this]; exact hRq)⟩

/-- Odd integers in `(A₀, A₁]` differ by at most `A₁ - A₀` (strictly less). -/
theorem abs_sub_le_of_mem_Ioc {A₀ A₁ : ℝ} {m m' : ℤ} (hm : m ∈ Ioc ⌊A₀⌋ ⌊A₁⌋)
    (hm' : m' ∈ Ioc ⌊A₀⌋ ⌊A₁⌋) : |((m - m' : ℤ) : ℝ)| ≤ A₁ - A₀ := by
  rw [mem_Ioc] at hm hm'
  have h1 : (⌊A₁⌋ : ℝ) ≤ A₁ := Int.floor_le _
  have h2 : A₀ < (⌊A₀⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have : |m - m'| ≤ ⌊A₁⌋ - ⌊A₀⌋ - 1 := by rw [abs_le]; omega
  have : ((|m - m'| : ℤ) : ℝ) ≤ ⌊A₁⌋ - ⌊A₀⌋ - 1 := by exact_mod_cast this
  rw [← Int.cast_abs]; linarith

/-- **[B, (5.56)]**: if `δ ≠ 0` and `x/4W + q ≤ x/|δ|q` (and `U' ≥ x/2W`), then
(i) `S₂ ≤ (W - W' + x/|δ|q) ∑ (log p)²`;
(ii) for `1 ≤ R ≤ W'` with `R² ≤ (x/|δ|q)/(q + x/4W)`,
`(φ(q)/q) log R · S₂ ≤ (W - W' + x/|δ|q) ∑ (log p)²` ([B]'s gain, with `R` capped at `W'`). -/
theorem prop_5_2_4_c {α x δ U' W' W : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hx : 0 < x) (hW : 0 < W)
    (hδ0 : δ ≠ 0) (hcond : x / (4 * W) + q ≤ x / (|δ| * q)) (hU' : x / (2 * W) ≤ U')
    (hW' : 0 ≤ W') :
    (S2 α x U' W' W ≤ (W - W' + x / (|δ| * q)) * logSqSum W' W) ∧
    (∀ R : ℝ, 1 ≤ R → R ≤ W' → R ^ 2 ≤ x / (|δ| * q) / (q + x / (4 * W)) →
      Nat.totient q / q * Real.log R * S2 α x U' W' W ≤
        (W - W' + x / (|δ| * q)) * logSqSum W' W) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hδpos : 0 < |δ| := abs_pos.2 hδ0
  set s := (Ioc ⌊U'⌋ ⌊x / W⌋).filter Odd
  have hS2 : S2 α x U' W' W = ∑ m ∈ s, ‖primeExpSum W' W (α * m)‖ ^ 2 := by
    rw [S2, oddSqSum, sum_filter]
  have hcond' : (q + x / (4 * W)) * |δ| / x ≤ 1 / q := by
    rw [div_le_div_iff₀ hx hq0]
    rw [le_div_iff₀ (by positivity)] at hcond
    nlinarith
  have hres := odd_block_bound hq hcop h2α hx hδ0 s (fun m hm => (mem_filter.1 hm).2) (W' := W')
    (W := W)
    (Δ := x / (4 * W)) (by positivity) (by
      intro m hm m' hm'
      have := abs_sub_le_of_mem_Ioc (mem_filter.1 hm).1 (mem_filter.1 hm').1
      have h2 : x / W - U' ≤ 2 * (x / (4 * W)) := by
        have : x / W - x / (2 * W) = 2 * (x / (4 * W)) := by field_simp; ring
        linarith
      linarith) hcond' hW'
  rw [hS2]
  refine ⟨hres.1, fun R hR hRW hR2 => hres.2 R hR hRW ?_⟩
  have hpos : 0 < (q : ℝ) + x / (4 * W) := by positivity
  rw [le_div_iff₀ hpos] at hR2
  have : R ^ 2 * (q + x / (4 * W)) * (|δ| * q) ≤ x := by
    rwa [le_div_iff₀ (by positivity)] at hR2
  rw [mul_div_assoc', div_le_one hx]
  nlinarith

/-- **[B, (5.53)]**: for `q ≤ ρQ`, `0 < ρ ≤ 1`, `W' ≥ W/2`, `U' ≥ x/2W`,
`S₂ ≤ (max(1, 2ρ)(x/8q + x/2W) + W/2 + 2q) ∑ (log p)²`. -/
theorem prop_5_2_4_a {α x Q ρ U' W' W : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hqρ : (q : ℝ) ≤ ρ * Q) (hx : 0 < x) (hW : 0 < W) (hW'W : W / 2 ≤ W')
    (hW'W' : W' ≤ W) (hU' : x / (2 * W) ≤ U') :
    S2 α x U' W' W ≤ (max 1 (2 * ρ) * (x / (8 * q) + x / (2 * W)) + W / 2 + 2 * q) *
      logSqSum W' W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := by nlinarith
  have hqQ : (q : ℝ) ≤ Q := hqρ.trans (by nlinarith)
  have hL := logSqSum_nonneg W' W
  have h := lemma_5_2_3_a hq hcop hα hqQ (by linarith) hW'W' (W' := W') (W := W) U' (x / W)
  rw [S2]
  refine h.trans ?_
  set m := min (2 * (q : ℝ)) Q
  have hm0 : 0 < m := lt_min (by positivity) hQ
  have hm : 1 / m ≤ max 1 (2 * ρ) / (2 * q) := by
    rcases min_choice (2 * (q : ℝ)) Q with h | h
    · rw [show m = 2 * (q : ℝ) from h, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [le_max_left 1 (2 * ρ)]
    · rw [show m = Q from h, div_le_div_iff₀ hQ (by positivity)]
      nlinarith [le_max_right 1 (2 * ρ)]
  set D := x / W - U'
  have hD : D ≤ x / (2 * W) := by
    simp only [D]; have : x / W - x / (2 * W) = x / (2 * W) := by field_simp; ring
    linarith
  have hM : 1 ≤ max 1 (2 * ρ) := le_max_left _ _
  have hB0 : 0 ≤ (W - W' + 2 * q) * logSqSum W' W := mul_nonneg (by linarith) hL
  rcases le_or_gt D 0 with hD0 | hD0
  · rw [Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg hD0 hm0.le)]
    simp only [Nat.cast_zero, zero_mul]
    have : 0 ≤ max 1 (2 * ρ) * (x / (8 * q) + x / (2 * W)) + W / 2 + 2 * q := by positivity
    positivity
  have hceil : (⌈D / m⌉₊ : ℝ) ≤ D / m + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hL
  have hDm : D / m ≤ x / (2 * W) * (max 1 (2 * ρ) / (2 * q)) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul hD hm (by positivity) (by positivity)
  calc (⌈D / m⌉₊ : ℝ) * (W - W' + 2 * q) ≤ (D / m + 1) * (W - W' + 2 * q) :=
        mul_le_mul_of_nonneg_right hceil (by linarith)
    _ = D / m * (W - W') + D / m * (2 * q) + (W - W' + 2 * q) := by ring
    _ ≤ x / (2 * W) * (max 1 (2 * ρ) / (2 * q)) * (W / 2) +
        x / (2 * W) * (max 1 (2 * ρ) / (2 * q)) * (2 * q) + (W / 2 + 2 * q) := by
        gcongr <;> linarith
    _ = _ := by field_simp; ring

/-- **[B, (5.55)]**: if `W > x/4q` (and `q ≤ Q`, `W' ≥ W/2`, `U' ≥ x/2W`),
`S₂ ≤ (W/2 + q/(1 - x/4Wq)) ∑ (log p)²`. -/
theorem prop_5_2_4_b {α x Q U' W' W : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hqQ : (q : ℝ) ≤ Q)
    (hx : 0 < x) (hW : 0 < W) (hWq : x / (4 * q) < W) (hW'W : W / 2 ≤ W') (hU' : x / (2 * W) ≤ U') :
    S2 α x U' W' W ≤ (W / 2 + q / (1 - x / (4 * W * q))) * logSqSum W' W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hϱ1 : x / (4 * W * q) < 1 := by
    rw [div_lt_one (by positivity)]; rw [div_lt_iff₀ (by positivity)] at hWq; linarith
  have h := lemma_5_2_3_c hq hcop hα (ϱ := x / (4 * W * q)) (ρ := 1) (by positivity) hϱ1.le
    zero_le_one (by linarith) (by linarith) (W' := W') (W := W) (by linarith) (A₀ := U')
    (A₁ := x / W) (by
      have : 2 * (x / (4 * W * q)) * q = x / (2 * W) := by field_simp; ring
      have h2 : x / W - x / (2 * W) = x / (2 * W) := by field_simp; ring
      linarith)
  rw [S2, mul_one] at *
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (logSqSum_nonneg _ _))
  linarith

/-- Splitting `∑_{⌊a⌋ < n ≤ ⌊b⌋} G(n)` (`G ≥ 0`) into blocks of real length `h > 0`. -/
theorem sum_Ioc_le_blocks_real {G : ℤ → ℝ} (hG : ∀ n, 0 ≤ G n) {h : ℝ} (hh : 0 < h) :
    ∀ (J : ℕ) (a b : ℝ), b ≤ a + J * h →
      ∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, G n ≤
        ∑ j ∈ range J, ∑ n ∈ Ioc ⌊a + j * h⌋ ⌊min (a + (j + 1) * h) b⌋, G n := by
  intro J
  induction J with
  | zero =>
    intro a b hab
    simp only [CharP.cast_eq_zero, zero_mul, add_zero] at hab
    rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hab))]; simp
  | succ J ih =>
    intro a b hab
    rw [sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, zero_add, one_mul]
    have hih := ih (a + h) b (by push_cast at hab; linarith)
    have hrw : ∀ j : ℕ, a + h + j * h = a + ((j + 1 : ℕ) : ℝ) * h := fun j => by push_cast; ring
    have hrw2 : ∀ j : ℕ, a + h + (j + 1) * h = a + (((j + 1 : ℕ) : ℝ) + 1) * h := fun j => by
      push_cast; ring
    simp_rw [hrw, hrw2] at hih
    rcases le_or_gt b (a + h) with hb | hb
    · rw [min_eq_right hb]
      have : ∑ n ∈ Ioc ⌊a + h⌋ ⌊b⌋, G n = 0 := by
        rw [Ioc_eq_empty (not_lt.2 (Int.floor_mono hb))]; simp
      have h0 : 0 ≤ ∑ j ∈ range J, ∑ n ∈ Ioc ⌊a + ((j + 1 : ℕ) : ℝ) * h⌋
          ⌊min (a + (((j + 1 : ℕ) : ℝ) + 1) * h) b⌋, G n :=
        sum_nonneg fun _ _ => sum_nonneg fun _ _ => hG _
      linarith
    · rw [min_eq_left hb.le]
      have hsplit : ∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, G n =
          ∑ n ∈ Ioc ⌊a⌋ ⌊a + h⌋, G n + ∑ n ∈ Ioc ⌊a + h⌋ ⌊b⌋, G n := by
        rw [← sum_union (Finset.disjoint_left.2 fun n h1 h2 => by
          simp only [mem_Ioc] at h1 h2; omega)]
        congr 1
        ext n; simp only [mem_Ioc, mem_union]
        have h1 : ⌊a⌋ ≤ ⌊a + h⌋ := Int.floor_mono (by linarith)
        have h2 : ⌊a + h⌋ ≤ ⌊b⌋ := Int.floor_mono hb.le
        omega
      rw [hsplit]; linarith

set_option maxHeartbeats 1000000 in
/-- **[B, (5.57)]**: if `δ ≠ 0`, `q ≤ ρQ`, `0 ≤ ρ < 1` (and `|δ/x| ≤ 1/qQ`, `W' ≥ W/2`,
`U' ≥ x/2W`), `S₂ ≤ (x/|δq| + W/2 + x/(8(1-ρ)Q) + x/(4(1-ρ)W)) ∑ (log p)²`. -/
theorem prop_5_2_4_d {α x δ Q ρ U' W' W : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (h2α : 2 * α = a / q + δ / x + k) (hδQ : |δ / x| ≤ 1 / (q * Q))
    (hρ1 : ρ < 1) (hqρ : (q : ℝ) ≤ ρ * Q) (hx : 0 < x) (hW : 0 < W) (hδ0 : δ ≠ 0)
    (hW'W : W / 2 ≤ W') (hU' : x / (2 * W) ≤ U') :
    S2 α x U' W' W ≤
      (x / (|δ| * q) + W / 2 + x / (8 * (1 - ρ) * Q) + x / (4 * (1 - ρ) * W)) * logSqSum W' W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hδpos : 0 < |δ| := abs_pos.2 hδ0
  have hL := logSqSum_nonneg W' W
  have hρ : 0 < ρ := by
    by_contra h; push Not at h
    have : ρ * Q ≤ 0 ∨ Q < 0 := by
      rcases le_or_gt 0 Q with hQ | hQ
      · left; nlinarith
      · right; exact hQ
    rcases this with h1 | h1
    · linarith
    · -- `|δ/x| ≤ 1/(qQ) < 0` is impossible.
      have : 1 / ((q : ℝ) * Q) < 0 := by
        rw [one_div]; exact inv_lt_zero.2 (by nlinarith)
      linarith [abs_nonneg (δ / x)]
  have hQ : 0 < Q := by nlinarith
  set Q' := x / (|δ| * q) with hQ'def
  have hQQ' : Q ≤ Q' := by
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity)] at hδQ
    rw [hQ'def, le_div_iff₀ (by positivity)]; nlinarith
  have hqQ' : (q : ℝ) ≤ ρ * Q' := hqρ.trans (by nlinarith)
  have hgap : (1 - ρ) * Q' ≤ Q' - q := by linarith
  have hQ'pos : 0 < Q' := by positivity
  have hgap0 : 0 < Q' - q := lt_of_lt_of_le (by nlinarith) hgap
  set h := 2 * (Q' - q)
  have hh : 0 < h := by positivity
  set J := ⌈(x / W - U') / h⌉₊
  have hblocks := sum_Ioc_le_blocks_real
    (G := fun m : ℤ => if Odd m then ‖primeExpSum W' W (α * m)‖ ^ 2 else 0)
    (fun m => by split_ifs; exacts [sq_nonneg _, le_rfl]) hh J U' (x / W) (by
      have := Nat.le_ceil ((x / W - U') / h); rw [div_le_iff₀ hh] at this; linarith)
  rw [S2, oddSqSum]
  refine hblocks.trans ?_
  have hblock : ∀ j ∈ range J,
      ∑ m ∈ Ioc ⌊U' + j * h⌋ ⌊min (U' + (j + 1) * h) (x / W)⌋,
        (if Odd m then ‖primeExpSum W' W (α * m)‖ ^ 2 else 0) ≤ (W / 2 + Q') * logSqSum W' W := by
    intro j _
    set B := Ioc ⌊U' + j * h⌋ ⌊min (U' + (j + 1) * h) (x / W)⌋
    rw [← sum_filter]
    have hres := (odd_block_bound hq hcop h2α hx hδ0 (B.filter Odd) (fun m hm => (mem_filter.1 hm).2)
      (Δ := Q' - q) hgap0.le (by
        intro m hm m' hm'
        have := abs_sub_le_of_mem_Ioc (mem_filter.1 hm).1 (mem_filter.1 hm').1
        have : min (U' + (j + 1) * h) (x / W) - (U' + j * h) ≤ h := by
          have := min_le_left (U' + (j + 1) * h) (x / W); linarith
        linarith) (by
        have e : ((q : ℝ) + (Q' - q)) * |δ| / x = 1 / q := by
          simp only [hQ'def]; field_simp; ring
        rw [e]) (W' := W') (W := W) (by linarith)).1
    refine hres.trans (mul_le_mul_of_nonneg_right ?_ hL)
    linarith
  refine (sum_le_sum hblock).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hL
  set D := x / W - U'
  have hD : D ≤ x / (2 * W) := by
    simp only [D]; have : x / W - x / (2 * W) = x / (2 * W) := by field_simp; ring
    linarith
  have hJ : (J : ℝ) ≤ 1 + x / (2 * W) / h := by
    rcases le_or_gt D 0 with hD0 | hD0
    · have : J = 0 := Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg hD0 hh.le)
      rw [this]; push_cast; positivity
    · have := (Nat.ceil_lt_add_one (show 0 ≤ D / h by positivity)).le
      have : D / h ≤ x / (2 * W) / h := div_le_div_of_nonneg_right hD hh.le
      linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hJ' : (J : ℝ) ≤ 1 + x / (4 * W * (1 - ρ) * Q') := by
    refine hJ.trans ?_
    have : x / (2 * W) / h ≤ x / (4 * W * (1 - ρ) * Q') := by
      simp only [h]
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hgap (show 0 ≤ x * (4 * W) by positivity)
      nlinarith
    linarith
  calc (J : ℝ) * (W / 2 + Q') ≤ (1 + x / (4 * W * (1 - ρ) * Q')) * (W / 2 + Q') :=
        mul_le_mul_of_nonneg_right hJ' (by positivity)
    _ = Q' + W / 2 + x / (8 * (1 - ρ) * Q') + x / (4 * (1 - ρ) * W) := by field_simp; ring
    _ ≤ Q' + W / 2 + x / (8 * (1 - ρ) * Q) + x / (4 * (1 - ρ) * W) := by
        gcongr

/-! ### [B, Lemma 5.2.3, (5.51)] -/

/-- The weighted large sieve for `S(β)`: `∑_r (W - W' + 1 + (3/2)δ_r⁻¹)⁻¹ |S(β_r)|² ≤ ∑ (log p)²`. -/
theorem large_sieve_primes_weighted {ι : Type*} (s : Finset ι) (β δ : ι → ℝ)
    (hδ : ∀ r ∈ s, 0 < δ r)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → δ r ≤ |(β r - β r') - round (β r - β r')|)
    {W' W : ℝ} (hW' : 0 ≤ W') :
    ∑ r ∈ s, (W - W' + 1 + 3 / 2 * (δ r)⁻¹)⁻¹ * ‖primeExpSum W' W (β r)‖ ^ 2 ≤ logSqSum W' W := by
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
    have hW0 : 0 ≤ W := by
      by_contra h; push Not at h
      have : ⌊W⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
      omega
    have hN : (N : ℝ) ≤ W - W' + 1 := by
      have h1 : (⌊W⌋₊ : ℝ) ≤ W := Nat.floor_le hW0
      have h2 : W' < (⌊W'⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one W'
      have : (N : ℝ) = ⌊W⌋₊ - ⌊W'⌋₊ := by simp only [N, M]; rw [Nat.cast_sub hlt.le]
      rw [this]; linarith
    rw [hL]
    refine le_trans ?_ (Prelim.large_sieve_weighted s β δ hδ hsep M N a)
    refine sum_le_sum fun r hr => ?_
    rw [hS]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h0 : 0 < (N : ℝ) + 3 / 2 * (δ r)⁻¹ := by
      have := hδ r hr; positivity
    exact inv_anti₀ h0 (by linarith)
  · have hempty : Ioc ⌊W'⌋₊ ⌊W⌋₊ = ∅ := Ioc_eq_empty (not_lt.2 hge)
    simp [primeExpSum, logSqSum, hempty]

/-- The general separation of `A/q + b/r - b'/r' + u` (`r, r'` coprime to `q`,
`(b, r) = (b', r') = 1`): unless `q | A`, `r = r'`, `b = b'`, it is `≥ 1/(qrr') - |u|`. -/
theorem frac_sep {q r r' b b' : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (hrq : Nat.Coprime r q) (hr'q : Nat.Coprime r' q) (hb : b < r) (hb' : b' < r')
    (hbr : Nat.Coprime r b) (hb'r : Nat.Coprime r' b') {A : ℤ}
    (hne : ¬ ((q : ℤ) ∣ A ∧ r = r' ∧ b = b')) (u : ℝ) :
    1 / ((q : ℝ) * r * r') - |u| ≤
      |(A / q + b / r - b' / r' + u : ℝ) - round (A / q + b / r - b' / r' + u : ℝ)| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr'0 : (0 : ℝ) < r' := by exact_mod_cast hr'
  set M : ℤ := A * r * r' + q * (b * r' - b' * r)
  have hM : (A / q + b / r - b' / r' : ℝ) = M / (q * r * r') := by
    simp only [M]; push_cast; field_simp; ring
  have hdiv : ¬ ((q * r * r' : ℕ) : ℤ) ∣ M := by
    intro hdiv
    apply hne
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
    exact ⟨h5, rfl, rfl⟩
  apply le_dist_round_of_forall
  intro n
  have hne' : M - n * (q * r * r' : ℕ) ≠ 0 := by
    intro h; exact hdiv ⟨n, by linarith⟩
  have hqrr : (0 : ℝ) < q * r * r' := by positivity
  have h1 : 1 / ((q : ℝ) * r * r') ≤ |(M : ℝ) / (q * r * r') - n| := by
    have e : (M : ℝ) / (q * r * r') - n = ((M - n * (q * r * r' : ℕ) : ℤ) : ℝ) / (q * r * r') := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos hqrr]
    refine div_le_div_of_nonneg_right ?_ hqrr.le
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne'
  have h3 := abs_sub_abs_le_abs_sub ((M : ℝ) / (q * r * r') - n) (-u)
  have e2 : (A / q + b / r - b' / r' + u : ℝ) - n = ((M : ℝ) / (q * r * r') - n) - (-u) := by
    rw [← hM]; ring
  rw [e2]
  rw [abs_neg] at h3
  linarith

theorem dist_round_add_int (t : ℝ) (n : ℤ) : |(t + n) - round (t + n)| = |t - round t| := by
  rw [round_add_intCast]; push_cast; ring_nf

set_option maxHeartbeats 2000000 in
/-- One block of [B, (5.51)]: for odd `m` in a set of width `< 2q`, with `qR² < Q`, `1 ≤ R ≤ W'`,
`(∑_{r ≤ R, (r,q)=1} μ²(r)/φ(r) · (W - W' + 1 + (3/2)(1/(qrR) - 1/Q)⁻¹)⁻¹) ∑_m |S(αm)|² ≤ ∑ (log p)²`
(Montgomery's inequality and the weighted large sieve, [B, (5.46)–(5.48)]). -/
theorem odd_block_weighted {α Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) {R : ℝ} (hR1 : 1 ≤ R) (hRQ : q * R ^ 2 < Q)
    {W' W : ℝ} (hW' : 0 ≤ W') (hWW : W' ≤ W) (hRW : R ≤ W') (s : Finset ℤ) (hodd : ∀ m ∈ s, Odd m)
    (hwidth : ∀ m ∈ s, ∀ m' ∈ s, |m - m'| < 2 * q) :
    (∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
        (W - W' + 1 + 3 / 2 * (1 / (q * r * R) - 1 / Q)⁻¹)⁻¹ * (1 / Nat.totient r : ℝ)) *
      ∑ m ∈ s, ‖primeExpSum W' W (α * m)‖ ^ 2 ≤ logSqSum W' W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_le_of_lt (by positivity) hRQ
  set N := ⌊R⌋₊
  set C := (Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r q)
  set T := (s ×ˢ (C ×ˢ range N)).filter (fun t => t.2.2 < t.2.1 ∧ Nat.Coprime t.2.1 t.2.2)
  set β : ℤ × ℕ × ℕ → ℝ := fun t => α * t.1 + t.2.2 / t.2.1
  set δ : ℤ × ℕ × ℕ → ℝ := fun t => 1 / (q * t.2.1 * R) - 1 / Q
  set w : ℕ → ℝ := fun r => (W - W' + 1 + 3 / 2 * (1 / (q * r * R) - 1 / Q)⁻¹)⁻¹
  have hCmem : ∀ r ∈ C, 1 ≤ r ∧ (r : ℝ) ≤ R ∧ Squarefree r ∧ Nat.Coprime r q := by
    intro r hr
    rw [mem_filter, mem_Icc] at hr
    exact ⟨hr.1.1, (Nat.cast_le.2 hr.1.2).trans (Nat.floor_le (by linarith)), hr.2.1, hr.2.2⟩
  have hδpos : ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ R → 0 < 1 / (q * r * R) - 1 / Q := by
    intro r hr hrR
    have : (q : ℝ) * r * R < Q := by
      have : (q : ℝ) * r * R ≤ q * R ^ 2 := by
        rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrR hq0.le) (by linarith)
      linarith
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    rw [sub_pos]; exact one_div_lt_one_div_of_lt (by positivity) this
  have hw0 : ∀ r ∈ C, 0 ≤ w r := by
    intro r hr
    obtain ⟨hr1, hrR, _, _⟩ := hCmem r hr
    have := hδpos r hr1 hrR
    simp only [w]
    have : 0 ≤ W - W' := by linarith
    positivity
  -- The weighted large sieve over `T`.
  have hLS := large_sieve_primes_weighted T β δ (W' := W') (W := W) (by
      intro t ht
      rw [mem_filter, mem_product, mem_product] at ht
      obtain ⟨hr1, hrR, _, _⟩ := hCmem _ ht.1.2.1
      exact hδpos _ hr1 hrR) (by
      intro t ht t' ht' hne
      rw [mem_filter, mem_product, mem_product] at ht ht'
      obtain ⟨⟨hm, hr, _⟩, hb, hbr⟩ := ht
      obtain ⟨⟨hm', hr', _⟩, hb', hb'r⟩ := ht'
      obtain ⟨hr1, hrR, _, hrq⟩ := hCmem _ hr
      obtain ⟨hr1', hrR', _, hr'q⟩ := hCmem _ hr'
      obtain ⟨j, hj⟩ : ∃ j : ℤ, t.1 - t'.1 = 2 * j := by
        obtain ⟨u, hu⟩ := hodd _ hm; obtain ⟨u', hu'⟩ := hodd _ hm'; exact ⟨u - u', by omega⟩
      have hjq : |j| < q := by
        have := hwidth _ hm _ hm'; rw [hj, abs_mul] at this; norm_num at this; omega
      set ε := 2 * α - a / q - k
      have e : β t - β t' = ((j * a : ℤ) / q + t.2.2 / t.2.1 - t'.2.2 / t'.2.1 + j * ε : ℝ) +
          ((j * k : ℤ) : ℝ) := by
        simp only [β, ε]
        have : (t.1 : ℝ) - t'.1 = 2 * j := by exact_mod_cast hj
        push_cast
        linear_combination α * this
      rw [e, dist_round_add_int]
      have hfs := frac_sep hq hr1 hr1' hrq hr'q hb hb' hbr hb'r (A := j * a) (by
        rintro ⟨hA, hrr, hbb⟩
        have hqj : (q : ℤ) ∣ j := hcop.symm.dvd_of_dvd_mul_right hA
        have hj0 : j = 0 := by
          by_contra h0
          have := Int.le_of_dvd (abs_pos.2 h0) ((dvd_abs _ _).2 hqj); omega
        apply hne
        have : t.1 = t'.1 := by omega
        exact Prod.ext this (Prod.ext hrr hbb)) (j * ε)
      refine le_trans ?_ hfs
      simp only [δ]
      have h1 : 1 / ((q : ℝ) * t.2.1 * R) ≤ 1 / (q * t.2.1 * t'.2.1) := by
        have hr0 : (0 : ℝ) < t'.2.1 := by exact_mod_cast hr1'
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_left hrR' (by positivity)
      have h2 : |(j : ℝ) * ε| ≤ 1 / Q := by
        rw [abs_mul]
        have hjq' : |(j : ℝ)| ≤ q - 1 := by
          have : |j| ≤ q - 1 := by omega
          rw [← Int.cast_abs]; exact_mod_cast this
        calc |(j : ℝ)| * |ε| ≤ (q - 1) * (1 / (q * Q)) :=
              mul_le_mul hjq' hα (abs_nonneg _) (by linarith)
          _ ≤ 1 / Q := by
              rw [div_eq_mul_one_div 1 Q, mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) hQ]
              nlinarith
      linarith) hW'
  -- Rewrite the sum over `T`.
  have hT : ∑ t ∈ T, (W - W' + 1 + 3 / 2 * (δ t)⁻¹)⁻¹ * ‖primeExpSum W' W (β t)‖ ^ 2 =
      ∑ m ∈ s, ∑ r ∈ C, w r *
        ∑ b ∈ (range r).filter r.Coprime, ‖primeExpSum W' W (α * m + b / r)‖ ^ 2 := by
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun r hr => ?_
    have hrN : r ≤ N := (mem_Icc.1 (mem_filter.1 hr).1).2
    have hset : (range r).filter r.Coprime = (range N).filter (fun b => b < r ∧ r.Coprime b) := by
      ext b; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1.trans_le hrN, h1, h2⟩
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    rw [hset, sum_filter, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> simp [β, δ, w]
  rw [hT] at hLS
  -- Montgomery.
  have hMont : ∀ m : ℤ, ∀ r ∈ C, (1 / Nat.totient r : ℝ) * ‖primeExpSum W' W (α * m)‖ ^ 2 ≤
      ∑ b ∈ (range r).filter r.Coprime, ‖primeExpSum W' W (α * m + b / r)‖ ^ 2 := by
    intro m r hr
    obtain ⟨hr1, hrR, hrsq, _⟩ := hCmem r hr
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 hr1
    have hM := montgomery_ineq hrsq ((Ioc ⌊W'⌋₊ ⌊W⌋₊).filter Nat.Prime)
      (fun n => (Real.log n : ℂ)) (by
        intro p hp
        rw [mem_filter, mem_Ioc] at hp
        refine (Nat.Prime.coprime_iff_not_dvd hp.2).2 fun hpr => ?_
        have : p ≤ r := Nat.le_of_dvd hr1 hpr
        have h2 : W' < (⌊W'⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one W'
        have h3 : (p : ℝ) ≤ r := by exact_mod_cast this
        have h4 : (⌊W'⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
        linarith) (α * m)
    simp only [primeExpSum] at hM ⊢
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hφ]
    linarith [hM]
  refine le_trans ?_ hLS
  rw [sum_mul, sum_comm]
  refine sum_le_sum fun r hr => ?_
  rw [mul_sum]
  refine sum_le_sum fun m _ => ?_
  calc w r * (1 / Nat.totient r : ℝ) * ‖primeExpSum W' W (α * m)‖ ^ 2
      = w r * ((1 / Nat.totient r : ℝ) * ‖primeExpSum W' W (α * m)‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hMont m r hr) (hw0 r hr)

/-- Blocks of `2q` consecutive integers and a lower bound `K₀` for the weight sum of
`odd_block_weighted`: `∑_{A₀ < m ≤ A₁, m odd} |S(αm)|² ≤ ⌈(A₁ - A₀)/2q⌉ ∑ (log p)²/K₀`. -/
theorem odd_blocks_from_weight {α Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) {R : ℝ} (hR1 : 1 ≤ R)
    (hRQ : q * R ^ 2 < Q) {W' W : ℝ} (hW' : 0 ≤ W') (hWW : W' ≤ W) (hRW : R ≤ W') {K₀ : ℝ}
    (hK₀ : 0 < K₀)
    (hK : K₀ ≤ ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
        (W - W' + 1 + 3 / 2 * (1 / (q * r * R) - 1 / Q)⁻¹)⁻¹ * (1 / Nat.totient r : ℝ))
    (A₀ A₁ : ℝ) :
    oddSqSum α W' W A₀ A₁ ≤ ⌈(A₁ - A₀) / (2 * q)⌉₊ * (logSqSum W' W / K₀) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : 1 ≤ 2 * q := by omega
  have hblocks := sum_Ioc_le_blocks
    (G := fun m : ℤ => if Odd m then ‖primeExpSum W' W (α * m)‖ ^ 2 else 0)
    (fun m => by split_ifs; exacts [sq_nonneg _, le_rfl]) h2q ⌈(A₁ - A₀) / ((2 * q : ℕ) : ℝ)⌉₊ A₀ A₁
    (nblocks_spec (by positivity))
  rw [oddSqSum]
  refine hblocks.trans ?_
  have hcast : ((2 * q : ℕ) : ℝ) = 2 * q := by push_cast; ring
  rw [hcast] at *
  have hblock : ∀ j ∈ range ⌈(A₁ - A₀) / (2 * (q : ℝ))⌉₊,
      ∑ m ∈ Ioc ⌊A₀ + j * (2 * (q : ℝ))⌋ ⌊min (A₀ + (j + 1) * (2 * (q : ℝ))) A₁⌋,
        (if Odd m then ‖primeExpSum W' W (α * m)‖ ^ 2 else 0) ≤ logSqSum W' W / K₀ := by
    intro j _
    set B := Ioc ⌊A₀ + j * (2 * (q : ℝ))⌋ ⌊min (A₀ + (j + 1) * (2 * (q : ℝ))) A₁⌋
    rw [← sum_filter]
    have hw := odd_block_weighted hq hcop hα hR1 hRQ hW' hWW hRW (B.filter Odd)
      (fun m hm => (mem_filter.1 hm).2) (by
        intro m hm m' hm'
        have h1 := abs_sub_le_of_mem_Ioc (mem_filter.1 hm).1 (mem_filter.1 hm').1
        have h2 : min (A₀ + (j + 1) * (2 * (q : ℝ))) A₁ - (A₀ + j * (2 * q)) ≤ 2 * q := by
          have := min_le_left (A₀ + (j + 1) * (2 * (q : ℝ))) A₁; linarith
        have h3 : |((m - m' : ℤ) : ℝ)| < 2 * q := by
          rw [mem_filter, mem_Ioc] at hm hm'
          have h1' : (⌊min (A₀ + (j + 1) * (2 * (q : ℝ))) A₁⌋ : ℝ) ≤ min (A₀ + (j + 1) * (2 * (q : ℝ))) A₁ :=
            Int.floor_le _
          have h2' : A₀ + j * (2 * (q : ℝ)) < (⌊A₀ + j * (2 * (q : ℝ))⌋ : ℝ) + 1 := Int.lt_floor_add_one _
          have : |m - m'| ≤ ⌊min (A₀ + (j + 1) * (2 * (q : ℝ))) A₁⌋ - ⌊A₀ + j * (2 * (q : ℝ))⌋ - 1 := by
            rw [abs_le]; omega
          have : ((|m - m'| : ℤ) : ℝ) ≤ ⌊min (A₀ + (j + 1) * (2 * (q : ℝ))) A₁⌋ - ⌊A₀ + j * (2 * (q : ℝ))⌋ - 1 := by
            exact_mod_cast this
          rw [← Int.cast_abs]; linarith
        rw [← Int.cast_abs] at h3
        exact_mod_cast h3)
    rw [le_div_iff₀ hK₀]
    calc (∑ m ∈ B.filter Odd, ‖primeExpSum W' W (α * m)‖ ^ 2) * K₀
        ≤ (∑ m ∈ B.filter Odd, ‖primeExpSum W' W (α * m)‖ ^ 2) *
          ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
            (W - W' + 1 + 3 / 2 * (1 / (q * r * R) - 1 / Q)⁻¹)⁻¹ * (1 / Nat.totient r : ℝ) :=
          mul_le_mul_of_nonneg_left hK (sum_nonneg fun _ _ => sq_nonneg _)
      _ ≤ _ := by rw [mul_comm]; exact hw
  refine (sum_le_sum hblock).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]

/-- The weight sum for `R = √(σ₀W/q)`, `σ₀ = 0.30286`, `q ≤ W/13.5` [B, p. 96–97]. -/
theorem weight_caseA {Q W' W : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqW : 13.5 * q ≤ W) (hQW : 3.5 * W ≤ Q)
    (hW : 50000 ≤ W) (hW'W : W / 2 ≤ W') (hWW : W' ≤ W) :
    let R := √(0.30286 * W / q)
    2 ≤ R ∧ q * R ^ 2 < Q ∧ R ≤ W' ∧
    Nat.totient q / q * Real.log (W / (2 * q)) / W ≤
      ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
        (W - W' + 1 + 3 / 2 * (1 / (q * r * R) - 1 / Q)⁻¹)⁻¹ * (1 / Nat.totient r : ℝ) := by
  intro R
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hR2 : R ^ 2 = 0.30286 * W / q := Real.sq_sqrt (by positivity)
  have hR0 : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hRle : R ^ 2 ≤ 0.30286 * W := by
    rw [hR2, div_le_iff₀ hq0]; nlinarith
  have hRge : 2 ≤ R := by
    have : (4 : ℝ) ≤ R ^ 2 := by
      rw [hR2, le_div_iff₀ hq0]; nlinarith
    nlinarith
  have hqR : q * R ^ 2 = 0.30286 * W := by rw [hR2]; field_simp
  refine ⟨hRge, by rw [hqR]; linarith, ?_, ?_⟩
  · -- `R² ≤ σ₀W ≤ (W/2)²`.
    have : R ^ 2 ≤ (W / 2) ^ 2 := by nlinarith
    have : R ≤ W / 2 := by nlinarith
    linarith
  · -- Each weight is `≥ (2/W)(1 + r/R)⁻¹`.
    set C := (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q)
    have hw : ∀ r ∈ C, (2 / W) * ((1 + r / R)⁻¹ * (1 / Nat.totient r : ℝ)) ≤
        (W - W' + 1 + 3 / 2 * (1 / (q * r * R) - 1 / Q)⁻¹)⁻¹ * (1 / Nat.totient r : ℝ) := by
      intro r hr
      rw [mem_filter, mem_Icc] at hr
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.1.1
      have hrR : (r : ℝ) ≤ R := (Nat.cast_le.2 hr.1.2).trans (Nat.floor_le hR0.le)
      have hφ : (0 : ℝ) ≤ 1 / Nat.totient r := by positivity
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hφ
      -- `1/(qrR) - 1/Q ≥ (1 - σ₀/3.5)/(qrR)`.
      have hqrR : (q : ℝ) * r * R ≤ 0.30286 * W := by
        rw [← hqR, sq]; nlinarith [mul_le_mul_of_nonneg_left hrR hq0.le]
      have hqrR0 : (0 : ℝ) < q * r * R := by positivity
      have hδ : (1 - 0.30286 / 3.5) / (q * r * R) ≤ 1 / (q * r * R) - 1 / Q := by
        have : 1 / Q ≤ (0.30286 / 3.5) / (q * r * R) := by
          rw [div_le_div_iff₀ (by linarith) hqrR0]; nlinarith
        have e : (1 - 0.30286 / 3.5) / (q * r * R) = 1 / (q * r * R) - (0.30286 / 3.5) / (q * r * R) := by
          ring
        linarith
      have hδpos : 0 < (1 - 0.30286 / 3.5) / (q * r * R) := by positivity
      have hinv : (1 / (q * r * R) - 1 / Q)⁻¹ ≤ ((1 - 0.30286 / 3.5) / (q * r * R))⁻¹ :=
        inv_anti₀ hδpos hδ
      -- `(3/2) qrR/(1 - σ₀/3.5) ≤ (W/2)(r/R) c`, `c = 0.99465`.
      have hqRW : (q : ℝ) * R = 0.30286 * W / R := by
        field_simp
        linarith [hqR]
      have h1 : 3 / 2 * ((1 - 0.30286 / 3.5) / (q * r * R))⁻¹ ≤ W / 2 * (r / R) * 0.99465 := by
        rw [inv_div, show (q : ℝ) * r * R = r * (q * R) by ring, hqRW]
        rw [show 3 / 2 * (r * (0.30286 * W / R) / (1 - 0.30286 / 3.5)) =
          W / 2 * (r / R) * (3 * 0.30286 / (1 - 0.30286 / 3.5)) by field_simp]
        gcongr; norm_num
      -- `1 ≤ (W/2)(r/R)(1 - c)`.
      have h2 : 1 ≤ W / 2 * (r / R) * (1 - 0.99465) := by
        have hRW : R ≤ W / 2 * (1 - 0.99465) := by
          have : R ^ 2 ≤ (W / 2 * (1 - 0.99465)) ^ 2 := by nlinarith
          nlinarith
        have : 1 / R ≤ r / R := div_le_div_of_nonneg_right hr1 hR0.le
        have h3 : 1 ≤ W / 2 * (1 - 0.99465) * (1 / R) := by
          rw [mul_one_div, le_div_iff₀ hR0]; linarith
        calc (1 : ℝ) ≤ W / 2 * (1 - 0.99465) * (1 / R) := h3
          _ ≤ W / 2 * (1 - 0.99465) * (r / R) := by gcongr
          _ = _ := by ring
      have hden : W - W' + 1 + 3 / 2 * (1 / (q * r * R) - 1 / Q)⁻¹ ≤ W / 2 * (1 + r / R) := by
        have := mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 3 / 2 by norm_num)
        nlinarith
      have hpos : 0 < W - W' + 1 + 3 / 2 * (1 / (q * r * R) - 1 / Q)⁻¹ := by
        have : 0 < (1 / (q * r * R) - 1 / Q)⁻¹ := inv_pos.2 (lt_of_lt_of_le hδpos hδ)
        linarith
      calc 2 / W * (1 + r / R)⁻¹ = (W / 2 * (1 + r / R))⁻¹ := by field_simp
        _ ≤ _ := inv_anti₀ hpos hden
    refine le_trans ?_ (sum_le_sum hw)
    rw [← mul_sum]
    -- The coprime reduction and [MV73, Lemma 8].
    have hred := Prelim.sum_sqfree_div_totient_le hq (fun r => (1 + r / R)⁻¹)
      (fun n => by positivity) (fun m n hmn => by
        apply inv_anti₀ (by positivity)
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        have := div_le_div_of_nonneg_right this hR0.le; linarith) ⌊R⌋₊
    have hMV := Prelim.sum_weighted_mu_sq_div_totient hRge
    have hconv : ∀ s : Finset ℕ, ∑ r ∈ s, (1 + r / R)⁻¹ * (1 / Nat.totient r : ℝ) =
        ∑ r ∈ s, (1 + r / R)⁻¹ / Nat.totient r := fun s => sum_congr rfl fun r _ => by ring
    rw [hconv] at hMV ⊢
    have hφq : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
    -- `log R + 0.25068 ≥ (1/2) log(W/2q)`.
    have hlogR : 1 / 2 * Real.log (W / (2 * q)) ≤ Real.log R + 0.25068 := by
      have h1 : Real.log R = 1 / 2 * Real.log (0.30286 * W / q) := by
        rw [← hR2, Real.log_pow]; ring
      have h2 : Real.log (0.30286 * W / q) = Real.log (W / (2 * q)) + Real.log (2 * 0.30286) := by
        rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; field_simp
      have h3 : -0.50136 ≤ Real.log (2 * 0.30286) := by
        rw [Real.le_log_iff_exp_le (by norm_num), Real.exp_neg]
        have := exp_50136_ge
        rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        calc (2 * 0.30286 : ℝ)⁻¹ ≤ 1.65096 := by norm_num
          _ ≤ _ := this
      rw [h1, h2]; linarith
    have hS : 1 / 2 * Real.log (W / (2 * q)) ≤
        q / Nat.totient q * ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
          (1 + r / R)⁻¹ / Nat.totient r := by linarith
    have := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ 2 / W * (Nat.totient q / q) by positivity)
    calc Nat.totient q / q * Real.log (W / (2 * q)) / W
        = 2 / W * (Nat.totient q / q) * (1 / 2 * Real.log (W / (2 * q))) := by field_simp
      _ ≤ 2 / W * (Nat.totient q / q) * (q / Nat.totient q *
          ∑ r ∈ (Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
            (1 + r / R)⁻¹ / Nat.totient r) := this
      _ = _ := by field_simp; rfl

theorem aux_weight_eq {W v : ℝ} (hW : W ≠ 0) (hv : v ≠ 0) :
    W * ((1 / 2 + 1 / W) * v + 3 / 2) / v = W / 2 + 1 + 3 / 2 * (W / v) := by
  field_simp

/-- The weight sum for `R = 2`, `W/13.5 < q < W/2`, `q` odd [B, p. 97]. -/
theorem weight_caseB {Q W' W : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqodd : Odd q) (hqW : W < 13.5 * q)
    (hqW2 : 2 * q < W) (hQW : 3.5 * W ≤ Q) (hW : 10000 ≤ W) (hW'W : W / 2 ≤ W') (hWW : W' ≤ W) :
    Nat.totient q / q * Real.log (W / (2 * q)) / W ≤
      ∑ r ∈ (Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
        (W - W' + 1 + 3 / 2 * (1 / (q * r * 2) - 1 / Q)⁻¹)⁻¹ * (1 / Nat.totient r : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hQ0 : 0 < Q := by linarith
  have hC : (Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q) = {1, 2} := by
    rw [show ⌊(2 : ℝ)⌋₊ = 2 by norm_num]
    ext r
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨le_rfl, by norm_num⟩, squarefree_one, Nat.coprime_one_left q⟩
      · exact ⟨⟨by norm_num, le_rfl⟩, Nat.prime_two.squarefree, Nat.coprime_two_left.2 hqodd⟩
  rw [hC, sum_pair (by norm_num)]
  simp only [Nat.totient_one, Nat.totient_two, Nat.cast_one, div_one, mul_one, Nat.cast_ofNat]
  -- `z² = W/(2q)`, `A = 1/2 + 1/W`.
  set y := W / (2 * q) with hy
  have hy1 : 1 < y := by rw [hy, lt_div_iff₀ (by positivity)]; linarith
  have hy2 : y ≤ 6.76 := by rw [hy, div_le_iff₀ (by positivity)]; linarith
  set z := √y
  have hz2 : z ^ 2 = y := Real.sq_sqrt (by linarith)
  have hz1 : 1 ≤ z := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hy1.le
  have hz26 : z ≤ 13 / 5 := by
    rw [show (13 / 5 : ℝ) = √((13 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  set A := 1 / 2 + 1 / W
  have hA1 : 1 / 2 ≤ A := by simp only [A]; have : 0 < 1 / W := by positivity
                             linarith
  have hA2 : A ≤ 1 / 2 + 1 / 10000 := by
    simp only [A]; have : 1 / W ≤ 1 / 10000 := one_div_le_one_div_of_le (by norm_num) hW
    linarith
  -- The two weights.
  have hQinv : 1 / Q ≤ 2 / 7 / W := by
    rw [div_div, div_le_div_iff₀ hQ0 (by positivity)]; linarith
  have hweight : ∀ c : ℝ, (c = 1 ∨ c = 1 / 2) →
      (c * z ^ 2 - 2 / 7) / (A * (c * z ^ 2 - 2 / 7) + 3 / 2) / W ≤
        (W - W' + 1 + 3 / 2 * (c / (2 * q) - 1 / Q)⁻¹)⁻¹ := by
    intro c hc
    have hc0 : 1 / 2 ≤ c := by rcases hc with rfl | rfl <;> norm_num
    have hv : 0 < c * z ^ 2 - 2 / 7 := by nlinarith
    have h1 : (c * z ^ 2 - 2 / 7) / W ≤ c / (2 * q) - 1 / Q := by
      have : c / (2 * q) = c * z ^ 2 / W := by rw [hz2, hy]; field_simp
      rw [this]
      have : (c * z ^ 2 - 2 / 7) / W = c * z ^ 2 / W - 2 / 7 / W := by ring
      linarith
    have hpos : 0 < (c * z ^ 2 - 2 / 7) / W := by positivity
    have h2 : (c / (2 * q) - 1 / Q)⁻¹ ≤ W / (c * z ^ 2 - 2 / 7) := by
      have := inv_anti₀ hpos h1; rwa [inv_div] at this
    have h3 : W - W' + 1 + 3 / 2 * (c / (2 * q) - 1 / Q)⁻¹ ≤
        W * (A * (c * z ^ 2 - 2 / 7) + 3 / 2) / (c * z ^ 2 - 2 / 7) := by
      have e : W * (A * (c * z ^ 2 - 2 / 7) + 3 / 2) / (c * z ^ 2 - 2 / 7) =
          W / 2 + 1 + 3 / 2 * (W / (c * z ^ 2 - 2 / 7)) := aux_weight_eq hW0.ne' hv.ne'
      rw [e]; nlinarith
    have hpos2 : 0 < W - W' + 1 + 3 / 2 * (c / (2 * q) - 1 / Q)⁻¹ := by
      have : 0 < (c / (2 * q) - 1 / Q)⁻¹ := inv_pos.2 (lt_of_lt_of_le hpos h1)
      nlinarith
    calc (c * z ^ 2 - 2 / 7) / (A * (c * z ^ 2 - 2 / 7) + 3 / 2) / W
        = (W * (A * (c * z ^ 2 - 2 / 7) + 3 / 2) / (c * z ^ 2 - 2 / 7))⁻¹ := by
          field_simp
      _ ≤ _ := inv_anti₀ hpos2 h3
  have hw1 := hweight 1 (Or.inl rfl)
  have hw2 := hweight (1 / 2) (Or.inr rfl)
  have e1 : (1 : ℝ) / (q * 2) = 1 / (2 * q) := by ring
  have e2 : (1 : ℝ) / (q * 2 * 2) = 1 / 2 / (2 * q) := by field_simp
  rw [e1, e2]
  have hT := sub_inv_le_Tz hA1 hA2 hz1 hz26
  have hlog := two_log_le_sub_inv hz1
  have hlogy : Real.log y = 2 * Real.log z := by rw [← hz2, Real.log_pow]; norm_num
  have hTz : Tz A z = (1 * z ^ 2 - 2 / 7) / (A * (1 * z ^ 2 - 2 / 7) + 3 / 2) +
      (1 / 2 * z ^ 2 - 2 / 7) / (A * (1 / 2 * z ^ 2 - 2 / 7) + 3 / 2) := by
    unfold Tz; ring_nf
  have hφ : (Nat.totient q : ℝ) / q ≤ 1 := by
    rw [div_le_one hq0]; exact_mod_cast Nat.totient_le q
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1.le
  calc Nat.totient q / q * Real.log y / W ≤ 1 * Real.log y / W := by gcongr
    _ ≤ Tz A z / W := by rw [one_mul]; gcongr; linarith
    _ = _ := by rw [hTz, add_div]
    _ ≤ _ := add_le_add hw1 hw2

theorem totient_two_mul_le (m : ℕ) : Nat.totient (2 * m) ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd m with ⟨m', rfl⟩ | hodd
    · rcases Nat.eq_zero_or_pos m' with rfl | hm'
      · simp
      · rw [show m' + m' = 2 * m' by ring, Nat.totient_two_mul_of_even ⟨m', by ring⟩]
        have := ih m' (by omega)
        omega
    · rw [Nat.totient_two_mul_of_odd hodd]; exact Nat.totient_le m

/-- `(1/2 + 1/y) log y ≤ 2` for `1 ≤ y ≤ 6.76`. -/
theorem half_add_inv_mul_log_le {y : ℝ} (hy : 1 ≤ y) (hy2 : y ≤ 6.76) :
    (1 / 2 + 1 / y) * Real.log y ≤ 2 := by
  set z := √y
  have hz2 : z ^ 2 = y := Real.sq_sqrt (by linarith)
  have hz1 : 1 ≤ z := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hy
  have hz26 : z ≤ 13 / 5 := by
    rw [show (13 / 5 : ℝ) = √((13 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlog : Real.log y = 2 * Real.log z := by rw [← hz2, Real.log_pow]; norm_num
  have h := two_log_le_sub_inv hz1
  have hz0 : 0 < z := by linarith
  rw [hlog, ← hz2]
  have hl0 : 0 ≤ 2 * Real.log z := by have := Real.log_nonneg hz1; linarith
  calc (1 / 2 + 1 / z ^ 2) * (2 * Real.log z) ≤ (1 / 2 + 1 / z ^ 2) * (z - 1 / z) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 2 := by
        rw [show (1 / 2 + 1 / z ^ 2) * (z - 1 / z) = (z ^ 4 / 2 + z ^ 2 / 2 - 1) / z ^ 3 by
          field_simp; ring]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.2 hz1) (sub_nonneg.2 hz26),
          mul_nonneg (mul_nonneg (sub_nonneg.2 hz1) (sub_nonneg.2 hz26)) hz0.le,
          mul_nonneg (mul_nonneg (sub_nonneg.2 hz1) (sub_nonneg.2 hz26)) (sq_nonneg z)]

set_option maxHeartbeats 1000000 in
/-- **[B, Lemma 5.2.3], (5.51)**: if `2α = a/q + O*(1/qQ)`, `q < W/2`, `Q ≥ 3.5W` (and
`W ≥ 50000`, `W/2 ≤ W' ≤ W`),
`∑_{A₀ < m ≤ A₁, m odd} |S(αm)|² ≤ ⌈(A₁ - A₀)/2q⌉ (q/φ(q)) (W/log(W/2q)) ∑ (log p)²`.
The condition `W ≥ 50000` is ours: the number of integers in `(W', W]` is `≤ W/2 + 1`, not `≤ W/2`
as [B] uses, and the slack in [B]'s constants absorbs the `+1` only for `W` large. -/
theorem lemma_5_2_3_b {α Q : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) {W' W : ℝ} (hqW : 2 * q < W) (hQW : 3.5 * W ≤ Q)
    (hW : 50000 ≤ W) (hW'W : W / 2 ≤ W') (hWW : W' ≤ W) (A₀ A₁ : ℝ) :
    oddSqSum α W' W A₀ A₁ ≤
      ⌈(A₁ - A₀) / (2 * q)⌉₊ * (q / Nat.totient q * (W / Real.log (W / (2 * q))) * logSqSum W' W) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have hy1 : 1 < W / (2 * q) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hlog : 0 < Real.log (W / (2 * q)) := Real.log_pos hy1
  have hL := logSqSum_nonneg W' W
  set K₀ := Nat.totient q / q * Real.log (W / (2 * q)) / W
  have hK₀ : 0 < K₀ := by positivity
  have hLK : logSqSum W' W / K₀ = q / Nat.totient q * (W / Real.log (W / (2 * q))) * logSqSum W' W := by
    simp only [K₀]; field_simp
  rcases le_or_gt (13.5 * (q : ℝ)) W with hA | hB
  · obtain ⟨hR2, hRQ, hRW, hK⟩ := weight_caseA (Q := Q) hq hA hQW hW hW'W hWW
    have := odd_blocks_from_weight hq hcop hα (by linarith) hRQ (by linarith) hWW hRW hK₀ hK A₀ A₁
    rwa [hLK] at this
  · rcases Nat.even_or_odd q with hev | hodd
    · -- `q` even: (5.50) is better.
      have h := lemma_5_2_3_a hq hcop hα (by linarith : (q : ℝ) ≤ Q) (by linarith)
        hWW (W' := W') (W := W) A₀ A₁
      have hmin : min (2 * (q : ℝ)) Q = 2 * q := min_eq_left (by linarith)
      rw [hmin] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      refine mul_le_mul_of_nonneg_right ?_ hL
      have hqφ : 2 ≤ (q : ℝ) / Nat.totient q := by
        obtain ⟨m, hm⟩ := hev
        have h2m : q = 2 * m := by omega
        have h1 := totient_two_mul_le m
        rw [← h2m] at h1
        have h3 : (Nat.totient q : ℝ) ≤ m := by exact_mod_cast h1
        have h4 : (q : ℝ) = 2 * m := by exact_mod_cast h2m
        rw [le_div_iff₀ hφ]; linarith
      have hy2 : W / (2 * q) ≤ 6.76 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have hkey := half_add_inv_mul_log_le hy1.le hy2
      -- `W - W' + 2q ≤ W(1/2 + 2q/W) ≤ 2W/log(W/2q) ≤ (q/φ(q)) W/log(W/2q)`.
      have h1 : W - W' + 2 * q ≤ W * (1 / 2 + 1 / (W / (2 * q))) := by
        have : W * (1 / 2 + 1 / (W / (2 * q))) = W / 2 + 2 * q := by field_simp
        linarith
      have h2 : W * (1 / 2 + 1 / (W / (2 * q))) ≤ 2 * W / Real.log (W / (2 * q)) := by
        rw [le_div_iff₀ hlog]; nlinarith
      calc W - W' + 2 * q ≤ 2 * W / Real.log (W / (2 * q)) := h1.trans h2
        _ = 2 * (W / Real.log (W / (2 * q))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hqφ (by positivity)
    · have hK := weight_caseB (Q := Q) hq hodd hB hqW hQW (by linarith) hW'W hWW
      have := odd_blocks_from_weight hq hcop hα (R := 2) (by norm_num) (by nlinarith)
        (by linarith) hWW (by linarith) hK₀ hK A₀ A₁
      rwa [hLK] at this

/-- **[B, (5.54)]**: if `q < W/2` and `Q ≥ 3.5W` (and `W ≥ 50000`, `W/2 ≤ W' ≤ W`, `U' ≥ x/2W`),
`S₂ ≤ (x/(4φ(q) log(W/2q)) + (q/φ(q)) W/log(W/2q)) ∑ (log p)²`. -/
theorem prop_5_2_4_e {α x Q U' W' W : ℝ} {a k : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hcop : IsCoprime a (q : ℤ)) (hα : |2 * α - a / q - k| ≤ 1 / (q * Q)) (hx : 0 < x)
    (hqW : 2 * q < W) (hQW : 3.5 * W ≤ Q) (hW : 50000 ≤ W) (hW'W : W / 2 ≤ W') (hWW : W' ≤ W)
    (hU' : x / (2 * W) ≤ U') :
    S2 α x U' W' W ≤ (x / (4 * Nat.totient q * Real.log (W / (2 * q))) +
      q / Nat.totient q * (W / Real.log (W / (2 * q)))) * logSqSum W' W := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hW0 : 0 < W := by linarith
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have hy1 : 1 < W / (2 * q) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hlog : 0 < Real.log (W / (2 * q)) := Real.log_pos hy1
  have hL := logSqSum_nonneg W' W
  have h := lemma_5_2_3_b hq hcop hα hqW hQW hW hW'W hWW U' (x / W)
  rw [S2]
  refine h.trans ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hL
  set D := x / W - U'
  have hD : D ≤ x / (2 * W) := by
    simp only [D]; have : x / W - x / (2 * W) = x / (2 * W) := by field_simp; ring
    linarith
  have hJ : (⌈D / (2 * q)⌉₊ : ℝ) ≤ x / (4 * W * q) + 1 := by
    rcases le_or_gt D 0 with hD0 | hD0
    · rw [Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg hD0 (by positivity))]
      push_cast; positivity
    · have := (Nat.ceil_lt_add_one (show 0 ≤ D / (2 * q) by positivity)).le
      have : D / (2 * q) ≤ x / (4 * W * q) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 := mul_le_mul_of_nonneg_right hD (show (0 : ℝ) ≤ 4 * W * q by positivity)
        have h2 : x / (2 * W) * (4 * W * q) = x * (2 * q) := by field_simp; ring
        linarith
      linarith
  calc (⌈D / (2 * q)⌉₊ : ℝ) * (q / Nat.totient q * (W / Real.log (W / (2 * q))))
      ≤ (x / (4 * W * q) + 1) * (q / Nat.totient q * (W / Real.log (W / (2 * q)))) :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = _ := by field_simp

end TernaryGoldbach.MinorArcs
