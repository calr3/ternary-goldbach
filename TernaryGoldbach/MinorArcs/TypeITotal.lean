import TernaryGoldbach.MinorArcs.TypeILogProof
import TernaryGoldbach.MinorArcs.Eta2LogFourier
import TernaryGoldbach.Prelim.LambdaMu
import TernaryGoldbach.Prelim.MoebiusLog
import TernaryGoldbach.Prelim.LiouvilleBound

/-!
# Type I totals [B, §6.2.1]: `S_{I,1}`
-/

open Real Finset
open ArithmeticFunction (moebius)
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- The bound on `|∑_{m ≤ U/q, (m,2q)=1} μ(m)/m|` from (2.20), (2.22):
`min(1, 2.8(2q/φ(2q))/log(U/2q²))` (the second only if `2q² < U`; [B] has `4/5` from [Ramb], we prove
`2.8` in `Prelim/LiouvilleBound.lean`). -/
noncomputable def muBound (U : ℝ) (q : ℕ) : ℝ :=
  if 2 * (q : ℝ) ^ 2 < U then
    min 1 (2.8 * (2 * q / Nat.totient (2 * q)) / Real.log (U / (2 * q ^ 2))) else 1

/-- The bound on `|(log·η₂)^(-δ/2)|` from (B.17), (B.18): `min(2 - log 4, 96 log 2/(πδ)²)`. -/
noncomputable def logFourierBound (δ : ℝ) : ℝ :=
  if δ = 0 then 2 - Real.log 4 else min (2 - Real.log 4) (96 * Real.log 2 / (π * δ) ^ 2)

theorem abs_muSum_one_le {U : ℝ} {q : ℕ} (hq : 1 ≤ q) (hU : 0 < U) :
    |muSum U q (2 * q) fun _ => 1| ≤ muBound U q := by
  have h2q : 1 ≤ 2 * q := by omega
  have h1 : |muSum U q (2 * q) fun _ => 1| ≤ 1 := by
    have := Prelim.abs_sum_moebius_div_coprime_le_one (U / q) h2q
    simpa [muSum] using this
  unfold muBound
  split_ifs with h
  · refine le_min h1 ?_
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have h2 : ((2 * q : ℕ) : ℝ) < U / q := by
      push_cast; rw [lt_div_iff₀ hq0]; nlinarith
    have := Prelim.abs_sum_moebius_div_coprime_le_log h2q h2
    have e1 : (muSum U q (2 * q) fun _ => 1) =
        ∑ n ∈ Icc 1 ⌊U / q⌋₊, (if Nat.Coprime n (2 * q) then (μ n : ℝ) / n else 0) := by
      simp [muSum]
    have e2 : U / q / ((2 * q : ℕ) : ℝ) = U / (2 * q ^ 2) := by push_cast; field_simp
    rw [e1]; refine this.trans (le_of_eq ?_)
    rw [e2]; push_cast; ring
  · exact h1

theorem abs_muSum_log_le {x U : ℝ} {q : ℕ} (hq : 1 ≤ q) (hU : 0 < U) (hUx : U ≤ x) :
    |muSum U q (2 * q) fun m => Real.log (x / (m * q))| ≤
      (2 * q / Nat.totient (2 * q) + 2.67) + Real.log (x / U) * muBound U q := by
  have h2q : 1 ≤ 2 * q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsplit : (muSum U q (2 * q) fun m => Real.log (x / (m * q))) =
      (∑ n ∈ Icc 1 ⌊U / q⌋₊, if Nat.Coprime n (2 * q) then (μ n : ℝ) / n * Real.log (U / q / n)
        else 0) + Real.log (x / U) * muSum U q (2 * q) (fun _ => 1) := by
    unfold muSum
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.1 hm).1
    split_ifs
    · dsimp only
      have hx0 : 0 < x := lt_of_lt_of_le hU hUx
      rw [show x / (m * q) = (U / q / m) * (x / U) by field_simp,
        Real.log_mul (by positivity) (by positivity)]
      ring
    · ring
  rw [hsplit]
  have h1 := Prelim.abs_sum_moebius_div_log_coprime_le (x := U / q) (by positivity) h2q
  have h2 := abs_muSum_one_le hq hU
  have hl : 0 ≤ Real.log (x / U) := Real.log_nonneg (by rw [le_div_iff₀ hU]; linarith)
  push_cast at h1
  refine (abs_add_le _ _).trans (add_le_add h1 ?_)
  rw [abs_mul, abs_of_nonneg hl]
  exact mul_le_mul_of_nonneg_left h2 hl

theorem norm_fourier_logeta2_half_le (δ : ℝ) :
    ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ ≤ logFourierBound δ := by
  unfold logFourierBound
  split_ifs with h
  · exact norm_fourier_logeta2_le _
  · refine le_min (norm_fourier_logeta2_le _) ?_
    have hd := norm_fourier_logeta2_le_decay (-(δ / 2))
    have hp : 0 < (π * δ) ^ 2 := by have := Real.pi_pos; positivity
    rw [le_div_iff₀ hp]
    calc ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ * (π * δ) ^ 2
        = (2 * π * -(δ / 2)) ^ 2 * ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ := by ring
      _ ≤ _ := hd

/-- **[B, §6.2.1]**, our version of (6.3)/(6.4): for `U ≤ Q₀/2`,
`|S_{I,1}| ≤ (x/2q) min(1, c₀/(πδ)²) (2q/φ(2q) + 2.67 + log(x/U) μ_U)` ([B]: `1.00303 (2q/φ(2q))`)
`+ (x/2q) min(2 - log 4, 96 log 2/(πδ)²) μ_U + c₀(1/2 - 2/π²)(U²/(4qx) log(√e x/U) + 1/e)`
`+ (4.41)`, with `μ_U = min(1, 2.8(2q/φ(2q))/log(U/2q²))`. -/
theorem typeI1_le {α x δ Q₀ U : ℝ} {a : ℤ} {q : ℕ} (h : Approx2 α x δ a q Q₀)
    (hU : √3 ≤ U) (hUx : U ≤ min (x / 4) (x / rexp 1)) (hUQ : U ≤ Q₀ / 2) :
    ‖typeILog α x U‖ ≤
      x / (2 * q) * minInv c₀ (π * δ) *
          ((2 * q / Nat.totient (2 * q) + 2.67) + Real.log (x / U) * muBound U q) +
        x / (2 * q) * logFourierBound δ * muBound U q +
        c₀ * (1 / 2 - 2 / π ^ 2) * (U ^ 2 / (4 * q * x) * Real.log (rexp (1 / 2) * x / U) +
          1 / rexp 1) +
        bound_4_41 x q U := by
  have hle := lemma_4_2_3 h hU hUx (Or.inr hUQ)
  obtain ⟨hq, -, -, hδQ₀, hqQ₀⟩ := h
  have hU0 : 0 < U := lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) hU
  have hx : 0 < x := by have := hUx.trans (min_le_left _ _); linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- `M = U`.
  have hM : Mof x δ q U = U := by
    unfold Mof
    split_ifs with hδ
    · rfl
    · refine min_eq_right ?_
      have hδp : 0 < |δ| := abs_pos.2 hδ
      have hQ0 : 0 < Q₀ := lt_of_lt_of_le hq0 hqQ₀
      have hQ₀ : Q₀ ≤ x / (|δ| * q) := by
        rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity)] at hδQ₀
        rw [le_div_iff₀ (by positivity)]; nlinarith
      linarith
  refine hle.trans ?_
  unfold bound_4_40
  rw [hM]
  have hUx' : U ≤ x := by have := hUx.trans (min_le_left _ _); linarith
  have hmi : 0 ≤ minInv c₀ (π * δ) := by
    unfold minInv; split_ifs
    · norm_num
    · exact le_min zero_le_one (div_nonneg (by norm_num [c₀]) (sq_nonneg _))
  have hA := abs_muSum_log_le (x := x) hq hU0 hUx'
  have hB := abs_muSum_one_le hq hU0
  have hF := norm_fourier_logeta2_half_le δ
  have hc : 0 ≤ x / (2 * q) := by positivity
  have hmb : 0 ≤ muBound U q := (abs_nonneg _).trans hB
  have h1 : x / (2 * q) * minInv c₀ (π * δ) *
      |muSum U q (2 * q) fun m => Real.log (x / (m * q))| ≤ x / (2 * q) * minInv c₀ (π * δ) *
        ((2 * q / Nat.totient (2 * q) + 2.67) + Real.log (x / U) * muBound U q) :=
    mul_le_mul_of_nonneg_left hA (mul_nonneg hc hmi)
  have h2 : x / (2 * q) * ‖fourier (fun t => Real.log t * eta2 t) (-(δ / 2))‖ *
      |muSum U q (2 * q) fun _ => 1| ≤ x / (2 * q) * logFourierBound δ * muBound U q :=
    mul_le_mul (mul_le_mul_of_nonneg_left hF hc) hB (abs_nonneg _)
      (mul_nonneg hc ((norm_nonneg _).trans hF))
  linarith

end TernaryGoldbach.MinorArcs
