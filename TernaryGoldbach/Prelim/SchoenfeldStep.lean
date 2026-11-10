import TernaryGoldbach.Prelim.ElMarraki
import TernaryGoldbach.Prelim.SqfreeQ1
import TernaryGoldbach.Prelim.WeightsWalk

/-!
# One step of Schoenfeld's induction

`N_abs_le`: from Schoenfeld's identity, for `1 ≤ Y ≤ D`,
`|N(D)| ≤ |M(D)| + 1 + ∑_{1 < k ≤ Y} a_k |M(D/k)| + ∑_{m ≤ D/(Y+1)} μ²(m) |ρ(D/m)| + |ρ(Y)| |M(D/(Y+1))|`,
`a_k = |Λ(k) − 1|`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sch
open TernaryGoldbach.Prelim.Wts (aw)
open TernaryGoldbach.Prelim.Sqf (sq)

theorem abs_mu_eq_sq (m : ℕ) : |(μ m : ℝ)| = sq m := by
  unfold sq
  by_cases h : Squarefree m
  · rw [if_pos h, ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast; rw [abs_pow, abs_neg, abs_one, one_pow]
  · rw [if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp

theorem N_abs_le {D Y : ℕ} (hY1 : 1 ≤ Y) (hYD : Y ≤ D) :
    |Nn D| ≤ |Mn D| + 1 + ∑ k ∈ Ioc 1 Y, aw k * |Mn (D / k)| +
      ∑ m ∈ Ioc 0 (D / (Y + 1)), sq m * |ρn (D / m)| + |ρn Y| * |Mn (D / (Y + 1))| := by
  have h := schoenfeld_identity hY1 hYD
  have e : Nn D = Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k) -
      ∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m) + ρn Y * Mn (D / (Y + 1)) - 1 := by linarith
  rw [e]
  have h1 : |∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k)| ≤
      ∑ k ∈ Ioc 1 Y, aw k * |Mn (D / k)| :=
    (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k _ => by rw [abs_mul]; rfl))
  have h2 : |∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m)| ≤
      ∑ m ∈ Ioc 0 (D / (Y + 1)), sq m * |ρn (D / m)| :=
    (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun m _ => by rw [abs_mul, abs_mu_eq_sq]))
  have h3 : |ρn Y * Mn (D / (Y + 1))| = |ρn Y| * |Mn (D / (Y + 1))| := abs_mul _ _
  calc |Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k) -
        ∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m) + ρn Y * Mn (D / (Y + 1)) - 1|
      ≤ |Mn D| + |∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k)| +
        |∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m)| + |ρn Y * Mn (D / (Y + 1))| + 1 := by
        have := abs_sub (Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k) -
          ∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m) + ρn Y * Mn (D / (Y + 1))) 1
        have := abs_add_le (Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k) -
          ∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m)) (ρn Y * Mn (D / (Y + 1)))
        have := abs_sub (Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k))
          (∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m))
        have := abs_sub (Mn D) (∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k))
        simp only [abs_one] at *
        linarith
    _ ≤ _ := by rw [h3]; linarith

/-! ### The `k`-sum, block by block -/

open TernaryGoldbach.Prelim.Wts (Gw Hw)

theorem Gw_sub {α β : ℕ} (hα : 1 ≤ α) (hαβ : α ≤ β) :
    Gw β - Gw α = ∑ k ∈ Ioc α β, aw k / k := by
  unfold Gw
  rw [show Icc 2 β = Ioc 1 β by ext; simp; omega, show Icc 2 α = Ioc 1 α by ext; simp; omega,
    ← Finset.sum_Ioc_consecutive _ hα hαβ]; ring

theorem Hw_sub {α β : ℕ} (hα : 1 ≤ α) (hαβ : α ≤ β) :
    Hw β - Hw α = ∑ k ∈ Ioc α β, aw k / √(k : ℝ) := by
  unfold Hw
  rw [show Icc 2 β = Ioc 1 β by ext; simp; omega, show Icc 2 α = Ioc 1 α by ext; simp; omega,
    ← Finset.sum_Ioc_consecutive _ hα hαβ]; ring

theorem aw_nonneg (k : ℕ) : 0 ≤ aw k := abs_nonneg _

/-- One block `α < k ≤ β`, with `|M(u)| ≤ c √u + η u` at `u = D/k`. -/
theorem Ksum_block {D α β : ℕ} {c η : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η) (hα : 1 ≤ α) (hαβ : α ≤ β)
    (hM : ∀ k ∈ Ioc α β, |Mn (D / k)| ≤ c * √((D / k : ℕ) : ℝ) + η * ((D / k : ℕ) : ℝ)) :
    ∑ k ∈ Ioc α β, aw k * |Mn (D / k)| ≤ c * √(D : ℝ) * (Hw β - Hw α) + η * D * (Gw β - Gw α) := by
  rw [Hw_sub hα hαβ, Gw_sub hα hαβ, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by have := (mem_Ioc.1 hk).1; omega : 0 < k)
  have hu : ((D / k : ℕ) : ℝ) ≤ (D : ℝ) / k := Nat.cast_div_le
  have hsu : √((D / k : ℕ) : ℝ) ≤ √(D : ℝ) / √(k : ℝ) := by
    rw [← Real.sqrt_div' _ hk0.le]; exact Real.sqrt_le_sqrt hu
  have ha := aw_nonneg k
  calc aw k * |Mn (D / k)| ≤ aw k * (c * √((D / k : ℕ) : ℝ) + η * ((D / k : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hM k hk) ha
    _ ≤ aw k * (c * (√(D : ℝ) / √(k : ℝ)) + η * ((D : ℝ) / k)) := by
        gcongr
    _ = c * √(D : ℝ) * (aw k / √(k : ℝ)) + η * D * (aw k / k) := by ring

/-- The blocks `(β, c, η)` from `α`: the bound `∑ c √D (H(β) − H(α)) + η D (G(β) − G(α))`. -/
noncomputable def Kbd (D : ℕ) : ℕ → List (ℕ × ℝ × ℝ) → ℝ
  | _, [] => 0
  | α, (β, c, η) :: bs => c * √(D : ℝ) * (Hw β - Hw α) + η * D * (Gw β - Gw α) + Kbd D β bs

def lastB : ℕ → List (ℕ × ℝ × ℝ) → ℕ
  | α, [] => α
  | _, (β, _, _) :: bs => lastB β bs

/-- The hypotheses of the blocks. -/
def KOK (D : ℕ) : ℕ → List (ℕ × ℝ × ℝ) → Prop
  | _, [] => True
  | α, (β, c, η) :: bs => α ≤ β ∧ 0 ≤ c ∧ 0 ≤ η ∧
      (∀ k ∈ Ioc α β, |Mn (D / k)| ≤ c * √((D / k : ℕ) : ℝ) + η * ((D / k : ℕ) : ℝ)) ∧ KOK D β bs

theorem lastB_ge (D : ℕ) : ∀ (bs : List (ℕ × ℝ × ℝ)) (α : ℕ), KOK D α bs → α ≤ lastB α bs
  | [], α, _ => le_rfl
  | (β, c, η) :: bs, α, ⟨h, _, _, _, hr⟩ => le_trans h (lastB_ge D bs β hr)

theorem Ksum_le (D : ℕ) : ∀ (bs : List (ℕ × ℝ × ℝ)) (α : ℕ), 1 ≤ α → KOK D α bs →
    ∑ k ∈ Ioc α (lastB α bs), aw k * |Mn (D / k)| ≤ Kbd D α bs
  | [], α, _, _ => by simp [lastB, Kbd]
  | (β, c, η) :: bs, α, hα, ⟨hαβ, hc, hη, hM, hrest⟩ => by
    have ih := Ksum_le D bs β (le_trans hα hαβ) hrest
    have hlast : β ≤ lastB β bs := lastB_ge D bs β hrest
    simp only [lastB, Kbd]
    rw [← Finset.sum_Ioc_consecutive _ hαβ hlast]
    have hb := Ksum_block hc hη hα hαβ hM
    linarith

end TernaryGoldbach.Prelim.Sch
