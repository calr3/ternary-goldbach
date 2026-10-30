import TernaryGoldbach.CircleMethod

/-!
# Plancherel for absolutely convergent exponential series

`∫₀¹ |Σ aₙ e(nα)|² dα = Σ |aₙ|²` for `(aₙ) ∈ ℓ¹` (`setIntegral_norm_sq_expTsum`), from the finite
case (`setIntegral_norm_sq_expSum`) by dominated convergence.

Proved, with no `sorry`.
-/

open MeasureTheory Filter Topology Finset

namespace TernaryGoldbach

theorem summable_norm_sq_of_summable_norm {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) :
    Summable fun n => ‖a n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (ha.mul_left (∑' m, ‖a m‖))
  rw [sq]
  exact mul_le_mul_of_nonneg_right (ha.le_tsum n fun m _ => norm_nonneg (a m)) (norm_nonneg _)

theorem norm_expSum_le (X : ℕ) {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) (α : ℝ) :
    ‖expSum X a α‖ ≤ ∑' n, ‖a n‖ := by
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul_e]
  exact ha.sum_le_tsum _ fun n _ => norm_nonneg _

/-- **Plancherel** for `ℓ¹` coefficients. -/
theorem setIntegral_norm_sq_expTsum {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) :
    ∫ α in Set.Ioc (0:ℝ) 1, ‖expTsum a α‖ ^ 2 = ∑' n, ‖a n‖ ^ 2 := by
  set B := ∑' n, ‖a n‖
  -- pointwise convergence of the partial sums
  have hpt : ∀ α : ℝ, Tendsto (fun X : ℕ => ‖expSum X a α‖ ^ 2) atTop (𝓝 (‖expTsum a α‖ ^ 2)) := by
    intro α
    have hs : Summable fun n => a n * e (n * α) :=
      Summable.of_norm (by simpa only [norm_mul_e] using ha)
    have := (hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    exact ((continuous_norm.pow 2).tendsto _).comp this
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
    (F := fun (X : ℕ) (α : ℝ) => ‖expSum X a α‖ ^ 2) (f := fun α => ‖expTsum a α‖ ^ 2)
    (fun _ => B ^ 2)
    (fun X => ((continuous_expSum X a).norm.pow 2).aestronglyMeasurable)
    (integrable_const _)
    (fun X => Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖expSum X a α‖ ^ 2)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_expSum_le X ha α) 2)
    (Eventually.of_forall hpt)
  have hfun : (fun X : ℕ => ∫ α in Set.Ioc (0:ℝ) 1, ‖expSum X a α‖ ^ 2) =
      fun X => ∑ n ∈ range (X + 1), ‖a n‖ ^ 2 := funext fun X => setIntegral_norm_sq_expSum X a
  rw [hfun] at hlim
  have h2 := (summable_norm_sq_of_summable_norm ha).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hlim h2

end TernaryGoldbach
