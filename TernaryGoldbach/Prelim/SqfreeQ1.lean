import TernaryGoldbach.Prelim.SqfreeWalk

/-!
# `0.578 ≤ Q₁(t) − κ log t ≤ 1.166` for all `t ≥ 1`

On `[1, 10⁴)` from the kernel walk (`goodQ_small`); beyond, by summation by parts against
`Q(n) = κ n + R(n)`, `|R(n)| ≤ 3√n` (`Q_sub_le`): `|E(N) − E(10⁴)| ≤ κ/10⁴ + 12/100` for integers `N ≥ 10⁴`,
where `E(t) = Q₁(t) − κ log t`. Consequence: `Q₁(B) − Q₁(A) ≤ κ log(B/A) + 0.588` (`Q1_diff_le`).
-/

open Finset

namespace TernaryGoldbach.Prelim.Sqf
open TernaryGoldbach.Prelim.SmallE (S S_pos)

/-- `E(t) = Q₁(t) − κ log t`. -/
noncomputable def Eq1 (t : ℝ) : ℝ := Q1 t - kap * Real.log t

/-- `H(N) = ∑_{n ≤ N} 1/n`. -/
noncomputable def Hn (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (1 : ℝ) / n

/-- `R(n) = Q(n) − κ n`. -/
noncomputable def Rn (n : ℕ) : ℝ := Qs n - kap * n

/-- Summation by parts: `Q₁(N) = Q(N)/N + ∑_{n < N} Q(n)/(n(n+1))`, so
`Q₁(N) = κ H(N) + R(N)/N + ∑_{n < N} R(n)/(n(n+1))`. -/
theorem Q1_abel : ∀ N : ℕ, 1 ≤ N →
    Q1 N = kap * Hn N + Rn N / N + ∑ n ∈ Ico 1 N, Rn n / ((n : ℝ) * (n + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    have : Q1 ((1 : ℕ) : ℝ) = 1 := Q1_one
    simp only [Nat.cast_one] at this
    simp [this, Hn, Rn, Qs, Finset.filter_singleton, squarefree_one]
  | succ N hN ih =>
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hH : Hn (N + 1) = Hn N + 1 / ((N : ℝ) + 1) := by
      unfold Hn; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring
    have hR : Rn (N + 1) = Rn N + sq (N + 1) - kap := by
      unfold Rn; rw [Qs_nat_succ]; push_cast; ring
    rw [Q1_nat_succ, ih, hH, hR, Finset.sum_Ico_succ_top hN]
    push_cast
    field_simp
    ring

/-- `0 ≤ γ(T) − γ(N) ≤ 1/T` for `γ(n) = H(n) − log n`, `1 ≤ T ≤ N`. -/
theorem gam_diff {T : ℕ} (hT : 1 ≤ T) : ∀ N, T ≤ N →
    0 ≤ (Hn T - Real.log T) - (Hn N - Real.log N) ∧
      (Hn T - Real.log T) - (Hn N - Real.log N) ≤ 1 / T - 1 / N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (le_trans hT hN)
    have hH : Hn (N + 1) = Hn N + 1 / ((N : ℝ) + 1) := by
      unfold Hn; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring
    rw [hH]
    have l1 := Real.add_one_le_exp ((1 : ℝ) / N)
    have hl : Real.log ((N : ℝ) + 1) - Real.log N = Real.log (1 + 1 / N) := by
      rw [← Real.log_div (by positivity) hN0.ne']; congr 1; field_simp
    have hu : Real.log (1 + 1 / (N : ℝ)) ≤ 1 / N := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity); linarith
    have hlow : 1 / ((N : ℝ) + 1) ≤ Real.log (1 + 1 / (N : ℝ)) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
      have e : 1 - (1 + 1 / (N : ℝ))⁻¹ = 1 / ((N : ℝ) + 1) := by field_simp; ring
      linarith
    push_cast
    have e2 : 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) = 1 / ((N : ℝ) * (N + 1)) := by field_simp; ring
    constructor <;> nlinarith [ih.1, ih.2]

theorem Rn_le {n : ℕ} (hn : 1 ≤ n) : |Rn n| ≤ 3 * √(n : ℝ) := by
  have := Q_sub_le (x := n) (by exact_mod_cast hn); unfold Rn; exact this

/-- `∑_{T ≤ n < N} 3√n/(n(n+1)) ≤ 6/√T`, from `1/(√n (n+1)) ≤ 2/√n − 2/√(n+1)`. -/
theorem sum_R_tail {T : ℕ} (hT : 1 ≤ T) : ∀ N, T ≤ N →
    |∑ n ∈ Ico T N, Rn n / ((n : ℝ) * (n + 1))| ≤ 6 / √(T : ℝ) - 6 / √(N : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (le_trans hT hN)
    have hR := Rn_le (le_trans hT hN)
    have s0 : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN0
    have s1 : 0 < √((N : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
    have hss : √(N : ℝ) ≤ √((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have e0 := Real.mul_self_sqrt hN0.le
    have e1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ N + 1 by linarith)
    -- `3√N/(N(N+1)) ≤ 6/√N − 6/√(N+1)`
    have key : 3 * √(N : ℝ) / ((N : ℝ) * (N + 1)) ≤ 6 / √(N : ℝ) - 6 / √((N : ℝ) + 1) := by
      set b := √(N : ℝ)
      set c := √((N : ℝ) + 1)
      have hab : 2 * (c * b) ≤ b * b + c * c := by nlinarith [pow_two_nonneg (c - b)]
      have h21 : 0 ≤ 2 * c * c - 2 * c * b - 1 := by nlinarith
      have key' : 3 * b / ((b * b) * (c * c)) ≤ 6 / b - 6 / c := by
        rw [div_sub_div _ _ s0.ne' s1.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        have hp : 0 ≤ b * b * c * (2 * c * c - 2 * c * b - 1) := by positivity
        nlinarith [hp]
      rw [e0, e1] at key'
      exact key'
    have hdpos : (0 : ℝ) < (N : ℝ) * (N + 1) := mul_pos hN0 (by linarith)
    have hterm : |Rn N / ((N : ℝ) * (N + 1))| ≤ 3 * √(N : ℝ) / ((N : ℝ) * (N + 1)) := by
      rw [abs_div, abs_of_pos hdpos]; exact div_le_div_of_nonneg_right hR hdpos.le
    push_cast
    calc |∑ n ∈ Ico T N, Rn n / ((n : ℝ) * (n + 1)) + Rn N / ((N : ℝ) * (N + 1))|
        ≤ |∑ n ∈ Ico T N, Rn n / ((n : ℝ) * (n + 1))| + |Rn N / ((N : ℝ) * (N + 1))| := abs_add_le _ _
      _ ≤ 6 / √(T : ℝ) - 6 / √(N : ℝ) + (6 / √(N : ℝ) - 6 / √((N : ℝ) + 1)) := by linarith
      _ = 6 / √(T : ℝ) - 6 / √((N : ℝ) + 1) := by ring

/-- `|E(N) − E(T)| ≤ κ/T + 12/√T` for integers `1 ≤ T ≤ N`. -/
theorem Eq1_nat_diff {T N : ℕ} (hT : 1 ≤ T) (hTN : T ≤ N) :
    |Eq1 N - Eq1 T| ≤ kap / T + 12 / √(T : ℝ) := by
  have hN : 1 ≤ N := le_trans hT hTN
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have eN := Q1_abel N hN
  have eT := Q1_abel T hT
  have hsplit : ∑ n ∈ Ico 1 N, Rn n / ((n : ℝ) * (n + 1)) =
      ∑ n ∈ Ico 1 T, Rn n / ((n : ℝ) * (n + 1)) + ∑ n ∈ Ico T N, Rn n / ((n : ℝ) * (n + 1)) :=
    (Finset.sum_Ico_consecutive _ hT hTN).symm
  have hg := gam_diff hT N hTN
  have htail := sum_R_tail hT N hTN
  have hRN := Rn_le hN
  have hRT := Rn_le hT
  have sT : 0 < √(T : ℝ) := Real.sqrt_pos.2 hT0
  have sN : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN0
  have hsTN : √(T : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hTN)
  have dN : |Rn N / N| ≤ 3 / √(T : ℝ) := by
    rw [abs_div, abs_of_pos hN0, div_le_div_iff₀ hN0 sT]
    have e := Real.mul_self_sqrt hN0.le
    nlinarith [abs_nonneg (Rn N)]
  have dT : |Rn T / T| ≤ 3 / √(T : ℝ) := by
    rw [abs_div, abs_of_pos hT0, div_le_div_iff₀ hT0 sT]
    have e := Real.mul_self_sqrt hT0.le
    nlinarith [abs_nonneg (Rn T)]
  have hk := kap_pos
  have hkg : |kap * ((Hn N - Real.log N) - (Hn T - Real.log T))| ≤ kap / T := by
    rw [abs_mul, abs_of_pos hk, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    rw [abs_le]; constructor <;> nlinarith [hg.1, hg.2, show (0 : ℝ) ≤ 1 / N by positivity]
  have e : Eq1 N - Eq1 T = kap * ((Hn N - Real.log N) - (Hn T - Real.log T)) + Rn N / N - Rn T / T +
      ∑ n ∈ Ico T N, Rn n / ((n : ℝ) * (n + 1)) := by
    unfold Eq1; rw [eN, eT, hsplit]; ring
  rw [e]
  have h6 : 6 / √(T : ℝ) - 6 / √(N : ℝ) ≤ 6 / √(T : ℝ) := by
    have : 0 ≤ 6 / √(N : ℝ) := by positivity
    linarith
  calc |kap * ((Hn N - Real.log N) - (Hn T - Real.log T)) + Rn N / N - Rn T / T +
        ∑ n ∈ Ico T N, Rn n / ((n : ℝ) * (n + 1))|
      ≤ |kap * ((Hn N - Real.log N) - (Hn T - Real.log T))| + |Rn N / N| + |Rn T / T| +
        |∑ n ∈ Ico T N, Rn n / ((n : ℝ) * (n + 1))| := by
        have := abs_add_le (kap * ((Hn N - Real.log N) - (Hn T - Real.log T)) + Rn N / N - Rn T / T)
          (∑ n ∈ Ico T N, Rn n / ((n : ℝ) * (n + 1)))
        have := abs_sub (kap * ((Hn N - Real.log N) - (Hn T - Real.log T)) + Rn N / N) (Rn T / T)
        have := abs_add_le (kap * ((Hn N - Real.log N) - (Hn T - Real.log T))) (Rn N / N)
        linarith
    _ ≤ kap / T + 3 / √(T : ℝ) + 3 / √(T : ℝ) + 6 / √(T : ℝ) := by linarith
    _ = kap / T + 12 / √(T : ℝ) := by ring

/-- **`0.578 ≤ Q₁(t) − κ log t ≤ 1.166`** for `t ≥ 1`. -/
theorem Eq1_bounds {t : ℝ} (ht : 1 ≤ t) : 0.578 ≤ Eq1 t ∧ Eq1 t ≤ 1.166 := by
  set n := ⌊t⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa using ht)
  have h1 : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
  have h2 : t < n + 1 := Nat.lt_floor_add_one t
  obtain ⟨hsmall, hI⟩ := goodQ_small
  rcases lt_or_ge n 10000 with hlt | hge
  · exact hsmall n hn1 hlt t h1 h2
  · -- `E(10⁴)` from the final state of the walk
    obtain ⟨q1, q2, g1, g2⟩ := hI
    obtain ⟨k1, k2⟩ := kap_bounds
    have hSv : (S : ℝ) = 1000000000000 := by norm_num [S]
    rw [hSv] at q1 q2 g1 g2 k1 k2
    push_cast at q1 q2 g1 g2
    have hlog0 : (0 : ℝ) ≤ Real.log ((10000 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
    have hk0' := kap_pos
    have a1 : kap * Real.log ((10000 : ℕ) : ℝ) ≤ (607927101855 / 1000000000000) * (9211204671764 / 1000000000000) :=
      mul_le_mul (by simpa [kHi] using k2) (by simpa using g2) hlog0 (by norm_num)
    have a2 : (607927101854 / 1000000000000) * (9210273822826 / 1000000000000) ≤ kap * Real.log ((10000 : ℕ) : ℝ) :=
      mul_le_mul (by simpa [kLo] using k1) (by simpa using g1) (by norm_num) hk0'.le
    have hET : 1.0436 ≤ Eq1 ((10000 : ℕ) : ℝ) ∧ Eq1 ((10000 : ℕ) : ℝ) ≤ 1.0443 := by
      unfold Eq1
      push_cast at q1 q2 a1 a2 ⊢
      norm_num at q1 q2 a1 a2 ⊢
      constructor <;> linarith
    have hdiff := Eq1_nat_diff (T := 10000) (N := n) (by norm_num) hge
    have hsq : √((10000 : ℕ) : ℝ) = 100 := by
      rw [show ((10000 : ℕ) : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsq] at hdiff
    have hk1 := kap_le_one
    have hd : |Eq1 n - Eq1 ((10000 : ℕ) : ℝ)| ≤ 0.1201 := by
      refine hdiff.trans ?_
      have : kap / ((10000 : ℕ) : ℝ) ≤ 0.0001 := by
        rw [div_le_iff₀ (by norm_num)]; push_cast; linarith
      linarith
    rw [abs_le] at hd
    -- from `n` to `t`
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have ht0 : 0 < t := by linarith
    have hQ : Q1 t = Q1 n := Q1_const h1 h2
    have hl1 : Real.log n ≤ Real.log t := Real.log_le_log hn0 h1
    have hl2 : Real.log t - Real.log n ≤ 1 / 10000 := by
      rw [← Real.log_div ht0.ne' hn0.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < t / n by positivity)
      have hn' : (10000 : ℝ) ≤ n := by exact_mod_cast hge
      have : t / n - 1 ≤ 1 / 10000 := by
        rw [div_sub_one hn0.ne', div_le_div_iff₀ hn0 (by norm_num)]; nlinarith
      linarith
    have hk0 := kap_pos
    unfold Eq1 at hd ⊢
    rw [hQ]
    constructor <;> nlinarith

/-- **`∑_{A < j ≤ B} μ²(j)/j ≤ κ log(B/A) + 0.588`** for `1 ≤ A ≤ B`. -/
theorem Q1_diff_le {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) : Q1 B - Q1 A ≤ kap * Real.log (B / A) + 0.588 := by
  obtain ⟨a1, -⟩ := Eq1_bounds hA
  obtain ⟨-, b2⟩ := Eq1_bounds (le_trans hA hAB)
  unfold Eq1 at a1 b2
  rw [Real.log_div (by linarith) (by linarith)]
  linarith

end TernaryGoldbach.Prelim.Sqf
