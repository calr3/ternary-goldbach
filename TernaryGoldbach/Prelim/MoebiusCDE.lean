import TernaryGoldbach.Prelim.EOneNum
import TernaryGoldbach.Prelim.MoebiusDecay

/-!
# `∑_{n ≤ x} μ(n)/n` from `|M(x)| ≤ x/4345`: the splitting

With `E(u) = E₁Λ(u) + γ` and `m(x) = ∑_{n ≤ x} μ(n)/n`, `mlog_identity` (with `c = −γ`) gives
`m(x)(log x − γ) = −∑_{n ≤ x} μ(n)/n · E(x/n)`. Split at `n = D`:
* `n ≤ D`: `∑ |E(x/n)|/n` (`identity_split`);
* `n > D`: summation by parts against `M(n) = ∑_{k ≤ n} μ(k)` (`abel_mu`). With
  `|M(n)| ≤ β(n) n` and `|E(x/n)| ≤ F`, the part is at most
  `β(N)F + β(D)F + ∑_{D<n<N} β(n)(J(n) + log(1 + 1/n) + F/(n+1))`, where
  `J(n) = ∑_{x/(n+1) < k ≤ x/n} Λ(k)/k` (`tail_bound`).
-/

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens

/-- `M(k) = ∑_{n ≤ k} μ(n)`. -/
noncomputable def Mt (k : ℕ) : ℝ := ∑ n ∈ Icc 1 k, (μ n : ℝ)

theorem Mt_succ (k : ℕ) : Mt (k + 1) = Mt k + μ (k + 1) := by
  rw [Mt, sum_Icc_succ_top (by omega), Mt]

/-- Summation by parts against `M`. -/
theorem abel_mu (w : ℕ → ℝ) (D N : ℕ) (hDN : D < N) :
    ∑ n ∈ Ioc D N, (μ n : ℝ) * w n = Mt N * w N - Mt D * w (D + 1) +
      ∑ n ∈ Ioo D N, Mt n * (w n - w (n + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_or_ge D N with h | h
    · rw [Finset.sum_Ioc_succ_top (by omega), ih h, Mt_succ,
        show Ioo D (N + 1) = insert N (Ioo D N) by ext x; simp; omega,
        sum_insert (by simp)]
      ring
    · have hN : N = D := by omega
      subst hN
      rw [show Ioc N (N + 1) = {N + 1} by ext x; simp only [mem_Ioc, mem_singleton]; omega,
        show Ioo N (N + 1) = ∅ by ext x; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega,
        sum_singleton, sum_empty, Mt_succ]
      ring

/-- `E(u) = E₁Λ(u) + γ`. -/
noncomputable def Eg (u : ℝ) : ℝ := E₁Λ u + Real.eulerMascheroniConstant

/-- `m(x) = ∑_{n ≤ x} μ(n)/n`. -/
noncomputable def mx (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n

theorem abs_mu_le (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  exact_mod_cast h

theorem log_sub_gamma_pos {x : ℝ} (hx : 2 ≤ x) : 0 < Real.log x - Real.eulerMascheroniConstant := by
  have h1 := Real.eulerMascheroniConstant_lt_two_thirds
  have h2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h3 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  linarith

/-- **The splitting** at `D ≤ ⌊x⌋`. -/
theorem identity_split {x : ℝ} (hx : 2 ≤ x) {D : ℕ} (hD : D ≤ ⌊x⌋₊) :
    |mx x| * (Real.log x - Real.eulerMascheroniConstant) ≤
      ∑ n ∈ Icc 1 D, |Eg (x / n)| / n + |∑ n ∈ Ioc D ⌊x⌋₊, (μ n : ℝ) * (Eg (x / n) / n)| := by
  have hpos := log_sub_gamma_pos hx
  have hid := mlog_identity (x := x) (by linarith) (-Real.eulerMascheroniConstant)
  rw [← abs_of_pos hpos, ← abs_mul]
  have e : mx x * (Real.log x - Real.eulerMascheroniConstant) =
      -∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * (Eg (x / n) / n) := by
    rw [mx, sub_eq_add_neg, hid]
    congr 1; refine sum_congr rfl fun n _ => ?_
    simp only [Eg, sub_neg_eq_add]; ring
  rw [e, abs_neg]
  have hsplit : Icc 1 ⌊x⌋₊ = Icc 1 D ∪ Ioc D ⌊x⌋₊ := by
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 D) (Ioc D ⌊x⌋₊) := by
    rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  have hn0 : (0 : ℝ) < n := by have := (mem_Icc.1 hn).1; exact_mod_cast (by omega : 0 < n)
  rw [abs_mul, abs_div, abs_of_pos hn0]
  calc |(μ n : ℝ)| * (|Eg (x / n)| / n) ≤ 1 * (|Eg (x / n)| / n) :=
        mul_le_mul_of_nonneg_right (abs_mu_le n) (by positivity)
    _ = _ := one_mul _

/-- `J(n) = ∑_{x/(n+1) < k ≤ x/n} Λ(k)/k`. -/
noncomputable def Jx (x : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Ioc ⌊x / (n + 1)⌋₊ ⌊x / n⌋₊, (Λ k : ℝ) / k

theorem Jx_nonneg (x : ℝ) (n : ℕ) : 0 ≤ Jx x n :=
  sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

/-- `E(x/n) − E(x/(n+1)) = J(n) − log(1 + 1/n)`. -/
theorem Eg_sub {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    Eg (x / n) - Eg (x / (n + 1)) = Jx x n - Real.log (1 + 1 / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmono : ⌊x / (n + 1)⌋₊ ≤ ⌊x / n⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_left hx.le hn0 (by linarith))
  simp only [Eg, E₁Λ, Jx]
  rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hmono]
  have e : Real.log (x / n) - Real.log (x / (n + 1)) = Real.log (1 + 1 / n) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  linarith

/-- **The part `n > D`**, by summation by parts against `M`. -/
theorem tail_bound {x : ℝ} (hx : 1 ≤ x) {D : ℕ} (hD1 : 1 ≤ D) (hDN : D < ⌊x⌋₊) (β : ℕ → ℝ)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ : ∀ n, D ≤ n → n ≤ ⌊x⌋₊ → |Mt n| ≤ β n * n) {F : ℝ}
    (hF : ∀ n, D < n → n ≤ ⌊x⌋₊ → |Eg (x / n)| ≤ F) :
    |∑ n ∈ Ioc D ⌊x⌋₊, (μ n : ℝ) * (Eg (x / n) / n)| ≤ β ⌊x⌋₊ * F + β D * F +
      ∑ n ∈ Ioo D ⌊x⌋₊, β n * (Jx x n + Real.log (1 + 1 / n) + F / (n + 1)) := by
  set N := ⌊x⌋₊ with hN
  have hx0 : 0 < x := by linarith
  have hF0 : 0 ≤ F := le_trans (abs_nonneg _) (hF N hDN le_rfl)
  rw [abel_mu _ D N hDN]
  have hND : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have h1 : |Mt N * (Eg (x / N) / N)| ≤ β N * F := by
    rw [abs_mul, abs_div, abs_of_pos hND]
    calc |Mt N| * (|Eg (x / N)| / N) ≤ (β N * N) * (F / N) :=
          mul_le_mul (hβ N hDN.le le_rfl) (div_le_div_of_nonneg_right (hF N hDN le_rfl) hND.le)
            (by positivity) (mul_nonneg (hβ0 _) hND.le)
      _ = β N * F := by field_simp
  have h2 : |Mt D * (Eg (x / ((D + 1 : ℕ) : ℝ)) / ((D + 1 : ℕ) : ℝ))| ≤ β D * F := by
    have hD10 : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
    rw [abs_mul, abs_div, abs_of_pos hD10]
    calc |Mt D| * (|Eg (x / ((D + 1 : ℕ) : ℝ))| / ((D + 1 : ℕ) : ℝ)) ≤ (β D * D) * (F / D) := by
          refine mul_le_mul (hβ D le_rfl hDN.le) ?_ (by positivity) (mul_nonneg (hβ0 _) hD0.le)
          refine (div_le_div_of_nonneg_right (hF (D + 1) (by omega) (by omega)) hD10.le).trans ?_
          exact div_le_div_of_nonneg_left hF0 hD0 (by push_cast; linarith)
      _ = β D * F := by field_simp
  have h3 : ∀ n ∈ Ioo D N, |Mt n * (Eg (x / n) / n - Eg (x / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ))| ≤
      β n * (Jx x n + Real.log (1 + 1 / n) + F / (n + 1)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ioo.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e1]
    have e2 : Eg (x / n) / n - Eg (x / (n + 1)) / (n + 1) =
        (Eg (x / n) - Eg (x / (n + 1))) / n + Eg (x / (n + 1)) * (1 / (n * (n + 1))) := by
      field_simp; ring
    rw [e2, Eg_sub hx0 (by omega)]
    have hl : 0 ≤ Real.log (1 + 1 / n) := Real.log_nonneg (by have : (0 : ℝ) ≤ 1 / n := by positivity
                                                              linarith)
    have hJ := Jx_nonneg x n
    have hF1 : |Eg (x / ((n : ℝ) + 1))| ≤ F := by
      have := hF (n + 1) (by omega) (by omega); push_cast at this; exact this
    have hb : |(Jx x n - Real.log (1 + 1 / n)) / n + Eg (x / (n + 1)) * (1 / (n * (n + 1)))| ≤
        (Jx x n + Real.log (1 + 1 / n) + F / (n + 1)) / n := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos hn0, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n * (n + 1)))]
      have k1 : |Jx x n - Real.log (1 + 1 / n)| ≤ Jx x n + Real.log (1 + 1 / n) := by
        rw [abs_le]; constructor <;> linarith
      have k2 : |Eg (x / ((n : ℝ) + 1))| * (1 / (n * (n + 1))) ≤ F / (n + 1) / n := by
        rw [show F / ((n : ℝ) + 1) / n = F * (1 / (n * (n + 1))) by field_simp]
        exact mul_le_mul_of_nonneg_right hF1 (by positivity)
      calc |Jx x n - Real.log (1 + 1 / n)| / n + |Eg (x / ((n : ℝ) + 1))| * (1 / (n * (n + 1)))
          ≤ (Jx x n + Real.log (1 + 1 / n)) / n + F / (n + 1) / n :=
            add_le_add (div_le_div_of_nonneg_right k1 hn0.le) k2
        _ = _ := by ring
    rw [abs_mul]
    calc |Mt n| * |(Jx x n - Real.log (1 + 1 / n)) / n + Eg (x / (n + 1)) * (1 / (n * (n + 1)))|
        ≤ (β n * n) * ((Jx x n + Real.log (1 + 1 / n) + F / (n + 1)) / n) :=
          mul_le_mul (hβ n hn1.le hn2.le) hb (abs_nonneg _) (mul_nonneg (hβ0 _) hn0.le)
      _ = β n * (Jx x n + Real.log (1 + 1 / n) + F / (n + 1)) := by field_simp
  calc |Mt N * (Eg (x / N) / N) - Mt D * (Eg (x / ((D + 1 : ℕ) : ℝ)) / ((D + 1 : ℕ) : ℝ)) +
        ∑ n ∈ Ioo D N, Mt n * (Eg (x / n) / n - Eg (x / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ))|
      ≤ |Mt N * (Eg (x / N) / N)| + |Mt D * (Eg (x / ((D + 1 : ℕ) : ℝ)) / ((D + 1 : ℕ) : ℝ))| +
          ∑ n ∈ Ioo D N, |Mt n * (Eg (x / n) / n - Eg (x / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ))| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans le_rfl) (abs_sum_le_sum_abs _ _))
    _ ≤ _ := add_le_add (add_le_add h1 h2) (sum_le_sum h3)

/-- `∑_{0<n<K} (√(n+1) − √n) = √K − 1` for `K ≥ 1`. -/
theorem sum_Ioo_sqrt_telescope (K : ℕ) (hK : 1 ≤ K := by omega) :
    ∑ n ∈ Ioo 0 K, (√((n + 1 : ℕ) : ℝ) - √(n : ℝ)) = √(K : ℝ) - 1 := by
  induction K, hK using Nat.le_induction with
  | base => rw [show Ioo 0 1 = (∅ : Finset ℕ) by rfl]; simp
  | succ m hm ih =>
    rw [show Ioo 0 (m + 1) = insert m (Ioo 0 m) by ext x; simp; omega,
      sum_insert (by simp), ih]
    ring

/-! ### The sums in `tail_bound` -/

/-- The `J(n)` telescope: `∑_{n₁ ≤ n < n₂} J(n) = ∑_{x/n₂ < k ≤ x/n₁} Λ(k)/k`. -/
theorem sum_Jx {x : ℝ} (hx : 0 < x) {n₁ n₂ : ℕ} (h1 : 1 ≤ n₁) (h12 : n₁ ≤ n₂) :
    ∑ n ∈ Ico n₁ n₂, Jx x n = ∑ k ∈ Ioc ⌊x / n₂⌋₊ ⌊x / n₁⌋₊, (Λ k : ℝ) / k := by
  induction n₂, h12 using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    rw [Finset.sum_Ico_succ_top hm, ih]
    have hmono : ⌊x / ((m + 1 : ℕ) : ℝ)⌋₊ ≤ ⌊x / m⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hx.le hm0 (by push_cast; linarith))
    have hmono2 : ⌊x / m⌋₊ ≤ ⌊x / n₁⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hx.le (by exact_mod_cast (by omega : 0 < n₁))
        (by exact_mod_cast hm))
    rw [Jx, show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, add_comm,
      sum_Ioc_consecutive _ hmono hmono2]

/-- `∑_{k ≤ K} Λ(k)/√k ≤ 2.078 √K` (summation by parts with `ψ(k) ≤ 1.03883 k`). -/
theorem sum_Lambda_div_sqrt_le [Fact TernaryGoldbach.PlattGRH] (K : ℕ) :
    ∑ k ∈ Ioc 0 K, (Λ k : ℝ) / √(k : ℝ) ≤ 2.078 * √(K : ℝ) := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  set w : ℕ → ℝ := fun k => 1 / √(k : ℝ) with hw
  have hab := abel_Ioc w 0 K hK
  simp only [hw, mul_one_div] at hab
  rw [hab]
  have hψ : ∀ n, psiN n ≤ 1.03883 * n := fun n => (psi_bounds n).1
  have hψ0 : ∀ n, 0 ≤ psiN n := fun n =>
    sum_nonneg fun m _ => ArithmeticFunction.vonMangoldt_nonneg
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hsK : 0 < √(K : ℝ) := Real.sqrt_pos.2 hK0
  have h0 : psiN 0 = 0 := by simp [psiN]
  rw [h0, zero_div, sub_zero]
  -- `ψ(K)/√K ≤ 1.03883 √K`
  have hb1 : psiN K / √(K : ℝ) ≤ 1.03883 * √(K : ℝ) := by
    rw [div_le_iff₀ hsK]
    have := hψ K
    have hs := Real.mul_self_sqrt hK0.le
    nlinarith
  -- interior: `ψ(n)(1/√n − 1/√(n+1)) ≤ 1.03883 n (1/√n − 1/√(n+1)) ≤ 1.03883 (√(n+1) − √n)`
  have hstep : ∀ n ∈ Ioo 0 K, psiN n * (1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ)) ≤
      1.03883 * (√((n + 1 : ℕ) : ℝ) - √(n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioo.1 hn).1
    have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    have hs1 : 0 < √((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hle : √(n : ℝ) ≤ √((n + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
    have hd0 : 0 ≤ 1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ) := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hs0 hle
    have h1 : psiN n * (1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ)) ≤
        (1.03883 * n) * (1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (hψ n) hd0
    have hsn := Real.mul_self_sqrt hn0.le
    have h2 : (n : ℝ) * (1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ)) ≤ √((n + 1 : ℕ) : ℝ) - √(n : ℝ) := by
      have e : (n : ℝ) * (1 / √(n : ℝ) - 1 / √((n + 1 : ℕ) : ℝ)) =
          (√((n + 1 : ℕ) : ℝ) - √(n : ℝ)) * (√(n : ℝ) / √((n + 1 : ℕ) : ℝ)) := by
        have k1 : (n : ℝ) * (1 / √(n : ℝ)) = √(n : ℝ) := by rw [mul_one_div, Real.div_sqrt]
        have k2 : (√((n + 1 : ℕ) : ℝ) - √(n : ℝ)) * (√(n : ℝ) / √((n + 1 : ℕ) : ℝ)) =
            √(n : ℝ) - √(n : ℝ) * √(n : ℝ) / √((n + 1 : ℕ) : ℝ) := by field_simp
        rw [mul_sub, k1, k2, hsn, mul_one_div]
      rw [e]
      have hq : √(n : ℝ) / √((n + 1 : ℕ) : ℝ) ≤ 1 := by rw [div_le_one hs1]; exact hle
      have hd : 0 ≤ √((n + 1 : ℕ) : ℝ) - √(n : ℝ) := by linarith
      nlinarith
    nlinarith
  have hsum := sum_le_sum hstep
  rw [← mul_sum, sum_Ioo_sqrt_telescope K] at hsum
  have : 1.03883 * (√(K : ℝ) - 1) ≤ 1.03883 * √(K : ℝ) := by nlinarith
  linarith

/-- The telescope for any `g`: `∑_{n₁ ≤ n < n₂} ∑_{x/(n+1) < k ≤ x/n} g(k) = ∑_{x/n₂ < k ≤ x/n₁} g(k)`. -/
theorem sum_blocks {x : ℝ} (hx : 0 < x) (g : ℕ → ℝ) {n₁ n₂ : ℕ} (h1 : 1 ≤ n₁) (h12 : n₁ ≤ n₂) :
    ∑ n ∈ Ico n₁ n₂, ∑ k ∈ Ioc ⌊x / (n + 1)⌋₊ ⌊x / n⌋₊, g k = ∑ k ∈ Ioc ⌊x / n₂⌋₊ ⌊x / n₁⌋₊, g k := by
  induction n₂, h12 using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    rw [Finset.sum_Ico_succ_top hm, ih]
    have hmono : ⌊x / ((m + 1 : ℕ) : ℝ)⌋₊ ≤ ⌊x / m⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hx.le hm0 (by push_cast; linarith))
    have hmono2 : ⌊x / m⌋₊ ≤ ⌊x / n₁⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_left hx.le (by exact_mod_cast (by omega : 0 < n₁))
        (by exact_mod_cast hm))
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, add_comm,
      sum_Ioc_consecutive _ hmono hmono2]

/-- `∑_{D < n < N} 1/(n √n) ≤ 2/√D`. -/
theorem sum_inv_pow32_le {D : ℕ} (hD : 1 ≤ D) (N : ℕ) :
    ∑ n ∈ Ioo D N, (1 : ℝ) / (n * √(n : ℝ)) ≤ 2 / √(D : ℝ) := by
  have key : ∀ M : ℕ, ∑ n ∈ Ioc D (D + M), (1 : ℝ) / (n * √(n : ℝ)) ≤
      2 / √(D : ℝ) - 2 / √((D + M : ℕ) : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show D + (M + 1) = (D + M) + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
      set m := D + M with hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hs0 : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm0
      have hs1 : 0 < √((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
      have hsm := Real.mul_self_sqrt hm0.le
      have hsm1 := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))
      have hle : √(m : ℝ) ≤ √((m + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
      -- `1/((m+1)√(m+1)) ≤ 2/√m − 2/√(m+1)`
      have hstep : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * √((m + 1 : ℕ) : ℝ)) ≤ 2 / √(m : ℝ) - 2 / √((m + 1 : ℕ) : ℝ) := by
        set a := √(m : ℝ); set b := √((m + 1 : ℕ) : ℝ)
        have hb2 : b * b = a * a + 1 := by rw [hsm1, hsm]; push_cast; ring
        have hab : (b - a) * (b + a) = 1 := by nlinarith
        have e1 : 2 / a - 2 / b = 2 / (a * b * (a + b)) := by
          field_simp
          nlinarith
        have e2 : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * b) = 1 / (b * b * b) := by rw [← hsm1]
        rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hs0 hs1, mul_pos hs1 hs1, mul_nonneg hs0.le (sub_nonneg.2 hle)]
      linarith
  rcases Nat.lt_or_ge D N with h | h
  · have hsub : Ioo D N ⊆ Ioc D (D + (N - D)) := by
      intro n hn; simp only [mem_Ioo, mem_Ioc] at hn ⊢; omega
    refine (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity).trans ?_
    have := key (N - D)
    have : 0 ≤ 2 / √(((D + (N - D) : ℕ)) : ℝ) := by positivity
    linarith
  · rw [show Ioo D N = ∅ by ext n; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega,
      sum_empty]; positivity

/-- The `J/√n` sum: `∑_{D<n<N} J(n)/√n ≤ (1.005/√x) ∑_{k ≤ x/(D+1)} Λ(k)/√k` for `D ≥ 101`. -/
theorem sum_Jx_div_sqrt_le {x : ℝ} (hx : 0 < x) {D : ℕ} (hD : 101 ≤ D) (N : ℕ) (hN : N ≤ ⌊x⌋₊) :
    ∑ n ∈ Ioo D N, Jx x n / √(n : ℝ) ≤
      1.005 / √x * ∑ k ∈ Ioc 0 ⌊x / ((D + 1 : ℕ) : ℝ)⌋₊, (Λ k : ℝ) / √(k : ℝ) := by
  rcases Nat.lt_or_ge (D + 1) N with h | h
  · have hIoo : Ioo D N = Ico (D + 1) N := by ext n; simp only [mem_Ioo, mem_Ico]; omega
    rw [hIoo]
    have hsx : 0 < √x := Real.sqrt_pos.2 hx
    -- termwise
    have hterm : ∀ n ∈ Ico (D + 1) N, Jx x n / √(n : ℝ) ≤
        ∑ k ∈ Ioc ⌊x / (n + 1)⌋₊ ⌊x / n⌋₊, 1.005 / √x * ((Λ k : ℝ) / √(k : ℝ)) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := mem_Ico.1 hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn101 : (102 : ℝ) ≤ n := by exact_mod_cast (by omega : 102 ≤ n)
      have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
      rw [Jx, sum_div]
      refine sum_le_sum fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := mem_Ioc.1 hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk0
      -- `k > x/(n+1)`
      have hkx : x / (n + 1) < k := by
        have := Nat.lt_floor_add_one (x / (n + 1))
        have : ((⌊x / (n + 1)⌋₊ : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hk1
        linarith
      have hxk : x ≤ 1.0099 * (k * n) := by
        rw [div_lt_iff₀ (by linarith)] at hkx
        nlinarith
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := k)
      -- `1/(k √n) ≤ 1.005/(√x √k)`
      have hsq : √x ≤ 1.005 * √(k : ℝ) * √(n : ℝ) := by
        have hy : 0 ≤ 1.005 * √(k : ℝ) * √(n : ℝ) := by positivity
        have e : (1.005 * √(k : ℝ) * √(n : ℝ)) ^ 2 = 1.010025 * (k * n) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hk0.le, Real.sq_sqrt hn0.le]; ring
        calc √x ≤ √((1.005 * √(k : ℝ) * √(n : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by rw [e]; nlinarith)
          _ = _ := Real.sqrt_sq hy
      have hk2' : ((k : ℕ) : ℝ) = √(k : ℝ) * √(k : ℝ) := (Real.mul_self_sqrt hk0.le).symm
      rw [div_div, show (1.005 : ℝ) / √x * ((Λ k : ℝ) / √(k : ℝ)) = (Λ k : ℝ) * (1.005 / (√x * √(k : ℝ))) by
        field_simp]
      rw [div_eq_mul_one_div (Λ k : ℝ)]
      refine mul_le_mul_of_nonneg_left ?_ hΛ
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right hsq hsk.le
      nlinarith [mul_pos hsk hsn, hk2']
    refine (sum_le_sum hterm).trans ?_
    rw [sum_blocks hx _ (by omega) h.le, ← mul_sum]
    refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
      (Ioc_subset_Ioc (Nat.zero_le _) le_rfl) fun k _ _ => ?_) (by positivity)
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · rw [show Ioo D N = ∅ by ext n; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega,
      sum_empty]
    refine mul_nonneg (by positivity) (sum_nonneg fun k _ => ?_)
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

end TernaryGoldbach.Prelim
