import TernaryGoldbach.Prelim.SchoenfeldTailAux
import TernaryGoldbach.Prelim.SchoenfeldCells11

/-!
# The induction beyond the cells

For `D ≥ T` (the end of the last cell, `log T > 160.54`) we prove `|N(D)| ≤ ν∞ D`, `ν∞ = 0.033`, by
strong induction, with the identity at `y = ⌊D^{0.18}⌋`:
* the `k`-sum: `|M(u)| ≤ (ν∞/log u + c₂/log²u) u` for `u ∈ [U₀, D)` (the cells below `T`, and
  `M_of_N` above `T`); `G(10⁶)` from the table and `∑ Λ(k)/k` beyond;
* the `j`-sum: `|ρ(v)| ≤ 0.00985 v/log v` (`rho_C5`) on pieces `D^{c_i} ≤ v < D^{c_{i+1}}`.
-/

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim.Sch
open TernaryGoldbach.Prelim.Sqf (musq kap Q1)
open TernaryGoldbach.Prelim.Wts (aw)

set_option maxRecDepth 100000

variable [Fact TernaryGoldbach.PlattGRH]

/-! ### The pieces of the `j`-sum -/

theorem rho_term {D V m : ℕ} (hV : 1000000000000 ≤ V) (hm1 : 1 ≤ m) (hvV : V ≤ D / m) :
    musq m * |ρn (D / m)| ≤ D * (0.00985 / Real.log V) * (musq m / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hV0 : (0 : ℝ) < V := by exact_mod_cast (by omega : 0 < V)
  have hlV : 0 < Real.log V := Real.log_pos (by exact_mod_cast (by omega : 1 < V))
  have hvV' : (V : ℝ) ≤ ((D / m : ℕ) : ℝ) := by exact_mod_cast hvV
  have hl : Real.log V ≤ Real.log ((D / m : ℕ) : ℝ) := Real.log_le_log hV0 hvV'
  have hv : ((D / m : ℕ) : ℝ) ≤ (D : ℝ) / m := Nat.cast_div_le
  have hsq := Sqf.musq_nonneg m
  have hr := rho_C5 (le_trans hV hvV)
  have h2 : 0.00985 * ((D / m : ℕ) : ℝ) / Real.log ((D / m : ℕ) : ℝ) ≤ 0.00985 * ((D : ℝ) / m) / Real.log V := by
    apply div_le_div₀ (by positivity) (by linarith) hlV hl
  calc musq m * |ρn (D / m)| ≤ musq m * (0.00985 * ((D : ℝ) / m) / Real.log V) :=
        mul_le_mul_of_nonneg_left (le_trans hr h2) hsq
    _ = D * (0.00985 / Real.log V) * (musq m / m) := by ring

/-- One piece `V ≤ D/m < W`. -/
theorem rho_piece {D V W : ℕ} (hV : 1000000000000 ≤ V) (hVW : V ≤ W) (hWD : W ≤ D) :
    ∑ m ∈ Ioc (D / W) (D / V), musq m * |ρn (D / m)| ≤
      D * (0.00985 / Real.log V * (kap * Real.log ((W : ℝ) / V) + 0.588)) := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast (by omega : 0 < V)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hlV : 0 < Real.log V := Real.log_pos (by exact_mod_cast (by omega : 1 < V))
  have hterm : ∀ m ∈ Ioc (D / W) (D / V), musq m * |ρn (D / m)| ≤ D * (0.00985 / Real.log V) * (musq m / m) := by
    intro m hm
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hm
    have hm1 : 1 ≤ m := Nat.lt_of_le_of_lt (Nat.zero_le _) h1
    refine rho_term hV hm1 ?_
    rw [Nat.le_div_iff_mul_le hm1]; have := (Nat.le_div_iff_mul_le (by omega)).1 h2; linarith [mul_comm m V]
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hDW : D / W ≤ D / V := Nat.div_le_div_left hVW (by omega)
  rw [← Q1_nat_sub hDW]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have e1 : Q1 ((D / V : ℕ) : ℝ) = Q1 ((D : ℝ) / V) := by
    unfold Q1; rw [Nat.floor_natCast, Nat.floor_div_eq_div]
  have e2 : Q1 ((D / W : ℕ) : ℝ) = Q1 ((D : ℝ) / W) := by
    unfold Q1; rw [Nat.floor_natCast, Nat.floor_div_eq_div]
  rw [e1, e2]
  have hA : (1 : ℝ) ≤ (D : ℝ) / W := by
    rw [le_div_iff₀ hW0]; exact_mod_cast (by omega : 1 * W ≤ D)
  have hAB : (D : ℝ) / W ≤ (D : ℝ) / V := div_le_div_of_nonneg_left hD0.le hV0 (by exact_mod_cast hVW)
  have hdiff := Sqf.Q1_diff_le hA hAB
  have elog : (D : ℝ) / V / ((D : ℝ) / W) = (W : ℝ) / V := by field_simp
  rw [elog] at hdiff
  calc (D : ℝ) * (0.00985 / Real.log V) * (Q1 ((D : ℝ) / V) - Q1 ((D : ℝ) / W))
      ≤ D * (0.00985 / Real.log V) * (kap * Real.log ((W : ℝ) / V) + 0.588) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = _ := by ring

/-- The last piece `D/m ≥ V`. -/
theorem rho_last {D V : ℕ} (hV : 1000000000000 ≤ V) (hVD : V ≤ D) :
    ∑ m ∈ Ioc 0 (D / V), musq m * |ρn (D / m)| ≤
      D * (0.00985 / Real.log V * (kap * Real.log ((D : ℝ) / V) + 1.166)) := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast (by omega : 0 < V)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hlV : 0 < Real.log V := Real.log_pos (by exact_mod_cast (by omega : 1 < V))
  have hterm : ∀ m ∈ Ioc 0 (D / V), musq m * |ρn (D / m)| ≤ D * (0.00985 / Real.log V) * (musq m / m) := by
    intro m hm
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hm
    refine rho_term hV (by omega) ?_
    rw [Nat.le_div_iff_mul_le (by omega)]; have := (Nat.le_div_iff_mul_le (by omega)).1 h2; linarith [mul_comm m V]
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have e0 : ∑ m ∈ Ioc 0 (D / V), musq m / (m : ℝ) = Q1 ((D : ℝ) / V) := by
    unfold Q1; rw [Nat.floor_div_eq_div, show Icc 1 (D / V) = Ioc 0 (D / V) by ext; simp; omega]
  rw [e0]
  have hA : (1 : ℝ) ≤ (D : ℝ) / V := by rw [le_div_iff₀ hV0]; exact_mod_cast (by omega : 1 * V ≤ D)
  have hb := (Sqf.Eq1_bounds hA).2
  unfold Sqf.Eq1 at hb
  have : Q1 ((D : ℝ) / V) ≤ kap * Real.log ((D : ℝ) / V) + 1.166 := by linarith
  calc (D : ℝ) * (0.00985 / Real.log V) * Q1 ((D : ℝ) / V) ≤
        D * (0.00985 / Real.log V) * (kap * Real.log ((D : ℝ) / V) + 1.166) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- The `j`-sum bound over a list of points `(V, ℓ, u)` with `ℓ ≤ log V ≤ u`. -/
noncomputable def jT (L : ℝ) : ℕ × ℝ × ℝ → List (ℕ × ℝ × ℝ) → ℝ
  | v, [] => 0.00985 / v.2.1 * (kq * (L - v.2.1) + 1.166)
  | v, w :: ws => 0.00985 / v.2.1 * (kq * (w.2.2 - v.2.1) + 0.588) + jT L w ws

/-- The conditions on the points. -/
def jOK (D : ℕ) : ℕ × ℝ × ℝ → List (ℕ × ℝ × ℝ) → Prop
  | v, [] => 1000000000000 ≤ v.1 ∧ v.1 ≤ D ∧ 0 < v.2.1 ∧ v.2.1 ≤ Real.log v.1 ∧ Real.log v.1 ≤ v.2.2
  | v, w :: ws => 1000000000000 ≤ v.1 ∧ v.1 ≤ w.1 ∧ 0 < v.2.1 ∧ v.2.1 ≤ Real.log v.1 ∧
      Real.log v.1 ≤ v.2.2 ∧ jOK D w ws

theorem jOK_le (D : ℕ) : ∀ (ws : List (ℕ × ℝ × ℝ)) (v : ℕ × ℝ × ℝ), jOK D v ws → v.1 ≤ D
  | [], v, h => h.2.1
  | w :: ws, v, h => le_trans h.2.1 (jOK_le D ws w h.2.2.2.2.2)

theorem jT_spec {D : ℕ} : ∀ (ws : List (ℕ × ℝ × ℝ)) (v : ℕ × ℝ × ℝ), jOK D v ws →
    ∑ m ∈ Ioc 0 (D / v.1), musq m * |ρn (D / m)| ≤ D * jT (Real.log D) v ws
  | [], v, ⟨h1, h2, h3, h4, h5⟩ => by
    have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have hV0 : (0 : ℝ) < v.1 := by exact_mod_cast (by omega : 0 < v.1)
    refine le_trans (rho_last h1 h2) (mul_le_mul_of_nonneg_left ?_ hD0.le)
    simp only [jT]
    have hk := kap_le_kq
    have hk0 : 0 ≤ kap := Sqf.kap_pos.le
    rw [Real.log_div hD0.ne' hV0.ne']
    have hlD : Real.log v.1 ≤ Real.log D := Real.log_le_log hV0 (by exact_mod_cast h2)
    have hlV : 0 < Real.log v.1 := by linarith
    apply mul_le_mul (div_le_div_of_nonneg_left (by norm_num) h3 h4) _ (by nlinarith) (by positivity)
    nlinarith
  | w :: ws, v, ⟨h1, h2, h3, h4, h5, hr⟩ => by
    have hwD := jOK_le D ws w hr
    have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have ih := jT_spec ws w hr
    have hw : 1000000000000 ≤ w.1 ∧ 0 < w.2.1 ∧ w.2.1 ≤ Real.log w.1 ∧ Real.log w.1 ≤ w.2.2 := by
      cases ws with
      | nil => exact ⟨hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2⟩
      | cons _ _ => exact ⟨hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1⟩
    obtain ⟨w1, w3, w4, w5⟩ := hw
    have hV0 : (0 : ℝ) < v.1 := by exact_mod_cast (by omega : 0 < v.1)
    have hW0 : (0 : ℝ) < w.1 := by exact_mod_cast (by omega : 0 < w.1)
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le (D / w.1)) (Nat.div_le_div_left h2 (by omega))]
    have hp := rho_piece h1 h2 hwD
    simp only [jT]
    have hk := kap_le_kq
    have hk0 : 0 ≤ kap := Sqf.kap_pos.le
    rw [Real.log_div hW0.ne' hV0.ne'] at hp
    have hlW : Real.log v.1 ≤ Real.log w.1 := Real.log_le_log hV0 (by exact_mod_cast h2)
    have hlV : 0 < Real.log v.1 := by linarith
    have hq : 0.00985 / Real.log v.1 * (kap * (Real.log w.1 - Real.log v.1) + 0.588) ≤
        0.00985 / v.2.1 * (kq * (w.2.2 - v.2.1) + 0.588) :=
      mul_le_mul (div_le_div_of_nonneg_left (by norm_num) h3 h4) (by nlinarith) (by nlinarith) (by positivity)
    have := mul_le_mul_of_nonneg_left hq hD0.le
    rw [mul_add]; linarith

/-! ### `M` beyond the cells -/

/-- The end of the cells. -/
noncomputable abbrev TT : ℕ := d213.B

theorem logT_ge : (160.54 : ℝ) ≤ Real.log TT := by
  have := logLo_spec (q := 16054 / 100) (L := d213.B) (by decide +kernel)
  norm_num at this ⊢; exact this

theorem logT_le : Real.log TT ≤ (160.55 : ℝ) := by
  have := logUp_spec (q := 16055 / 100) (L := d213.B) (by decide +kernel)
  norm_num at this ⊢; exact this

theorem X0_lt_T : X0 + 1 ≤ TT := by decide +kernel

/-- `f(t) = t/log²t` does not decrease on `[T, ∞)`. -/
theorem f_mono {a b : ℕ} (ha : 160 ≤ Real.log a) (hab : a ≤ b) :
    (a : ℝ) / Real.log a ^ 2 ≤ b / Real.log b ^ 2 := by
  have h := sum_inv_log_sq_le ha b hab
  have h0 : 0 ≤ ∑ n ∈ Ico a b, 1 / Real.log n ^ 2 := sum_nonneg fun n _ => by positivity
  linarith

theorem K0_le : (626 + (d213.I' : ℝ)) ≤ 0.0059 * (TT / Real.log TT ^ 2) := by
  have hl := logT_le
  have hl0 : 0 < Real.log TT := by linarith [logT_ge]
  have hT0 : (0 : ℝ) < TT := by exact_mod_cast (show 0 < d213.B by decide +kernel)
  have hq : (626 + d213.I') * (16055 / 100) ^ 2 ≤ (59 / 10000 : ℚ) * d213.B := by decide +kernel
  have hq' : ((626 + (d213.I' : ℝ))) * (160.55 : ℝ) ^ 2 ≤ 0.0059 * (TT : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hq; push_cast at this; norm_num at this ⊢; linarith
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have hI0 : (0 : ℝ) ≤ 626 + d213.I' := by
    have : (0 : ℚ) ≤ d213.I' := by decide +kernel
    have := (Rat.cast_le (K := ℝ)).2 this; push_cast at this; linarith
  calc (626 + (d213.I' : ℝ)) * Real.log TT ^ 2 ≤ (626 + d213.I') * 160.55 ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0.le hl 2) hI0
    _ ≤ _ := hq'

/-- `|M(u)| ≤ (ν∞/log u + c₂/log²u) u` for `u ≥ T`, given `|N(n)| ≤ ν∞ n` on `[T, u]`. -/
theorem M_above {u : ℕ} (hu : TT ≤ u) (hN : ∀ n, TT ≤ n → n ≤ u → |Nn n| ≤ 0.033 * n) :
    |Mn u| ≤ (0.033 / Real.log u + 0.0395 / Real.log u ^ 2) * u := by
  have hT := logT_ge
  have hX := X0_lt_T
  have hlu : Real.log TT ≤ Real.log u :=
    Real.log_le_log (by exact_mod_cast (show 0 < TT by omega)) (by exact_mod_cast hu)
  have hlu0 : 0 < Real.log u := by linarith
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hM := M_of_N (a := X0) (by norm_num [X0]) u (by omega)
  have hsplit : ∑ n ∈ Ioo X0 u, Nn n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
      ∑ n ∈ Ioo X0 TT, Nn n * wN n + ∑ n ∈ Ico TT u, Nn n * wN n := by
    rw [← Finset.Ico_add_one_left_eq_Ioo, ← Finset.Ico_add_one_left_eq_Ioo, ← Finset.sum_Ico_consecutive _ hX hu]; rfl
  rw [hsplit] at hM
  have hC := C0_le
  obtain ⟨-, -, hI⟩ := st213
  have hA : |∑ n ∈ Ioo X0 TT, Nn n * wN n| ≤ d213.I' := by
    refine le_trans (abs_sum_le_sum_abs _ _) (le_of_eq_of_le (sum_congr rfl fun n hn => ?_) hI)
    have : 2 ≤ n := by have := (mem_Ioo.1 hn).1; unfold X0 at this; omega
    rw [abs_mul, abs_of_nonneg (wN_nonneg this)]
  have hB : |∑ n ∈ Ico TT u, Nn n * wN n| ≤ 0.033 * (1.013 * ((u : ℝ) / Real.log u ^ 2 - TT / Real.log TT ^ 2)) := by
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    refine le_trans (sum_le_sum fun n hn => ?_) (le_trans (le_of_eq (mul_sum _ _ _).symm)
      (mul_le_mul_of_nonneg_left (sum_inv_log_sq_le (by linarith) u hu) (by norm_num)))
    obtain ⟨h1, h2⟩ := mem_Ico.1 hn
    have h2n : 2 ≤ n := by have : 2 ≤ TT := le_trans (by norm_num [X0]) hX
                           omega
    have hw := wN_nonneg h2n
    have hln : Real.log TT ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast (show 0 < TT by omega)) (by exact_mod_cast h1)
    rw [abs_mul, abs_of_nonneg hw]
    have hNn := hN n h1 h2.le
    have hnw := n_wN_le h2n (L := Real.log n) (by linarith) le_rfl
    calc |Nn n| * wN n ≤ 0.033 * n * wN n := mul_le_mul_of_nonneg_right hNn hw
      _ = 0.033 * (n * wN n) := by ring
      _ ≤ 0.033 * (1 / Real.log n ^ 2) := mul_le_mul_of_nonneg_left hnw (by norm_num)
  have hNu := hN u hu le_rfl
  have hK := K0_le
  have hf := f_mono (a := TT) (b := u) (by linarith) hu
  have hTf : (0 : ℝ) ≤ TT / Real.log TT ^ 2 := by positivity
  rw [hM]
  calc |Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1) + Nn u / Real.log u +
        (∑ n ∈ Ioo X0 TT, Nn n * wN n + ∑ n ∈ Ico TT u, Nn n * wN n)|
      ≤ |Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1)| + |Nn u| / Real.log u +
        (|∑ n ∈ Ioo X0 TT, Nn n * wN n| + |∑ n ∈ Ico TT u, Nn n * wN n|) := by
        rw [← abs_of_pos hlu0, ← abs_div, abs_of_pos hlu0]
        exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ 626 + 0.033 * u / Real.log u + (d213.I' + 0.033 * (1.013 * ((u : ℝ) / Real.log u ^ 2 - TT / Real.log TT ^ 2))) := by
        gcongr
    _ ≤ (0.033 / Real.log u + 0.0395 / Real.log u ^ 2) * u := by
        have e : (0.033 / Real.log u + 0.0395 / Real.log u ^ 2) * u =
            0.033 * u / Real.log u + 0.0395 * (u / Real.log u ^ 2) := by ring
        rw [e]
        have : (0 : ℝ) ≤ u / Real.log u ^ 2 := by positivity
        nlinarith

/-- `U₀ = 10⁵⁷ ≤ D^{0.82}`. -/
def U0 : ℕ := 10 ^ 57

theorem logU0_le : Real.log U0 ≤ 131.25 := by
  have := logUp_spec (q := 13125 / 100) (L := U0) (by decide +kernel)
  norm_num at this ⊢; exact this

theorem etaStar : etaMax (X0 + 1) cs213 U0 (d213.B - 1) ≤ 33 / 160550 := by decide +kernel

/-- `|M(u)| ≤ (ν∞/log u + c₂/log²u) u` for `U₀ ≤ u < D`, given `|N(n)| ≤ ν∞ n` on `[T, D)`. -/
theorem M_unif {D : ℕ} (hN : ∀ n, TT ≤ n → n < D → |Nn n| ≤ 0.033 * n) {u : ℕ} (h1 : U0 ≤ u) (h2 : u < D) :
    |Mn u| ≤ (0.033 / Real.log u + 0.0395 / Real.log u ^ 2) * u := by
  rcases le_or_gt TT u with h | h
  · exact M_above h fun n hn1 hn2 => hN n hn1 (by omega)
  · obtain ⟨hc, he, -⟩ := st213
    have hu0 : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by unfold U0 at h1; omega)
    have hs := etaMax_spec cs213 (X0 + 1) hc U0 (d213.B - 1) u (by unfold U0 at h1; unfold X0; omega)
      (by rw [he]; exact h) h1 (by show u ≤ TT - 1; omega)
    have hη : ((etaMax (X0 + 1) cs213 U0 (d213.B - 1) : ℚ) : ℝ) ≤ 0.033 / 160.55 := by
      have := (Rat.cast_le (K := ℝ)).2 etaStar; push_cast at this; norm_num at this ⊢; linarith
    have hlu : Real.log u ≤ Real.log TT := Real.log_le_log hu0 (by exact_mod_cast h.le)
    have hlu0 : 0 < Real.log u := by
      have : (1e57 : ℝ) ≤ u := by have : ((10 ^ 57 : ℕ) : ℝ) ≤ u := by exact_mod_cast h1
                                  norm_num at this ⊢; linarith
      exact Real.log_pos (by linarith)
    have h3 : (0.033 : ℝ) / 160.55 ≤ 0.033 / Real.log u :=
      div_le_div_of_nonneg_left (by norm_num) hlu0 (le_trans hlu logT_le)
    have h4 : 0 ≤ 0.0395 / Real.log u ^ 2 := by positivity
    calc |Mn u| ≤ (etaMax (X0 + 1) cs213 U0 (d213.B - 1) : ℝ) * u := hs
      _ ≤ (0.033 / Real.log u + 0.0395 / Real.log u ^ 2) * u :=
          mul_le_mul_of_nonneg_right (by linarith) hu0.le

/-! ### Helpers -/

omit [Fact TernaryGoldbach.PlattGRH] in
theorem floor_div_ge {D k : ℕ} (hk : 1 ≤ k) (hkD : k ≤ D) : (D : ℝ) / (2 * k) ≤ ((D / k : ℕ) : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hq1 : 1 ≤ D / k := (Nat.one_le_div_iff hk).2 hkD
  have hlt : D < (D / k + 1) * k := by
    rw [mul_comm]; exact Nat.lt_mul_div_succ D (by omega)
  have hlt' : (D : ℝ) < ((D / k : ℕ) + 1) * k := by exact_mod_cast hlt
  have hq1' : (1 : ℝ) ≤ ((D / k : ℕ) : ℝ) := by exact_mod_cast hq1
  rw [div_le_iff₀ (by positivity)]
  nlinarith

omit [Fact TernaryGoldbach.PlattGRH] in
theorem log_div_nat_ge {D k : ℕ} (hk : 1 ≤ k) (hkD : k ≤ D) :
    Real.log D - Real.log k - 0.6932 ≤ Real.log ((D / k : ℕ) : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have h := floor_div_ge hk hkD
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_div hD0.ne' (by positivity), Real.log_mul (by norm_num) hk0.ne'] at hl
  have := Real.log_two_lt_d9
  linarith

omit [Fact TernaryGoldbach.PlattGRH] in
theorem exp28_ge : (1.4e12 : ℝ) ≤ Real.exp 28 := by
  have := TernaryGoldbach.Explicit.exp_nat_ge' 28; push_cast at this
  have : (1.4e12 : ℝ) ≤ 2.7182818283 ^ 28 := by norm_num
  linarith

omit [Fact TernaryGoldbach.PlattGRH] in
/-- `V = ⌊e^x⌋` for `28 ≤ x ≤ log D`. -/
theorem vfloor {D : ℕ} {x : ℝ} (hx : 28 ≤ x) (hxD : x ≤ Real.log D) (hD : 1 ≤ D) :
    1000000000000 ≤ ⌊Real.exp x⌋₊ ∧ ⌊Real.exp x⌋₊ ≤ D ∧ x - 1e-9 ≤ Real.log ⌊Real.exp x⌋₊ ∧
      Real.log ⌊Real.exp x⌋₊ ≤ x := by
  have he := exp28_ge
  have hex : Real.exp 28 ≤ Real.exp x := Real.exp_le_exp.2 hx
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  refine ⟨Nat.le_floor (by push_cast; linarith), ?_, ?_, ?_⟩
  · have : Real.exp x ≤ D := by rw [← Real.exp_log hD0]; exact Real.exp_le_exp.2 hxD
    exact_mod_cast le_trans (Nat.floor_le (Real.exp_pos x).le) this
  · have h := log_floor_ge (x := Real.exp x) (by linarith)
    rw [Real.log_exp] at h
    have : 2 / Real.exp x ≤ 1e-9 := by rw [div_le_iff₀ (Real.exp_pos x)]; linarith
    linarith
  · have hf0 : (0 : ℝ) < ⌊Real.exp x⌋₊ := by
      have : (1 : ℝ) ≤ ⌊Real.exp x⌋₊ := by exact_mod_cast Nat.le_floor (by push_cast; linarith)
      linarith
    have := Real.log_le_log hf0 (Nat.floor_le (Real.exp_pos x).le)
    rwa [Real.log_exp] at this

omit [Fact TernaryGoldbach.PlattGRH] in
theorem eta_anti {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    0.033 / u + 0.0395 / u ^ 2 ≤ 0.033 / l + 0.0395 / l ^ 2 := by
  have h1 : 0.033 / u ≤ 0.033 / l := div_le_div_of_nonneg_left (by norm_num) hl hlu
  have h2 : 0.0395 / u ^ 2 ≤ 0.0395 / l ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hl.le hlu 2)
  linarith

omit [Fact TernaryGoldbach.PlattGRH] in
theorem frac_anti {a b c d L L0 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 ≤ d)
    (h0 : d < c * L0) (hL : L0 ≤ L) : (a * L + b) / (c * L - d) ≤ (a * L0 + b) / (c * L0 - d) := by
  have h1 : 0 < c * L - d := by nlinarith
  rw [div_le_div_iff₀ h1 (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg ha hd) (sub_nonneg.2 hL), mul_nonneg (mul_nonneg hb hc.le) (sub_nonneg.2 hL)]

omit [Fact TernaryGoldbach.PlattGRH] in
theorem log1e6_le : Real.log ((10 ^ 6 : ℕ) : ℝ) ≤ 13.8156 := by
  have := logUp_spec (q := 138156 / 10000) (L := 10 ^ 6) (by decide +kernel)
  norm_num at this ⊢; exact this

omit [Fact TernaryGoldbach.PlattGRH] in
theorem log1e6_ge : 13.8155 ≤ Real.log ((10 ^ 6 : ℕ) : ℝ) := by
  have := logLo_spec (q := 138155 / 10000) (L := 10 ^ 6) (by decide +kernel)
  norm_num at this ⊢; exact this

omit [Fact TernaryGoldbach.PlattGRH] in
theorem log32_le : Real.log (3 / √2) ≤ 0.7523 := by
  have h3 := logUp_spec (q := 10987 / 10000) (L := 3) (by decide +kernel)
  have h2 := Real.log_two_gt_d9
  rw [Real.log_div (by norm_num) (by positivity), Real.log_sqrt (by norm_num)]
  norm_num at h3 ⊢; linarith

/-- `|M(D)| ≤ C₀ + |N(D)|/log D + I + ν∞ λ D/log²D`, given `|N(n)| ≤ ν∞ n` on `[T, D)`. -/
theorem M_D_bound {D : ℕ} (hD : TT ≤ D) (hN : ∀ n, TT ≤ n → n < D → |Nn n| ≤ 0.033 * n) :
    |Mn D| ≤ 626 + |Nn D| / Real.log D + d213.I' + 0.033 * 1.013 * (D / Real.log D ^ 2) := by
  have hT := logT_ge
  have hX := X0_lt_T
  have hlu : Real.log TT ≤ Real.log D :=
    Real.log_le_log (by exact_mod_cast (show 0 < TT by omega)) (by exact_mod_cast hD)
  have hlu0 : 0 < Real.log D := by linarith
  have hM := M_of_N (a := X0) (by norm_num [X0]) D (by omega)
  have hsplit : ∑ n ∈ Ioo X0 D, Nn n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
      ∑ n ∈ Ioo X0 TT, Nn n * wN n + ∑ n ∈ Ico TT D, Nn n * wN n := by
    rw [← Finset.Ico_add_one_left_eq_Ioo, ← Finset.Ico_add_one_left_eq_Ioo, ← Finset.sum_Ico_consecutive _ hX hD]; rfl
  rw [hsplit] at hM
  have hC := C0_le
  obtain ⟨-, -, hI⟩ := st213
  have hA : |∑ n ∈ Ioo X0 TT, Nn n * wN n| ≤ d213.I' := by
    refine le_trans (abs_sum_le_sum_abs _ _) (le_of_eq_of_le (sum_congr rfl fun n hn => ?_) hI)
    have : 2 ≤ n := by have := (mem_Ioo.1 hn).1; unfold X0 at this; omega
    rw [abs_mul, abs_of_nonneg (wN_nonneg this)]
  have hB : |∑ n ∈ Ico TT D, Nn n * wN n| ≤ 0.033 * (1.013 * ((D : ℝ) / Real.log D ^ 2 - TT / Real.log TT ^ 2)) := by
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    refine le_trans (sum_le_sum fun n hn => ?_) (le_trans (le_of_eq (mul_sum _ _ _).symm)
      (mul_le_mul_of_nonneg_left (sum_inv_log_sq_le (by linarith) D hD) (by norm_num)))
    obtain ⟨h1, h2⟩ := mem_Ico.1 hn
    have h2n : 2 ≤ n := by have : 2 ≤ TT := le_trans (by norm_num [X0]) hX
                           omega
    have hw := wN_nonneg h2n
    rw [abs_mul, abs_of_nonneg hw]
    have hNn := hN n h1 h2
    have hnw := n_wN_le h2n (L := Real.log n) (by
      have : Real.log TT ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast (show 0 < TT by omega)) (by exact_mod_cast h1)
      linarith) le_rfl
    calc |Nn n| * wN n ≤ 0.033 * n * wN n := mul_le_mul_of_nonneg_right hNn hw
      _ = 0.033 * (n * wN n) := by ring
      _ ≤ 0.033 * (1 / Real.log n ^ 2) := mul_le_mul_of_nonneg_left hnw (by norm_num)
  have hTf : (0 : ℝ) ≤ TT / Real.log TT ^ 2 := by positivity
  rw [hM]
  calc |Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1) + Nn D / Real.log D +
        (∑ n ∈ Ioo X0 TT, Nn n * wN n + ∑ n ∈ Ico TT D, Nn n * wN n)|
      ≤ |Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1)| + |Nn D| / Real.log D +
        (|∑ n ∈ Ioo X0 TT, Nn n * wN n| + |∑ n ∈ Ico TT D, Nn n * wN n|) := by
        rw [← abs_of_pos hlu0, ← abs_div, abs_of_pos hlu0]
        exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ 626 + |Nn D| / Real.log D + (d213.I' + 0.033 * (1.013 * ((D : ℝ) / Real.log D ^ 2 - TT / Real.log TT ^ 2))) := by
        gcongr
    _ ≤ _ := by nlinarith

/-- `η(ℓ) = ν∞/ℓ + c₂/ℓ²`. -/
noncomputable def etaT (l : ℝ) : ℝ := 0.033 / l + 0.0395 / l ^ 2

theorem G6_le : Wts.Gw 1000000 ≤ 19925014134314 / 1000000000000 := by
  have h := (ghq_spec (m := 1000000) (by decide +kernel)).2.1
  have e : (ghq 1000000).2.1 = 19925014134314 / 1000000000000 := by decide +kernel
  rw [e] at h; push_cast at h; exact h

theorem aw_le (k : ℕ) : aw k ≤ (Λ k : ℝ) + 1 := by
  unfold aw
  have := ArithmeticFunction.vonMangoldt_nonneg (n := k)
  rw [abs_le]; constructor <;> linarith

/-- `G(y) − G(10⁶) ≤ 2 log y − 2 log 10⁶ + log(3/√2)`. -/
theorem G_tail_le {y : ℕ} (hy : 10 ^ 6 ≤ y) :
    Wts.Gw y - Wts.Gw (10 ^ 6) ≤ 2 * Real.log y - 2 * 13.8155 + 0.7523 := by
  rw [Gw_sub (by norm_num) hy]
  have h1 := sum_Lambda_div_Ioc (a := 10 ^ 6) (b := y) (by norm_num) hy
  have h2 := sum_inv_le_log (a := 10 ^ 6) (b := y) (by norm_num) hy
  have h3 : ∑ k ∈ Ioc (10 ^ 6) y, aw k / k ≤ ∑ k ∈ Ioc (10 ^ 6) y, ((Λ k : ℝ) / k + 1 / k) := by
    refine sum_le_sum fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := (mem_Ioc.1 hk).1; omega)
    rw [← add_div]; exact div_le_div_of_nonneg_right (aw_le k) hk0.le
  rw [sum_add_distrib] at h3
  have h4 := log1e6_ge
  have h5 := log32_le
  have h6 : Real.log ((10 ^ 6 : ℕ) : ℝ) ≤ Real.log (((10 ^ 6 : ℕ) : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h7 := le_trans h3 (add_le_add h1 h2)
  refine le_trans h7 ?_
  set a := Real.log (((10 ^ 6 : ℕ) : ℝ) + 1)
  set b := Real.log ((10 ^ 6 : ℕ) : ℝ)
  set c := Real.log (3 / √2)
  set d := Real.log (y : ℝ)
  linarith

/-- **The `k`-sum** beyond the cells. -/
theorem ksum_tail {D y : ℕ} (hN : ∀ n, TT ≤ n → n < D → |Nn n| ≤ 0.033 * n) (hL : 160.54 ≤ Real.log D)
    (hy6 : 10 ^ 6 ≤ y) (hyD : U0 * y ≤ D) (hly : Real.log y ≤ 0.18 * Real.log D) :
    ∑ k ∈ Ioc 1 y, aw k * |Mn (D / k)| ≤
      D * (19925014134314 / 1000000000000 * etaT (Real.log D - 14.5089) +
        (0.36 * Real.log D - 26.8787) * etaT (0.82 * Real.log D - 0.6933)) := by
  set L := Real.log D
  have hD0 : (0 : ℝ) < D := by
    exact_mod_cast lt_of_lt_of_le (Nat.mul_pos (by norm_num [U0]) (by omega)) hyD
  have hyD' : y ≤ D := le_trans (Nat.le_mul_of_pos_left y (by norm_num [U0])) hyD
  have hl2 := Real.log_two_lt_d9
  -- `U₀ ≤ D/k < D` for `2 ≤ k ≤ y`
  have hU : ∀ k, 2 ≤ k → k ≤ y → U0 ≤ D / k ∧ D / k < D := by
    intro k h1 h2
    refine ⟨(Nat.le_div_iff_mul_le (by omega)).2 (le_trans (Nat.mul_le_mul_left _ h2) hyD), ?_⟩
    exact Nat.div_lt_self (by exact_mod_cast hD0) (by omega)
  have hb1 : ∀ k ∈ Ioc 1 (10 ^ 6), |Mn (D / k)| ≤ 0 * √((D / k : ℕ) : ℝ) +
      etaT (L - 14.5089) * ((D / k : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨k1, k2⟩ := mem_Ioc.1 hk
    obtain ⟨u1, u2⟩ := hU k k1 (le_trans k2 hy6)
    have hM := M_unif hN u1 u2
    have hlk : Real.log k ≤ 13.8156 :=
      le_trans (Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast k2)) log1e6_le
    have hlu := log_div_nat_ge (D := D) (k := k) (by omega) (by omega)
    have := eta_anti (l := L - 14.5089) (u := Real.log ((D / k : ℕ) : ℝ)) (by linarith) (by linarith)
    rw [zero_mul, zero_add]
    exact le_trans hM (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _))
  have hb2 : ∀ k ∈ Ioc (10 ^ 6) y, |Mn (D / k)| ≤ 0 * √((D / k : ℕ) : ℝ) +
      etaT (0.82 * L - 0.6933) * ((D / k : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨k1, k2⟩ := mem_Ioc.1 hk
    obtain ⟨u1, u2⟩ := hU k (by omega) k2
    have hM := M_unif hN u1 u2
    have hlk : Real.log k ≤ Real.log y :=
      Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast k2)
    have hlu := log_div_nat_ge (D := D) (k := k) (by omega) (by omega)
    have := eta_anti (l := 0.82 * L - 0.6933) (u := Real.log ((D / k : ℕ) : ℝ)) (by linarith) (by linarith)
    rw [zero_mul, zero_add]
    exact le_trans hM (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _))
  have he1 : 0 ≤ etaT (L - 14.5089) := by unfold etaT; have : 0 < L - 14.5089 := by linarith
                                          positivity
  have he2 : 0 ≤ etaT (0.82 * L - 0.6933) := by unfold etaT; have : 0 < 0.82 * L - 0.6933 := by linarith
                                                positivity
  have k1 := Ksum_block (D := D) le_rfl he1 le_rfl (by norm_num) hb1
  have k2 := Ksum_block (D := D) le_rfl he2 (by norm_num) hy6 hb2
  rw [← Finset.sum_Ioc_consecutive _ (by norm_num : 1 ≤ 10 ^ 6) hy6]
  have g1 : Wts.Gw (10 ^ 6) - Wts.Gw 1 ≤ 19925014134314 / 1000000000000 := by
    have : Wts.Gw 1 = 0 := by simp [Wts.Gw]
    rw [this, sub_zero]; exact G6_le
  have g2 := G_tail_le hy6
  have g2' : Wts.Gw y - Wts.Gw (10 ^ 6) ≤ 0.36 * L - 26.8787 := by linarith
  have t1 : etaT (L - 14.5089) * D * (Wts.Gw (10 ^ 6) - Wts.Gw 1) ≤
      D * (19925014134314 / 1000000000000 * etaT (L - 14.5089)) := by
    have := mul_le_mul_of_nonneg_left g1 (mul_nonneg he1 hD0.le); linarith
  have t2 : etaT (0.82 * L - 0.6933) * D * (Wts.Gw y - Wts.Gw (10 ^ 6)) ≤
      D * ((0.36 * L - 26.8787) * etaT (0.82 * L - 0.6933)) := by
    have := mul_le_mul_of_nonneg_left g2' (mul_nonneg he2 hD0.le); linarith
  simp only [zero_mul] at k1 k2
  linarith

/-! ### The pieces `D^c ≤ v < D^{c'}` -/

/-- `c ≤ c₁ ≤ c₂ ≤ …`. -/
def srt : ℝ → List ℝ → Prop
  | _, [] => True
  | c, c' :: cs => c ≤ c' ∧ srt c' cs

/-- The point `(⌊D^c⌋, c L − δ, c L + δ)`. -/
noncomputable def pt (L c : ℝ) : ℕ × ℝ × ℝ := (⌊Real.exp (c * L)⌋₊, c * L - 1e-9, c * L + 1e-9)

/-- The value of `jT` on the points `c, cs`. -/
noncomputable def jV (L : ℝ) : ℝ → List ℝ → ℝ
  | c, [] => 0.00985 / (c * L - 1e-9) * (kq * (L - (c * L - 1e-9)) + 1.166)
  | c, c' :: cs => 0.00985 / (c * L - 1e-9) * (kq * ((c' * L + 1e-9) - (c * L - 1e-9)) + 0.588) + jV L c' cs

omit [Fact TernaryGoldbach.PlattGRH] in
theorem jT_pt (L : ℝ) : ∀ (cs : List ℝ) (v : ℕ × ℝ × ℝ) (c : ℝ), v.2.1 = c * L - 1e-9 →
    jT L v (cs.map (pt L)) = jV L c cs
  | [], v, c, h => by simp [jT, jV, h]
  | c' :: cs, v, c, h => by
    simp only [List.map_cons, jT, jV, h]
    rw [jT_pt L cs (pt L c') c' rfl]
    simp [pt]

omit [Fact TernaryGoldbach.PlattGRH] in
theorem jOK_pt {D : ℕ} (hD : 1 ≤ D) {L : ℝ} (hL : L = Real.log D) (hL0 : 0 < L) :
    ∀ (cs : List ℝ) (c : ℝ), 28 ≤ c * L → c ≤ 1 → srt c cs →
      (∀ c' ∈ cs, c' ≤ 1) → jOK D (pt L c) (cs.map (pt L))
  | [], c, h1, h2, _, _ => by
    obtain ⟨v1, v2, v3, v4⟩ := vfloor (D := D) h1 (by rw [← hL]; nlinarith) hD
    exact ⟨v1, v2, by simp only [pt]; linarith, v3, by simp only [pt]; linarith⟩
  | c' :: cs, c, h1, h2, hch, hcs => by
    obtain ⟨v1, v2, v3, v4⟩ := vfloor (D := D) h1 (by rw [← hL]; nlinarith) hD
    have hcc : c ≤ c' := hch.1
    refine ⟨v1, ?_, by simp only [pt]; linarith, v3, by simp only [pt]; linarith, ?_⟩
    · exact Nat.floor_le_floor (Real.exp_le_exp.2 (by nlinarith))
    · exact jOK_pt hD hL hL0 cs c' (by nlinarith) (hcs c' (by simp))
        hch.2 (fun x hx => hcs x (by simp [hx]))

omit [Fact TernaryGoldbach.PlattGRH] in
theorem jV_anti {L L0 : ℝ} (hL : L0 ≤ L) (hL0 : 0 < L0) :
    ∀ (cs : List ℝ) (c : ℝ), 1e-9 < c * L0 → c ≤ 1 → srt c cs → (∀ c' ∈ cs, c' ≤ 1) →
      jV L c cs ≤ jV L0 c cs
  | [], c, h1, h2, _, _ => by
    simp only [jV]
    have hc : 0 < c := by
      by_contra h; push_neg at h; nlinarith
    have hk : (0 : ℝ) ≤ kq := by norm_num [kq]
    have e : ∀ M : ℝ, 0 < c * M - 1e-9 → 0.00985 / (c * M - 1e-9) * (kq * (M - (c * M - 1e-9)) + 1.166) =
        (0.00985 * kq * (1 - c) * M + 0.00985 * (kq * 1e-9 + 1.166)) / (c * M - 1e-9) := by
      intro M hM; field_simp; ring
    rw [e L (by nlinarith), e L0 (by linarith)]
    exact frac_anti (by have := hk; nlinarith) (by positivity) hc (by norm_num) h1 hL
  | c' :: cs, c, h1, h2, hch, hcs => by
    simp only [jV]
    have hc : 0 < c := by
      by_contra h; push_neg at h; nlinarith
    have hcc : c ≤ c' := hch.1
    have hk : (0 : ℝ) ≤ kq := by norm_num [kq]
    have e : ∀ M : ℝ, 0 < c * M - 1e-9 → 0.00985 / (c * M - 1e-9) * (kq * ((c' * M + 1e-9) - (c * M - 1e-9)) + 0.588) =
        (0.00985 * kq * (c' - c) * M + 0.00985 * (kq * 2e-9 + 0.588)) / (c * M - 1e-9) := by
      intro M hM; field_simp; ring
    rw [e L (by nlinarith), e L0 (by linarith)]
    have ih := jV_anti hL hL0 cs c' (by nlinarith) (hcs c' (by simp)) hch.2
      (fun x hx => hcs x (by simp [hx]))
    have := frac_anti (a := 0.00985 * kq * (c' - c)) (b := 0.00985 * (kq * 2e-9 + 0.588))
      (by have : 0 ≤ c' - c := by linarith
          positivity) (by positivity) hc (by norm_num) h1 hL
    linarith

/-- The exponents of the pieces. -/
noncomputable def expL : List ℝ := [0.216, 0.2592, 0.311, 0.3732, 0.4479, 0.5375, 0.645, 0.774, 0.9288]

omit [Fact TernaryGoldbach.PlattGRH] in
theorem numeric_tail :
    1e-9 + 0.039329 / 160.54 ^ 2 + 19925014134314 / 1000000000000 * etaT (160.54 - 14.5089) +
      0.033 * 0.36 / 0.82 + 0.36 * 0.0395 * (160.54 / (0.82 * 160.54 - 0.6933) ^ 2) +
      jV 160.54 0.18 expL + 0.00985 * etaT (0.82 * 160.54 - 0.6933) / (0.18 * 160.54 - 1e-9) ≤
      0.033 * (1 - 1 / 160.54) := by
  norm_num [etaT, jV, expL, kq]

set_option maxHeartbeats 2000000 in
/-- **The step beyond the cells**: `|N(n)| ≤ ν∞ n` on `[T, D)` gives `|N(D)| ≤ ν∞ D`. -/
theorem tail_step {D : ℕ} (hD : TT ≤ D) (hN : ∀ n, TT ≤ n → n < D → |Nn n| ≤ 0.033 * n) :
    |Nn D| ≤ 0.033 * D := by
  have hT := logT_ge
  have hT0 : 0 < TT := lt_of_lt_of_le (by norm_num [X0]) X0_lt_T
  have hD0' : 0 < D := lt_of_lt_of_le hT0 hD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD0'
  set L := Real.log D with hLdef
  have hL : 160.54 ≤ L := le_trans hT (Real.log_le_log (by exact_mod_cast hT0) (by exact_mod_cast hD))
  have hL0 : 0 < L := by linarith
  have hDexp : Real.exp L = D := Real.exp_log hD0
  -- `y = ⌊D^{0.18}⌋`
  set y := ⌊Real.exp (0.18 * L)⌋₊ with hydef
  obtain ⟨y1, y2, y3, y4⟩ := vfloor (D := D) (x := 0.18 * L) (by linarith) (by linarith) (by omega)
  rw [← hydef] at y1 y2 y3 y4
  have hy6 : 10 ^ 6 ≤ y := le_trans (by norm_num) y1
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hy1 : Real.exp (0.18 * L) < (y : ℝ) + 1 := Nat.lt_floor_add_one _
  have hly1 : 0.18 * L ≤ Real.log ((y : ℝ) + 1) := by
    rw [← Real.log_exp (0.18 * L)]; exact Real.log_le_log (Real.exp_pos _) hy1.le
  have hly1' : Real.log ((y : ℝ) + 1) ≤ 0.18 * L + 1e-9 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((y : ℝ) + 1) / y by positivity)
    rw [Real.log_div (by linarith) hy0.ne'] at this
    have e : ((y : ℝ) + 1) / y - 1 = 1 / y := by field_simp; ring
    have hy12 : (1e12 : ℝ) ≤ y := by
      have : ((1000000000000 : ℕ) : ℝ) ≤ y := by exact_mod_cast y1
      norm_num at this ⊢; linarith
    have : 1 / (y : ℝ) ≤ 1e-9 := by rw [div_le_iff₀ hy0]; linarith
    linarith
  have hU0 : (U0 : ℝ) ≤ Real.exp 131.25 := by
    have hU : (0 : ℝ) < U0 := by norm_num [U0]
    rw [← Real.exp_log hU]; exact Real.exp_le_exp.2 logU0_le
  have hUy1 : U0 * (y + 1) ≤ D := by
    have h1 : (y : ℝ) + 1 ≤ Real.exp (0.18 * L + 1e-9) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < (y : ℝ) + 1)]; exact Real.exp_le_exp.2 hly1'
    have h2 : (U0 : ℝ) * ((y : ℝ) + 1) ≤ D := by
      calc (U0 : ℝ) * ((y : ℝ) + 1) ≤ Real.exp 131.25 * Real.exp (0.18 * L + 1e-9) :=
            mul_le_mul hU0 h1 (by positivity) (by positivity)
        _ = Real.exp (131.25 + (0.18 * L + 1e-9)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp L := Real.exp_le_exp.2 (by linarith)
        _ = D := hDexp
    exact_mod_cast h2
  have hUy : U0 * y ≤ D := le_trans (Nat.mul_le_mul_left _ (by omega)) hUy1
  -- the identity
  have hNabs := N_abs_le (D := D) (Y := y) (by omega) y2
  have hMD := M_D_bound hD hN
  have hK := ksum_tail hN hL hy6 hUy y4
  -- the `j`-sum
  have hjok : jOK D ((y + 1 : ℕ), 0.18 * L - 1e-9, 0.18 * L + 1e-9) (expL.map (pt L)) := by
    simp only [expL, List.map_cons]
    refine ⟨by omega, ?_, by linarith, by push_cast; linarith, by push_cast; linarith, ?_⟩
    · simp only [pt]
      refine Nat.le_floor ?_
      have : (y : ℝ) + 1 ≤ Real.exp (0.18 * L + 1e-9) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (y : ℝ) + 1)]; exact Real.exp_le_exp.2 hly1'
      push_cast; exact le_trans this (Real.exp_le_exp.2 (by linarith))
    · have := jOK_pt (D := D) (by omega) hLdef hL0 [0.2592, 0.311, 0.3732, 0.4479, 0.5375, 0.645, 0.774, 0.9288]
        0.216 (by linarith) (by norm_num) (by norm_num [srt]) (by intro c hc; simp at hc; rcases hc with h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num)
      simpa using this
  have hJ := jT_spec (D := D) _ _ hjok
  rw [show D / ((y + 1 : ℕ), 0.18 * L - 1e-9, 0.18 * L + 1e-9).1 = D / (y + 1) from rfl] at hJ
  rw [jT_pt L expL _ 0.18 rfl] at hJ
  -- the boundary term
  set l2 := 0.82 * L - 0.6933 with hl2
  have hl20 : 0 < l2 := by linarith
  have hBd : |ρn y| * |Mn (D / (y + 1))| ≤ D * (0.00985 * etaT l2 / (0.18 * L - 1e-9)) := by
    have hr := rho_C5 y1
    have hu1 : U0 ≤ D / (y + 1) := (Nat.le_div_iff_mul_le (by omega)).2 hUy1
    have hu2 : D / (y + 1) < D := Nat.div_lt_self hD0' (by omega)
    have hM := M_unif hN hu1 hu2
    have hlu := log_div_nat_ge (D := D) (k := y + 1) (by omega) (by
      calc y + 1 ≤ U0 * (y + 1) := Nat.le_mul_of_pos_left _ (by norm_num [U0])
        _ ≤ D := hUy1)
    push_cast at hlu
    have he := eta_anti (l := l2) (u := Real.log ((D / (y + 1) : ℕ) : ℝ)) hl20 (by linarith)
    have hM' : |Mn (D / (y + 1))| ≤ etaT l2 * ((D : ℝ) / ((y : ℝ) + 1)) := by
      refine le_trans hM (le_trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)) ?_)
      have : ((D / (y + 1) : ℕ) : ℝ) ≤ (D : ℝ) / ((y : ℝ) + 1) := by
        have := Nat.cast_div_le (α := ℝ) (m := D) (n := y + 1); push_cast at this; exact this
      have : 0 ≤ etaT l2 := by unfold etaT; positivity
      unfold etaT at *; nlinarith
    have hly0 : 0 < Real.log y := by linarith
    have hη0 : 0 ≤ etaT l2 := by unfold etaT; positivity
    calc |ρn y| * |Mn (D / (y + 1))| ≤ (0.00985 * y / Real.log y) * (etaT l2 * ((D : ℝ) / ((y : ℝ) + 1))) :=
          mul_le_mul hr hM' (abs_nonneg _) (by positivity)
      _ = (0.00985 * etaT l2 * D) * ((y : ℝ) / ((y : ℝ) + 1)) / Real.log y := by field_simp
      _ ≤ (0.00985 * etaT l2 * D) * 1 / Real.log y := by
          gcongr; rw [div_le_one (by positivity)]; linarith
      _ ≤ (0.00985 * etaT l2 * D) * 1 / (0.18 * L - 1e-9) := by
          gcongr; linarith
      _ = D * (0.00985 * etaT l2 / (0.18 * L - 1e-9)) := by ring
  -- `C₀ + I ≤ 0.0059 D/L²`
  have hK0 := K0_le
  have hf := f_mono (a := TT) (b := D) (by linarith) hD
  have hK0' : 626 + (d213.I' : ℝ) ≤ 0.0059 * (D / L ^ 2) :=
    le_trans hK0 (mul_le_mul_of_nonneg_left hf (by norm_num))
  have h1D : (1 : ℝ) ≤ 1e-9 * D := by
    have : (1e57 : ℝ) ≤ D := by
      have := hUy; have h' : ((U0 * y : ℕ) : ℝ) ≤ D := by exact_mod_cast this
      push_cast at h'; norm_num [U0] at h'
      have : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
      nlinarith
    linarith
  -- the bound `Ψ(L)`
  set Ψ := 1e-9 + 0.039329 / L ^ 2 + (19925014134314 / 1000000000000 * etaT (L - 14.5089) +
    (0.36 * L - 26.8787) * etaT l2) + jV L 0.18 expL + 0.00985 * etaT l2 / (0.18 * L - 1e-9) with hΨ
  have hmain : |Nn D| * (1 - 1 / L) ≤ D * Ψ := by
    have e1 : |Nn D| / L = |Nn D| * (1 / L) := by ring
    have e2 : (D : ℝ) * Ψ = 1e-9 * D + 0.039329 * (D / L ^ 2) + D * (19925014134314 / 1000000000000 * etaT (L - 14.5089) +
        (0.36 * L - 26.8787) * etaT l2) + D * jV L 0.18 expL + D * (0.00985 * etaT l2 / (0.18 * L - 1e-9)) := by
      rw [hΨ]; ring
    rw [e2]
    have : 0.033 * 1.013 * ((D : ℝ) / L ^ 2) + 0.0059 * (D / L ^ 2) ≤ 0.039329 * (D / L ^ 2) := by
      have : (0 : ℝ) ≤ D / L ^ 2 := by positivity
      nlinarith
    nlinarith
  -- `Ψ(L) ≤ Ψ(L₀) ≤ ν∞ (1 − 1/L₀)`
  have hΨle : Ψ ≤ 0.033 * (1 - 1 / L) := by
    have a1 : 0.039329 / L ^ 2 ≤ 0.039329 / 160.54 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 2)
    have a2 : etaT (L - 14.5089) ≤ etaT (160.54 - 14.5089) := eta_anti (by norm_num) (by linarith)
    have a3 : (0.36 * L - 26.8787) * (0.033 / l2) ≤ 0.033 * 0.36 / 0.82 := by
      rw [mul_div_assoc', div_le_div_iff₀ hl20 (by norm_num)]; nlinarith
    have a4 : (0.36 * L - 26.8787) * (0.0395 / l2 ^ 2) ≤ 0.36 * 0.0395 * (160.54 / (0.82 * 160.54 - 0.6933) ^ 2) := by
      have h1 : (0.36 * L - 26.8787) * (0.0395 / l2 ^ 2) ≤ 0.36 * 0.0395 * (L / l2 ^ 2) := by
        rw [show 0.36 * 0.0395 * (L / l2 ^ 2) = (0.36 * L) * (0.0395 / l2 ^ 2) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h2 : L / l2 ^ 2 ≤ 160.54 / (0.82 * 160.54 - 0.6933) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num), hl2]
        nlinarith [mul_nonneg (sub_nonneg.2 hL) (sub_nonneg.2 hL), sub_nonneg.2 hL]
      nlinarith
    have a5 : jV L 0.18 expL ≤ jV 160.54 0.18 expL :=
      jV_anti hL (by norm_num) _ 0.18 (by norm_num) (by norm_num) (by norm_num [srt, expL])
        (by intro c hc; simp [expL] at hc; rcases hc with h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num)
    have a6 : 0.00985 * etaT l2 / (0.18 * L - 1e-9) ≤ 0.00985 * etaT (0.82 * 160.54 - 0.6933) / (0.18 * 160.54 - 1e-9) := by
      have e1 : etaT l2 ≤ etaT (0.82 * 160.54 - 0.6933) := eta_anti (by norm_num) (by linarith)
      have e0 : 0 ≤ etaT l2 := by unfold etaT; positivity
      apply div_le_div₀ (by unfold etaT; norm_num) (by linarith) (by norm_num) (by linarith)
    have a7 : 0.033 * (1 - 1 / 160.54) ≤ 0.033 * (1 - 1 / L) := by
      have : 1 / L ≤ 1 / 160.54 := one_div_le_one_div_of_le (by norm_num) hL
      linarith
    have hn := numeric_tail
    have e : (0.36 * L - 26.8787) * etaT l2 = (0.36 * L - 26.8787) * (0.033 / l2) +
        (0.36 * L - 26.8787) * (0.0395 / l2 ^ 2) := by unfold etaT; ring
    have hG : (0 : ℝ) ≤ 19925014134314 / 1000000000000 := by norm_num
    have a2' := mul_le_mul_of_nonneg_left a2 hG
    rw [hΨ, e]; linarith
  have h1L : 0 < 1 - 1 / L := by
    have : 1 / L < 1 := by rw [div_lt_one hL0]; linarith
    linarith
  have := le_trans hmain (mul_le_mul_of_nonneg_left hΨle hD0.le)
  have e : (D : ℝ) * (0.033 * (1 - 1 / L)) = 0.033 * D * (1 - 1 / L) := by ring
  rw [e] at this
  exact le_of_mul_le_mul_right this h1L

/-- **`|N(D)| ≤ 0.033 D` for `D ≥ T`.** -/
theorem N_tail : ∀ D, TT ≤ D → |Nn D| ≤ 0.033 * D := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro hD
    exact tail_step hD fun n h1 h2 => ih n h2 h1

/-- **`|M(u)| ≤ (0.033/log u + 0.0395/log²u) u` for `u ≥ T`.** -/
theorem M_tail {u : ℕ} (hu : TT ≤ u) : |Mn u| ≤ (0.033 / Real.log u + 0.0395 / Real.log u ^ 2) * u :=
  M_above hu fun n h1 _ => N_tail n h1

end TernaryGoldbach.Prelim.Sch
