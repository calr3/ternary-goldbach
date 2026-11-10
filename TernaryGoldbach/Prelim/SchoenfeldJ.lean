import TernaryGoldbach.Prelim.SchoenfeldStep
import TernaryGoldbach.Prelim.EOneRanges
import TernaryGoldbach.Prelim.ThetaExplicit

/-!
# The `j`-sum of Schoenfeld's identity

`ρ(v) = ψ(v) − v`. `rho_le`: `|ρ(v)| ≤ 2√v + [v ≥ 10⁹] 35.5√v + [v > 3.2·10¹⁰] 72√v +
[v ≥ 10¹²] v (1/log³v + 4.92·10⁻⁷ + 1.4262/√v)` for `v ≥ 12` (at each `v` one term suffices; the
others are non-negative).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sch
open TernaryGoldbach.Prelim.Sqf (sq kap Q1)

theorem rho_eq (v : ℕ) : ρn v = psiN v - v := by
  unfold ρn psiN
  rw [show Ioc 0 v = Icc 1 v by ext; simp; omega, sum_sub_distrib]
  simp

/-- `ε(v) = 1/log³v + 4.92·10⁻⁷ + 1.4262/√v`. -/
noncomputable def epsv (v : ℝ) : ℝ := 1 / Real.log v ^ 3 + 4.92e-7 + 1.4262 / √v

/-- The bound for `|ρ(v)|`. -/
noncomputable def rb (v : ℕ) : ℝ :=
  2 * √(v : ℝ) + (if 1000000000 ≤ v then 35.5 * √(v : ℝ) else 0) +
    (if 32000000000 < v then 72 * √(v : ℝ) else 0) + (if 1000000000000 ≤ v then epsv v * v else 0)

variable [Fact TernaryGoldbach.PlattGRH]

theorem rho_le {v : ℕ} (hv : 12 ≤ v) : |ρn v| ≤ rb v := by
  rw [rho_eq]
  have hs := Real.sqrt_nonneg (v : ℝ)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  unfold rb
  rcases lt_or_ge v 1000000000 with h1 | h1
  · have := psi_le_two hv h1
    have e1 : ¬ 32000000000 < v := by omega
    have e2 : ¬ 1000000000000 ≤ v := by omega
    simp only [show ¬ 1000000000 ≤ v by omega, e1, e2, if_false]; linarith
  rcases le_or_gt v 32000000000 with h2 | h2
  · have h := psi_two_sided hv (by omega)
    have hc := cB_le_355 h2
    have : cB v * √(v : ℝ) ≤ 35.5 * √(v : ℝ) := mul_le_mul_of_nonneg_right hc hs
    unfold psiN
    simp only [h1, if_true, show ¬ 32000000000 < v by omega, show ¬ 1000000000000 ≤ v by omega, if_false]
    linarith
  rcases lt_or_ge v 1000000000000 with h3 | h3
  · have h := psi_two_sided hv (by omega)
    have hc := cB_le_72 (by omega : v ≤ 10 ^ 15)
    have : cB v * √(v : ℝ) ≤ 72 * √(v : ℝ) := mul_le_mul_of_nonneg_right hc hs
    unfold psiN
    simp only [h1, h2, if_true, show ¬ 1000000000000 ≤ v by omega, if_false]
    nlinarith
  · -- `θ` explicit and `ψ − θ < 1.4262 √v`
    have ht := theta_explicit h3
    have hnp := sum_vonMangoldt_nonprime_lt (y := (v : ℝ)) hv0
    rw [Nat.floor_natCast] at hnp
    have hsplit : psiN v = ∑ p ∈ (Icc 1 v).filter Nat.Prime, Real.log p +
        ∑ n ∈ Icc 1 v, (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ)) := by
      unfold psiN
      rw [Finset.sum_filter, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      by_cases hp : n.Prime
      · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      · simp [hp]
    have hnp0 : 0 ≤ ∑ n ∈ Icc 1 v, (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℝ)) :=
      sum_nonneg fun n _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
    have hep := epl_le (v : ℝ)
    have hlog : 0 < Real.log v := Real.log_pos (by exact_mod_cast (by omega : 1 < v))
    have e : epsv v * v = v / Real.log v ^ 3 + 4.92e-7 * v + 1.4262 * √(v : ℝ) := by
      unfold epsv
      have hsv := Real.mul_self_sqrt hv0.le
      have : √(v : ℝ) ≠ 0 := (Real.sqrt_pos.2 hv0).ne'
      field_simp; nlinarith [hsv]
    simp only [h1, h2, h3, if_true]
    rw [e, hsplit]
    rw [abs_lt] at ht
    have : epl (v : ℝ) * v ≤ 4.92e-7 * v := mul_le_mul_of_nonneg_right hep hv0.le
    rw [abs_le]; constructor <;> nlinarith [hs]

/-! ### Summing over `m` -/

omit [Fact TernaryGoldbach.PlattGRH] in
/-- `SS(J) = 2κ√J + 4.5 + 1.5 log J` bounds `∑_{m ≤ J} μ²(m)/√m` (and `0` for `J = 0`). -/
theorem sum_sq_sqrt_le (J : ℕ) :
    ∑ m ∈ Ioc 0 J, sq m / √(m : ℝ) ≤ (if J = 0 then 0 else 2 * kap * √(J : ℝ) + 4.5 + 1.5 * Real.log J) := by
  split_ifs with h
  · subst h; simp
  · rw [show Ioc 0 J = Icc 1 J by ext; simp; omega]
    exact Sqf.sum_sq_div_sqrt J (by omega)

omit [Fact TernaryGoldbach.PlattGRH] in
theorem sq_div_sqrt_term {D m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 ≤ c) :
    sq m * (c * √((D / m : ℕ) : ℝ)) ≤ c * √(D : ℝ) * (sq m / √(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : ((D / m : ℕ) : ℝ) ≤ (D : ℝ) / m := Nat.cast_div_le
  have hsu : √((D / m : ℕ) : ℝ) ≤ √(D : ℝ) / √(m : ℝ) := by
    rw [← Real.sqrt_div' _ hm0.le]; exact Real.sqrt_le_sqrt hu
  have := Sqf.sq_nonneg m
  calc sq m * (c * √((D / m : ℕ) : ℝ)) ≤ sq m * (c * (√(D : ℝ) / √(m : ℝ))) := by gcongr
    _ = c * √(D : ℝ) * (sq m / √(m : ℝ)) := by ring

omit [Fact TernaryGoldbach.PlattGRH] in
/-- A `√`-piece: `∑_{m ≤ D/(Y+1)} μ²(m) [D/m ≥ a] c √(D/m) ≤ c √D SS(D/a)`. -/
theorem sqrt_piece {D Y a : ℕ} (ha : 1 ≤ a) {c : ℝ} (hc : 0 ≤ c) :
    ∑ m ∈ Ioc 0 (D / (Y + 1)), sq m * (if a ≤ D / m then c * √((D / m : ℕ) : ℝ) else 0) ≤
      c * √(D : ℝ) * (if D / a = 0 then 0 else 2 * kap * √((D / a : ℕ) : ℝ) + 4.5 + 1.5 * Real.log (D / a : ℕ)) := by
  have hsub : ∀ m ∈ Ioc 0 (D / (Y + 1)), sq m * (if a ≤ D / m then c * √((D / m : ℕ) : ℝ) else 0) ≤
      if m ∈ Ioc 0 (D / a) then c * √(D : ℝ) * (sq m / √(m : ℝ)) else 0 := by
    intro m hm
    have hm1 : 1 ≤ m := (mem_Ioc.1 hm).1
    split_ifs with h1 h2 h2
    · exact sq_div_sqrt_term hm1 hc
    · exfalso; apply h2; refine mem_Ioc.2 ⟨by omega, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      have := (Nat.le_div_iff_mul_le (by omega)).1 h1
      linarith [mul_comm m a]
    · simp
    · simp
  refine (sum_le_sum hsub).trans ?_
  rw [← sum_filter]
  have hss : ∀ m ∈ (Ioc 0 (D / (Y + 1))).filter (fun m => m ∈ Ioc 0 (D / a)), 0 ≤ c * √(D : ℝ) * (sq m / √(m : ℝ)) :=
    fun m _ => mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg (Sqf.sq_nonneg m) (Real.sqrt_nonneg _))
  calc ∑ m ∈ (Ioc 0 (D / (Y + 1))).filter (fun m => m ∈ Ioc 0 (D / a)), c * √(D : ℝ) * (sq m / √(m : ℝ))
      ≤ ∑ m ∈ Ioc 0 (D / a), c * √(D : ℝ) * (sq m / √(m : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (fun m hm => (mem_filter.1 hm).2) fun m _ _ =>
          mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg (Sqf.sq_nonneg m) (Real.sqrt_nonneg _))
    _ = c * √(D : ℝ) * ∑ m ∈ Ioc 0 (D / a), sq m / √(m : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_sq_sqrt_le _) (mul_nonneg hc (Real.sqrt_nonneg _))

/-! ### The part `v ≥ 10¹²` -/

omit [Fact TernaryGoldbach.PlattGRH] in
theorem epsv_anti {a b : ℝ} (ha : 1000000000000 ≤ a) (hab : a ≤ b) : epsv b ≤ epsv a := by
  unfold epsv
  have ha0 : 0 < a := by linarith
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hl : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have h1 : 1 / Real.log b ^ 3 ≤ 1 / Real.log a ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hla.le hl 3)
  have h2 : 1.4262 / √b ≤ 1.4262 / √a :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 ha0) (Real.sqrt_le_sqrt hab)
  linarith

omit [Fact TernaryGoldbach.PlattGRH] in
theorem epsv_nonneg {a : ℝ} (ha : 1 ≤ a) : 0 ≤ epsv a := by
  unfold epsv; have := Real.log_nonneg ha; positivity

/-- The term of the part `v ≥ 10¹²`. -/
noncomputable def tE (D m : ℕ) : ℝ := sq m * (epsv ((D / m : ℕ) : ℝ) * ((D / m : ℕ) : ℝ))

omit [Fact TernaryGoldbach.PlattGRH] in
theorem Q1_nat_sub {a b : ℕ} (hab : a ≤ b) :
    Q1 (b : ℝ) - Q1 (a : ℝ) = ∑ m ∈ Ioc a b, sq m / m := by
  unfold Q1
  rw [Nat.floor_natCast, Nat.floor_natCast, show Icc 1 b = Ioc 0 b by ext; simp; omega,
    show Icc 1 a = Ioc 0 a by ext; simp; omega, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

omit [Fact TernaryGoldbach.PlattGRH] in
/-- One piece `V ≤ D/m < W`: `∑ tE ≤ D ε(V) (κ log(W/V) + 0.588)`. -/
theorem eps_piece {D V W : ℕ} (hV : 1000000000000 ≤ V) (hVW : V ≤ W) (hWD : W ≤ D) :
    ∑ m ∈ Ioc (D / W) (D / V), tE D m ≤ D * (epsv V * (kap * Real.log ((W : ℝ) / V) + 0.588)) := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast (by omega : 0 < V)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hepsV := epsv_nonneg (a := (V : ℝ)) (by exact_mod_cast (by omega : 1 ≤ V))
  have hterm : ∀ m ∈ Ioc (D / W) (D / V), tE D m ≤ D * epsv V * (sq m / m) := by
    intro m hm
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hm
    have hm1 : 1 ≤ m := by omega
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hvV : V ≤ D / m := by
      rw [Nat.le_div_iff_mul_le hm1]; have := (Nat.le_div_iff_mul_le (by omega)).1 h2; linarith [mul_comm m V]
    have hvV' : (V : ℝ) ≤ ((D / m : ℕ) : ℝ) := by exact_mod_cast hvV
    have he := epsv_anti (by exact_mod_cast hV) hvV'
    have hv : ((D / m : ℕ) : ℝ) ≤ (D : ℝ) / m := Nat.cast_div_le
    have hsq := Sqf.sq_nonneg m
    have hev := epsv_nonneg (a := ((D / m : ℕ) : ℝ)) (by exact_mod_cast (le_trans (by omega : 1 ≤ V) hvV))
    unfold tE
    calc sq m * (epsv ((D / m : ℕ) : ℝ) * ((D / m : ℕ) : ℝ)) ≤ sq m * (epsv V * ((D : ℝ) / m)) := by
          gcongr
      _ = D * epsv V * (sq m / m) := by ring
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
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiff hepsV) hD0.le |>.trans (le_of_eq (by ring))

omit [Fact TernaryGoldbach.PlattGRH] in
/-- The last piece `D/m ≥ V`: `∑ tE ≤ D ε(V) (κ log(D/V) + 1.166)`. -/
theorem eps_last {D V : ℕ} (hV : 1000000000000 ≤ V) (hVD : V ≤ D) :
    ∑ m ∈ Ioc 0 (D / V), tE D m ≤ D * (epsv V * (kap * Real.log ((D : ℝ) / V) + 1.166)) := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast (by omega : 0 < V)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hepsV := epsv_nonneg (a := (V : ℝ)) (by exact_mod_cast (by omega : 1 ≤ V))
  have hterm : ∀ m ∈ Ioc 0 (D / V), tE D m ≤ D * epsv V * (sq m / m) := by
    intro m hm
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hm
    have hm1 : 1 ≤ m := by omega
    have hvV : V ≤ D / m := by
      rw [Nat.le_div_iff_mul_le hm1]; have := (Nat.le_div_iff_mul_le (by omega)).1 h2; linarith [mul_comm m V]
    have hvV' : (V : ℝ) ≤ ((D / m : ℕ) : ℝ) := by exact_mod_cast hvV
    have he := epsv_anti (by exact_mod_cast hV) hvV'
    have hv : ((D / m : ℕ) : ℝ) ≤ (D : ℝ) / m := Nat.cast_div_le
    have hsq := Sqf.sq_nonneg m
    have hev := epsv_nonneg (a := ((D / m : ℕ) : ℝ)) (by exact_mod_cast (le_trans (by omega : 1 ≤ V) hvV))
    unfold tE
    calc sq m * (epsv ((D / m : ℕ) : ℝ) * ((D / m : ℕ) : ℝ)) ≤ sq m * (epsv V * ((D : ℝ) / m)) := by
          gcongr
      _ = D * epsv V * (sq m / m) := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have e0 : ∑ m ∈ Ioc 0 (D / V), sq m / (m : ℝ) = Q1 ((D : ℝ) / V) := by
    unfold Q1; rw [Nat.floor_div_eq_div, show Icc 1 (D / V) = Ioc 0 (D / V) by ext; simp; omega]
  rw [e0]
  have hA : (1 : ℝ) ≤ (D : ℝ) / V := by rw [le_div_iff₀ hV0]; exact_mod_cast (by omega : 1 * V ≤ D)
  have hb := (Sqf.Eq1_bounds hA).2
  unfold Sqf.Eq1 at hb
  have : Q1 ((D : ℝ) / V) ≤ kap * Real.log ((D : ℝ) / V) + 1.166 := by linarith
  calc (D : ℝ) * epsv V * Q1 ((D : ℝ) / V) ≤ D * epsv V * (kap * Real.log ((D : ℝ) / V) + 1.166) :=
        mul_le_mul_of_nonneg_left this (mul_nonneg hD0.le hepsV)
    _ = _ := by ring

end TernaryGoldbach.Prelim.Sch
