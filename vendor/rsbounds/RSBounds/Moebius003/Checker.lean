/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.JSum
import RSBounds.Moebius003.Step
import RSBounds.Moebius003.Schoenfeld
import RSBounds.Moebius003.CellsDefs

/-!
# The checker for the cells of §4 of the note, and its soundness

`checkCells` runs Proposition 8 and Corollary 9 over a list of cells with rational data:
endpoints `D₋ < D₊`, the parameter `y`, the block endpoints of the `k`-sum, and the claimed
`ν`, `η` (rounded up). The running sums `I` and `T` are recomputed and rounded up. `checkCells_sound`
shows that a successful check gives `(H_i)` on every cell, the profile bounds needed by
Proposition 10, and the theorem on `[X₀, D_end)`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius

/-- The data of one cell; `ν` and `η` are given in units of `10⁻¹²`. -/
structure CellIn where
  Dlo : ℕ
  Dhi : ℕ
  y : ℕ
  bs : List ℕ
  nuN : ℕ
  etaN : ℕ

/-- `ν` of the cell. -/
def CellIn.nu (c : CellIn) : ℚ := (c.nuN : ℚ) / 10 ^ 12

/-- `η` of the cell. -/
def CellIn.eta (c : CellIn) : ℚ := (c.etaN : ℚ) / 10 ^ 12

/-- The state after the cells checked so far. -/
structure CState where
  prev : List CellRec
  D : ℕ
  I : ℚ
  T : ℚ

/-- Rounding up to a multiple of `2⁻⁴⁰`. -/
def roundUp (q : ℚ) : ℚ := (LogCert.qceil (q * 2 ^ 40) : ℚ) / 2 ^ 40

theorem le_roundUp (q : ℚ) : q ≤ roundUp q := by
  unfold roundUp
  rw [le_div_iff₀ (by positivity), LogCert.qceil_eq]
  exact Int.le_ceil _

def C0Bq : ℚ := 1743
def I0Bq : ℚ := 36113

/-- `K` (the `k`-sum and the `ρ(y)` term, divided by `D`). -/
def cellK (prev : List CellRec) (c : CellIn) (sD sy : ℚ) : Option ℚ :=
  match ksumW prev c.Dlo c.Dhi sD 1 c.bs with
  | some K => some (K + rhoW prev c.Dlo c.Dhi c.y sD sy)
  | none => none

/-- The checks of Proposition 8 and Corollary 9 for one cell, given `K`. -/
def cellOkK (st : CState) (c : CellIn) (K : ℚ) : Bool :=
  let Lm := LogCert.logLo c.Dlo
  let Lp := LogCert.logHi c.Dhi
  let sD := LogCert.sqrtLo c.Dlo
  let sy := LogCert.sqrtLo c.y
  let X := 1 / (c.Dlo : ℚ) + K + jW c.Dlo c.Dhi c.y sD sy Lm Lp
  let δ := 1 - (c.Dlo : ℚ) / c.Dhi
  decide (st.D = c.Dlo) && decide (X0 ≤ c.Dlo) && decide (c.Dlo < c.Dhi) &&
  decide (c.Dhi ≤ 2 * c.Dlo) && decide (1500 ≤ c.y) && decide (c.y ≤ 2 ^ 20) &&
  decide (33 * c.y ≤ c.Dlo) && decide (endOf 1 c.bs = c.y) && decide (0 < sD) && decide (0 < sy) &&
  decide (1 < Lm) && decide (0 ≤ c.nu) &&
  decide (X + (C0Bq + st.I) / c.Dlo ≤ c.nu * (1 - 1 / Lm - δ / Lm ^ 2)) &&
  decide (c.nu / Lm + (C0Bq + st.I) / c.Dlo + c.nu * δ / Lm ^ 2 ≤ c.eta) &&
  decide (Lp * (c.eta + max ((I0Bq + st.T) / c.Dlo) ((I0Bq + st.T + c.eta * (c.Dhi - c.Dlo)) / c.Dhi) +
    Lp / c.Dlo) ≤ 3 / 100) &&
  decide (c.nu ≤ 17 / 1000) && (decide (c.Dhi ≤ Dmid) || decide (c.nu ≤ 14 / 1000))

/-- The check for one cell. -/
def cellOk (st : CState) (c : CellIn) : Bool :=
  match cellK st.prev c (LogCert.sqrtLo c.Dlo) (LogCert.sqrtLo c.y) with
  | some K => cellOkK st c K
  | none => false

/-- The state after a cell. -/
def nextState (st : CState) (c : CellIn) : CState :=
  { prev := (c.Dlo, c.Dhi, c.eta) :: st.prev
    D := c.Dhi
    I := roundUp (st.I + c.nu * (c.Dhi - c.Dlo) / (LogCert.logLo c.Dlo) ^ 2)
    T := roundUp (st.T + c.eta * (c.Dhi - c.Dlo)) }

/-- The check over a list of cells. -/
def checkCells : CState → List CellIn → Bool
  | st, [] => decide (st.D = Dend)
  | st, c :: rest => cellOk st c && checkCells (nextState st c) rest

/-- The initial state. -/
def st0 : CState := { prev := [], D := X0, I := 0, T := 0 }

/-! ### Soundness -/

/-- The invariant. -/
structure StateOK (st : CState) : Prop where
  prof : ProfileOK st.prev st.D
  bnd : ∀ c ∈ st.prev, c.2.1 ≤ st.D
  hX : X0 ≤ st.D
  hI : Iint X0 st.D ≤ st.I
  hT : ∑ t ∈ Ico X0 st.D, |M t| * Real.log (1 + 1 / (t : ℝ)) ≤ st.T
  nuBar : ∀ n : ℕ, X0 ≤ n → n < st.D → |N n| ≤ 0.017 * n
  nuInf : ∀ n : ℕ, Dmid ≤ n → n < st.D → |N n| ≤ 0.014 * n
  mB : ∀ n : ℕ, X0 ≤ n → n < st.D → |msum n| * Real.log (n + 1) ≤ 0.03

theorem st0_ok : StateOK st0 where
  prof := ⟨by simp [st0], fun u h1 h2 => by simp [st0] at h2; omega, by simp [st0], by simp [st0]⟩
  bnd := by simp [st0]
  hX := le_rfl
  hI := by simp [st0, Iint]
  hT := by simp [st0]
  nuBar := fun n h1 h2 => by simp [st0] at h2; omega
  nuInf := fun n h1 h2 => by
    simp [st0] at h2
    exfalso; have : Dmid ≤ X0 := le_trans h1 h2.le; unfold Dmid X0 at this; omega
  mB := fun n h1 h2 => by simp [st0] at h2; omega

/-- Step 1 of Proposition 8: `|N(D)| ≤ |M(D)| + D·X` on the cell. -/
theorem cell_NM (h : Inputs) {st : CState} (hst : StateOK st) {c : CellIn} {K : ℚ}
    (hK : cellK st.prev c (LogCert.sqrtLo c.Dlo) (LogCert.sqrtLo c.y) = some K)
    (hD : st.D = c.Dlo) (hX0 : X0 ≤ c.Dlo) (h2D : c.Dhi ≤ 2 * c.Dlo) (hy1 : 1500 ≤ c.y)
    (hy2 : c.y ≤ 2 ^ 20) (hy33 : 33 * c.y ≤ c.Dlo) (hend : endOf 1 c.bs = c.y)
    (hsD0 : 0 < LogCert.sqrtLo c.Dlo) (hsy0 : 0 < LogCert.sqrtLo c.y)
    (hLm0 : 0 < LogCert.logLo c.Dlo) :
    ∀ D : ℕ, c.Dlo ≤ D → D < c.Dhi → |N D| ≤ |M D| + D *
      ((1 / (c.Dlo : ℚ) + K + jW c.Dlo c.Dhi c.y (LogCert.sqrtLo c.Dlo) (LogCert.sqrtLo c.y)
        (LogCert.logLo c.Dlo) (LogCert.logHi c.Dhi) : ℚ) : ℝ) := by
  intro D hD1 hD2
  have hP : ProfileOK st.prev c.Dlo := hD ▸ hst.prof
  have hsD := LogCert.sqrtLo_le (c.Dlo : ℚ)
  have hsy := LogCert.sqrtLo_le (c.y : ℚ)
  push_cast at hsD hsy
  have hLm := LogCert.logLo_le (q := (c.Dlo : ℚ)) (by
    have : (0 : ℚ) < c.Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < c.Dlo)
    exact this)
  have hLp := LogCert.le_logHi (q := (c.Dhi : ℚ)) (by
    have : (0 : ℚ) < c.Dhi := by exact_mod_cast (by omega : 0 < c.Dhi)
    exact this)
  push_cast at hLm hLp
  unfold cellK at hK
  split at hK
  · rename_i Kb hKb
    simp only [Option.some.injEq] at hK
    subst hK
    have hks := ksum_bound h hP hX0 h2D hD1 hD2 hsD0 hsD 1 c.bs Kb le_rfl hKb
    rw [hend] at hks
    have hrho := rho_y_bound h hP hX0 h2D hy1 hy2 hy33 hD1 hD2 hsD0 hsD hsy0 hsy
    have hj := jsum_bound h hX0 hy1 hy2 hy33 hD1 hD2 hsD0 hsD hsy0 hsy hLm0 hLm hLp
    have hyD : c.y ≤ D := by omega
    have hS := schoenfeld_identity (x := D) (y := c.y) (by omega) hyD
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < D)
    have hDlopos : (0 : ℝ) < c.Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < c.Dlo)
    -- `|∑_{2 ≤ k ≤ y} (Λ(k) − 1) M(D/k)| ≤ ∑ |Λ(k) − 1| |M(D/k)|`
    have hk : |∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k)| ≤ ∑ k ∈ Ioc 1 c.y, |Λ k - 1| * |M (D / k)| := by
      have e : Icc 2 c.y = Ioc 1 c.y := by ext; simp; omega
      rw [e]
      refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact sum_congr rfl fun k _ => abs_mul _ _
    have h1 : (1 : ℝ) ≤ D * (1 / c.Dlo) := by
      rw [mul_one_div, le_div_iff₀ hDlopos, one_mul]; exact_mod_cast hD1
    have hN : |N D| ≤ |M D| + 1 + |∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k)| +
        |∑ j ∈ Icc 1 (D / c.y), (μ j : ℝ) * ρ (D / j)| + |ρ c.y| * |M (D / c.y)| := by
      have e : N D = M D - ∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k) -
          ∑ j ∈ Icc 1 (D / c.y), (μ j : ℝ) * ρ (D / j) + ρ c.y * M (D / c.y) - 1 := by linarith
      rw [e, ← abs_mul]
      calc |M D - ∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k) - ∑ j ∈ Icc 1 (D / c.y), (μ j : ℝ) * ρ (D / j) +
            ρ c.y * M (D / c.y) - 1|
          ≤ |M D| + |∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k)| + |∑ j ∈ Icc 1 (D / c.y), (μ j : ℝ) * ρ (D / j)| +
            |ρ c.y * M (D / c.y)| + |(1 : ℝ)| := by
            have := abs_sub (M D - ∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k) -
              ∑ j ∈ Icc 1 (D / c.y), (μ j : ℝ) * ρ (D / j) + ρ c.y * M (D / c.y)) 1
            have := abs_add_le (M D - ∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k) -
              ∑ j ∈ Icc 1 (D / c.y), (μ j : ℝ) * ρ (D / j)) (ρ c.y * M (D / c.y))
            have := abs_sub (M D - ∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k))
              (∑ j ∈ Icc 1 (D / c.y), (μ j : ℝ) * ρ (D / j))
            have := abs_sub (M D) (∑ k ∈ Icc 2 c.y, (Λ k - 1) * M (D / k))
            linarith
        _ = _ := by rw [abs_one]; ring
    push_cast
    rw [mul_add, mul_add, mul_add]
    linarith
  · simp at hK

theorem cellOk_sound (h : Inputs) {st : CState} (hst : StateOK st) {c : CellIn}
    (hc : cellOk st c = true) : StateOK (nextState st c) := by
  unfold cellOk at hc
  split at hc
  · rename_i K hK
    unfold cellOkK at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hX0⟩, hlt⟩, h2D⟩, hy1⟩, hy2⟩, hy33⟩, hend⟩, hsD0⟩, hsy0⟩, hLm1⟩, hν0⟩,
      hν⟩, hη⟩, hm⟩, hνbar⟩, hνinf⟩ := hc
    set Lm := LogCert.logLo c.Dlo with hLmdef
    set Lp := LogCert.logHi c.Dhi with hLpdef
    have hLm0 : 0 < Lm := lt_trans (by norm_num) hLm1
    have hNM := cell_NM h hst hK hD hX0 h2D hy1 hy2 hy33 hend hsD0 hsy0 hLm0
    have hLm := LogCert.logLo_le (q := (c.Dlo : ℚ)) (by
      have : (0 : ℚ) < c.Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < c.Dlo)
      exact this)
    have hLp := LogCert.le_logHi (q := (c.Dhi : ℚ)) (by
      have : (0 : ℚ) < c.Dhi := by exact_mod_cast (by omega : 0 < c.Dhi)
      exact this)
    push_cast at hLm hLp
    have hI : Iint X0 c.Dlo ≤ (st.I : ℝ) := hD ▸ hst.hI
    have hT : ∑ t ∈ Ico X0 c.Dlo, |M t| * Real.log (1 + 1 / (t : ℝ)) ≤ (st.T : ℝ) := hD ▸ hst.hT
    have hC : C0B = ((C0Bq : ℚ) : ℝ) := by unfold C0B C0Bq; norm_num
    have hI0 : I0B = ((I0Bq : ℚ) : ℝ) := by unfold I0B I0Bq; norm_num
    have hν' := (Rat.cast_le (K := ℝ)).mpr hν
    have hη' := (Rat.cast_le (K := ℝ)).mpr hη
    push_cast at hν' hη'
    rw [← hC] at hν' hη'
    have hLm1' : (1 : ℝ) < Lm := by exact_mod_cast hLm1
    have hν0' : (0 : ℝ) ≤ c.nu := by exact_mod_cast hν0
    have hstep := step_abstract h (ν := c.nu) (η := c.eta) (I := st.I) hX0 hlt hLm1' hLm hI
      (fun D hD1 hD2 => by have := hNM D hD1 hD2; push_cast at this; exact this) hν0'
      (by push_cast at hν'; linarith) hη'
    have hmb := cell_m_bound h (η := c.eta) (T := st.T) (Lp := Lp) hX0 hlt
      (fun n h1 h2 => (hstep n h1 h2).2) hT hLp
    have hm' := (Rat.cast_le (K := ℝ)).mpr hm
    push_cast at hm'
    rw [← hI0] at hm'
    have hDlopos : (0 : ℝ) < c.Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < c.Dlo)
    refine
      { prof := ⟨?_, ?_, ?_, ?_⟩
        bnd := ?_
        hX := ?_
        hI := ?_
        hT := ?_
        nuBar := ?_
        nuInf := ?_
        mB := ?_ }
    · intro r hr u h1 h2
      simp only [nextState, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact (hstep u h1 h2).2
      · exact hst.prof.1 r hr u h1 h2
    · intro u h1 h2
      simp only [nextState] at h2 ⊢
      by_cases hu : u < c.Dlo
      · obtain ⟨r, hr, hr1, hr2⟩ := hst.prof.2.1 u h1 (hD ▸ hu)
        exact ⟨r, List.mem_cons_of_mem _ hr, hr1, hr2⟩
      · exact ⟨(c.Dlo, c.Dhi, c.eta), List.mem_cons_self, by simp; omega, h2⟩
    · simp only [nextState]
      rw [List.pairwise_cons]
      exact ⟨fun r hr => hD ▸ hst.bnd r hr, hst.prof.2.2.1⟩
    · intro r hr
      simp only [nextState, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hlt.le
      · exact hst.prof.2.2.2 r hr
    · intro r hr
      simp only [nextState, List.mem_cons] at hr ⊢
      rcases hr with rfl | hr
      · exact le_rfl
      · exact le_trans (hst.bnd r hr) (hD ▸ hlt.le)
    · simp only [nextState]; omega
    · simp only [nextState]
      rw [Iint_add hX0 hlt.le]
      have h4 := Iint_le (a := c.Dlo) (b := c.Dhi) (by unfold X0 at hX0; omega) hlt.le hν0'
        (by exact_mod_cast hLm0) hLm (fun n h1 h2 => (hstep n h1 h2).1)
      have h5 := le_roundUp (st.I + c.nu * (c.Dhi - c.Dlo) / Lm ^ 2)
      have h5' := (Rat.cast_le (K := ℝ)).mpr h5
      push_cast at h5'
      linarith
    · simp only [nextState]
      rw [← sum_Ico_consecutive _ hX0 hlt.le]
      have h3 : ∑ t ∈ Ico c.Dlo c.Dhi, |M t| * Real.log (1 + 1 / (t : ℝ)) ≤ c.eta * ((c.Dhi : ℝ) - c.Dlo) := by
        have hcard : ((c.Dhi : ℝ) - c.Dlo) = ∑ t ∈ Ico c.Dlo c.Dhi, (1 : ℝ) := by
          simp [Nat.cast_sub hlt.le]
        rw [hcard, mul_sum]
        refine sum_le_sum fun t ht => ?_
        obtain ⟨ht1, ht2⟩ := mem_Ico.1 ht
        have htpos : (0 : ℝ) < t := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < t)
        have hMt := (hstep t ht1 ht2).2
        have hl := log_one_add_inv_le t (by unfold X0 at hX0; omega)
        have hl0 : 0 ≤ Real.log (1 + 1 / (t : ℝ)) := by
          have : 0 ≤ 1 / (t : ℝ) := by positivity
          exact Real.log_nonneg (by linarith)
        calc |M t| * Real.log (1 + 1 / (t : ℝ)) ≤ (c.eta : ℝ) * t * (1 / t) :=
              mul_le_mul hMt hl hl0 (le_trans (abs_nonneg _) hMt)
          _ = c.eta * 1 := by field_simp
      have h5 := le_roundUp (st.T + c.eta * (c.Dhi - c.Dlo))
      have h5' := (Rat.cast_le (K := ℝ)).mpr h5
      push_cast at h5'
      linarith
    · intro n h1 h2
      simp only [nextState] at h2
      by_cases hn : n < c.Dlo
      · exact hst.nuBar n h1 (hD ▸ hn)
      · have := (hstep n (by omega) h2).1
        have hb : (c.nu : ℝ) ≤ 0.017 := by
          have := (Rat.cast_le (K := ℝ)).mpr hνbar; push_cast at this; norm_num at this ⊢; linarith
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith
    · intro n h1 h2
      simp only [nextState] at h2
      by_cases hn : n < c.Dlo
      · exact hst.nuInf n h1 (hD ▸ hn)
      · have := (hstep n (by omega) h2).1
        rcases hνinf with hc | hc
        · exfalso; omega
        · have hb : (c.nu : ℝ) ≤ 0.014 := by
            have := (Rat.cast_le (K := ℝ)).mpr hc; push_cast at this; norm_num at this ⊢; linarith
          have hn0 : (0 : ℝ) ≤ n := by positivity
          nlinarith
    · intro n h1 h2
      simp only [nextState] at h2
      by_cases hn : n < c.Dlo
      · exact hst.mB n h1 (hD ▸ hn)
      · have := hmb n (by omega) h2
        refine this.trans ?_
        norm_num at hm' ⊢
        linarith
  · simp at hc

theorem checkCells_sound (h : Inputs) : ∀ (cells : List CellIn) (st : CState),
    StateOK st → checkCells st cells = true →
    (∀ n : ℕ, X0 ≤ n → n < Dend → |N n| ≤ 0.017 * n) ∧
    (∀ n : ℕ, Dmid ≤ n → n < Dend → |N n| ≤ 0.014 * n) ∧
    (∀ n : ℕ, X0 ≤ n → n < Dend → |msum n| * Real.log (n + 1) ≤ 0.03)
  | [], st, hst, hc => by
    simp only [checkCells, decide_eq_true_eq] at hc
    rw [← hc]
    exact ⟨hst.nuBar, hst.nuInf, hst.mB⟩
  | c :: rest, st, hst, hc => by
    simp only [checkCells, Bool.and_eq_true] at hc
    exact checkCells_sound h rest (nextState st c) (cellOk_sound h hst hc.1) hc.2

end TernaryGoldbach.RSBounds.Moebius003
