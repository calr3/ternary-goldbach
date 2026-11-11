/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Rho
import RSBounds.Moebius003.Misc
import RSBounds.Moebius003.Weights

/-!
# Proposition 8, step 1: the `k`-sum and the term `ρ(y) M(D/y)`

The `k`-sum `∑_{2 ≤ k ≤ y} |Λ(k) − 1| |M(D/k)|` is cut into blocks `(α, β]` whose endpoints are
checkpoints of `ghTable` (or `1`). On a block, every `u = ⌊D/k⌋` lies in
`[⌊D₋ / β⌋, ⌊(D₊ − 1) / max(α+1, 2)⌋]`; there `|M(u)| ≤ c_M √u` if `u ≤ X₀` (by (M)), and
`|M(u)| ≤ η u` with `η` the largest `η_r` of an earlier cell meeting that range if `u > X₀`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real

/-! ### The table -/

/-- Enclosures `(gLo, gHi, hLo, hHi)` of `G(N)`, `H(N)` in units of `10⁻⁶`, at `N = 1` and at the
checkpoints of `ghTable`. -/
def ghLookup (N : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  if N = 1 then some (0, 0, 0, 0) else
  match LambdaInputs.ghTable.find? (fun r => r.N == N) with
  | some r => some (r.gLo, r.gHi, r.hLo, r.hHi)
  | none => none

theorem G_one : LambdaInputs.G 1 = 0 := by simp [LambdaInputs.G]
theorem H_one : LambdaInputs.H 1 = 0 := by simp [LambdaInputs.H]

theorem ghLookup_sound (h : Inputs) {N gl gh hl hh : ℕ}
    (hL : ghLookup N = some (gl, gh, hl, hh)) :
    (gl : ℝ) / 10 ^ 6 ≤ LambdaInputs.G N ∧ LambdaInputs.G N ≤ (gh : ℝ) / 10 ^ 6 ∧
      (hl : ℝ) / 10 ^ 6 ≤ LambdaInputs.H N ∧ LambdaInputs.H N ≤ (hh : ℝ) / 10 ^ 6 := by
  unfold ghLookup at hL
  split_ifs at hL with h1
  · subst h1
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hL
    simp [G_one, H_one]
  · split at hL
    · rename_i r hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hL
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hL
      have hmem := List.mem_of_find?_eq_some hr
      have hN : r.N = N := by
        have := List.find?_some hr; simpa using this
      have := h.GH r hmem
      rw [hN] at this
      exact this
    · simp at hL

/-- `G(β) − G(α) = ∑_{α < k ≤ β} a_k/k`. -/
theorem G_sub {α β : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ β) :
    LambdaInputs.G β - LambdaInputs.G α = ∑ k ∈ Ioc α β, |Λ k - 1| / k := by
  unfold LambdaInputs.G
  have e : ∀ n, Icc 2 n = Ioc 1 n := fun n => by ext; simp; omega
  rw [e, e, ← sum_Ioc_consecutive _ h1 h2]; ring

theorem H_sub {α β : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ β) :
    LambdaInputs.H β - LambdaInputs.H α = ∑ k ∈ Ioc α β, |Λ k - 1| / Real.sqrt k := by
  unfold LambdaInputs.H
  have e : ∀ n, Icc 2 n = Ioc 1 n := fun n => by ext; simp; omega
  rw [e, e, ← sum_Ioc_consecutive _ h1 h2]; ring

/-! ### The profile of earlier cells -/

/-- An earlier cell: `(D_r, D_{r+1}, η_r)`. -/
abbrev CellRec := ℕ × ℕ × ℚ

/-- The largest `η_r` over the cells meeting `[lo, hi]` (and `0`). The list is newest first, so
the scan stops at the first cell ending at or below `lo`. -/
def etaMax : List CellRec → ℕ → ℕ → ℚ
  | [], _, _ => 0
  | (a, b, e) :: rest, lo, hi =>
    if b ≤ lo then 0 else if a ≤ hi then max e (etaMax rest lo hi) else etaMax rest lo hi

/-- The earlier cells cover `[X₀, D)`, satisfy their bound for `M`, and are listed newest first. -/
def ProfileOK (prev : List CellRec) (D : ℕ) : Prop :=
  (∀ c ∈ prev, ∀ u : ℕ, c.1 ≤ u → u < c.2.1 → |M u| ≤ (c.2.2 : ℝ) * u) ∧
  (∀ u : ℕ, X0 ≤ u → u < D → ∃ c ∈ prev, c.1 ≤ u ∧ u < c.2.1) ∧
  prev.Pairwise (fun x z => z.2.1 ≤ x.1) ∧ (∀ c ∈ prev, c.1 ≤ c.2.1)

theorem etaMax_nonneg : ∀ (prev : List CellRec) (lo hi : ℕ), 0 ≤ etaMax prev lo hi
  | [], _, _ => le_rfl
  | (a, b, e) :: rest, lo, hi => by
    unfold etaMax
    split_ifs
    · exact le_rfl
    · exact le_max_of_le_right (etaMax_nonneg rest lo hi)
    · exact etaMax_nonneg rest lo hi

theorem etaMax_ge : ∀ (prev : List CellRec) (lo hi : ℕ),
    prev.Pairwise (fun x z => z.2.1 ≤ x.1) → (∀ c ∈ prev, c.1 ≤ c.2.1) →
    ∀ (c : CellRec), c ∈ prev → c.1 ≤ hi → lo < c.2.1 → c.2.2 ≤ etaMax prev lo hi
  | [], _, _, _, _, _, hc, _, _ => by simp at hc
  | (a, b, e) :: rest, lo, hi, hpw, hwf, c, hc, h1, h2 => by
    unfold etaMax
    rw [List.pairwise_cons] at hpw
    have hab : a ≤ b := hwf (a, b, e) List.mem_cons_self
    rcases List.mem_cons.1 hc with rfl | hc'
    · rw [if_neg (by simp only at h2; omega), if_pos h1]; exact le_max_left _ _
    · have hcb : c.2.1 ≤ a := hpw.1 c hc'
      have := etaMax_ge rest lo hi hpw.2 (fun d hd => hwf d (List.mem_cons_of_mem _ hd)) c hc' h1 h2
      split_ifs with hb
      · exfalso; omega
      · exact le_max_of_le_right this
      · exact this

theorem M_le_etaMax {prev : List CellRec} {D : ℕ} (hP : ProfileOK prev D) {lo hi u : ℕ}
    (hlo : lo ≤ u) (hhi : u ≤ hi) (hX : X0 ≤ u) (hD : u < D) :
    |M u| ≤ (etaMax prev lo hi : ℝ) * u := by
  obtain ⟨c, hc, h1, h2⟩ := hP.2.1 u hX hD
  have hb := hP.1 c hc u h1 h2
  have hge := etaMax_ge prev lo hi hP.2.2.1 hP.2.2.2 c hc (le_trans h1 hhi) (lt_of_le_of_lt hlo h2)
  calc |M u| ≤ (c.2.2 : ℝ) * u := hb
    _ ≤ (etaMax prev lo hi : ℝ) * u := by gcongr

/-! ### One block -/

/-- `c_M` as a rational. -/
def cMq : ℚ := 571 / 1000

theorem cM_eq : cM = (cMq : ℝ) := by unfold cM cMq; norm_num

/-- The bound for one block `(α, β]`, divided by `D`. -/
def blockW (prev : List CellRec) (Dlo Dhi : ℕ) (sD : ℚ) (α β : ℕ) : Option ℚ :=
  match ghLookup α, ghLookup β with
  | some (glα, _, hlα, _), some (_, ghβ, _, hhβ) =>
    some ((if Dlo / β ≤ X0 then cMq * (((hhβ : ℚ) - hlα) / 10 ^ 6) / sD else 0) +
      (if X0 < (Dhi - 1) / max (α + 1) 2 then
        etaMax prev (max (Dlo / β) (X0 + 1)) ((Dhi - 1) / max (α + 1) 2) * (((ghβ : ℚ) - glα) / 10 ^ 6)
      else 0))
  | _, _ => none

theorem sqrt_div_le {D k : ℕ} (hk : 0 < k) : Real.sqrt ((D / k : ℕ) : ℝ) ≤ Real.sqrt D / Real.sqrt k := by
  rw [← Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ k)]
  exact Real.sqrt_le_sqrt Nat.cast_div_le

theorem block_bound (h : Inputs) {prev : List CellRec} {Dlo Dhi D α β : ℕ} {sD w : ℚ}
    (hP : ProfileOK prev Dlo) (hX0 : X0 ≤ Dlo) (h2D : Dhi ≤ 2 * Dlo)
    (hβ33 : 33 * β ≤ Dlo) (hα : 1 ≤ α) (hαβ : α < β)
    (hD1 : Dlo ≤ D) (hD2 : D < Dhi) (hsD0 : 0 < sD) (hsD : (sD : ℝ) ≤ Real.sqrt Dlo)
    (hw : blockW prev Dlo Dhi sD α β = some w) :
    ∑ k ∈ Ioc α β, |Λ k - 1| * |M (D / k)| ≤ D * (w : ℝ) := by
  unfold blockW at hw
  split at hw
  · rename_i glα _x1 hlα _x2 _x3 ghβ _x4 hhβ hα' hβ'
    simp only [Option.some.injEq] at hw
    subst hw
    obtain ⟨hGα, -, hHα, -⟩ := ghLookup_sound h hα'
    obtain ⟨-, hGβ, -, hHβ⟩ := ghLookup_sound h hβ'
    set lo := Dlo / β
    set hi := (Dhi - 1) / max (α + 1) 2
    set ηs := etaMax prev (max lo (X0 + 1)) hi
    have hηs0 : (0 : ℝ) ≤ ηs := by exact_mod_cast etaMax_nonneg _ _ _
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < D)
    have hDlopos : (0 : ℝ) < Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < Dlo)
    have hsDlo : 0 < Real.sqrt Dlo := Real.sqrt_pos.2 hDlopos
    have hsDD : Real.sqrt Dlo ≤ Real.sqrt D := Real.sqrt_le_sqrt (by exact_mod_cast hD1)
    have hsqD : Real.sqrt (D : ℝ) * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
    set fLo : ℝ := if lo ≤ X0 then 1 else 0
    set fHi : ℝ := if X0 < hi then 1 else 0
    have hfLo0 : 0 ≤ fLo := by simp only [fLo]; split_ifs <;> norm_num
    have hfHi0 : 0 ≤ fHi := by simp only [fHi]; split_ifs <;> norm_num
    -- the per-`k` bound
    have hpt : ∀ k ∈ Ioc α β, |Λ k - 1| * |M (D / k)| ≤
        D * (fLo * (cM * (|Λ k - 1| / Real.sqrt k) / Real.sqrt Dlo) + fHi * (ηs * (|Λ k - 1| / k))) := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := mem_Ioc.1 hk
      have hkpos : 0 < k := by omega
      have hk' : (0 : ℝ) < k := by exact_mod_cast hkpos
      have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk'
      have ha0 : 0 ≤ |Λ k - 1| := abs_nonneg _
      set u := D / k with hu
      have hulo : lo ≤ u := Nat.div_le_div hD1 hk2 (by omega)
      have huhi : u ≤ hi := Nat.div_le_div (by omega) (by omega) (by omega)
      have hu33 : 33 ≤ u := le_trans ((Nat.le_div_iff_mul_le (by omega)).2 (by linarith)) hulo
      have huDlo : u < Dlo := by
        have : u ≤ D / 2 := Nat.div_le_div_left (by omega) (by omega)
        omega
      have hureal : (u : ℝ) ≤ D / k := by rw [hu]; exact Nat.cast_div_le
      rcases le_or_gt u X0 with hX | hX
      · -- `(M)` applies
        have hfLo : fLo = 1 := by simp only [fLo]; rw [if_pos (le_trans hulo hX)]
        have hM := abs_M_le_sqrt h hu33 hX
        have hsu := sqrt_div_le (D := D) hkpos
        rw [← hu] at hsu
        have hcM : (0 : ℝ) ≤ cM := by unfold cM; norm_num
        have h1 : |Λ k - 1| * |M u| ≤ |Λ k - 1| * (cM * (Real.sqrt D / Real.sqrt k)) :=
          mul_le_mul_of_nonneg_left (hM.trans (mul_le_mul_of_nonneg_left hsu hcM)) ha0
        have h2 : |Λ k - 1| * (cM * (Real.sqrt D / Real.sqrt k)) ≤
            D * (cM * (|Λ k - 1| / Real.sqrt k) / Real.sqrt Dlo) := by
          rw [show D * (cM * (|Λ k - 1| / Real.sqrt k) / Real.sqrt Dlo) =
            |Λ k - 1| * (cM * ((D / Real.sqrt Dlo) / Real.sqrt k)) by ring]
          gcongr
          rw [le_div_iff₀ hsDlo]
          nlinarith
        have h3 : 0 ≤ D * (fHi * (ηs * (|Λ k - 1| / k))) := by positivity
        rw [hfLo, one_mul]
        nlinarith
      · -- an earlier cell
        have hfHi : fHi = 1 := by simp only [fHi]; rw [if_pos (lt_of_lt_of_le hX huhi)]
        have hM := M_le_etaMax hP (lo := max lo (X0 + 1)) (hi := hi) (max_le hulo hX) huhi hX.le huDlo
        have h1 : |Λ k - 1| * |M u| ≤ |Λ k - 1| * (ηs * (D / k)) :=
          mul_le_mul_of_nonneg_left (hM.trans (mul_le_mul_of_nonneg_left hureal hηs0)) ha0
        have h2 : |Λ k - 1| * (ηs * (D / k)) = D * (ηs * (|Λ k - 1| / k)) := by ring
        have hcM : (0 : ℝ) ≤ cM := by unfold cM; norm_num
        have h3 : 0 ≤ D * (fLo * (cM * (|Λ k - 1| / Real.sqrt k) / Real.sqrt Dlo)) := by positivity
        rw [hfHi, one_mul]
        linarith
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_div, ← mul_sum, ← mul_sum,
      ← H_sub hα hαβ.le, ← G_sub hα hαβ.le]
    apply mul_le_mul_of_nonneg_left _ hDpos.le
    have hHd : LambdaInputs.H β - LambdaInputs.H α ≤ ((hhβ : ℝ) - hlα) / 10 ^ 6 := by
      rw [sub_div]; linarith
    have hGd : LambdaInputs.G β - LambdaInputs.G α ≤ ((ghβ : ℝ) - glα) / 10 ^ 6 := by
      rw [sub_div]; linarith
    have hHd0 : 0 ≤ LambdaInputs.H β - LambdaInputs.H α := by
      rw [H_sub hα hαβ.le]; exact sum_nonneg fun k _ => by positivity
    have hGd0 : 0 ≤ LambdaInputs.G β - LambdaInputs.G α := by
      rw [G_sub hα hαβ.le]; exact sum_nonneg fun k _ => by positivity
    have hcM : (0 : ℝ) ≤ cM := by unfold cM; norm_num
    have hsD0' : (0 : ℝ) < sD := by exact_mod_cast hsD0
    rw [Rat.cast_add]
    apply add_le_add
    · simp only [fLo]
      split_ifs
      · push_cast
        rw [one_mul, ← cM_eq]
        calc cM * (LambdaInputs.H β - LambdaInputs.H α) / Real.sqrt Dlo
            ≤ cM * (((hhβ : ℝ) - hlα) / 10 ^ 6) / Real.sqrt Dlo := by gcongr
          _ ≤ cM * (((hhβ : ℝ) - hlα) / 10 ^ 6) / sD := by
            apply div_le_div_of_nonneg_left _ hsD0' hsD
            exact mul_nonneg hcM (le_trans hHd0 hHd)
      · simp
    · simp only [fHi]
      split_ifs
      · push_cast
        rw [one_mul]; gcongr
      · simp
  · simp at hw

/-! ### The whole `k`-sum -/

/-- The bound for the blocks `(α, b₁], (b₁, b₂], …`, divided by `D`; it also checks
`α < b₁ < b₂ < …` and `33 b ≤ D_-`. -/
def ksumW (prev : List CellRec) (Dlo Dhi : ℕ) (sD : ℚ) : ℕ → List ℕ → Option ℚ
  | _, [] => some 0
  | α, β :: rest =>
    match blockW prev Dlo Dhi sD α β, ksumW prev Dlo Dhi sD β rest with
    | some w, some r => if α < β ∧ 33 * β ≤ Dlo then some (w + r) else none
    | _, _ => none

/-- The right end of the blocks. -/
def endOf : ℕ → List ℕ → ℕ
  | α, [] => α
  | _, β :: rest => endOf β rest

theorem le_endOf : ∀ (α : ℕ) (bs : List ℕ) (K : ℚ) (prev : List CellRec) (Dlo Dhi : ℕ) (sD : ℚ),
    ksumW prev Dlo Dhi sD α bs = some K → α ≤ endOf α bs
  | _, [], _, _, _, _, _, _ => le_rfl
  | α, β :: rest, K, prev, Dlo, Dhi, sD, hK => by
    unfold ksumW at hK
    split at hK
    · rename_i w r _ hr
      split_ifs at hK with hc
      exact le_trans hc.1.le (le_endOf β rest r prev Dlo Dhi sD hr)
    · simp at hK

theorem ksum_bound (h : Inputs) {prev : List CellRec} {Dlo Dhi D : ℕ} {sD : ℚ}
    (hP : ProfileOK prev Dlo) (hX0 : X0 ≤ Dlo) (h2D : Dhi ≤ 2 * Dlo)
    (hD1 : Dlo ≤ D) (hD2 : D < Dhi) (hsD0 : 0 < sD) (hsD : (sD : ℝ) ≤ Real.sqrt Dlo) :
    ∀ (α : ℕ) (bs : List ℕ) (K : ℚ), 1 ≤ α → ksumW prev Dlo Dhi sD α bs = some K →
      ∑ k ∈ Ioc α (endOf α bs), |Λ k - 1| * |M (D / k)| ≤ D * (K : ℝ)
  | α, [], K, _, hK => by
    simp only [ksumW, Option.some.injEq] at hK; subst hK; simp [endOf]
  | α, β :: rest, K, hα, hK => by
    unfold ksumW at hK
    split at hK
    · rename_i w r hw hr
      split_ifs at hK with hc
      simp only [Option.some.injEq] at hK
      subst hK
      have h1 := block_bound h hP hX0 h2D hc.2 hα hc.1 hD1 hD2 hsD0 hsD hw
      have h2 := ksum_bound h hP hX0 h2D hD1 hD2 hsD0 hsD β rest r (by omega) hr
      have hle := le_endOf β rest r prev Dlo Dhi sD hr
      simp only [endOf]
      rw [← sum_Ioc_consecutive _ hc.1.le hle]
      push_cast
      linarith
    · simp at hK

/-! ### The term `ρ(y) M(D/y)` -/

/-- The bound for `|ρ(y) M(D/y)|`, divided by `D`. -/
def rhoW (prev : List CellRec) (Dlo Dhi y : ℕ) (sD sy : ℚ) : ℚ :=
  (if Dlo / y ≤ X0 then 4 / 5 * cMq / sD else 0) +
    (if X0 < (Dhi - 1) / y then 4 / 5 * etaMax prev (max (Dlo / y) (X0 + 1)) ((Dhi - 1) / y) / sy
    else 0)

theorem rho_y_bound (h : Inputs) {prev : List CellRec} {Dlo Dhi D y : ℕ} {sD sy : ℚ}
    (hP : ProfileOK prev Dlo) (hX0 : X0 ≤ Dlo) (h2D : Dhi ≤ 2 * Dlo)
    (hy1 : 1500 ≤ y) (hy2 : y ≤ 2 ^ 20) (hy33 : 33 * y ≤ Dlo)
    (hD1 : Dlo ≤ D) (hD2 : D < Dhi)
    (hsD0 : 0 < sD) (hsD : (sD : ℝ) ≤ Real.sqrt Dlo) (hsy0 : 0 < sy) (hsy : (sy : ℝ) ≤ Real.sqrt y) :
    |ρ y| * |M (D / y)| ≤ D * (rhoW prev Dlo Dhi y sD sy : ℝ) := by
  have hρ := rho_P_nat h hy1 (by omega)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < D)
  have hDlopos : (0 : ℝ) < Dlo := by exact_mod_cast (by unfold X0 at hX0; omega : 0 < Dlo)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hsy' : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hsDlo : 0 < Real.sqrt Dlo := Real.sqrt_pos.2 hDlopos
  have hsDD : Real.sqrt Dlo ≤ Real.sqrt D := Real.sqrt_le_sqrt (by exact_mod_cast hD1)
  have hsqD : Real.sqrt (D : ℝ) * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
  have hsqy : Real.sqrt (y : ℝ) * Real.sqrt y = y := Real.mul_self_sqrt hypos.le
  set u := D / y with hu
  set lo := Dlo / y
  set hi := (Dhi - 1) / y
  set ηs := etaMax prev (max lo (X0 + 1)) hi
  have hηs0 : (0 : ℝ) ≤ ηs := by exact_mod_cast etaMax_nonneg _ _ _
  have hulo : lo ≤ u := Nat.div_le_div_right hD1
  have huhi : u ≤ hi := Nat.div_le_div_right (by omega)
  have hu33 : 33 ≤ u := le_trans ((Nat.le_div_iff_mul_le (by omega)).2 (by linarith)) hulo
  have huDlo : u < Dlo := by
    have : u ≤ D / 2 := Nat.div_le_div_left (by omega) (by omega)
    omega
  have hureal : (u : ℝ) ≤ D / y := by rw [hu]; exact Nat.cast_div_le
  have hcM : (0 : ℝ) ≤ cM := by unfold cM; norm_num
  have hsD0' : (0 : ℝ) < sD := by exact_mod_cast hsD0
  have hsy0' : (0 : ℝ) < sy := by exact_mod_cast hsy0
  have hA' : (0 : ℝ) ≤ ((if lo ≤ X0 then 4 / 5 * cMq / sD else 0 : ℚ) : ℝ) := by
    split_ifs
    · push_cast; exact div_nonneg (by unfold cMq; norm_num) hsD0'.le
    · simp
  have hB' : (0 : ℝ) ≤ ((if X0 < hi then 4 / 5 * ηs / sy else 0 : ℚ) : ℝ) := by
    split_ifs
    · push_cast; positivity
    · simp
  unfold rhoW
  rw [Rat.cast_add]
  rcases le_or_gt u X0 with hX | hX
  · have hM := abs_M_le_sqrt h hu33 hX
    have hsu := sqrt_div_le (D := D) (k := y) (by omega)
    rw [← hu] at hsu
    have hlo : lo ≤ X0 := le_trans hulo hX
    have hAv : ((if lo ≤ X0 then 4 / 5 * cMq / sD else 0 : ℚ) : ℝ) = 4 / 5 * cM / sD := by
      rw [if_pos hlo, cM_eq]; push_cast; ring
    rw [hAv] at hA'
    rw [show (if Dlo / y ≤ X0 then 4 / 5 * cMq / sD else 0 : ℚ) =
      (if lo ≤ X0 then 4 / 5 * cMq / sD else 0 : ℚ) from rfl, hAv]
    have h1 : |ρ y| * |M u| ≤ 0.8 * Real.sqrt y * (cM * (Real.sqrt D / Real.sqrt y)) :=
      mul_le_mul hρ (hM.trans (mul_le_mul_of_nonneg_left hsu hcM)) (abs_nonneg _) (by positivity)
    have h2 : 0.8 * Real.sqrt y * (cM * (Real.sqrt D / Real.sqrt y)) = 0.8 * cM * Real.sqrt D := by
      field_simp
    have h3 : 0.8 * cM * Real.sqrt D ≤ D * (4 / 5 * cM / sD) := by
      rw [mul_div_assoc', le_div_iff₀ hsD0']
      have : Real.sqrt D * sD ≤ D := by
        calc Real.sqrt D * sD ≤ Real.sqrt D * Real.sqrt D :=
              mul_le_mul_of_nonneg_left (hsD.trans hsDD) (Real.sqrt_nonneg _)
          _ = D := hsqD
      nlinarith
    have : (0 : ℝ) ≤ D * ((if X0 < hi then 4 / 5 * ηs / sy else 0 : ℚ) : ℝ) := by positivity
    nlinarith
  · have hhi : X0 < hi := lt_of_lt_of_le hX huhi
    have hBv : ((if X0 < hi then 4 / 5 * ηs / sy else 0 : ℚ) : ℝ) = 4 / 5 * ηs / sy := by
      rw [if_pos hhi]; push_cast; ring
    rw [show (if X0 < (Dhi - 1) / y then 4 / 5 * etaMax prev (max (Dlo / y) (X0 + 1)) ((Dhi - 1) / y) / sy else 0 : ℚ) =
      (if X0 < hi then 4 / 5 * ηs / sy else 0 : ℚ) from rfl, hBv]
    have hM := M_le_etaMax hP (lo := max lo (X0 + 1)) (hi := hi) (max_le hulo hX) huhi hX.le huDlo
    have h1 : |ρ y| * |M u| ≤ 0.8 * Real.sqrt y * (ηs * (D / y)) :=
      mul_le_mul hρ (hM.trans (mul_le_mul_of_nonneg_left hureal hηs0)) (abs_nonneg _) (by positivity)
    have e : Real.sqrt (y : ℝ) * (1 / y) = 1 / Real.sqrt y := by
      rw [mul_one_div, div_eq_div_iff hypos.ne' hsy'.ne', one_mul, hsqy]
    have h2 : 0.8 * Real.sqrt y * (ηs * (D / y)) = D * (4 / 5 * ηs / Real.sqrt y) := by
      have : 0.8 * Real.sqrt y * (ηs * (D / y)) = 0.8 * ηs * D * (Real.sqrt (y : ℝ) * (1 / y)) := by ring
      rw [this, e]; ring
    have h3 : D * (4 / 5 * (ηs : ℝ) / Real.sqrt y) ≤ D * (4 / 5 * ηs / sy) := by
      gcongr
    have : (0 : ℝ) ≤ D * ((if lo ≤ X0 then 4 / 5 * cMq / sD else 0 : ℚ) : ℝ) := by positivity
    nlinarith

end TernaryGoldbach.RSBounds.Moebius003
