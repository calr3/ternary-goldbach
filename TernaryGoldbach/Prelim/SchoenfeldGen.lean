import TernaryGoldbach.Prelim.SchoenfeldM
import TernaryGoldbach.Prelim.SchoenfeldJ
import TernaryGoldbach.Prelim.SchoenfeldCell
import TernaryGoldbach.Prelim.WeightsMain
import TernaryGoldbach.Prelim.SqfreeWalk

/-!
# One cell of the induction, as a check over `ℚ`

`chkCell` checks the numerical side conditions of one cell `[A, B)` of the induction (`cell_step`),
with the bound for `|N(D)| − |M(D)|` from the identity (`N_abs_le`) estimated by
* the `k`-sum (`k ≤ Y`): blocks `(α, β]` with `|M(u)| ≤ c √u + η u` on the range of `u = D/k`
  (`c = 0.571` below `X₀ = 10⁸`, `M_low`; `η` from the earlier cells) and `G`, `H` from `GHtab`;
* the `j`-sum (`J_le`): the three `√`-pieces and the pieces `V_j ≤ v < V_{j+1}` of `ε(v) v`;
* the boundary term `|ρ(Y)| |M(D/(Y+1))|`.
`cell_sound` turns a successful check into the bound `|M(u)| ≤ η u` on the cell and the update of
`∑ |N(n)| (1/log n − 1/log(n+1))`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sch
open TernaryGoldbach.Prelim.Sqf (musq kap Q1)
open TernaryGoldbach.Prelim.Wts (aw)

/-! ### Logarithm certificates -/

/-- `q ≤ log L`. -/
def logLo (q : ℚ) (L : ℕ) : Bool := decide (0 ≤ q) && decide (0 < L) && Small.chkLow q.num.toNat q.den L

/-- `log L ≤ q`. -/
def logUp (q : ℚ) (L : ℕ) : Bool := decide (0 ≤ q) && decide (0 < L) && Small.chkStep q.num.toNat q.den 1 L

theorem logLo_spec {q : ℚ} {L : ℕ} (h : logLo q L = true) : (q : ℝ) ≤ Real.log L := by
  simp only [logLo, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hq, hL⟩, hc⟩ := h
  have := Small.le_log_of_chk q.den_pos hL hc
  have e : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)
    rw [Rat.cast_def]; congr 1; exact_mod_cast h1
  rwa [e] at this

theorem logUp_spec {q : ℚ} {L : ℕ} (h : logUp q L = true) : Real.log L ≤ q := by
  simp only [logUp, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hq, hL⟩, hc⟩ := h
  have := Small.log_lt_of_chk q.den_pos hL hc
  have e : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) * ((1 : ℕ) : ℝ) = (q : ℝ) := by
    have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)
    rw [Nat.cast_one, mul_one, Rat.cast_def]; congr 1; exact_mod_cast h1
  rw [e] at this; exact this.le

/-! ### `G`, `H` from the table -/

def S12 : ℚ := 1000000000000

/-- `(G_lo, G_hi, H_lo, H_hi)` at `m`, from a list. -/
def ghL : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ → ℚ × ℚ × ℚ × ℚ
  | [], _ => (0, 0, 0, 0)
  | e :: es, m => if e.1 = m then (e.2.1 / S12, e.2.2.1 / S12, e.2.2.2.1 / S12, e.2.2.2.2 / S12) else ghL es m

def ghq (m : ℕ) : ℚ × ℚ × ℚ × ℚ := if m = 1 then (0, 0, 0, 0) else ghL Wts.GHtab m

def ghOK (m : ℕ) : Bool := m = 1 || Wts.GHtab.any (fun e => e.1 = m)

theorem ghL_spec : ∀ (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (m : ℕ), (∀ e ∈ l, e.1 = m →
    (e.2.1 : ℝ) / SmallE.S ≤ Wts.Gw e.1 ∧ Wts.Gw e.1 ≤ (e.2.2.1 : ℝ) / SmallE.S ∧
    (e.2.2.2.1 : ℝ) / SmallE.S ≤ Wts.Hw e.1 ∧ Wts.Hw e.1 ≤ (e.2.2.2.2 : ℝ) / SmallE.S) →
    l.any (fun e => e.1 = m) = true →
    ((ghL l m).1 : ℝ) ≤ Wts.Gw m ∧ Wts.Gw m ≤ (ghL l m).2.1 ∧
    ((ghL l m).2.2.1 : ℝ) ≤ Wts.Hw m ∧ Wts.Hw m ≤ (ghL l m).2.2.2
  | [], m, _, h => by simp at h
  | e :: es, m, hs, h => by
    simp only [ghL]
    split_ifs with he
    · have := hs e (by simp) he
      rw [he] at this
      have eS : ((S12 : ℚ) : ℝ) = (SmallE.S : ℝ) := by norm_num [S12, SmallE.S]
      simp only [Rat.cast_div, Rat.cast_natCast, eS]
      exact this
    · simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact absurd h he
      · exact ghL_spec es m (fun e' he' => hs e' (List.mem_cons_of_mem _ he')) h

theorem ghq_spec {m : ℕ} (h : ghOK m = true) :
    ((ghq m).1 : ℝ) ≤ Wts.Gw m ∧ Wts.Gw m ≤ (ghq m).2.1 ∧
    ((ghq m).2.2.1 : ℝ) ≤ Wts.Hw m ∧ Wts.Hw m ≤ (ghq m).2.2.2 := by
  unfold ghq
  split_ifs with h1
  · subst h1; simp [Wts.Gw, Wts.Hw]
  · simp only [ghOK, Bool.or_eq_true, decide_eq_true_eq, h1, false_or] at h
    exact ghL_spec _ m (fun e he _ => Wts.GHtab_spec e he) h

/-! ### The bounds `|M(u)| ≤ η u` on the cells so far -/

/-- Cells `[s, b₁), [b₁, b₂), …` with `|M(u)| ≤ η u`. -/
def McovR : ℕ → List (ℕ × ℚ) → Prop
  | _, [] => True
  | s, (b, η) :: cs => (∀ u, s ≤ u → u < b → |Mn u| ≤ (η : ℝ) * u) ∧ McovR b cs

def endC : ℕ → List (ℕ × ℚ) → ℕ
  | s, [] => s
  | _, (b, _) :: cs => endC b cs

/-- The largest `η` over the cells meeting `[lo, hi]` (`0` if none). -/
def etaMax : ℕ → List (ℕ × ℚ) → ℕ → ℕ → ℚ
  | _, [], _, _ => 0
  | s, (b, η) :: cs, lo, hi => if hi < s ∨ b ≤ lo then etaMax b cs lo hi else max η (etaMax b cs lo hi)

theorem etaMax_nonneg : ∀ (cs : List (ℕ × ℚ)) (s lo hi : ℕ), 0 ≤ etaMax s cs lo hi
  | [], _, _, _ => le_rfl
  | (b, η) :: cs, s, lo, hi => by
    simp only [etaMax]
    have := etaMax_nonneg cs b lo hi
    split_ifs
    · exact this
    · exact le_trans this (le_max_right _ _)

theorem etaMax_spec : ∀ (cs : List (ℕ × ℚ)) (s : ℕ), McovR s cs → ∀ lo hi u, s ≤ u → u < endC s cs →
    lo ≤ u → u ≤ hi → |Mn u| ≤ (etaMax s cs lo hi : ℝ) * u
  | [], s, _, lo, hi, u, h1, h2, _, _ => by simp [endC] at h2; omega
  | (b, η) :: cs, s, ⟨hc, hr⟩, lo, hi, u, h1, h2, h3, h4 => by
    simp only [etaMax]
    have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    rcases lt_or_ge u b with hb | hb
    · have hn : ¬ (hi < s ∨ b ≤ lo) := by omega
      rw [if_neg hn]
      refine le_trans (hc u h1 hb) (mul_le_mul_of_nonneg_right ?_ hu)
      exact_mod_cast le_max_left _ _
    · have ih := etaMax_spec cs b hr lo hi u hb h2 h3 h4
      split_ifs
      · exact ih
      · refine le_trans ih (mul_le_mul_of_nonneg_right ?_ hu)
        exact_mod_cast le_max_right _ _

theorem McovR_append : ∀ (cs : List (ℕ × ℚ)) (s b : ℕ) (η : ℚ), McovR s cs →
    (∀ u, endC s cs ≤ u → u < b → |Mn u| ≤ (η : ℝ) * u) →
    McovR s (cs ++ [(b, η)]) ∧ endC s (cs ++ [(b, η)]) = b
  | [], s, b, η, _, h => ⟨⟨h, trivial⟩, rfl⟩
  | (b', η') :: cs, s, b, η, ⟨hc, hr⟩, h => by
    obtain ⟨h1, h2⟩ := McovR_append cs b' b η hr h
    exact ⟨⟨hc, h1⟩, h2⟩

/-- `(c, η)` with `|M(u)| ≤ c √u + η u` for `lo ≤ u ≤ hi`. -/
def Mrange (cs : List (ℕ × ℚ)) (lo hi : ℕ) : ℚ × ℚ :=
  (if lo ≤ X0 then 571 / 1000 else 0, if X0 < hi then etaMax (X0 + 1) cs lo hi else 0)

theorem Mrange_nonneg (cs : List (ℕ × ℚ)) (lo hi : ℕ) : 0 ≤ (Mrange cs lo hi).1 ∧ 0 ≤ (Mrange cs lo hi).2 := by
  simp only [Mrange]; constructor
  · split_ifs <;> norm_num
  · split_ifs
    · exact etaMax_nonneg _ _ _ _
    · exact le_rfl

theorem Mrange_spec {cs : List (ℕ × ℚ)} (hc : McovR (X0 + 1) cs) {lo hi : ℕ} (hlo : 100 ≤ lo)
    (hhi : hi < endC (X0 + 1) cs) {u : ℕ} (h1 : lo ≤ u) (h2 : u ≤ hi) :
    |Mn u| ≤ ((Mrange cs lo hi).1 : ℝ) * √(u : ℝ) + ((Mrange cs lo hi).2 : ℝ) * u := by
  obtain ⟨n1, n2⟩ := Mrange_nonneg cs lo hi
  have n1' : (0 : ℝ) ≤ (Mrange cs lo hi).1 := by exact_mod_cast n1
  have n2' : (0 : ℝ) ≤ (Mrange cs lo hi).2 := by exact_mod_cast n2
  have hs := Real.sqrt_nonneg (u : ℝ)
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  rcases le_or_gt u X0 with h | h
  · have hM := M_low (u := u) (by omega) (by unfold X0 at h; omega)
    have e : (Mrange cs lo hi).1 = 571 / 1000 := by
      show (if lo ≤ X0 then (571 / 1000 : ℚ) else 0) = _; rw [if_pos (by omega)]
    rw [e]; push_cast
    have := mul_nonneg n2' hu
    linarith
  · have e : (Mrange cs lo hi).2 = etaMax (X0 + 1) cs lo hi := by
      show (if X0 < hi then etaMax (X0 + 1) cs lo hi else 0) = _; rw [if_pos (by omega)]
    rw [e]
    have := etaMax_spec cs (X0 + 1) hc lo hi u (by omega) (by omega) h1 h2
    have := mul_nonneg n1' hs
    linarith

/-! ### The `k`-sum -/

theorem sqrt_le_div {sA D : ℕ} (hsA : 1 ≤ sA) (hsAD : sA * sA ≤ D) : √(D : ℝ) ≤ (D : ℝ) / sA := by
  have hs0 : (0 : ℝ) < sA := by exact_mod_cast hsA
  have hsq : (sA : ℝ) ≤ √(D : ℝ) := by
    rw [show (sA : ℝ) = √((sA : ℝ) * sA) by rw [Real.sqrt_mul_self hs0.le]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hsAD)
  rw [le_div_iff₀ hs0]
  have := Real.mul_self_sqrt (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
  nlinarith [Real.sqrt_nonneg (D : ℝ)]

/-- The check of the blocks `(α, β]` of the `k`-sum. -/
def kChk (cs : List (ℕ × ℚ)) (A B : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | α, β :: bs => decide (1 ≤ α) && decide (α < β) && ghOK α && ghOK β && decide (100 ≤ A / β) &&
      decide ((B - 1) / (α + 1) < A) && decide ((ghq α).2.2.1 ≤ (ghq β).2.2.2) && kChk cs A B β bs

/-- The bound of the `k`-sum, divided by `D`. -/
def kVal (cs : List (ℕ × ℚ)) (A B sA : ℕ) : ℕ → List ℕ → ℚ
  | _, [] => 0
  | α, β :: bs => (Mrange cs (A / β) ((B - 1) / (α + 1))).1 * ((ghq β).2.2.2 - (ghq α).2.2.1) / sA +
      (Mrange cs (A / β) ((B - 1) / (α + 1))).2 * ((ghq β).2.1 - (ghq α).1) + kVal cs A B sA β bs

def lastK : ℕ → List ℕ → ℕ
  | α, [] => α
  | _, β :: bs => lastK β bs

theorem lastK_ge {cs : List (ℕ × ℚ)} {A B : ℕ} : ∀ (bs : List ℕ) (α : ℕ), kChk cs A B α bs = true →
    α ≤ lastK α bs
  | [], _, _ => le_rfl
  | β :: bs, α, h => by
    simp only [kChk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact le_trans h.1.1.1.1.1.1.2.le (lastK_ge bs β h.2)

theorem kSum_le {cs : List (ℕ × ℚ)} (hc : McovR (X0 + 1) cs) {A B sA D : ℕ}
    (hend : endC (X0 + 1) cs = A) (hsA : 1 ≤ sA) (hsAA : sA * sA ≤ A) (hAD : A ≤ D) (hDB : D < B) :
    ∀ (bs : List ℕ) (α : ℕ), kChk cs A B α bs = true →
      ∑ k ∈ Ioc α (lastK α bs), aw k * |Mn (D / k)| ≤ D * (kVal cs A B sA α bs : ℝ)
  | [], α, _ => by simp [lastK, kVal]
  | β :: bs, α, h => by
    have hlast := lastK_ge (β :: bs) α h
    simp only [kChk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hα, hαβ⟩, gα⟩, gβ⟩, hlo⟩, hhi⟩, hH⟩, hr⟩ := h
    have ih := kSum_le hc hend hsA hsAA hAD hDB bs β hr
    have hlβ : β ≤ lastK β bs := lastK_ge bs β hr
    simp only [lastK, kVal] at hlast ⊢
    rw [← Finset.sum_Ioc_consecutive _ hαβ.le hlβ]
    set p := Mrange cs (A / β) ((B - 1) / (α + 1)) with hp
    obtain ⟨p1, p2⟩ := Mrange_nonneg cs (A / β) ((B - 1) / (α + 1))
    have p1' : (0 : ℝ) ≤ p.1 := by exact_mod_cast p1
    have p2' : (0 : ℝ) ≤ p.2 := by exact_mod_cast p2
    have hM : ∀ k ∈ Ioc α β, |Mn (D / k)| ≤ (p.1 : ℝ) * √((D / k : ℕ) : ℝ) + (p.2 : ℝ) * ((D / k : ℕ) : ℝ) := by
      intro k hk
      obtain ⟨k1, k2⟩ := mem_Ioc.1 hk
      refine Mrange_spec hc hlo (by omega) ?_ ?_
      · exact le_trans (Nat.div_le_div_left k2 (by omega)) (Nat.div_le_div_right hAD)
      · exact le_trans (Nat.div_le_div_left (show α + 1 ≤ k by omega) (by omega))
          (Nat.div_le_div_right (show D ≤ B - 1 by omega))
    have hb := Ksum_block p1' p2' hα hαβ.le hM
    obtain ⟨Gα1, -, Hα1, -⟩ := ghq_spec gα
    obtain ⟨-, Gβ2, -, Hβ2⟩ := ghq_spec gβ
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have hsD := sqrt_le_div hsA (le_trans hsAA hAD)
    have hs0 := Real.sqrt_nonneg (D : ℝ)
    have hH' : (((ghq α).2.2.1 : ℚ) : ℝ) ≤ (ghq β).2.2.2 := by exact_mod_cast hH
    have hsA0 : (0 : ℝ) < sA := by exact_mod_cast hsA
    have t1 : (p.1 : ℝ) * √(D : ℝ) * (Wts.Hw β - Wts.Hw α) ≤
        D * ((p.1 : ℝ) * (((ghq β).2.2.2 : ℝ) - (ghq α).2.2.1) / sA) := by
      have e : (D : ℝ) * ((p.1 : ℝ) * (((ghq β).2.2.2 : ℝ) - (ghq α).2.2.1) / sA) =
          (p.1 : ℝ) * ((D : ℝ) / sA) * (((ghq β).2.2.2 : ℝ) - (ghq α).2.2.1) := by ring
      rw [e]
      calc (p.1 : ℝ) * √(D : ℝ) * (Wts.Hw β - Wts.Hw α) ≤
            (p.1 : ℝ) * √(D : ℝ) * (((ghq β).2.2.2 : ℝ) - (ghq α).2.2.1) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ (p.1 : ℝ) * ((D : ℝ) / sA) * (((ghq β).2.2.2 : ℝ) - (ghq α).2.2.1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsD p1') (by linarith)
    have t2 : (p.2 : ℝ) * D * (Wts.Gw β - Wts.Gw α) ≤ D * ((p.2 : ℝ) * (((ghq β).2.1 : ℝ) - (ghq α).1)) := by
      have := mul_le_mul_of_nonneg_left (show Wts.Gw β - Wts.Gw α ≤ ((ghq β).2.1 : ℝ) - (ghq α).1 by linarith)
        (mul_nonneg p2' hD0)
      linarith
    push_cast
    nlinarith

/-! ### The `√`-pieces of the `j`-sum -/

/-- `κ ≤ kq`. -/
def kq : ℚ := 607927101855 / 1000000000000

theorem kap_le_kq : kap ≤ (kq : ℝ) := by
  have := Sqf.kap_bounds.2
  have e : ((kq : ℚ) : ℝ) = (Sqf.kHi : ℝ) / SmallE.S := by norm_num [kq, Sqf.kHi, SmallE.S]
  rw [e]; exact this

theorem jPiece {D a r sA : ℕ} {coef u : ℝ} (hcoef : 0 ≤ coef) (hr : 1 ≤ r) (hra : r * r ≤ a)
    (hsA : 1 ≤ sA) (hsAD : sA * sA ≤ D) (hu : 0 ≤ u) (hlog : 1 ≤ D / a → Real.log (D / a : ℕ) ≤ u) :
    coef * √(D : ℝ) * SS (D / a) ≤ D * (coef * (2 * kq / r + (4.5 + 1.5 * u) / sA)) := by
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hsA0 : (0 : ℝ) < sA := by exact_mod_cast hsA
  have hk := kap_le_kq
  have hk0 : 0 ≤ kap := Sqf.kap_pos.le
  unfold SS
  split_ifs with h0
  · have hkq : (0 : ℝ) ≤ kq := by norm_num [kq]
    simp only [mul_zero]
    exact mul_nonneg hD0 (mul_nonneg hcoef (add_nonneg (by positivity) (by positivity)))
  · have h1 : 1 ≤ D / a := Nat.pos_of_ne_zero h0
    have hl := hlog h1
    have ha : 1 ≤ a := by nlinarith
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    have hsD := sqrt_le_div hsA hsAD
    have hs0 := Real.sqrt_nonneg (D : ℝ)
    -- `√D √(D/a) ≤ D/r`
    have hJ : √(D : ℝ) * √((D / a : ℕ) : ℝ) ≤ D / r := by
      have h2 : √((D / a : ℕ) : ℝ) ≤ √(D : ℝ) / √(a : ℝ) := by
        rw [← Real.sqrt_div' _ ha0.le]; exact Real.sqrt_le_sqrt Nat.cast_div_le
      have hsa : (r : ℝ) ≤ √(a : ℝ) := by
        rw [show (r : ℝ) = √((r : ℝ) * r) by rw [Real.sqrt_mul_self hr0.le]]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hra)
      have hsa0 : 0 < √(a : ℝ) := Real.sqrt_pos.2 ha0
      calc √(D : ℝ) * √((D / a : ℕ) : ℝ) ≤ √(D : ℝ) * (√(D : ℝ) / √(a : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 hs0
        _ = D / √(a : ℝ) := by rw [← mul_div_assoc, Real.mul_self_sqrt hD0]
        _ ≤ D / r := div_le_div_of_nonneg_left hD0 hr0 hsa
    have hJ' : √(D : ℝ) * (4.5 + 1.5 * Real.log (D / a : ℕ)) ≤ D / sA * (4.5 + 1.5 * u) :=
      mul_le_mul hsD (by linarith) (by
        have := Real.log_nonneg (show (1 : ℝ) ≤ ((D / a : ℕ) : ℝ) by exact_mod_cast h1); linarith)
        (by positivity)
    have hJk : 2 * kap * (√(D : ℝ) * √((D / a : ℕ) : ℝ)) ≤ 2 * kq * (D / r) :=
      mul_le_mul (by linarith) hJ (by positivity) (by linarith)
    have e1 : coef * √(D : ℝ) * (2 * kap * √((D / a : ℕ) : ℝ) + 4.5 + 1.5 * Real.log (D / a : ℕ)) =
        coef * (2 * kap * (√(D : ℝ) * √((D / a : ℕ) : ℝ)) + √(D : ℝ) * (4.5 + 1.5 * Real.log (D / a : ℕ))) := by
      ring
    have e2 : (D : ℝ) * (coef * (2 * kq / r + (4.5 + 1.5 * u) / sA)) =
        coef * (2 * kq * (D / r) + D / sA * (4.5 + 1.5 * u)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (by linarith) hcoef

/-- The check of a `√`-piece `a` with `r² ≤ a`, `log((B−1)/a) ≤ u`. -/
def jChk (B a r : ℕ) (u : ℚ) : Bool :=
  decide ((B - 1) / a = 0) || (decide (1 ≤ r) && decide (r * r ≤ a) && logUp u ((B - 1) / a))

def jVal (B a r sA : ℕ) (coef u : ℚ) : ℚ :=
  if (B - 1) / a = 0 then 0 else coef * (2 * kq / r + (9 / 2 + 3 / 2 * u) / sA)

theorem jVal_spec {B a r sA D : ℕ} {coef u : ℚ} (hcoef : 0 ≤ coef) (h : jChk B a r u = true)
    (hsA : 1 ≤ sA) (hsAD : sA * sA ≤ D) (hDB : D < B) :
    (coef : ℝ) * √(D : ℝ) * SS (D / a) ≤ D * (jVal B a r sA coef u : ℝ) := by
  unfold jVal
  have hc0 : (0 : ℝ) ≤ coef := by exact_mod_cast hcoef
  split_ifs with h0
  · have : D / a = 0 := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; simp
      · exact Nat.eq_zero_of_le_zero (le_trans (Nat.div_le_div_right (show D ≤ B - 1 by omega)) h0.le)
    rw [this]; simp [SS]
  · simp only [jChk, h0, decide_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hra⟩, hl⟩ := h
    have hu := logUp_spec hl
    have hu0 : (0 : ℚ) ≤ u := by
      simp only [logUp, Bool.and_eq_true, decide_eq_true_eq] at hl; exact hl.1.1
    have := jPiece (coef := (coef : ℝ)) (u := (u : ℝ)) hc0 hr hra hsA hsAD (by exact_mod_cast hu0) (by
      intro h1
      refine le_trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < D / a)) ?_) hu
      exact_mod_cast Nat.div_le_div_right (show D ≤ B - 1 by omega))
    push_cast
    convert this using 3; ring

/-! ### The pieces `V ≤ v < W` of `ε(v) v` -/

/-- A point `(V, ℓ, u, r)`: `10¹² ≤ V ≤ A`, `0 < ℓ ≤ log V ≤ u`, `1 ≤ r`, `r² ≤ V`. -/
def vOK (A : ℕ) (v : ℕ × ℚ × ℚ × ℕ) : Bool :=
  decide (1000000000000 ≤ v.1) && decide (v.1 ≤ A) && decide (0 < v.2.1) && logLo v.2.1 v.1 &&
    logUp v.2.2.1 v.1 && decide (1 ≤ v.2.2.2) && decide (v.2.2.2 * v.2.2.2 ≤ v.1)

/-- `ε(V) ≤ 1/ℓ³ + 4.92·10⁻⁷ + 1.4262/r`. -/
def epsq (l : ℚ) (r : ℕ) : ℚ := 1 / l ^ 3 + 492 / 1000000000 + 14262 / 10000 / r

def eChk (A : ℕ) : ℕ × ℚ × ℚ × ℕ → List (ℕ × ℚ × ℚ × ℕ) → Bool
  | v, [] => vOK A v
  | v, w :: ws => vOK A v && decide (v.1 ≤ w.1) && eChk A w ws

def eVal (uB : ℚ) : ℕ × ℚ × ℚ × ℕ → List (ℕ × ℚ × ℚ × ℕ) → ℚ
  | v, [] => epsq v.2.1 v.2.2.2 * (kq * (uB - v.2.1) + 1166 / 1000)
  | v, w :: ws => epsq v.2.1 v.2.2.2 * (kq * (w.2.2.1 - v.2.1) + 588 / 1000) + eVal uB w ws

theorem vOK_spec {A : ℕ} {v : ℕ × ℚ × ℚ × ℕ} (h : vOK A v = true) :
    1000000000000 ≤ v.1 ∧ v.1 ≤ A ∧ ((v.2.1 : ℚ) : ℝ) ≤ Real.log v.1 ∧ Real.log v.1 ≤ v.2.2.1 ∧
      epsv v.1 ≤ (epsq v.2.1 v.2.2.2 : ℝ) ∧ 0 ≤ epsv v.1 := by
  simp only [vOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hl := logLo_spec h4
  have hu := logUp_spec h5
  refine ⟨h1, h2, hl, hu, ?_, epsv_nonneg (by exact_mod_cast (by omega : 1 ≤ v.1))⟩
  have hl0 : (0 : ℝ) < v.2.1 := by exact_mod_cast h3
  have hr0 : (0 : ℝ) < v.2.2.2 := by exact_mod_cast h6
  have hV0 : (0 : ℝ) < v.1 := by exact_mod_cast (by omega : 0 < v.1)
  unfold epsv epsq; push_cast
  have a1 : 1 / Real.log v.1 ^ 3 ≤ 1 / (v.2.1 : ℝ) ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl0.le hl 3)
  have hsr : (v.2.2.2 : ℝ) ≤ √(v.1 : ℝ) := by
    rw [show (v.2.2.2 : ℝ) = √((v.2.2.2 : ℝ) * v.2.2.2) by rw [Real.sqrt_mul_self hr0.le]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast h7)
  have a2 : 1.4262 / √(v.1 : ℝ) ≤ 14262 / 10000 / (v.2.2.2 : ℝ) := by
    rw [show (14262 / 10000 : ℝ) = 1.4262 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) hr0 hsr
  have : (4.92e-7 : ℝ) = 492 / 1000000000 := by norm_num
  linarith

theorem prod_bound {e eq x xq c : ℝ} (he : 0 ≤ e) (heq : e ≤ eq) (hx : 0 ≤ x) (hxq : x ≤ xq) (hc : 0 ≤ c) :
    e * (kap * x + c) ≤ eq * (kq * xq + c) := by
  have hk := kap_le_kq
  have hk0 : 0 ≤ kap := Sqf.kap_pos.le
  have h1 : kap * x ≤ kq * xq := mul_le_mul hk hxq hx (le_trans hk0 hk)
  exact mul_le_mul heq (by linarith) (by positivity) (le_trans he heq)

theorem eSum_le {A D : ℕ} {uB : ℚ} (hAD : A ≤ D) (hB : Real.log D ≤ uB) :
    ∀ (ws : List (ℕ × ℚ × ℚ × ℕ)) (v : ℕ × ℚ × ℚ × ℕ), eChk A v ws = true →
      ∑ m ∈ Ioc 0 (D / v.1), tE D m ≤ D * (eVal uB v ws : ℝ)
  | [], v, h => by
    obtain ⟨h1, h2, hl, -, he, he0⟩ := vOK_spec h
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have hV0 : (0 : ℝ) < v.1 := by exact_mod_cast (by omega : 0 < v.1)
    have hVD : (v.1 : ℝ) ≤ D := by exact_mod_cast (by omega : v.1 ≤ D)
    have := eps_last h1 (by omega : v.1 ≤ D)
    refine le_trans this (mul_le_mul_of_nonneg_left ?_ hD0)
    rw [Real.log_div (by linarith) hV0.ne']
    refine le_trans (prod_bound (x := Real.log D - Real.log v.1) (xq := (uB : ℝ) - (v.2.1 : ℝ)) (c := 1.166)
      he0 he (by have := Real.log_le_log hV0 hVD; linarith) (by linarith) (by norm_num)) (le_of_eq ?_)
    simp only [eVal]; push_cast; norm_num
  | w :: ws, v, h => by
    simp only [eChk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hv, hvw⟩, hr⟩ := h
    have ih := eSum_le hAD hB ws w hr
    have hw : vOK A w = true := by cases ws <;> simp_all [eChk]
    obtain ⟨h1, h2, hl, -, he, he0⟩ := vOK_spec hv
    obtain ⟨w1, w2, -, wu, -, -⟩ := vOK_spec hw
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have hV0 : (0 : ℝ) < v.1 := by exact_mod_cast (by omega : 0 < v.1)
    have hVW : (v.1 : ℝ) ≤ w.1 := by exact_mod_cast hvw
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le (D / w.1)) (Nat.div_le_div_left hvw (by omega))]
    have hp := eps_piece h1 hvw (by omega : w.1 ≤ D)
    have hlog : Real.log ((w.1 : ℝ) / v.1) ≤ ((w.2.2.1 : ℚ) : ℝ) - ((v.2.1 : ℚ) : ℝ) := by
      rw [Real.log_div (by linarith) hV0.ne']; linarith
    have hlog0 : 0 ≤ Real.log ((w.1 : ℝ) / v.1) :=
      Real.log_nonneg (by rw [le_div_iff₀ hV0]; linarith)
    have hq := prod_bound (c := 0.588) he0 he hlog0 hlog (by norm_num)
    have hp' := le_trans hp (mul_le_mul_of_nonneg_left hq hD0)
    have e : ((eVal uB v (w :: ws) : ℚ) : ℝ) = (epsq v.2.1 v.2.2.2 : ℝ) * (kq * ((w.2.2.1 : ℝ) - v.2.1) + 0.588) +
        (eVal uB w ws : ℝ) := by
      simp only [eVal]; push_cast; norm_num
    rw [e, mul_add]
    linarith

/-! ### The boundary term `|ρ(Y)| |M(D/(Y+1))|` -/

def bVal (cs : List (ℕ × ℚ)) (A B Y sA rY : ℕ) : ℚ :=
  2 * (Mrange cs (A / (Y + 1)) ((B - 1) / (Y + 1))).1 / sA + 2 * (Mrange cs (A / (Y + 1)) ((B - 1) / (Y + 1))).2 / rY

theorem bTerm_le [Fact TernaryGoldbach.PlattGRH] {cs : List (ℕ × ℚ)} (hc : McovR (X0 + 1) cs)
    {A B Y sA rY D : ℕ} (hend : endC (X0 + 1) cs = A) (hY : 12 ≤ Y) (hY9 : Y < 1000000000)
    (hlo : 100 ≤ A / (Y + 1)) (hhi : (B - 1) / (Y + 1) < A) (hsA : 1 ≤ sA) (hsAA : sA * sA ≤ A)
    (hrY : 1 ≤ rY) (hrY2 : rY * rY ≤ Y + 1) (hAD : A ≤ D) (hDB : D < B) :
    |ρn Y| * |Mn (D / (Y + 1))| ≤ D * (bVal cs A B Y sA rY : ℝ) := by
  set p := Mrange cs (A / (Y + 1)) ((B - 1) / (Y + 1))
  obtain ⟨p1, p2⟩ := Mrange_nonneg cs (A / (Y + 1)) ((B - 1) / (Y + 1))
  have p1' : (0 : ℝ) ≤ p.1 := by exact_mod_cast p1
  have p2' : (0 : ℝ) ≤ p.2 := by exact_mod_cast p2
  set u := D / (Y + 1) with hu
  have hM : |Mn u| ≤ (p.1 : ℝ) * √(u : ℝ) + (p.2 : ℝ) * u :=
    Mrange_spec hc hlo (by omega) (Nat.div_le_div_right hAD) (Nat.div_le_div_right (by omega))
  have hρ : |ρn Y| ≤ 2 * √(Y : ℝ) := by
    have := rho_le hY
    unfold rb at this
    simp only [show ¬ 1000000000 ≤ Y by omega, show ¬ 32000000001 ≤ Y by omega,
      show ¬ 1000000000000 ≤ Y by omega, if_false] at this
    linarith
  have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hsY := Real.sqrt_nonneg (Y : ℝ)
  have hsu := Real.sqrt_nonneg (u : ℝ)
  have hYu : ((Y : ℝ) + 1) * u ≤ D := by
    have := Nat.div_mul_le_self D (Y + 1)
    have h' : ((u * (Y + 1) : ℕ) : ℝ) ≤ D := by exact_mod_cast this
    push_cast at h'; linarith
  -- `√Y √u ≤ √D ≤ D/sA`
  have h1 : √(Y : ℝ) * √(u : ℝ) ≤ D / sA := by
    rw [← Real.sqrt_mul hY0]
    refine le_trans (Real.sqrt_le_sqrt (by nlinarith)) (sqrt_le_div hsA (le_trans hsAA hAD))
  -- `√Y u ≤ D/rY`
  have h2 : √(Y : ℝ) * u ≤ D / rY := by
    have hr0 : (0 : ℝ) < rY := by exact_mod_cast hrY
    have hY1 : (0 : ℝ) ≤ (Y : ℝ) + 1 := by linarith
    have hs1 := Real.sq_sqrt hY1
    have hsle : √(Y : ℝ) ≤ √((Y : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hrle : (rY : ℝ) ≤ √((Y : ℝ) + 1) := by
      rw [show (rY : ℝ) = √((rY : ℝ) * rY) by rw [Real.sqrt_mul_self hr0.le]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by push_cast at hrY2 ⊢; exact_mod_cast hrY2 : rY * rY ≤ Y + 1))
    rw [le_div_iff₀ hr0]
    have hs10 := Real.sqrt_nonneg ((Y : ℝ) + 1)
    calc √(Y : ℝ) * u * rY ≤ √((Y : ℝ) + 1) * u * √((Y : ℝ) + 1) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hsle hu0) hrle (by positivity) (by positivity)
      _ = ((Y : ℝ) + 1) * u := by rw [mul_comm, ← mul_assoc, ← sq, hs1]
      _ ≤ D := hYu
  have hsA0 : (0 : ℝ) < sA := by exact_mod_cast hsA
  have hr0 : (0 : ℝ) < rY := by exact_mod_cast hrY
  have e : (D : ℝ) * (bVal cs A B Y sA rY : ℝ) = 2 * p.1 * (D / sA) + 2 * p.2 * (D / rY) := by
    show (D : ℝ) * ((2 * p.1 / sA + 2 * p.2 / rY : ℚ) : ℝ) = _
    push_cast; field_simp
  rw [e]
  calc |ρn Y| * |Mn u| ≤ 2 * √(Y : ℝ) * ((p.1 : ℝ) * √(u : ℝ) + (p.2 : ℝ) * u) :=
        mul_le_mul hρ hM (abs_nonneg _) (by positivity)
    _ = 2 * p.1 * (√(Y : ℝ) * √(u : ℝ)) + 2 * p.2 * (√(Y : ℝ) * u) := by ring
    _ ≤ 2 * p.1 * (D / sA) + 2 * p.2 * (D / rY) := by
        gcongr

/-! ### One cell -/

/-- The data of a cell `[A, B)`. -/
structure CellD where
  A : ℕ
  B : ℕ
  /-- the split point of the identity -/
  Y : ℕ
  /-- `sA² ≤ A` -/
  sA : ℕ
  /-- `L ≤ log A` -/
  L : ℚ
  /-- the ends `β` of the blocks `(α, β]` of the `k`-sum, ending at `Y` -/
  ks : List ℕ
  /-- certificates of the `√`-pieces at `Y + 1`, `10⁹`, `32 000 000 001` -/
  r1 : ℕ
  u1 : ℚ
  r2 : ℕ
  u2 : ℚ
  r3 : ℕ
  u3 : ℚ
  /-- `log(B − 1) ≤ uB` -/
  uB : ℚ
  /-- the points `V` of the `ε`-pieces, from `10¹²` (for `B > 10¹²`) -/
  vs : List (ℕ × ℚ × ℚ × ℕ)
  ν : ℚ
  η : ℚ
  I' : ℚ

def epsPart (d : CellD) : ℚ :=
  if d.B ≤ 1000000000000 then 0 else
    match d.vs with
    | [] => 0
    | v :: ws => eVal d.uB v ws

def epsChk (d : CellD) : Bool :=
  if d.B ≤ 1000000000000 then true else
    match d.vs with
    | [] => false
    | v :: ws => decide (v.1 = 1000000000000) && eChk d.A v ws && logUp d.uB (d.B - 1)

/-- `X` with `|N(D)| ≤ |M(D)| + X D` on the cell. -/
def Xq (cs : List (ℕ × ℚ)) (d : CellD) : ℚ :=
  1 / d.A + kVal cs d.A d.B d.sA 1 d.ks + jVal d.B (d.Y + 1) d.r1 d.sA 2 d.u1 +
    jVal d.B 1000000000 d.r2 d.sA (71 / 2) d.u2 + jVal d.B 32000000001 d.r3 d.sA 72 d.u3 + epsPart d +
    bVal cs d.A d.B d.Y d.sA d.r1

def C0q : ℚ := 626

def chkCell (cs : List (ℕ × ℚ)) (I : ℚ) (d : CellD) : Bool :=
  decide (X0 < d.A) && decide (d.A < d.B) && decide (1 ≤ d.sA) && decide (d.sA * d.sA ≤ d.A) &&
  decide (1 < d.L) && logLo d.L d.A && decide (12 ≤ d.Y) && decide (d.Y < 1000000000) &&
  decide (100 ≤ d.A / (d.Y + 1)) && decide ((d.B - 1) / (d.Y + 1) < d.A) &&
  decide (1 ≤ d.r1) && decide (d.r1 * d.r1 ≤ d.Y + 1) &&
  kChk cs d.A d.B 1 d.ks && decide (lastK 1 d.ks = d.Y) &&
  jChk d.B (d.Y + 1) d.r1 d.u1 && jChk d.B 1000000000 d.r2 d.u2 && jChk d.B 32000000001 d.r3 d.u3 &&
  epsChk d && decide (0 ≤ d.ν) &&
  decide (Xq cs d + (C0q + I) / d.A + d.ν * (((d.B : ℚ) - d.A) / d.B) / d.L ^ 2 ≤ d.ν * (1 - 1 / d.L)) &&
  decide (d.ν / d.L + (C0q + I) / d.A + d.ν * (((d.B : ℚ) - d.A) / d.B) / d.L ^ 2 ≤ d.η) &&
  decide (I + d.ν * ((d.B : ℚ) - d.A) / d.L ^ 2 ≤ d.I')

theorem eps_part_le {d : CellD} (h : epsChk d = true) {D : ℕ} (hA : 0 < d.A) (hAD : d.A ≤ D) (hDB : D < d.B) :
    ∑ m ∈ Ioc 0 (D / 1000000000000), tE D m ≤ D * (epsPart d : ℝ) := by
  unfold epsChk at h; unfold epsPart
  split_ifs at h ⊢ with hB
  · rw [show D / 1000000000000 = 0 by apply Nat.div_eq_of_lt; omega]; simp
  · rcases hv : d.vs with _ | ⟨v, ws⟩
    · rw [hv] at h; simp at h
    · rw [hv] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hlog : Real.log D ≤ d.uB := by
        refine le_trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < D)) ?_) (logUp_spec h3)
        exact_mod_cast (by omega : D ≤ d.B - 1)
      have := eSum_le hAD hlog ws v h2
      rw [h1] at this
      exact this

variable [Fact TernaryGoldbach.PlattGRH]

theorem N_le_X {cs : List (ℕ × ℚ)} (hc : McovR (X0 + 1) cs) {I : ℚ} {d : CellD}
    (hend : endC (X0 + 1) cs = d.A) (h : chkCell cs I d = true) {D : ℕ} (hAD : d.A ≤ D) (hDB : D < d.B) :
    |Nn D| ≤ |Mn D| + (Xq cs d : ℝ) * D := by
  simp only [chkCell, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hX0, hAB⟩, hsA⟩, hsAA⟩, hL1⟩, hL⟩, hY⟩, hY9⟩, hlo⟩, hhi⟩, hr1⟩, hr1Y⟩,
    hk⟩, hkY⟩, hj1⟩, hj2⟩, hj3⟩, he⟩, hν⟩, hcond⟩, hη⟩, hI'⟩ := h
  have hYD : d.Y ≤ D := by
    have : d.Y + 1 ≤ d.A := by
      by_contra hc'; push_neg at hc'
      have : d.A / (d.Y + 1) = 0 := Nat.div_eq_of_lt hc'
      omega
    omega
  have hN := N_abs_le (D := D) (Y := d.Y) (by omega) hYD
  have hK := kSum_le hc hend hsA hsAA hAD hDB d.ks 1 hk
  rw [hkY] at hK
  have hJ := J_le (D := D) (by omega : 11 ≤ d.Y) (by omega : d.Y + 1 ≤ 1000000000000)
  have hsAD : d.sA * d.sA ≤ D := le_trans hsAA hAD
  have j1 := jVal_spec (coef := 2) (by norm_num) hj1 hsA hsAD hDB
  have j2 := jVal_spec (coef := 71 / 2) (by norm_num) hj2 hsA hsAD hDB
  have j3 := jVal_spec (coef := 72) (by norm_num) hj3 hsA hsAD hDB
  have hE := eps_part_le he (by unfold X0 at hX0; omega) hAD hDB
  have hB := bTerm_le hc hend hY hY9 hlo hhi hsA hsAA hr1 hr1Y hAD hDB
  have h1 : (1 : ℝ) ≤ D * (1 / (d.A : ℝ)) := by
    have hA0 : (0 : ℝ) < d.A := by exact_mod_cast (by omega : 0 < d.A)
    rw [mul_one_div, le_div_iff₀ hA0, one_mul]; exact_mod_cast hAD
  have eX : (Xq cs d : ℝ) = 1 / (d.A : ℝ) + (kVal cs d.A d.B d.sA 1 d.ks : ℝ) +
      (jVal d.B (d.Y + 1) d.r1 d.sA 2 d.u1 : ℝ) + (jVal d.B 1000000000 d.r2 d.sA (71 / 2) d.u2 : ℝ) +
      (jVal d.B 32000000001 d.r3 d.sA 72 d.u3 : ℝ) + (epsPart d : ℝ) + (bVal cs d.A d.B d.Y d.sA d.r1 : ℝ) := by
    simp only [Xq, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [eX]
  have c2 : ((2 : ℚ) : ℝ) = 2 := by norm_num
  have c3 : ((71 / 2 : ℚ) : ℝ) = 35.5 := by norm_num
  have c4 : ((72 : ℚ) : ℝ) = 72 := by norm_num
  rw [c2] at j1; rw [c3] at j2; rw [c4] at j3
  nlinarith

/-- **One cell**: a successful check gives `|M(u)| ≤ η u` on `[A, B)` and the update of the
`N`-sum. -/
theorem cell_sound {cs : List (ℕ × ℚ)} (hc : McovR (X0 + 1) cs) {I : ℚ} {d : CellD}
    (hend : endC (X0 + 1) cs = d.A) (hI : ∑ n ∈ Ioo X0 d.A, |Nn n| * wN n ≤ I)
    (h : chkCell cs I d = true) :
    McovR (X0 + 1) (cs ++ [(d.B, d.η)]) ∧ endC (X0 + 1) (cs ++ [(d.B, d.η)]) = d.B ∧
      ∑ n ∈ Ioo X0 d.B, |Nn n| * wN n ≤ d.I' := by
  have hNM := fun D (h1 : d.A ≤ D) (h2 : D < d.B) => N_le_X hc hend h h1 h2
  simp only [chkCell, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hX0, hAB⟩, hsA⟩, hsAA⟩, hL1⟩, hL⟩, hY⟩, hY9⟩, hlo⟩, hhi⟩, hr1⟩, hr1Y⟩,
    hk⟩, hkY⟩, hj1⟩, hj2⟩, hj3⟩, he⟩, hν⟩, hcond⟩, hη⟩, hI'⟩ := h
  have hLA := logLo_spec hL
  have hL1' : (1 : ℝ) < d.L := by exact_mod_cast hL1
  have hν' : (0 : ℝ) ≤ d.ν := by exact_mod_cast hν
  have hcond' := (Rat.cast_le (K := ℝ)).2 hcond
  have hη' := (Rat.cast_le (K := ℝ)).2 hη
  have hI'' := (Rat.cast_le (K := ℝ)).2 hI'
  push_cast at hcond' hη' hI''
  have hC0 : |Mn X0 - Nn X0 / Real.log ((X0 : ℝ) + 1)| ≤ ((C0q : ℚ) : ℝ) := by
    have := C0_le; norm_num [C0q]; exact this
  obtain ⟨-, hM, hS⟩ := cell_step (X0 := X0) (A := d.A) (B := d.B) (by norm_num [X0]) hX0 hAB
    (X := (Xq cs d : ℝ)) (C0 := ((C0q : ℚ) : ℝ)) (I := (I : ℝ)) (ν := (d.ν : ℝ)) (L := (d.L : ℝ))
    hL1' hLA hν' hC0 hI hNM (by linarith)
  refine McovR_append cs (X0 + 1) d.B d.η hc ?_ |>.imp_right ?_ |> fun ⟨a, b⟩ => ⟨a, b, ?_⟩
  · intro u h1 h2
    rw [hend] at h1
    have := hM u h1 h2
    have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    refine le_trans this (mul_le_mul_of_nonneg_right ?_ hu)
    linarith
  · exact id
  · linarith

end TernaryGoldbach.Prelim.Sch
