/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.LambdaInputs
import RSBounds.LambdaCert.Masks
import RSBounds.LambdaCert.LogSeries
import Mathlib.Tactic

/-!
# Soundness of the checker

`Inv s` says what a state means: bounds, at scale `S`, for `log q`, `A(n)`, `G(n)`, `H(n)`, and
`A(m) ≤ 2 (m - 1)` for all `1 ≤ m ≤ n`.  It holds for `init` and is preserved by `checkSeg`.
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

open scoped ArithmeticFunction.vonMangoldt
open Real

/-- `A(n) = ∑_{2 ≤ k ≤ n} |Λ(k) - 1|`. -/
noncomputable def Asum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 2 n, |Λ k - 1|

/-- The meaning of a state. -/
structure Inv (s : State) : Prop where
  n_pos : 1 ≤ s.n
  n_le : s.n ≤ TOP
  q_pos : 1 ≤ s.q
  q_le : s.q ≤ s.n
  llo : (s.llo : ℝ) ≤ S * log s.q
  lhi : (S : ℝ) * log s.q ≤ s.lhi
  ahi : (S : ℝ) * Asum s.n ≤ s.ahi
  hist : ∀ m, 1 ≤ m → m ≤ s.n → Asum m ≤ 2 * ((m : ℝ) - 1)
  glo : (s.glo : ℝ) ≤ S * G s.n
  ghi : (S : ℝ) * G s.n ≤ s.ghi
  hlo : (s.hlo : ℝ) ≤ S * H s.n
  hhi : (S : ℝ) * H s.n ≤ s.hhi

theorem div_raw (x y : ℕ) : Nat.div x y = x / y := rfl

theorem mod_raw (x y : ℕ) : Nat.mod x y = x % y := rfl

theorem S_eq : S = 10 ^ 24 := by norm_num [S]

theorem R_eq : R = 10 ^ 15 := by norm_num [R]

theorem RR_eq : RR = R * R := by norm_num [R, RR]

theorem SR_eq : SR = S * R := by norm_num [S, R, SR]

/-! ## The sums -/

theorem Asum_succ (n : ℕ) (hn : 1 ≤ n) : Asum (n + 1) = Asum n + |Λ (n + 1) - 1| :=
  Finset.sum_Icc_succ_top (by omega) _

theorem G_succ (n : ℕ) (hn : 1 ≤ n) :
    G (n + 1) = G n + |Λ (n + 1) - 1| / ((n + 1 : ℕ) : ℝ) :=
  Finset.sum_Icc_succ_top (by omega) _

theorem H_succ (n : ℕ) (hn : 1 ≤ n) :
    H (n + 1) = H n + |Λ (n + 1) - 1| / Real.sqrt ((n + 1 : ℕ) : ℝ) :=
  Finset.sum_Icc_succ_top (by omega) _

/-! ## Square roots -/

theorem sqrt_bounds (k x : ℕ) (hx : 1 ≤ x) (h1 : x * x ≤ k * RR) (h2 : k * RR ≤ (x + 1) * (x + 1)) :
    (R : ℝ) / (x + 1) ≤ 1 / Real.sqrt k ∧ 1 / Real.sqrt k ≤ (R : ℝ) / x := by
  have hR : (0 : ℝ) < R := by norm_num [R]
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1' : (x : ℝ) ^ 2 ≤ k * (R : ℝ) ^ 2 := by
    have : ((x * x : ℕ) : ℝ) ≤ ((k * (R * R) : ℕ) : ℝ) := by rw [← RR_eq]; exact_mod_cast h1
    push_cast at this; nlinarith
  have h2' : (k : ℝ) * (R : ℝ) ^ 2 ≤ ((x : ℝ) + 1) ^ 2 := by
    have : ((k * (R * R) : ℕ) : ℝ) ≤ (((x + 1) * (x + 1) : ℕ) : ℝ) := by
      rw [← RR_eq]; exact_mod_cast h2
    push_cast at this; nlinarith
  have e : Real.sqrt ((k : ℝ) * (R : ℝ) ^ 2) = R * Real.sqrt k := by
    rw [Real.sqrt_mul hk0, Real.sqrt_sq hR.le]; ring
  have hA : (x : ℝ) ≤ R * Real.sqrt k := by
    rw [← e]; exact (Real.le_sqrt' (by linarith)).2 h1'
  have hB : (R : ℝ) * Real.sqrt k ≤ x + 1 := by
    rw [← e]; exact Real.sqrt_le_iff.2 ⟨by positivity, h2'⟩
  have hk1 : (1 : ℝ) ≤ k := by
    by_contra hc
    rw [not_le] at hc
    have hk00 : k = 0 := by
      have : (k : ℝ) < 1 := hc
      exact_mod_cast (show k < 1 by exact_mod_cast this) |> Nat.lt_one_iff.1
    subst hk00
    simp at h1'
    nlinarith
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 (by linarith)
  constructor
  · rw [div_le_div_iff₀ (by linarith) hsk]; linarith
  · rw [div_le_div_iff₀ hsk (by linarith)]; linarith

/-! ## Generic update of the sums -/

theorem update_sums (s : State) (k x al ah : ℕ) (hs : Inv s) (hk : k = s.n + 1)
    (hαl : (al : ℝ) ≤ S * |Λ k - 1|) (hαh : (S : ℝ) * |Λ k - 1| ≤ ah)
    (hx1 : 1 ≤ x) (hxx : x * x ≤ k * RR) (hxk : k * RR ≤ (x + 1) * (x + 1))
    (hA : s.ahi + ah ≤ 2 * s.n * S) :
    (S : ℝ) * Asum k ≤ ((s.ahi + ah : ℕ) : ℝ) ∧
      (∀ m, 1 ≤ m → m ≤ k → Asum m ≤ 2 * ((m : ℝ) - 1)) ∧
      ((s.glo + al / k : ℕ) : ℝ) ≤ S * G k ∧ (S : ℝ) * G k ≤ ((s.ghi + (ah / k + 1) : ℕ) : ℝ) ∧
      ((s.hlo + al * R / (x + 1) : ℕ) : ℝ) ≤ S * H k ∧
      (S : ℝ) * H k ≤ ((s.hhi + (ah * R / x + 1) : ℕ) : ℝ) := by
  have hn := hs.n_pos
  subst hk
  have hS := S_pos
  have hk0 : (0 : ℝ) < ((s.n + 1 : ℕ) : ℝ) := by positivity
  have hα0 : (0 : ℝ) ≤ |Λ (s.n + 1) - 1| := abs_nonneg _
  set α := |Λ (s.n + 1) - 1| with hα
  obtain ⟨hsl, hsh⟩ := sqrt_bounds (s.n + 1) x hx1 hxx hxk
  have hsq0 : 0 < Real.sqrt ((s.n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hk0
  have hAk : (S : ℝ) * Asum (s.n + 1) ≤ ((s.ahi + ah : ℕ) : ℝ) := by
    rw [Asum_succ s.n hn]; push_cast; nlinarith [hs.ahi]
  refine ⟨hAk, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm1 hm
    rcases Nat.lt_or_ge m (s.n + 1) with hlt | hge
    · exact hs.hist m hm1 (by omega)
    · have hm' : m = s.n + 1 := by omega
      subst hm'
      have hA' : ((s.ahi + ah : ℕ) : ℝ) ≤ ((2 * s.n * S : ℕ) : ℝ) := by exact_mod_cast hA
      push_cast at hA' ⊢
      have : (S : ℝ) * Asum (s.n + 1) ≤ 2 * s.n * S := by push_cast at hAk; linarith
      have : Asum (s.n + 1) ≤ 2 * s.n := by
        by_contra hc; rw [not_le] at hc; nlinarith
      linarith
  · rw [G_succ s.n hn]
    have h1 := cast_div_le' al (s.n + 1)
    have h2 : (al : ℝ) / ((s.n + 1 : ℕ) : ℝ) ≤ S * α / ((s.n + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hαl hk0.le
    have hg := hs.glo
    push_cast at h1 h2 ⊢
    rw [mul_add, mul_div_assoc']
    linarith
  · rw [G_succ s.n hn]
    have h1 := le_cast_div_add_one ah (s.n + 1) (by omega)
    have h2 : S * α / ((s.n + 1 : ℕ) : ℝ) ≤ (ah : ℝ) / ((s.n + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hαh hk0.le
    have hg := hs.ghi
    push_cast at h1 h2 ⊢
    rw [mul_add, mul_div_assoc']
    linarith
  · rw [H_succ s.n hn]
    have h1 := cast_div_le' (al * R) (x + 1)
    have hal0 : (0 : ℝ) ≤ al := Nat.cast_nonneg al
    have h2 : ((al * R : ℕ) : ℝ) / ((x + 1 : ℕ) : ℝ) ≤ S * α / Real.sqrt ((s.n + 1 : ℕ) : ℝ) := by
      have e1 : ((al * R : ℕ) : ℝ) / ((x + 1 : ℕ) : ℝ) = al * ((R : ℝ) / (x + 1)) := by
        push_cast; ring
      have e2 : S * α / Real.sqrt ((s.n + 1 : ℕ) : ℝ) = (S * α) * (1 / Real.sqrt ((s.n + 1 : ℕ) : ℝ)) := by
        ring
      rw [e1, e2]
      have hR0 : (0 : ℝ) ≤ (R : ℝ) / (x + 1) := by positivity
      calc (al : ℝ) * ((R : ℝ) / (x + 1)) ≤ (S * α) * ((R : ℝ) / (x + 1)) :=
            mul_le_mul_of_nonneg_right hαl hR0
        _ ≤ (S * α) * (1 / Real.sqrt ((s.n + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hsl (by positivity)
    have hh := hs.hlo
    push_cast at h1 h2 ⊢
    rw [mul_add, mul_div_assoc']
    linarith
  · rw [H_succ s.n hn]
    have hx0 : 0 < x := by omega
    have h1 := le_cast_div_add_one (ah * R) x hx0
    have h2 : S * α / Real.sqrt ((s.n + 1 : ℕ) : ℝ) ≤ ((ah * R : ℕ) : ℝ) / (x : ℝ) := by
      have e1 : ((ah * R : ℕ) : ℝ) / (x : ℝ) = ah * ((R : ℝ) / x) := by push_cast; ring
      have e2 : S * α / Real.sqrt ((s.n + 1 : ℕ) : ℝ) = (S * α) * (1 / Real.sqrt ((s.n + 1 : ℕ) : ℝ)) := by
        ring
      rw [e1, e2]
      have hsq0' : (0 : ℝ) ≤ 1 / Real.sqrt ((s.n + 1 : ℕ) : ℝ) := by positivity
      calc (S * α) * (1 / Real.sqrt ((s.n + 1 : ℕ) : ℝ)) ≤ ah * (1 / Real.sqrt ((s.n + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hαh hsq0'
        _ ≤ ah * ((R : ℝ) / x) := mul_le_mul_of_nonneg_left hsh (Nat.cast_nonneg _)
    have hh := hs.hhi
    push_cast at h1 h2 ⊢
    rw [mul_add, mul_div_assoc']
    linarith


/-! ## The step -/

theorem State.eq_of_beq {a b : State} (h : a.beq b = true) : a = b := by
  cases a; cases b
  simp only [State.beq, Bool.and_eq_true, Nat.beq_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

theorem commonOK_spec {s t : State} {k x : ℕ} (h : commonOK s t k x = true) :
    1 ≤ x ∧ x * x ≤ k * RR ∧ k * RR ≤ (x + 1) * (x + 1) ∧ k ≤ TOP ∧ t.ahi ≤ 2 * s.n * S := by
  simp only [commonOK, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem aBounds_spec {lo hi al ah : ℕ} (h : aBounds lo hi = (true, al, ah)) {lam : ℝ}
    (hlo : (lo : ℝ) ≤ S * lam) (hhi : (S : ℝ) * lam ≤ hi) :
    (al : ℝ) ≤ S * |lam - 1| ∧ (S : ℝ) * |lam - 1| ≤ ah := by
  have hS := S_pos
  unfold aBounds at h
  cases h1 : Nat.ble hi S with
  | true =>
    rw [h1] at h
    simp only [Bool.cond_true, Prod.mk.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := h
    have hle : hi ≤ S := by simpa using h1
    have hle' : (hi : ℝ) ≤ S := by exact_mod_cast hle
    have hloS : lo ≤ S := by
      have : (lo : ℝ) ≤ S := by linarith
      exact_mod_cast this
    have hlam : lam ≤ 1 := by
      by_contra hc
      have : (S : ℝ) * 1 < S * lam := mul_lt_mul_of_pos_left (by linarith) hS
      linarith
    rw [abs_of_nonpos (by linarith)]
    simp only [Nat.sub_eq]
    push_cast [hle, hloS]
    constructor <;> nlinarith
  | false =>
    rw [h1] at h
    simp only [Bool.cond_false] at h
    cases h2 : Nat.ble S lo with
    | true =>
      rw [h2] at h
      simp only [Bool.cond_true, Prod.mk.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      have hle : S ≤ lo := by simpa using h2
      have hle' : (S : ℝ) ≤ lo := by exact_mod_cast hle
      have hhiS : S ≤ hi := by
        have : (S : ℝ) ≤ hi := by linarith
        exact_mod_cast this
      have hlam : 1 ≤ lam := by
        by_contra hc
        have : (S : ℝ) * lam < S * 1 := mul_lt_mul_of_pos_left (by linarith) hS
        linarith
      rw [abs_of_nonneg (by linarith)]
      simp only [Nat.sub_eq]
      push_cast [hle, hhiS]
      constructor <;> nlinarith
    | false =>
      rw [h2] at h
      simp at h

theorem ppFinish_some {s t : State} {k x l1 l2 : ℕ} {a : Bool × ℕ × ℕ}
    (h : ppFinish s k x l1 l2 a = some t) :
    a.1 = true ∧ s.q < k ∧ 3 * (k - s.q) ≤ k + s.q ∧ commonOK s t k x = true ∧
      t = nextPP s k x l1 l2 a.2.1 a.2.2 := by
  unfold ppFinish at h
  beta_reduce at h
  by_cases hc : (a.1 && Nat.blt s.q k && Nat.ble (Nat.mul 3 (Nat.sub k s.q)) (Nat.add k s.q) &&
      commonOK s (nextPP s k x l1 l2 a.2.1 a.2.2) k x) = true
  · rw [hc] at h
    simp only [Bool.cond_true, Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq, Nat.sub_eq, Nat.add_eq,
      and_assoc] at hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact ⟨h1, h2, h3, h4, rfl⟩
  · rw [Bool.not_eq_true] at hc
    rw [hc] at h
    simp at h

theorem stepPP_some {s t : State} {k x j : ℕ} (h : stepPP s k x j = some t) :
    (aBounds ((s.llo + (logRatio (k - s.q) (k + s.q)).1) / j)
        ((s.lhi + (logRatio (k - s.q) (k + s.q)).2) / j + 1)).1 = true ∧
      s.q < k ∧ 3 * (k - s.q) ≤ k + s.q ∧ commonOK s t k x = true ∧
      t = nextPP s k x (s.llo + (logRatio (k - s.q) (k + s.q)).1)
        (s.lhi + (logRatio (k - s.q) (k + s.q)).2)
        (aBounds ((s.llo + (logRatio (k - s.q) (k + s.q)).1) / j)
          ((s.lhi + (logRatio (k - s.q) (k + s.q)).2) / j + 1)).2.1
        (aBounds ((s.llo + (logRatio (k - s.q) (k + s.q)).1) / j)
          ((s.lhi + (logRatio (k - s.q) (k + s.q)).2) / j + 1)).2.2 :=
  ppFinish_some h

theorem nextPP_eq (s : State) (k x l1 l2 al ah : ℕ) :
    nextPP s k x l1 l2 al ah = ⟨k, k, l1, l2, s.ahi + ah, s.glo + al / k, s.ghi + (ah / k + 1),
      s.hlo + al * R / (x + 1), s.hhi + (ah * R / x + 1), x⟩ := rfl

theorem nextNP_eq (s : State) (k x : ℕ) :
    nextNP s k x = ⟨k, s.q, s.llo, s.lhi, s.ahi + S, s.glo + S / k, s.ghi + (S / k + 1),
      s.hlo + S * R / (x + 1), s.hhi + (S * R / x + 1), x⟩ := by
  rw [← SR_eq]; rfl

theorem inv_stepPP {s t : State} {k x j : ℕ} (hs : Inv s) (hk : k = s.n + 1) (hj : 1 ≤ j)
    (hpp : ∃ p, p.Prime ∧ p ^ j = k) (h : stepPP s k x j = some t) : Inv t ∧ t.n = k := by
  obtain ⟨ha, hqk, h3, hok, rfl⟩ := stepPP_some h
  have hk1 : 1 ≤ k := by omega
  generalize hd : logRatio (k - s.q) (k + s.q) = d at ha hok ⊢
  generalize hab : aBounds ((s.llo + d.1) / j) ((s.lhi + d.2) / j + 1) = a at ha hok ⊢
  obtain ⟨b, al, ah⟩ := a
  simp only at ha
  subst ha
  rw [nextPP_eq] at hok ⊢
  obtain ⟨hx1, hxx, hxk, hkT, hA⟩ := commonOK_spec hok
  simp only at hA
  have hS := S_pos
  -- logarithm of `k`
  have hq0 := hs.q_pos
  have hlog := logRatio_sound k s.q (by omega) hqk h3
  rw [hd] at hlog
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hl1 : ((s.llo + d.1 : ℕ) : ℝ) ≤ S * log k := by
    push_cast; nlinarith [hs.llo, hlog.1]
  have hl2 : (S : ℝ) * log k ≤ ((s.lhi + d.2 : ℕ) : ℝ) := by
    push_cast; nlinarith [hs.lhi, hlog.2]
  -- `Λ k = log p` and `log k = j log p`
  obtain ⟨p, hp, hpk⟩ := hpp
  have hΛ : Λ k = log p := by
    rw [← hpk, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlogk : log k = j * log p := by
    rw [← hpk]; push_cast; rw [Real.log_pow]
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlamlo : (((s.llo + d.1) / j : ℕ) : ℝ) ≤ S * Λ k := by
    have := cast_div_le' (s.llo + d.1) j
    rw [hΛ]
    calc (((s.llo + d.1) / j : ℕ) : ℝ) ≤ ((s.llo + d.1 : ℕ) : ℝ) / j := this
      _ ≤ S * log k / j := div_le_div_of_nonneg_right hl1 hj0.le
      _ = S * log p := by rw [hlogk]; field_simp
  have hlamhi : (S : ℝ) * Λ k ≤ (((s.lhi + d.2) / j + 1 : ℕ) : ℝ) := by
    have := le_cast_div_add_one (s.lhi + d.2) j hj
    rw [hΛ]
    calc (S : ℝ) * log p = S * log k / j := by rw [hlogk]; field_simp
      _ ≤ ((s.lhi + d.2 : ℕ) : ℝ) / j := div_le_div_of_nonneg_right hl2 hj0.le
      _ ≤ _ := this
  obtain ⟨hal, hah⟩ := aBounds_spec hab hlamlo hlamhi
  obtain ⟨hAk, hhist, hglo, hghi, hhlo, hhhi⟩ :=
    update_sums s k x al ah hs hk hal hah hx1 hxx hxk hA
  refine ⟨⟨hk1, hkT, hk1, le_rfl, hl1, hl2, hAk, hhist, hglo, hghi, hhlo, hhhi⟩, rfl⟩

theorem inv_stepNP {s t : State} {k x : ℕ} (hs : Inv s) (hk : k = s.n + 1)
    (hnpp : ¬ IsPrimePow k) (h : stepNP s k x = some t) : Inv t ∧ t.n = k := by
  unfold stepNP at h
  beta_reduce at h
  by_cases hc : commonOK s (nextNP s k x) k x = true
  · rw [hc] at h
    simp only [Bool.cond_true, Option.some.injEq] at h
    subst h
    rw [nextNP_eq] at hc ⊢
    obtain ⟨hx1, hxx, hxk, hkT, hA⟩ := commonOK_spec hc
    simp only at hA
    have hΛ : Λ k = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hnpp
    have hα : |Λ k - 1| = 1 := by rw [hΛ]; norm_num
    have hal : ((S : ℕ) : ℝ) ≤ S * |Λ k - 1| := by rw [hα, mul_one]
    have hah : (S : ℝ) * |Λ k - 1| ≤ ((S : ℕ) : ℝ) := by rw [hα, mul_one]
    obtain ⟨hAk, hhist, hglo, hghi, hhlo, hhhi⟩ :=
      update_sums s k x S S hs hk hal hah hx1 hxx hxk hA
    have hq := hs.q_le
    exact ⟨⟨show 1 ≤ k by omega, hkT, hs.q_pos, show s.q ≤ k by omega, hs.llo, hs.lhi, hAk, hhist,
      hglo, hghi, hhlo, hhhi⟩, rfl⟩
  · rw [Bool.not_eq_true] at hc
    rw [hc] at h
    simp at h

theorem hpLookup_spec (k : ℕ) :
    ∀ l : List (ℕ × ℕ × ℕ), hpLookup k l ≠ 0 → ∃ e ∈ l, e.1 = k ∧ e.2.2 = hpLookup k l := by
  intro l
  induction l with
  | nil => intro h; simp [hpLookup] at h
  | cons e l ih =>
    intro h
    have he : hpLookup k (e :: l) = cond (Nat.beq e.1 k) e.2.2 (hpLookup k l) := rfl
    cases hb : Nat.beq e.1 k with
    | true =>
      rw [he, hb, Bool.cond_true]
      exact ⟨e, List.mem_cons_self, by simpa using hb, rfl⟩
    | false =>
      rw [he, hb, Bool.cond_false] at h ⊢
      obtain ⟨e', he', h1, h2⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩

theorem stepPP_n {s t : State} {k x j : ℕ} (h : stepPP s k x j = some t) : k ≤ TOP := by
  obtain ⟨-, -, -, hok, -⟩ := stepPP_some h
  exact (commonOK_spec hok).2.2.2.1

theorem stepNP_n {s t : State} {k x : ℕ} (h : stepNP s k x = some t) : k ≤ TOP := by
  unfold stepNP at h
  beta_reduce at h
  by_cases hc : commonOK s (nextNP s k x) k x = true
  · exact (commonOK_spec hc).2.2.2.1
  · rw [Bool.not_eq_true] at hc
    rw [hc] at h
    simp at h

theorem inv_advance {s t : State} {cm hm : ℕ} (hs : Inv s) (hmf : MaskFacts cm hm (s.n + 1))
    (h : advance s (cm % 2) (hm % 2) = some t) : Inv t ∧ t.n = s.n + 1 := by
  unfold advance advanceX at h
  generalize newton _ _ _ = x at h
  have hk : Nat.add s.n 1 = s.n + 1 := rfl
  rw [hk] at h
  cases hhb : Nat.beq (hm % 2) 1 with
  | true =>
    rw [hhb, Bool.cond_true] at h
    unfold stepHP at h
    cases hj : Nat.beq (hpLookup (s.n + 1) hpList) 0 with
    | true =>
      rw [hj] at h
      simp at h
    | false =>
      rw [hj, Bool.cond_false] at h
      have hj0 : hpLookup (s.n + 1) hpList ≠ 0 := Nat.ne_of_beq_eq_false hj
      obtain ⟨e, he, he1, he2⟩ := hpLookup_spec (s.n + 1) hpList hj0
      obtain ⟨hp, hpe, hj1⟩ := hpList_sound he
      refine inv_stepPP hs rfl (by omega) ⟨e.2.1, hp, ?_⟩ h
      rw [← he2, hpe, he1]
  | false =>
    rw [hhb, Bool.cond_false] at h
    have hhb' : hm % 2 ≠ 1 := Nat.ne_of_beq_eq_false hhb
    cases hcb : Nat.beq (cm % 2) 0 with
    | true =>
      rw [hcb, Bool.cond_true] at h
      have hcb' : cm % 2 = 0 := Nat.eq_of_beq_eq_true hcb
      have hkT := stepPP_n h
      have hprime := (hmf hkT).1 hcb'
      exact inv_stepPP hs rfl le_rfl ⟨s.n + 1, hprime, pow_one _⟩ h
    | false =>
      rw [hcb, Bool.cond_false] at h
      have hcb' : cm % 2 ≠ 0 := Nat.ne_of_beq_eq_false hcb
      have hkT := stepNP_n h
      exact inv_stepNP hs rfl ((hmf hkT).2 hcb' hhb') h

/-! ## Segments -/

theorem runSeg_succ (f : ℕ) (s : State) (cm hm : ℕ) :
    runSeg (f + 1) s cm hm = (advance s (cm % 2) (hm % 2)).bind (fun t => runSeg f t (cm / 2) (hm / 2)) :=
  rfl

theorem inv_runSeg : ∀ (fuel : ℕ) (s : State) (cm hm : ℕ) (t : State), Inv s →
    (∀ i < fuel, MaskFacts (cm / 2 ^ i) (hm / 2 ^ i) (s.n + 1 + i)) →
    runSeg fuel s cm hm = some t → Inv t := by
  intro fuel
  induction fuel with
  | zero =>
    intro s cm hm t hs _ h
    have : runSeg 0 s cm hm = some s := rfl
    rw [this] at h
    cases h
    exact hs
  | succ f ih =>
    intro s cm hm t hs hmf h
    rw [runSeg_succ] at h
    cases hadv : advance s (cm % 2) (hm % 2) with
    | none => rw [hadv] at h; simp at h
    | some u =>
      rw [hadv] at h
      simp only [Option.bind_some] at h
      have h0 := hmf 0 (by omega)
      simp only [pow_zero, Nat.div_one, add_zero] at h0
      obtain ⟨hu, hun⟩ := inv_advance hs h0 hadv
      refine ih u (cm / 2) (hm / 2) t hu ?_ h
      intro i hi
      have := hmf (i + 1) (by omega)
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, hun]
      rw [pow_succ, mul_comm] at this
      rw [show s.n + 1 + 1 + i = s.n + 1 + (i + 1) by omega]
      exact this

theorem inv_checkSeg {a b : State} (h : checkSeg a b = true) (ha : Inv a) : Inv b := by
  unfold checkSeg at h
  split at h
  · rename_i c hc
    have hcb := State.eq_of_beq h
    subst hcb
    refine inv_runSeg _ a _ _ c ha ?_ hc
    intro i hi
    have := maskFacts_seg (a.n + 1) (c.n - a.n) i (by have := ha.n_pos; omega) hi
    exact this
  · simp at h

theorem inv_init : Inv init where
  n_pos := le_rfl
  n_le := by norm_num [init, TOP]
  q_pos := le_rfl
  q_le := le_rfl
  llo := by simp [init]
  lhi := by simp [init]
  ahi := by simp [init, Asum]
  hist := by
    intro m hm1 hm
    have : m = 1 := by simp [init] at hm; omega
    subst this
    simp [Asum]
  glo := by simp [init, G]
  ghi := by simp [init, G]
  hlo := by simp [init, H]
  hhi := by simp [init, H]

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
