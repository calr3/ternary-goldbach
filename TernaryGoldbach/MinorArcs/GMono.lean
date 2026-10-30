import TernaryGoldbach.MinorArcs.GBound
import TernaryGoldbach.MinorArcs.SecondNumerics

/-!
# `g_x(r)` is non-increasing in `r` [B, Lemma 11.2.4 for `φ = δ₁`]

`gx x` is antitone on `[670, x^{1/3}/6]` (`gx_antitoneOn`).

We do not follow [B]'s derivative test (11.23)–(11.25).  Instead, writing `s = log r`, each
term of `g_x(r)` has the form `Q(s) e^{-ps}` (`p = 1/2` or `1`), and such a function is
antitone wherever `Q' ≤ pQ` (`antitoneOn_mul_exp_neg`).  For the main term
`Q = (R log 2r + 0.8103) √Ϝ`, the elasticities are `≤ 0.27125/ℓ` for `R` (`ℓ = log(9x^{1/3}/4.008r)
≥ 2.5` because `r ≤ x^{1/3}/6`), `1/log 2r` for `log 2r`, and `≤ e^γ/(2·3.8 log r)` for `√Ϝ`.
Since `R ≥ 0.41415`, the total stays below `1/2` with room to spare.

Proved, with no `sorry`.
-/

open Real Set

namespace TernaryGoldbach.MinorArcs

/-- If `Q' ≤ p Q` on `[s₁, s₂]`, then `s ↦ Q(s) e^{-ps}` is antitone there. -/
theorem antitoneOn_mul_exp_neg {Q Q' : ℝ → ℝ} {s₁ s₂ p : ℝ}
    (hd : ∀ s ∈ Icc s₁ s₂, HasDerivAt Q (Q' s) s) (hle : ∀ s ∈ Icc s₁ s₂, Q' s ≤ p * Q s) :
    AntitoneOn (fun s => Q s * rexp (-p * s)) (Icc s₁ s₂) := by
  have hD : ∀ s ∈ Icc s₁ s₂, HasDerivAt (fun s => Q s * rexp (-p * s))
      (Q' s * rexp (-p * s) + Q s * (rexp (-p * s) * (-p))) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => -p * s) (-p) s := by
      simpa using (hasDerivAt_id s).const_mul (-p)
    exact (hd s hs).mul h1.exp
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (interior_subset hs)).differentiableAt.differentiableWithinAt) fun s hs => ?_
  rw [(hD s (interior_subset hs)).deriv]
  have := hle s (interior_subset hs)
  have he := (Real.exp_pos (-p * s)).le
  nlinarith [mul_nonneg (sub_nonneg.2 this) he]

/-- Composition with `log`: antitone on `[s₁, s₂]` gives antitone on `[e^{s₁}, e^{s₂}]`. -/
theorem antitoneOn_comp_log {f : ℝ → ℝ} {s₁ s₂ : ℝ} (h : AntitoneOn f (Icc s₁ s₂)) :
    AntitoneOn (fun r => f (Real.log r)) (Icc (rexp s₁) (rexp s₂)) := by
  intro a ha b hb hab
  have mem : ∀ c ∈ Icc (rexp s₁) (rexp s₂), Real.log c ∈ Icc s₁ s₂ := fun c hc =>
    ⟨by rw [← Real.log_exp s₁]; exact Real.log_le_log (exp_pos _) hc.1,
     by rw [← Real.log_exp s₂]; exact Real.log_le_log (lt_of_lt_of_le (exp_pos _) hc.1) hc.2⟩
  exact h (mem a ha) (mem b hb) (Real.log_le_log (lt_of_lt_of_le (exp_pos _) ha.1) hab)

/-! ## `Ϝ` in the variable `s = log r` -/

/-- `Ϝ(e^s) = e^γ log s + 2.50637/log s`. -/
noncomputable def Fs (s : ℝ) : ℝ :=
  rexp eulerMascheroniConstant * Real.log s + 2.50637 / Real.log s

theorem Fr_eq_Fs (r : ℝ) : Fr r = Fs (Real.log r) := rfl

theorem one_half_le_exp_gamma : 1.5 ≤ rexp eulerMascheroniConstant := by
  have h := Real.add_one_le_exp eulerMascheroniConstant
  have := Real.one_half_lt_eulerMascheroniConstant
  linarith

theorem Fs_ge {s : ℝ} (hs : 1 < s) : 3.8 ≤ Fs s := by
  unfold Fs
  set t := Real.log s
  have ht : 0 < t := Real.log_pos hs
  have hc := one_half_le_exp_gamma
  have h1 : 3.8 * t ≤ 1.5 * t ^ 2 + 2.50637 := by nlinarith [sq_nonneg (t - 1.2667)]
  have h2 : (rexp eulerMascheroniConstant * t + 2.50637 / t) * t =
      rexp eulerMascheroniConstant * t ^ 2 + 2.50637 := by field_simp
  refine le_of_mul_le_mul_right ?_ ht
  rw [h2]; nlinarith

theorem Fs_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt Fs (rexp eulerMascheroniConstant / s - 2.50637 / (s * Real.log s ^ 2)) s := by
  have hs0 : s ≠ 0 := by linarith
  have hl : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  have h1 := Real.hasDerivAt_log hs0
  unfold Fs
  refine ((h1.const_mul (rexp eulerMascheroniConstant)).add
    ((hasDerivAt_const s (2.50637 : ℝ)).div h1 hl)).congr_deriv ?_
  field_simp
  ring

theorem Fs_deriv_le {s : ℝ} (hs : 1 < s) :
    rexp eulerMascheroniConstant / s - 2.50637 / (s * Real.log s ^ 2) ≤ 1.7882 / s := by
  have hs0 : 0 < s := by linarith
  have : 0 ≤ 2.50637 / (s * Real.log s ^ 2) := by positivity
  have h := exp_gamma_le_sharp
  have : rexp eulerMascheroniConstant / s ≤ 1.7882 / s := div_le_div_of_nonneg_right h hs0.le
  linarith

/-! ## `R_{x,2r}` in the variable `s = log r` -/

/-- `R_{x,2e^s} = 0.27125 log(1 + (log 8 + s)/(2(B - s))) + 0.41415`, `B = log(9x^{1/3}/4.008)`. -/
noncomputable def Rs (B s : ℝ) : ℝ :=
  0.27125 * Real.log (1 + (Real.log 8 + s) / (2 * (B - s))) + 0.41415

theorem R_eq_Rs {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    R x (2 * r) = Rs (Real.log (9 * x ^ (1 / 3 : ℝ) / 4.008)) (Real.log r) := by
  unfold R Rs
  have hT : 0 < x ^ (1 / 3 : ℝ) := by positivity
  rw [show 4 * (2 * r) = 8 * r by ring, Real.log_mul (by norm_num) hr.ne',
    show 9 * x ^ (1 / 3 : ℝ) / (2.004 * (2 * r)) = 9 * x ^ (1 / 3 : ℝ) / 4.008 / r by
      field_simp; ring,
    Real.log_div (by positivity) hr.ne']

theorem Rs_ge {B s : ℝ} (hs : 0 ≤ Real.log 8 + s) (hB : s < B) : 0.41415 ≤ Rs B s := by
  unfold Rs
  have : 0 ≤ (Real.log 8 + s) / (2 * (B - s)) := div_nonneg hs (by linarith)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + (Real.log 8 + s) / (2 * (B - s)) by linarith)
  linarith

theorem Rs_hasDerivAt {B s : ℝ} (hs : 0 ≤ Real.log 8 + s) (hB : s < B) :
    HasDerivAt (Rs B) (0.27125 * ((B + Real.log 8) / ((B - s) * (2 * B - s + Real.log 8)))) s := by
  have hBs : B - s ≠ 0 := by linarith
  have hu := ((hasDerivAt_id s).const_add (Real.log 8)).div
    (((hasDerivAt_id s).const_sub B).const_mul 2) (by simp; exact hBs)
  have hpos : 0 < 1 + (Real.log 8 + s) / (2 * (B - s)) := by
    have : 0 ≤ (Real.log 8 + s) / (2 * (B - s)) := div_nonneg hs (by linarith)
    linarith
  have h2 : 2 * B - s + Real.log 8 ≠ 0 := by linarith
  unfold Rs
  refine ((((hu.const_add 1).log hpos.ne').const_mul 0.27125).add_const 0.41415).congr_deriv ?_
  simp only [id, Pi.div_apply]
  field_simp
  ring

theorem Rs_deriv_le {B s : ℝ} (hs : 0 ≤ Real.log 8 + s) (hB : s < B) :
    0.27125 * ((B + Real.log 8) / ((B - s) * (2 * B - s + Real.log 8))) ≤ 0.27125 / (B - s) := by
  have hBs : 0 < B - s := by linarith
  have h2 : 0 < 2 * B - s + Real.log 8 := by linarith
  rw [mul_div_assoc']
  rw [div_le_div_iff₀ (by positivity) hBs]
  have : (B + Real.log 8) * (B - s) ≤ (B - s) * (2 * B - s + Real.log 8) := by nlinarith
  nlinarith

/-! ## Numerical facts -/

theorem exp_six_le : rexp 6 ≤ 670 := by
  have h := Real.exp_one_lt_d9
  have e : rexp 6 = rexp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc rexp 1 ^ 6 ≤ 2.7182818286 ^ 6 := by gcongr
    _ ≤ 670 := by norm_num

theorem exp_two_point_five_le : rexp 2.5 ≤ 13.4 := by
  have h := Real.exp_one_lt_d9
  have hh : rexp 0.5 ≤ 1.65 := by
    have e : rexp 0.5 ^ 2 = rexp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos 0.5]
  have e : rexp 2.5 = rexp 1 ^ 2 * rexp 0.5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  calc rexp 1 ^ 2 * rexp 0.5 ≤ 2.7182818286 ^ 2 * 1.65 := by gcongr
    _ ≤ 13.4 := by norm_num

/-! ## The three pieces of `g_x(r)` -/

/-- The main term `(R_{x,2r} log 2r + 0.8103) √Ϝ(r)` as a function of `s = log r`. -/
noncomputable def QA (B s : ℝ) : ℝ := (Rs B s * (Real.log 2 + s) + 0.8103) * √(Fs s)

theorem QA_antitoneOn {B : ℝ} (hB : 8.5 ≤ B) :
    AntitoneOn (fun s => QA B s * rexp (-(1 / 2) * s)) (Icc 6 (B - 2.5)) := by
  have hl2 : 0.69 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  refine antitoneOn_mul_exp_neg (Q' := fun s =>
      (0.27125 * ((B + Real.log 8) / ((B - s) * (2 * B - s + Real.log 8))) * (Real.log 2 + s) +
        Rs B s) * √(Fs s) + (Rs B s * (Real.log 2 + s) + 0.8103) *
        ((rexp eulerMascheroniConstant / s - 2.50637 / (s * Real.log s ^ 2)) / (2 * √(Fs s))))
    (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨hs1, hs2⟩ := hs
    have hsB : s < B := by linarith
    have hF := Fs_ge (show (1:ℝ) < s by linarith)
    have hRd := Rs_hasDerivAt (B := B) (s := s) (by linarith) hsB
    have hFd := (Fs_hasDerivAt (show (1:ℝ) < s by linarith)).sqrt (by linarith)
    have hlin : HasDerivAt (fun s => Real.log 2 + s) 1 s := (hasDerivAt_id s).const_add _
    unfold QA
    exact (((hRd.mul hlin).add_const 0.8103).mul hFd).congr_deriv (by simp only [Pi.mul_apply]; ring)
  · obtain ⟨hs1, hs2⟩ := hs
    simp only [QA]
    have hsB : s < B := by linarith
    have hBs : 2.5 ≤ B - s := by linarith
    have hF := Fs_ge (show (1:ℝ) < s by linarith)
    have ha : 0 < √(Fs s) := Real.sqrt_pos.2 (by linarith)
    have ha2 : √(Fs s) ^ 2 = Fs s := Real.sq_sqrt (by linarith)
    have hR := Rs_ge (B := B) (s := s) (by linarith) hsB
    have hRd := Rs_deriv_le (B := B) (s := s) (by linarith) hsB
    have hRd' : 0.27125 * ((B + Real.log 8) / ((B - s) * (2 * B - s + Real.log 8))) ≤ 0.1085 := by
      refine hRd.trans ?_
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hFd := Fs_deriv_le (show (1:ℝ) < s by linarith)
    set D := rexp eulerMascheroniConstant / s - 2.50637 / (s * Real.log s ^ 2) with hD
    have hD' : D ≤ 0.29804 := by
      refine hFd.trans ?_; rw [div_le_iff₀ (by linarith)]; nlinarith
    -- `D/(2√Ϝ) ≤ 0.0393 √Ϝ`
    have hq : D / (2 * √(Fs s)) ≤ 0.0393 * √(Fs s) := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    set L := Real.log 2 + s
    have hL : 6.69 ≤ L := by simp only [L]; linarith
    set N := Rs B s * L + 0.8103
    have hN : 0 ≤ N := by positivity
    set a := √(Fs s)
    have hRL : 0 ≤ 0.27125 * ((B + Real.log 8) / ((B - s) * (2 * B - s + Real.log 8))) := by
      have : 0 < 2 * B - s + Real.log 8 := by linarith
      positivity
    have t1 : (0.27125 * ((B + Real.log 8) / ((B - s) * (2 * B - s + Real.log 8))) * L + Rs B s) * a
        ≤ (0.1085 * L + Rs B s) * a := by gcongr
    have t2 : N * (D / (2 * a)) ≤ N * (0.0393 * a) := mul_le_mul_of_nonneg_left hq hN
    -- `0.1085 L + R + 0.0393 N ≤ N/2`
    have key : 0.1085 * L + Rs B s + 0.0393 * N ≤ 1 / 2 * N := by
      simp only [N]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right key ha.le]

/-- The `L_{2r}` term `Ϝ(r)(13/4 log 2r + 7.82) + 13.66 log 2r + 37.55` in `s = log r`. -/
noncomputable def QC (s : ℝ) : ℝ :=
  Fs s * (13 / 4 * (Real.log 2 + s) + 7.82) + 13.66 * (Real.log 2 + s) + 37.55

theorem QC_antitoneOn (S₂ : ℝ) : AntitoneOn (fun s => QC s * rexp (-1 * s)) (Icc 6 S₂) := by
  have hl2 : 0.69 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  refine antitoneOn_mul_exp_neg (Q' := fun s =>
      (rexp eulerMascheroniConstant / s - 2.50637 / (s * Real.log s ^ 2)) *
        (13 / 4 * (Real.log 2 + s) + 7.82) + Fs s * (13 / 4 * 1) + 13.66 * 1)
    (fun s hs => ?_) (fun s hs => ?_)
  · have hs1 : (1 : ℝ) < s := by linarith [hs.1]
    have hlin : HasDerivAt (fun s => Real.log 2 + s) 1 s := (hasDerivAt_id s).const_add _
    unfold QC
    exact ((((Fs_hasDerivAt hs1).mul ((hlin.const_mul (13 / 4)).add_const 7.82)).add
      (hlin.const_mul 13.66)).add_const 37.55).congr_deriv
      (by ring)
  · have hs1 : 6 ≤ s := hs.1
    simp only [QC]
    have hF := Fs_ge (show (1:ℝ) < s by linarith)
    have hD := Fs_deriv_le (show (1:ℝ) < s by linarith)
    set D := rexp eulerMascheroniConstant / s - 2.50637 / (s * Real.log s ^ 2)
    have hD' : D ≤ 0.29804 := by
      refine hD.trans ?_; rw [div_le_iff₀ (by linarith)]; nlinarith
    set M := 13 / 4 * (Real.log 2 + s) + 7.82
    have hM : 29 ≤ M := by simp only [M]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hD' (by linarith : (0:ℝ) ≤ M),
      mul_le_mul_of_nonneg_right hF (by linarith : (0:ℝ) ≤ M - 13 / 4)]

theorem exp_nine_le : rexp 9 ≤ 8200 := by
  have h := Real.exp_one_lt_d9
  have e : rexp 9 = rexp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc rexp 1 ^ 9 ≤ 2.7182818286 ^ 9 := by gcongr
    _ ≤ 8200 := by norm_num

/-- `g_x(r)` split into the three pieces, in the variable `s = log r`. -/
theorem gx_eq {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    gx x r = QA (Real.log (9 * x ^ (1 / 3 : ℝ) / 4.008)) (Real.log r) *
        rexp (-(1 / 2) * Real.log r) / √2 + 2.5 / √(2 * r) +
      QC (Real.log r) * rexp (-1 * Real.log r) + 3.8 * x ^ (-1 / 6 : ℝ) := by
  have e1 : rexp (-(1 / 2) * Real.log r) = (√r)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, ← Real.exp_neg]; ring_nf
  have e2 : rexp (-1 * Real.log r) = r⁻¹ := by
    rw [neg_one_mul, Real.exp_neg, Real.exp_log hr]
  unfold gx QA QC Lg
  rw [e1, e2, R_eq_Rs hx hr, Fr_eq_Fs, show 2 * r / 2 = r by ring, Fr_eq_Fs,
    Real.log_mul (by norm_num) hr.ne', Real.sqrt_mul (by norm_num)]
  field_simp

/-- **[B, Lemma 11.2.4] for a single scale** (our `g_x`): `r ↦ g_x(r)` is non-increasing on
`[670, x^{1/3}/6]`. -/
theorem gx_antitoneOn {x : ℝ} (hx : 2.16e20 ≤ x) : AntitoneOn (gx x) (Icc 670 (x ^ (1 / 3 : ℝ) / 6)) := by
  obtain ⟨hT, -, -, -⟩ := cube_root_facts hx
  have hx0 : 0 < x := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T, T = x ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hTdef] at hT ⊢
  obtain ⟨B, hBdef⟩ : ∃ B, B = Real.log (9 * T / 4.008) := ⟨_, rfl⟩
  have hB : 8.5 ≤ B := by
    rw [hBdef, Real.le_log_iff_exp_le (by positivity)]
    have : rexp 8.5 ≤ rexp 9 := Real.exp_le_exp.2 (by norm_num)
    have h9 : (8200 : ℝ) ≤ 9 * T / 4.008 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith [exp_nine_le]
  have hsub : Icc 670 (T / 6) ⊆ Icc (rexp 6) (rexp (B - 2.5)) := by
    intro r hr
    refine ⟨exp_six_le.trans hr.1, hr.2.trans ?_⟩
    rw [Real.exp_sub, hBdef, Real.exp_log (by positivity), le_div_iff₀ (Real.exp_pos _)]
    have h1 : T / 6 * rexp 2.5 ≤ T / 6 * 13.4 := by gcongr; exact exp_two_point_five_le
    have h2 : T / 6 * 13.4 ≤ 9 * T / 4.008 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  have hA := (antitoneOn_comp_log (QA_antitoneOn hB)).mono hsub
  have hC := (antitoneOn_comp_log (QC_antitoneOn (B - 2.5))).mono hsub
  intro a ha b hb hab
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := by linarith [hb.1]
  rw [gx_eq hx0 ha0, gx_eq hx0 hb0, ← hTdef, ← hBdef]
  have h1 := hA ha hb hab
  have h2 := hC ha hb hab
  simp only at h1 h2
  have h3 : 2.5 / √(2 * b) ≤ 2.5 / √(2 * a) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (Real.sqrt_le_sqrt (by linarith))
  have h4 := div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg 2)
  linarith

end TernaryGoldbach.MinorArcs
