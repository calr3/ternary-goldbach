import TernaryGoldbach.MinorArcs.MinorTotal

/-!
# Generic lemmas for the numerics of the minor-arc total (`numerics_M`)

* `ghatY_le_num`: a certified upper bound for `ĝ(Y, M)` from numerical bounds on the
  logarithms involved (supplied by `log_le_num`/`le_log_num`);
* `ghatY_mono_y`: `ĝ(y, M) ≤ ĝ(Y, M)` for `y ≥ Y`;
* `sum_Ico_log_le`: `Σ_{M ≤ n < M'} f(n) log((n+1)/n) ≤ f(M) log(M'/M)` for antitone `f ≥ 0`.
-/

open Real Set Finset

namespace TernaryGoldbach.MinorArcs

theorem rpow_neg_sixth_le {Y t : ℝ} (ht : 0 < t) (h : (1 / t) ^ 6 ≤ Y) :
    Y ^ (-1 / 6 : ℝ) ≤ t := by
  have h1 : ((1 / t) ^ 6) ^ (-1 / 6 : ℝ) = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [Real.rpow_neg_one, inv_inv]
  calc Y ^ (-1 / 6 : ℝ) ≤ ((1 / t) ^ 6) ^ (-1 / 6 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h (by norm_num)
    _ = t := h1

theorem le_rpow_third {Y u : ℝ} (hu : 0 ≤ u) (h : u ^ 3 ≤ Y) : u ≤ Y ^ (1 / 3 : ℝ) := by
  have h1 : (u ^ 3) ^ (1 / 3 : ℝ) = u := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu]; norm_num
  calc u = (u ^ 3) ^ (1 / 3 : ℝ) := h1.symm
    _ ≤ Y ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h (by norm_num)

theorem hfun_le_num {Y ℓ sq t : ℝ} (hY : 1 ≤ Y) (hl : Real.log Y ≤ ℓ) (hsq : ℓ ≤ sq ^ 2)
    (hsq0 : 0 ≤ sq) (ht : Y ^ (-1 / 6 : ℝ) ≤ t) :
    hfun Y ≤ 0.276 * t * (ℓ * sq) + 1234 * t ^ 2 * ℓ := by
  have hY0 : 0 < Y := by linarith
  have hl0 : 0 ≤ Real.log Y := Real.log_nonneg hY
  have h6 : 0 ≤ Y ^ (-1 / 6 : ℝ) := by positivity
  have h32 : Real.log Y ^ (3 / 2 : ℝ) ≤ ℓ * sq := by
    have e : Real.log Y ^ (3 / 2 : ℝ) = Real.log Y * √(Real.log Y) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hl0 (by norm_num)]; norm_num
    rw [e]
    have : √(Real.log Y) ≤ sq := by
      rw [Real.sqrt_le_left hsq0]; linarith
    exact mul_le_mul hl this (Real.sqrt_nonneg _) (hl0.trans hl)
  have h3 : Y ^ (-1 / 3 : ℝ) ≤ t ^ 2 := by
    have : Y ^ (-1 / 3 : ℝ) = (Y ^ (-1 / 6 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; norm_num
    rw [this]; exact pow_le_pow_left₀ h6 ht 2
  unfold hfun
  have := mul_le_mul ht h32 (by positivity) (h6.trans ht)
  have := mul_le_mul h3 hl hl0 (by positivity)
  nlinarith

/-- **Certified evaluation of `ĝ(Y, M)`.** -/
theorem ghatY_le_num {Y M u a₁ b₁ b₂ ρ c₁ c₂ s₁ s₂ t₁ h₁ G : ℝ}
    (hY : 1e25 ≤ Y) (hM : 670 ≤ M) (hu : 0 ≤ u) (hu3 : u ^ 3 ≤ Y) (hMu : M ≤ u / 6)
    (h1 : Real.log (2 * M) ≤ a₁) (h2 : Real.log (8 * M) ≤ b₁)
    (h3 : b₂ ≤ Real.log (9 * u / (4.008 * M))) (hb₂ : 0 < b₂)
    (h4 : Real.log (1 + b₁ / (2 * b₂)) ≤ ρ) (h5 : Real.log (Real.log M) ≤ c₁)
    (h6 : c₂ ≤ Real.log (Real.log M)) (hc₂ : 0 < c₂)
    (h7 : 1.7882 * c₁ + 2.50637 / c₂ ≤ s₁ ^ 2) (hs₁ : 0 ≤ s₁) (h8 : s₂ ^ 2 ≤ 2 * M) (hs₂ : 0 < s₂)
    (h9 : Y ^ (-1 / 6 : ℝ) ≤ t₁) (h10 : hfun Y ≤ h₁)
    (hGa : 1.398 * ((((0.27125 * ρ + 0.41415) * a₁ + 0.8764) * s₁ + 2.526) / s₂ +
        ((1.7882 * c₁ + 2.50637 / c₂) * (13 / 4 * a₁ + 7.82) + 13.66 * a₁ + 37.55) / M + 3.8 * t₁) +
        17 * (670 / M) ^ 3 / 3 ≤ G)
    (hGb : 1.398 * h₁ + 17 * (670 / M) ^ 3 / 3 ≤ G) :
    ghatY Y M ≤ G := by
  have hY0 : 0 < Y := by linarith
  have hM0 : 0 < M := by linarith
  have hYu : u ≤ Y ^ (1 / 3 : ℝ) := le_rpow_third hu hu3
  -- `R`
  have hl8 : 0 ≤ Real.log (8 * M) := Real.log_nonneg (by linarith)
  have hR : R Y (2 * M) ≤ 0.27125 * ρ + 0.41415 := by
    unfold R
    have e : 9 * Y ^ (1 / 3 : ℝ) / (2.004 * (2 * M)) = 9 * Y ^ (1 / 3 : ℝ) / (4.008 * M) := by ring
    rw [show 4 * (2 * M) = 8 * M by ring, e]
    have hu0 : 0 < u := by linarith
    have hv : b₂ ≤ Real.log (9 * Y ^ (1 / 3 : ℝ) / (4.008 * M)) :=
      h3.trans (Real.log_le_log (by positivity) (by gcongr))
    have hq : Real.log (8 * M) / (2 * Real.log (9 * Y ^ (1 / 3 : ℝ) / (4.008 * M))) ≤ b₁ / (2 * b₂) :=
      div_le_div₀ (hl8.trans h2) h2 (by positivity) (by linarith)
    have hq0 : 0 ≤ Real.log (8 * M) / (2 * Real.log (9 * Y ^ (1 / 3 : ℝ) / (4.008 * M))) :=
      div_nonneg hl8 (by linarith)
    have := Real.log_le_log (by linarith)
      (show 1 + Real.log (8 * M) / (2 * Real.log (9 * Y ^ (1 / 3 : ℝ) / (4.008 * M))) ≤
        1 + b₁ / (2 * b₂) by linarith)
    linarith
  have hR0 : 0 ≤ R Y (2 * M) := R_nonneg (by linarith) (by linarith)
  have hl2 : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
  have hFpos := Fr_pos hM
  have hF : Fr M ≤ 1.7882 * c₁ + 2.50637 / c₂ := by
    unfold Fr
    have hg := exp_gamma_le_sharp
    have hll : 0 < Real.log (Real.log M) := lt_of_lt_of_le hc₂ h6
    have t1 : rexp eulerMascheroniConstant * Real.log (Real.log M) ≤ 1.7882 * c₁ :=
      mul_le_mul hg h5 hll.le (by norm_num)
    have t2 : 2.50637 / Real.log (Real.log M) ≤ 2.50637 / c₂ :=
      div_le_div_of_nonneg_left (by norm_num) hc₂ h6
    linarith
  have hsF : √(Fr M) ≤ s₁ := by
    rw [Real.sqrt_le_left hs₁]; linarith
  have hs2M : s₂ ≤ √(2 * M) := Real.le_sqrt_of_sq_le h8
  have hA : ((R Y (2 * M) * Real.log (2 * M) + 0.8764) * √(Fr M) + 2.526) / √(2 * M) ≤
      (((0.27125 * ρ + 0.41415) * a₁ + 0.8764) * s₁ + 2.526) / s₂ := by
    have hnum : (R Y (2 * M) * Real.log (2 * M) + 0.8764) * √(Fr M) + 2.526 ≤
        ((0.27125 * ρ + 0.41415) * a₁ + 0.8764) * s₁ + 2.526 := by
      have : R Y (2 * M) * Real.log (2 * M) ≤ (0.27125 * ρ + 0.41415) * a₁ :=
        mul_le_mul hR h1 hl2 (hR0.trans hR)
      have := mul_le_mul (add_le_add_right this 0.8764) hsF (Real.sqrt_nonneg _)
        (by have := mul_nonneg (hR0.trans hR) (hl2.trans h1); linarith)
      linarith
    exact div_le_div₀ (by
      have := mul_nonneg (hR0.trans hR) (hl2.trans h1)
      have : 0 ≤ s₁ := hs₁
      positivity) hnum hs₂ hs2M
  have hL : Lg (2 * M) / M ≤ ((1.7882 * c₁ + 2.50637 / c₂) * (13 / 4 * a₁ + 7.82) + 13.66 * a₁ + 37.55) / M := by
    apply div_le_div_of_nonneg_right _ hM0.le
    unfold Lg
    rw [show 2 * M / 2 = M by ring]
    have := mul_le_mul hF (show 13 / 4 * Real.log (2 * M) + 7.82 ≤ 13 / 4 * a₁ + 7.82 by linarith)
      (by linarith) (by linarith [hFpos.le.trans hF])
    linarith
  have hgx : gx Y M ≤ (((0.27125 * ρ + 0.41415) * a₁ + 0.8764) * s₁ + 2.526) / s₂ +
      ((1.7882 * c₁ + 2.50637 / c₂) * (13 / 4 * a₁ + 7.82) + 13.66 * a₁ + 37.55) / M + 3.8 * t₁ := by
    unfold gx; linarith
  unfold ghatY
  rcases le_total (gx Y M) (hfun Y) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem ghatY_mono_y {Y y M : ℝ} (hY : 1e25 ≤ Y) (hYy : Y ≤ y) (hM : 670 ≤ M)
    (hMY : M ≤ Y ^ (1 / 3 : ℝ) / 6) : ghatY y M ≤ ghatY Y M := by
  have hY0 : 0 < Y := by linarith
  have hw : 1 ≤ y / Y := by rw [le_div_iff₀ hY0]; linarith
  have h1 := gx_scale_le_of_one_le hY0 hw hM hMY
  rw [div_mul_cancel₀ _ hY0.ne'] at h1
  have h2 := hfun_antitone (exp_nine_le_y hY) hYy
  unfold ghatY
  have := max_le_max h1 h2
  linarith

theorem sum_Ico_log_eq {M M' : ℕ} (hM : 1 ≤ M) (hMM : M ≤ M') :
    ∑ n ∈ Finset.Ico M M', Real.log (((n : ℝ) + 1) / n) = Real.log ((M' : ℝ) / M) := by
  induction M', hMM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hM.trans hk
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; push_cast; field_simp

/-- Block bound: `Σ_{M ≤ n < M'} f(n) log((n+1)/n) ≤ f(M) log(M'/M)` for `f` antitone and `≥ 0`. -/
theorem sum_Ico_log_le {f : ℕ → ℝ} {M M' : ℕ} (hM : 1 ≤ M) (hMM : M ≤ M')
    (hf : ∀ n, M ≤ n → n < M' → f n ≤ f M) :
    ∑ n ∈ Finset.Ico M M', f n * Real.log (((n : ℝ) + 1) / n) ≤ f M * Real.log ((M' : ℝ) / M) := by
  have hlog : ∀ n ∈ Finset.Ico M M', 0 ≤ Real.log (((n : ℝ) + 1) / n) := fun n hn => by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hM.trans (Finset.mem_Ico.1 hn).1
    exact Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  calc ∑ n ∈ Finset.Ico M M', f n * Real.log (((n : ℝ) + 1) / n)
      ≤ ∑ n ∈ Finset.Ico M M', f M * Real.log (((n : ℝ) + 1) / n) := by
        refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (hlog n hn)
        exact hf n (Finset.mem_Ico.1 hn).1 (Finset.mem_Ico.1 hn).2
    _ = f M * Real.log ((M' : ℝ) / M) := by rw [← Finset.mul_sum, sum_Ico_log_eq hM hMM]

/-- Chains of blocks. -/
theorem sum_Ico_chain_le {f : ℕ → ℝ} (p : ℕ → ℕ) (k : ℕ) (hp1 : 1 ≤ p 0)
    (hpm : ∀ i < k, p i ≤ p (i + 1))
    (hf : ∀ i < k, ∀ n, p i ≤ n → n < p (i + 1) → f n ≤ f (p i)) :
    ∑ n ∈ Finset.Ico (p 0) (p k), f n * Real.log (((n : ℝ) + 1) / n) ≤
      ∑ i ∈ range k, f (p i) * Real.log ((p (i + 1) : ℝ) / p i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmono : ∀ i ≤ k, p 0 ≤ p i := by
      intro i hi
      induction i with
      | zero => exact le_rfl
      | succ j ihj => exact (ihj (by omega)).trans (hpm j (by omega))
    rw [← Finset.sum_Ico_consecutive _ (hmono k le_rfl) (hpm k (by omega)), Finset.sum_range_succ]
    refine add_le_add (ih (fun i hi => hpm i (by omega)) (fun i hi => hf i (by omega))) ?_
    exact sum_Ico_log_le (hp1.trans (hmono k le_rfl)) (hpm k (by omega)) (hf k (by omega))

/-! ## `σ` and `D` as functions of `L = log x` -/

/-- `D(x) = L/2 - (log 14 - c_E)`. -/
theorem Dx_eq {x : ℝ} (hx : 0 < x) : Dx x = Real.log x / 2 - (Real.log 14 - cE) := by
  unfold Dx
  have h784 : Real.log 784 = 2 * Real.log 28 := by
    rw [show (784:ℝ) = 28 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h28 : Real.log 28 = Real.log 2 + Real.log 14 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity),
    Real.log_div hx.ne' (by norm_num), h784, h28]
  ring

theorem log14_bounds : 2.6390 ≤ Real.log 14 ∧ Real.log 14 ≤ 2.6391 := by
  constructor
  · have := le_log_num (z := 14) 2 0.6390 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num at this ⊢; linarith
  · have := log_le_num (z := 14) 2 0.6391 (by norm_num) (by norm_num) (by unfold taylor6; norm_num)
    norm_num at this ⊢; linarith

/-- `σ(x) ≤ a L - 0.021095` with `a = 0.640208000017`, for `x ≥ 4.9·10²⁶`. -/
theorem sig_le_lin {x : ℝ} (hx : 4.9e26 ≤ x) :
    sig x ≤ 0.640208000017 * Real.log x - 0.021095 := by
  unfold sig
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hs : (2.2e13 : ℝ) ≤ √x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
  have : 366.91 / √x ≤ 0.000000000017 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  nlinarith

/-- `σ/D ≤ (a L₀ - 0.021095)/(L₀/2 - d)` for `L = log x ≥ L₀ ≥ 60`. -/
theorem sig_div_Dx_le {x L₀ : ℝ} (hx : 4.9e26 ≤ x) (hL₀ : 60 ≤ L₀) (hL : L₀ ≤ Real.log x) :
    sig x / Dx x ≤ (0.640208000017 * L₀ - 0.021095) / (L₀ / 2 - (Real.log 14 - cE)) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨h14a, h14b⟩ := log14_bounds
  have hcE : cE = 1.33258 := rfl
  set d := Real.log 14 - cE
  have hd1 : 1.3064 ≤ d := by simp only [d, hcE]; linarith
  have hd2 : d ≤ 1.3066 := by simp only [d, hcE]; linarith
  rw [Dx_eq hx0]
  set L := Real.log x
  have hD : 0 < L / 2 - d := by linarith
  have hD₀ : 0 < L₀ / 2 - d := by linarith
  have hs := sig_le_lin hx
  have hs0 : 0 ≤ 0.640208000017 * L - 0.021095 := by linarith
  calc sig x / (L / 2 - d) ≤ (0.640208000017 * L - 0.021095) / (L / 2 - d) :=
        div_le_div_of_nonneg_right hs hD.le
    _ ≤ (0.640208000017 * L₀ - 0.021095) / (L₀ / 2 - d) := by
        rw [div_le_div_iff₀ hD hD₀]
        nlinarith

/-- `σ(x)(1 - c/D(x)) ≤ (a L₁ - 0.021095)(1 - c/(L₁/2 - d))` for `log x ≤ L₁`. -/
theorem tail_le {x L₁ c : ℝ} (hx : 4.9e26 ≤ x) (hL : Real.log x ≤ L₁) (hc0 : 0 ≤ c)
    (hcD : c ≤ Dx x) :
    sig x - c * sig x / Dx x ≤
      (0.640208000017 * L₁ - 0.021095) * (1 - c / (L₁ / 2 - (Real.log 14 - cE))) := by
  have hx0 : 0 < x := by linarith
  have hl60 : 60 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    calc rexp 60 = rexp 1 ^ 60 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 60 := by gcongr
      _ ≤ 4.9e26 := by norm_num
      _ ≤ x := hx
  have hDpos : 0 < Dx x := by
    rw [Dx_eq hx0]; obtain ⟨h1, h2⟩ := log14_bounds; unfold cE; linarith
  have hDeq := Dx_eq hx0
  set d := Real.log 14 - cE
  have hs := sig_le_lin hx
  have hsig0 : 0 ≤ sig x := by
    unfold sig
    have : 0 ≤ 366.91 / √x * Real.log x := by positivity
    nlinarith
  have e : sig x - c * sig x / Dx x = sig x * (1 - c / Dx x) := by field_simp
  rw [e]
  have h1 : 0 ≤ 1 - c / Dx x := by rw [sub_nonneg, div_le_one hDpos]; exact hcD
  have h2 : 1 - c / Dx x ≤ 1 - c / (L₁ / 2 - d) := by
    have hD1 : Dx x ≤ L₁ / 2 - d := by rw [hDeq]; linarith
    have := div_le_div_of_nonneg_left hc0 hDpos hD1
    linarith
  have h3 : sig x ≤ 0.640208000017 * L₁ - 0.021095 := by linarith
  exact mul_le_mul h3 h2 h1 (by linarith)

/-! ## One cell -/

open TernaryGoldbach.Helfgott (κ)

/-- **A cell of the numerics.** For `x ∈ [X, X']` (`y = x/κ ≥ Y`), with block points
`150001 = p 0 < … < p k = r₂` and certified bounds `G i ≥ ĝ(Y, p i)`, `ℓ i ≥ log(p(i+1)/p i)`,
`G0 ≥ ĝ(Y, 150000)`, `Gt ≥ ĝ(Y, r₂)`, the final rational inequality gives `Mexpr x r₂ ≤ 1.037`. -/
theorem cell_bound {x Y L₀ L₁ cl0 clt G0 Gt : ℝ} {r₂ k : ℕ} (p : ℕ → ℕ) (G ℓ : ℕ → ℝ)
    (hx : 4.9e26 ≤ x) (hY : 1e25 ≤ Y) (hYx : Y ≤ x / κ)
    (hL₀ : 60 ≤ L₀) (hL₀x : L₀ ≤ Real.log x) (hL₁x : Real.log x ≤ L₁)
    (hp0 : p 0 = 150001) (hpk : p k = r₂) (hpm : ∀ i < k, p i ≤ p (i + 1))
    (hr2Y : (r₂ : ℝ) ≤ Y ^ (1 / 3 : ℝ) / 6)
    (hG : ∀ i < k, ghatY Y (p i) ≤ G i) (hℓ : ∀ i < k, Real.log ((p (i + 1) : ℝ) / p i) ≤ ℓ i)
    (hG0 : ghatY Y 150000 ≤ G0) (hGt : ghatY Y r₂ ≤ Gt)
    (hcl0 : cL 150000 ≤ cl0) (hclt : clt ≤ cL (r₂ - 1)) (hclt0 : 0 ≤ clt) (hcD : cL (r₂ - 1) ≤ Dx x)
    {sD' τ' : ℝ}
    (hsD' : (0.640208000017 * L₀ - 0.021095) / (L₀ / 2 - 1.3066) ≤ sD')
    (hτ' : (0.640208000017 * L₁ - 0.021095) * (1 - clt / (L₁ / 2 - 1.3064)) ≤ τ')
    (hb : 8.6294 ≤ cl0 * sD') (hτ0 : 0 ≤ τ')
    (hfin : G0 * (cl0 * sD' - 8.6294) + sD' * ∑ i ∈ Finset.range k, G i * ℓ i + Gt * τ' ≤ 1.037) :
    Mexpr x r₂ ≤ 1.037 := by
  obtain ⟨h14a, h14b⟩ := log14_bounds
  have hcE : cE = 1.33258 := rfl
  have hL1 : 60 ≤ L₁ := (hL₀.trans hL₀x).trans hL₁x
  have hsD'' : (0.640208000017 * L₀ - 0.021095) / (L₀ / 2 - (Real.log 14 - cE)) ≤ sD' := by
    refine le_trans ?_ hsD'
    apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by rw [hcE]; linarith)
  have hτ'' : (0.640208000017 * L₁ - 0.021095) * (1 - clt / (L₁ / 2 - (Real.log 14 - cE))) ≤ τ' := by
    refine le_trans ?_ hτ'
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have : clt / (L₁ / 2 - 1.3064) ≤ clt / (L₁ / 2 - (Real.log 14 - cE)) :=
      div_le_div_of_nonneg_left hclt0 (by rw [hcE]; linarith) (by rw [hcE]; linarith)
    linarith
  have hx0 : 0 < x := by linarith
  set y := x / κ with hy_def
  have hy : 1e25 ≤ y := hY.trans hYx
  have hYr : (r₂ : ℝ) ≤ y ^ (1 / 3 : ℝ) / 6 :=
    hr2Y.trans (by gcongr)
  set sD := sD' with hsD_def
  have hsD := (sig_div_Dx_le hx hL₀ hL₀x).trans hsD''
  have hDpos : 0 < Dx x := by
    rw [Dx_eq hx0]; obtain ⟨h1, h2⟩ := log14_bounds; unfold cE
    have : 60 ≤ Real.log x := hL₀.trans hL₀x
    linarith
  have hsig0 : 0 ≤ sig x := by
    unfold sig
    have : 60 ≤ Real.log x := hL₀.trans hL₀x
    have : 0 ≤ 366.91 / √x * Real.log x := by positivity
    nlinarith
  have hsD0 : 0 ≤ sig x / Dx x := div_nonneg hsig0 hDpos.le
  have hpmono : ∀ i j, i ≤ j → j ≤ k → p i ≤ p j := by
    intro i j hij hjk
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih => exact (ih (by omega)).trans (hpm m (by omega))
  have hpk1 : ∀ i ≤ k, 150001 ≤ p i := fun i hi => hp0 ▸ hpmono 0 i (Nat.zero_le _) hi
  have hpr : ∀ i ≤ k, p i ≤ r₂ := fun i hi => hpk ▸ hpmono i k hi le_rfl
  have h150r : 150001 ≤ r₂ := hpk ▸ hpk1 k le_rfl
  -- the middle sum
  have hmid : ∑ n ∈ Finset.Ioo 150000 r₂, ghatY y n * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) ≤
      sD * ∑ i ∈ Finset.range k, G i * ℓ i := by
    have e : ∑ n ∈ Finset.Ioo 150000 r₂, ghatY y n * (Real.log (((n : ℝ) + 1) / n) * sig x / Dx x) =
        sig x / Dx x * ∑ n ∈ Finset.Ico (p 0) (p k), ghatY y n * Real.log (((n : ℝ) + 1) / n) := by
      have hIoo : Finset.Ioo 150000 r₂ = Finset.Ico (p 0) (p k) := by
        rw [hp0, hpk, ← Finset.Ico_add_one_left_eq_Ioo]; rfl
      rw [hIoo, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [e]
    have hch := sum_Ico_chain_le (f := fun n => ghatY y n) p k (by rw [hp0]; norm_num) hpm
      (fun i hi n hn1 hn2 => by
        have h1 : (670 : ℝ) ≤ p i := by
          have := hpk1 i hi.le
          have : (150001 : ℝ) ≤ p i := by exact_mod_cast this
          linarith
        have h2 : (p i : ℝ) ≤ n := by exact_mod_cast hn1
        have h3 : (n : ℝ) ≤ r₂ := by
          have := hpr (i + 1) (by omega); exact_mod_cast (le_of_lt hn2).trans this
        exact ghatY_antitone (by linarith) h1 h2 (h3.trans hYr))
    have hs2 : ∑ i ∈ Finset.range k, ghatY y (p i) * Real.log ((p (i + 1) : ℝ) / p i) ≤
        ∑ i ∈ Finset.range k, G i * ℓ i := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have hp670 : (670 : ℝ) ≤ p i := by
        have := hpk1 i hi'.le
        have : (150001 : ℝ) ≤ p i := by exact_mod_cast this
        linarith
      have hpY : (p i : ℝ) ≤ Y ^ (1 / 3 : ℝ) / 6 := by
        have := hpr i hi'.le; exact (by exact_mod_cast this : (p i : ℝ) ≤ r₂).trans hr2Y
      have hg1 := (ghatY_mono_y hY hYx hp670 hpY).trans (hG i hi')
      have hg0 := ghatY_nonneg (y := y) (by linarith) (show (0:ℝ) < p i by linarith)
      have hl0 : 0 ≤ Real.log ((p (i + 1) : ℝ) / p i) := Real.log_nonneg (by
        rw [le_div_iff₀ (by linarith)]; simp only [one_mul]; exact_mod_cast hpm i hi')
      exact mul_le_mul hg1 (hℓ i hi') hl0 (hg0.trans hg1)
    have hS0 : 0 ≤ ∑ n ∈ Finset.Ico (p 0) (p k), ghatY y n * Real.log (((n : ℝ) + 1) / n) := by
      refine Finset.sum_nonneg fun n hn => ?_
      have hn1 : (1 : ℝ) ≤ n := by
        have := (Finset.mem_Ico.1 hn).1; rw [hp0] at this; exact_mod_cast (by omega : 1 ≤ n)
      exact mul_nonneg (ghatY_nonneg (by linarith) (by linarith))
        (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    calc sig x / Dx x * ∑ n ∈ Finset.Ico (p 0) (p k), ghatY y n * Real.log (((n : ℝ) + 1) / n)
        ≤ sD * ∑ n ∈ Finset.Ico (p 0) (p k), ghatY y n * Real.log (((n : ℝ) + 1) / n) :=
          mul_le_mul_of_nonneg_right hsD hS0
      _ ≤ sD * ∑ i ∈ Finset.range k, G i * ℓ i := by
          refine mul_le_mul_of_nonneg_left (hch.trans hs2) ?_
          exact hsD0.trans hsD
  -- base and tail
  have hy670 : (670 : ℝ) ≤ 150000 := by norm_num
  have hr0Y : (150000 : ℝ) ≤ Y ^ (1 / 3 : ℝ) / 6 := by
    have : (150000 : ℝ) ≤ r₂ := by exact_mod_cast (by omega : 150000 ≤ r₂)
    linarith
  have hgb := (ghatY_mono_y hY hYx hy670 hr0Y).trans hG0
  have hgb0 := ghatY_nonneg (y := y) (n := 150000) (by linarith) (by norm_num)
  have hbase : ghatY y 150000 * (cL 150000 * sig x / Dx x - 8.6294) ≤ G0 * (cl0 * sD - 8.6294) := by
    have h1 : cL 150000 * sig x / Dx x ≤ cl0 * sD := by
      have hc0 : 0 ≤ cL 150000 := by
        unfold cL
        exact add_nonneg (Real.log_nonneg (by push_cast; norm_num)) (by norm_num)
      rw [mul_div_assoc]
      exact mul_le_mul hcl0 hsD hsD0 (hc0.trans hcl0)
    have h2 : 0 ≤ cl0 * sD - 8.6294 := by linarith
    calc ghatY y 150000 * (cL 150000 * sig x / Dx x - 8.6294)
        ≤ ghatY y 150000 * (cl0 * sD - 8.6294) := mul_le_mul_of_nonneg_left (by linarith) hgb0
      _ ≤ G0 * (cl0 * sD - 8.6294) := mul_le_mul_of_nonneg_right hgb h2
  have hr2_670 : (670 : ℝ) ≤ r₂ := by exact_mod_cast (by omega : 670 ≤ r₂)
  have hgt := (ghatY_mono_y hY hYx hr2_670 hr2Y).trans hGt
  have hgt0 := ghatY_nonneg (y := y) (n := r₂) (by linarith) (by linarith)
  have htail : ghatY y r₂ * (sig x - cL (r₂ - 1) * sig x / Dx x) ≤ Gt * τ' := by
    have h1 := tail_le hx hL₁x (hclt0.trans hclt) hcD
    have h2 : (0.640208000017 * L₁ - 0.021095) * (1 - cL (r₂ - 1) / (L₁ / 2 - (Real.log 14 - cE))) ≤
        (0.640208000017 * L₁ - 0.021095) * (1 - clt / (L₁ / 2 - (Real.log 14 - cE))) := by
      have hL1 : 60 ≤ L₁ := (hL₀.trans hL₀x).trans hL₁x
      obtain ⟨h14a, h14b⟩ := log14_bounds
      have hden : 0 < L₁ / 2 - (Real.log 14 - cE) := by unfold cE; linarith
      have : clt / (L₁ / 2 - (Real.log 14 - cE)) ≤ cL (r₂ - 1) / (L₁ / 2 - (Real.log 14 - cE)) :=
        div_le_div_of_nonneg_right hclt hden.le
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 : 0 ≤ sig x - cL (r₂ - 1) * sig x / Dx x := by
      have e : sig x - cL (r₂ - 1) * sig x / Dx x = sig x * (1 - cL (r₂ - 1) / Dx x) := by field_simp
      rw [e]; exact mul_nonneg hsig0 (by rw [sub_nonneg, div_le_one hDpos]; exact hcD)
    calc ghatY y r₂ * (sig x - cL (r₂ - 1) * sig x / Dx x)
        ≤ ghatY y r₂ * τ' := mul_le_mul_of_nonneg_left ((h1.trans h2).trans hτ'') hgt0
      _ ≤ _ := mul_le_mul_of_nonneg_right hgt hτ0
  unfold Mexpr
  rw [← hy_def]
  linarith

/-- The size conditions on `r₂` in `numerics_M`, from numerical facts at the left end `X` of a
cell. -/
theorem cell_conditions {x X ℓr L₀ : ℝ} {r₂ : ℕ} (hXx : X ≤ x) (hX : 0 < X) (hr : 1 ≤ r₂)
    (c1 : (20000 * (r₂ : ℝ)) ^ 2 ≤ X / 784) (c2 : (2 * (r₂ : ℝ)) ^ 10 ≤ (4 * X / 784) ^ 3)
    (c3 : (6 * (r₂ : ℝ)) ^ 3 ≤ X / 49) (c4 : 2.16e20 * (r₂ : ℝ) ≤ 670 * (X / 49))
    (c5 : Real.log (2 * r₂) ≤ ℓr) (c6 : ℓr + 2 ≤ L₀ / 2 - 1.3066) (hL₀ : L₀ ≤ Real.log x) :
    (20000 * (r₂ : ℝ)) ^ 2 ≤ x / 784 ∧ 2 * (r₂ : ℝ) ≤ (2 * √(x / 784)) ^ (0.6 : ℝ) ∧
      (r₂ : ℝ) ≤ (x / κ) ^ (1 / 3 : ℝ) / 6 ∧ 2.16e20 * r₂ ≤ 670 * (x / κ) ∧ cL (r₂ - 1) ≤ Dx x := by
  have hκ : (κ : ℝ) = 49 := rfl
  have hx0 : 0 < x := by linarith
  refine ⟨c1.trans (by gcongr), ?_, ?_, ?_, ?_⟩
  · set a := 2 * √(x / 784)
    have ha0 : 0 ≤ a := by positivity
    have ha2 : a ^ 2 = 4 * x / 784 := by
      simp only [a]; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hb : (2 * (r₂ : ℝ)) ^ 10 ≤ (a ^ 2) ^ 3 := by
      rw [ha2]; exact c2.trans (by gcongr)
    have e1 : ((2 * (r₂ : ℝ)) ^ 10) ^ (1 / 10 : ℝ) = 2 * r₂ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have e2 : ((a ^ 2) ^ 3) ^ (1 / 10 : ℝ) = a ^ (0.6 : ℝ) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul ha0]; norm_num
    rw [← e1, ← e2]
    exact Real.rpow_le_rpow (by positivity) hb (by norm_num)
  · rw [hκ]
    have := le_rpow_third (Y := x / 49) (u := 6 * r₂) (by positivity) (c3.trans (by gcongr))
    linarith
  · rw [hκ]; exact c4.trans (by gcongr)
  · have hr1 : ((r₂ - 1 : ℕ) : ℝ) + 1 = r₂ := by
      rw [Nat.cast_sub hr]; push_cast; ring
    unfold cL
    rw [hr1, Dx_eq hx0]
    obtain ⟨h1, h2⟩ := log14_bounds
    unfold cE
    linarith

theorem le_cL_pred {r : ℕ} (hr : 1 ≤ r) {c : ℝ} (h : c ≤ Real.log (2 * (r : ℝ)) + 2) :
    c ≤ cL (r - 1) := by
  unfold cL
  rw [Nat.cast_sub hr]; push_cast
  simpa using h

theorem cL_le {n : ℕ} {c : ℝ} (h : Real.log (2 * ((n : ℝ) + 1)) + 2 ≤ c) : cL n ≤ c := h

/-- The block chain, for any `y ≥ Y`. -/
theorem chain_le {y Y : ℝ} {k : ℕ} (p : ℕ → ℕ) (G ℓ : ℕ → ℝ) (hY : 1e25 ≤ Y) (hYy : Y ≤ y)
    (hp0 : 670 ≤ p 0) (hpm : ∀ i < k, p i ≤ p (i + 1)) (hpkY : (p k : ℝ) ≤ Y ^ (1 / 3 : ℝ) / 6)
    (hG : ∀ i < k, ghatY Y (p i) ≤ G i) (hℓ : ∀ i < k, Real.log ((p (i + 1) : ℝ) / p i) ≤ ℓ i) :
    ∑ n ∈ Finset.Ico (p 0) (p k), ghatY y n * Real.log (((n : ℝ) + 1) / n) ≤
      ∑ i ∈ Finset.range k, G i * ℓ i := by
  have hpmono : ∀ i j, i ≤ j → j ≤ k → p i ≤ p j := by
    intro i j hij hjk
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih => exact (ih (by omega)).trans (hpm m (by omega))
  have hYy' : Y ^ (1 / 3 : ℝ) ≤ y ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by linarith) hYy (by norm_num)
  have hch := sum_Ico_chain_le (f := fun n => ghatY y n) p k (by omega) hpm
    (fun i hi n hn1 hn2 => by
      have h1 : (670 : ℝ) ≤ p i := by
        have := hpmono 0 i (Nat.zero_le _) hi.le
        exact_mod_cast hp0.trans this
      have h2 : (p i : ℝ) ≤ n := by exact_mod_cast hn1
      have h3 : (n : ℝ) ≤ p k := by
        have := hpmono (i + 1) k (by omega) le_rfl; exact_mod_cast (le_of_lt hn2).trans this
      exact ghatY_antitone (by linarith) h1 h2 (by linarith))
  refine hch.trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  have hp670 : (670 : ℝ) ≤ p i := by
    have := hpmono 0 i (Nat.zero_le _) hi'.le; exact_mod_cast hp0.trans this
  have hpY : (p i : ℝ) ≤ Y ^ (1 / 3 : ℝ) / 6 := by
    have := hpmono i k hi'.le le_rfl
    exact (by exact_mod_cast this : (p i : ℝ) ≤ p k).trans hpkY
  have hg1 := (ghatY_mono_y hY hYy hp670 hpY).trans (hG i hi')
  have hg0 := ghatY_nonneg (y := y) (by linarith) (show (0:ℝ) < p i by linarith)
  have hl0 : 0 ≤ Real.log ((p (i + 1) : ℝ) / p i) := Real.log_nonneg (by
    rw [le_div_iff₀ (by linarith)]; simp only [one_mul]; exact_mod_cast hpm i hi')
  exact mul_le_mul hg1 (hℓ i hi') hl0 (hg0.trans hg1)

end TernaryGoldbach.MinorArcs
