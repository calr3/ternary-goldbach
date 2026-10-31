import TernaryGoldbach.Prelim.Shan
import TernaryGoldbach.Prelim.HilbertIdentity

/-!
# The Montgomery–Vaughan weighted Hilbert inequality on the real line

For a finite set `S ⊂ ℝ` with `0 < δ_y ≤ |y − z|` (`y ≠ z ∈ S`):
`|∑_{m ≠ n} w_m w̄_n/(m − n)| ≤ 4.66 ∑ |w_n|²/δ_n`  (Montgomery–Vaughan: `3π/2 = 4.712`).

Route (W. Yangjit, arXiv:2203.14950, Prop 3.1 and Preissmann's argument for Thm 1.2): the eigenvector
identity gives `μ² ≤ π²/3 + 2U`, with `U = ∑_{m≠n} δ_m^{3/2}δ_n^{1/2} t_m t_n/(m−n)²`, and by
Cauchy–Schwarz `U² ≤ V(π⁴V/45 + 2KU)`. Here `K` comes from a bound for
`∑_{n ≠ l,m} δ_n/((n−l)²(n−m)²) ≤ K(1/δ_l + 1/δ_m)/(l−m)²`. Preissmann's Lemme 6 gives `K = π²/3`.
Our own, weaker version gives `K = π²/3 + (1 − ½log 2)² + 2/e ≤ 4.4527`. It comes from the partial fractions
`D⁻²(1/a² + 1/b² − 2/(ab))` and from a bound for the in-between points,
`∑_{l<n<m} δ_n/(n−l) ≤ (1 − ½log 2) + log((m−l)/δ_l)`, which uses `min(a_n,a_{n+1})/λ_n ≤
½ log(λ_{n+1}/λ_{n−1})`. This gives `U ≤ 9.2V`, and `μ² ≤ π²/3 + 18.4 ≤ 4.66²`.
-/

open Finset Real Matrix

namespace TernaryGoldbach.Prelim.Hilbert

/-! ### Elementary inequalities -/

/-- `2u ≤ log(1+u) − log(1−u)` for `0 ≤ u < 1`. -/
theorem two_mul_le_log_sub {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    2 * u ≤ Real.log (1 + u) - Real.log (1 - u) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := u) (by rw [abs_of_nonneg hu0]; exact hu1)
  have := le_hasSum h 0 fun j _ => by positivity
  simpa using this

/-- `min(x, y)/(L + x) ≤ ½ (log(L + x + y) − log L)`. -/
theorem min_div_le_half_log {L x y : ℝ} (hL : 0 < L) (hx : 0 < x) (hy : 0 < y) :
    min x y / (L + x) ≤ (Real.log (L + x + y) - Real.log L) / 2 := by
  set m := min x y
  set P := L + x
  have hm0 : 0 < m := lt_min hx hy
  have hmx : m ≤ x := min_le_left _ _
  have hmy : m ≤ y := min_le_right _ _
  have hP : 0 < P := by positivity
  set u := m / P
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by rw [div_lt_one hP]; simp only [P]; linarith
  have h1 := two_mul_le_log_sub hu0 hu1
  -- `(1 + u)/(1 − u) = (P + m)/(P − m) ≤ (L + x + y)/L`.
  have hPm : 0 < P - m := by simp only [P]; linarith
  have hlog1 : Real.log (1 + u) - Real.log (1 - u) = Real.log (P + m) - Real.log (P - m) := by
    have e1 : 1 + u = (P + m) / P := by simp only [u]; field_simp
    have e2 : 1 - u = (P - m) / P := by simp only [u]; field_simp
    rw [e1, e2, Real.log_div (by positivity) hP.ne', Real.log_div hPm.ne' hP.ne']; ring
  have hlog2 : Real.log (P + m) - Real.log (P - m) ≤ Real.log (L + x + y) - Real.log L := by
    have hA : Real.log (P + m) ≤ Real.log (L + x + y) :=
      Real.log_le_log (by positivity) (by simp only [P]; linarith)
    have hB : Real.log L ≤ Real.log (P - m) := Real.log_le_log hL (by simp only [P]; linarith)
    linarith
  have : u ≤ (Real.log (L + x + y) - Real.log L) / 2 := by linarith
  simpa [u] using this

/-- `c₀ = 1 − ½ log 2`. -/
noncomputable def c0 : ℝ := 1 - Real.log 2 / 2

theorem c0_pos : 0 < c0 := by
  unfold c0; have := Real.log_two_lt_d9; linarith

/-- `t − ½ log(1 + t) ≤ c₀` for `0 ≤ t ≤ 1`. -/
theorem t_sub_half_log_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t - Real.log (1 + t) / 2 ≤ c0 := by
  unfold c0
  have h := Real.log_le_sub_one_of_pos (x := 2 / (1 + t)) (by positivity)
  rw [Real.log_div (by norm_num) (by positivity)] at h
  have : 2 / (1 + t) - 1 = (1 - t) / (1 + t) := by field_simp; ring
  rw [this] at h
  have h2 : (1 - t) / (1 + t) ≤ 1 - t := div_le_self (by linarith) (by linarith)
  linarith

/-! ### The in-between sum, sequence form -/

/-- For gaps `a₀ ≥ 1`, `a_i > 0`, positions `λ_n = a₀ + ⋯ + a_n` and weights
`w_n ≤ min(a_n, a_{n+1})`: `∑_{n<N} w_n/λ_n ≤ c₀ + log λ_N`. -/
theorem between_seq {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (h0 : 1 ≤ a 0) (N : ℕ) :
    ∑ n ∈ range N, min (a n) (a (n + 1)) / Shan.lam a n ≤ c0 + Real.log (Shan.lam a N) := by
  have hlam1 := Shan.one_le_lam hpos h0
  have hlam0 : ∀ n, 0 < Shan.lam a n := fun n => lt_of_lt_of_le one_pos (hlam1 n)
  have hlog0 : ∀ n, 0 ≤ Real.log (Shan.lam a n) := fun n => Real.log_nonneg (hlam1 n)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp only [range_zero, sum_empty]; linarith [c0_pos, hlog0 0]
  -- the terms `n ≥ 1`
  have hstep : ∀ n, 1 ≤ n → min (a n) (a (n + 1)) / Shan.lam a n ≤
      (Real.log (Shan.lam a (n + 1)) - Real.log (Shan.lam a (n - 1))) / 2 := by
    intro n hn
    have e1 : Shan.lam a n = Shan.lam a (n - 1) + a n := by
      have := Shan.lam_succ a (n - 1); rwa [show n - 1 + 1 = n by omega] at this
    have e2 : Shan.lam a (n + 1) = Shan.lam a (n - 1) + a n + a (n + 1) := by
      rw [Shan.lam_succ, e1]
    rw [e1, e2]
    exact min_div_le_half_log (hlam0 _) (hpos n) (hpos _)
  -- two-step telescoping
  have htel : ∀ M, 1 ≤ M → ∑ n ∈ Ico 1 M,
      (Real.log (Shan.lam a (n + 1)) - Real.log (Shan.lam a (n - 1))) / 2 =
      (Real.log (Shan.lam a M) + Real.log (Shan.lam a (M - 1)) - Real.log (Shan.lam a 1) -
        Real.log (Shan.lam a 0)) / 2 := by
    intro M hM
    induction M with
    | zero => omega
    | succ M ih =>
      rcases Nat.eq_zero_or_pos M with h | h
      · subst h; simp
      · rw [sum_Ico_succ_top (by omega), ih h, show M + 1 - 1 = M by omega]; ring
  have hsplit : ∑ n ∈ range N, min (a n) (a (n + 1)) / Shan.lam a n =
      min (a 0) (a 1) / Shan.lam a 0 + ∑ n ∈ Ico 1 N, min (a n) (a (n + 1)) / Shan.lam a n := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hN]
  rw [hsplit]
  have hsum := sum_le_sum fun n (hn : n ∈ Ico 1 N) => hstep n (mem_Ico.1 hn).1
  rw [htel N hN] at hsum
  -- the first term
  set t := min (a 0) (a 1) / a 0
  have hlam00 : Shan.lam a 0 = a 0 := by simp [Shan.lam]
  have ht0 : 0 ≤ t := div_nonneg (le_min (hpos 0).le (hpos 1).le) (hpos 0).le
  have ht1 : t ≤ 1 := by rw [div_le_one (hpos 0)]; exact min_le_left _ _
  have hlam11 : a 0 * (1 + t) ≤ Shan.lam a 1 := by
    rw [Shan.lam_succ, hlam00]
    have : a 0 * t = min (a 0) (a 1) := by simp only [t]; field_simp
    rw [mul_add, mul_one, this]; linarith [min_le_right (a 0) (a 1)]
  have hlog1 : Real.log (1 + t) ≤ Real.log (Shan.lam a 1) := by
    refine Real.log_le_log (by linarith) (le_trans ?_ hlam11)
    nlinarith
  have hmono : Real.log (Shan.lam a (N - 1)) ≤ Real.log (Shan.lam a N) := by
    refine Real.log_le_log (hlam0 _) ?_
    have := Shan.lam_succ a (N - 1); rw [show N - 1 + 1 = N by omega] at this
    linarith [hpos N]
  have hc := t_sub_half_log_le ht0 ht1
  have hfirst : min (a 0) (a 1) / Shan.lam a 0 = t := by rw [hlam00]
  have hl0 := hlog0 0
  linarith

/-! ### The in-between sum, set form -/

/-- For `l < m` in `S`: `∑_{n ∈ S, l < n < m} δ_n/(n − l) ≤ c₀ + log((m − l)/δ_l)`. -/
theorem between_set (S : Finset ℝ) {l m : ℝ} (hl : l ∈ S) (hm : m ∈ S) (hlm : l < m) (δ : ℝ → ℝ)
    (hδ : ∀ y ∈ S, 0 < δ y) (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) :
    ∑ n ∈ S.filter (fun y => l < y ∧ y < m), δ n / (n - l) ≤ c0 + Real.log ((m - l) / δ l) := by
  set B := S.filter (fun y => l < y ∧ y < m) with hB
  set N := B.card with hN
  have hδl := hδ l hl
  set e := B.orderEmbOfFin hN.symm
  have heB : ∀ i, e i ∈ B := fun i => B.orderEmbOfFin_mem hN.symm i
  have heS : ∀ i, e i ∈ S := fun i => (mem_filter.1 (heB i)).1
  have hel : ∀ i, l < e i := fun i => (mem_filter.1 (heB i)).2.1
  have hem : ∀ i, e i < m := fun i => (mem_filter.1 (heB i)).2.2
  let pos : ℕ → ℝ := fun n => if h : n < N then e ⟨n, h⟩ else m
  let prev : ℕ → ℝ := fun n => if n = 0 then l else pos (n - 1)
  let a : ℕ → ℝ := fun n => if n ≤ N then (pos n - prev n) / δ l else 1
  have hposS : ∀ n, pos n ∈ S := fun n => by
    simp only [pos]; split_ifs; exacts [heS _, hm]
  have hpos_l : ∀ n, l < pos n := fun n => by
    simp only [pos]; split_ifs; exacts [hel _, hlm]
  have hpos_mono : ∀ n n', n < n' → n' ≤ N → pos n < pos n' := by
    intro n n' hnn' hn'
    simp only [pos]
    rw [dif_pos (show n < N by omega)]
    split_ifs with h
    · exact e.strictMono (by simp only [Fin.mk_lt_mk]; omega)
    · exact hem _
  have hprevS : ∀ n, prev n ∈ S := fun n => by
    simp only [prev]; split_ifs; exacts [hl, hposS _]
  have hgap : ∀ n, n ≤ N → 0 < pos n - prev n := by
    intro n hn
    simp only [prev]; split_ifs with h0
    · linarith [hpos_l n]
    · linarith [hpos_mono (n - 1) n (by omega) hn]
  have ha_pos : ∀ n, 0 < a n := fun n => by
    simp only [a]; split_ifs with h
    · exact div_pos (hgap n h) hδl
    · exact one_pos
  have ha0 : 1 ≤ a 0 := by
    simp only [a, if_pos (Nat.zero_le N), prev]
    rw [le_div_iff₀ hδl, one_mul]
    have h := hsep l hl (pos 0) (hposS 0) (ne_of_gt (hpos_l 0))
    rwa [abs_sub_comm, abs_of_pos (by linarith [hpos_l 0])] at h
  have hlam : ∀ n, n ≤ N → Shan.lam a n = (pos n - l) / δ l := by
    intro n hn
    induction n with
    | zero =>
      rw [Shan.lam, zero_add, sum_range_one]
      simp [a, prev]
    | succ n ih =>
      rw [Shan.lam_succ, ih (by omega)]
      simp only [a, if_pos hn, prev, if_neg (Nat.succ_ne_zero n), show n + 1 - 1 = n by omega]
      field_simp; ring
  have hw : ∀ n, n < N → δ (pos n) / δ l ≤ min (a n) (a (n + 1)) := by
    intro n hn
    rw [div_le_iff₀ hδl, min_mul_of_nonneg _ _ hδl.le]
    refine le_min ?_ ?_
    · simp only [a, if_pos hn.le]
      rw [div_mul_cancel₀ _ hδl.ne']
      have h := hsep (pos n) (hposS n) (prev n) (hprevS n) (ne_of_lt (by linarith [hgap n hn.le]))
      rwa [abs_of_pos (hgap n hn.le)] at h
    · simp only [a, if_pos (show n + 1 ≤ N by omega), prev, if_neg (Nat.succ_ne_zero n),
        show n + 1 - 1 = n by omega]
      rw [div_mul_cancel₀ _ hδl.ne']
      have hlt := hpos_mono n (n + 1) (by omega) (by omega)
      have h := hsep (pos n) (hposS n) (pos (n + 1)) (hposS _) (ne_of_gt hlt)
      rwa [abs_sub_comm, abs_of_pos (by linarith)] at h
  have hsum : ∑ y ∈ B, δ y / (y - l) = ∑ n ∈ range N, δ (pos n) / δ l / Shan.lam a n := by
    rw [← B.image_orderEmbOfFin_univ hN.symm, sum_image fun i _ j _ h => e.injective h,
      ← Fin.sum_univ_eq_sum_range (fun n => δ (pos n) / δ l / Shan.lam a n) N]
    refine sum_congr rfl fun i _ => ?_
    rw [hlam i i.2.le]
    have hp : pos i = e i := by simp only [pos, dif_pos i.2]
    rw [hp]
    have : e i - l ≠ 0 := by linarith [hel i]
    field_simp
  rw [hsum]
  have hmain := between_seq ha_pos ha0 N
  rw [hlam N le_rfl] at hmain
  have hposN : pos N = m := by simp [pos]
  rw [hposN] at hmain
  refine le_trans (sum_le_sum fun n hn => ?_) hmain
  have hn := mem_range.1 hn
  exact div_le_div_of_nonneg_right (hw n hn) (Shan.one_le_lam ha_pos ha0 n |>.trans' zero_le_one)

/-- The in-between sum from either endpoint: `∑_{(n−l)(n−m)<0} δ_n/|n − l| ≤ c₀ + log(|l − m|/δ_l)`. -/
theorem between_abs (S : Finset ℝ) {l m : ℝ} (hl : l ∈ S) (hm : m ∈ S) (hlm : l ≠ m) (δ : ℝ → ℝ)
    (hδ : ∀ y ∈ S, 0 < δ y) (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) :
    ∑ n ∈ S.filter (fun y => (y - l) * (y - m) < 0), δ n / |n - l| ≤
      c0 + Real.log (|l - m| / δ l) := by
  rcases lt_or_gt_of_ne hlm with h | h
  · have hf : S.filter (fun y => (y - l) * (y - m) < 0) = S.filter (fun y => l < y ∧ y < m) := by
      refine filter_congr fun y _ => ?_
      constructor
      · intro hy
        rcases lt_or_ge y l with h1 | h1
        · nlinarith
        · rcases lt_or_ge y m with h2 | h2
          · refine ⟨lt_of_le_of_ne h1 ?_, h2⟩; rintro rfl; simp at hy
          · nlinarith
      · rintro ⟨h1, h2⟩; nlinarith
    rw [hf, abs_of_neg (by linarith : l - m < 0), neg_sub]
    refine le_trans (le_of_eq (sum_congr rfl fun n hn => ?_)) (between_set S hl hm h δ hδ hsep)
    rw [abs_of_pos (by linarith [(mem_filter.1 hn).2.1])]
  · -- reflect
    have hmain := between_set (S.image (fun y => -y)) (l := -l) (m := -m) (mem_image_of_mem _ hl)
      (mem_image_of_mem _ hm) (by linarith) (fun y => δ (-y))
      (fun y hy => by obtain ⟨y', hy', rfl⟩ := mem_image.1 hy; simpa using hδ y' hy')
      (fun y hy z hz hzy => by
        obtain ⟨y', hy', rfl⟩ := mem_image.1 hy
        obtain ⟨z', hz', rfl⟩ := mem_image.1 hz
        have := hsep y' hy' z' hz' (fun h' => hzy (by rw [h']))
        show δ (-(-y')) ≤ |(-y') - (-z')|
        rw [neg_neg, show -y' - -z' = -(y' - z') by ring, abs_neg]; exact this)
    rw [show -m - -l = l - m by ring, neg_neg] at hmain
    rw [abs_of_pos (by linarith : 0 < l - m)]
    refine le_trans (le_of_eq ?_) hmain
    rw [filter_image, sum_image fun x _ y _ hxy => neg_injective hxy]
    · refine sum_congr ?_ fun n hn => ?_
      · ext y; simp only [mem_filter]
        constructor
        · rintro ⟨hy, hy'⟩
          refine ⟨hy, ?_, ?_⟩
          · by_contra hc; push Not at hc
            rcases eq_or_lt_of_le hc with hc | hc
            · have : y = l := by linarith
              subst this; simp at hy'
            · nlinarith
          · by_contra hc; push Not at hc; nlinarith
        · rintro ⟨hy, h1, h2⟩; exact ⟨hy, by nlinarith⟩
      · have := (mem_filter.1 hn).2
        rw [abs_of_neg (by nlinarith), neg_neg]
        congr 1; ring

/-- `K = π²/3 + c₀² + 2/e`. -/
noncomputable def Kc : ℝ := Real.pi ^ 2 / 3 + c0 ^ 2 + 2 / Real.exp 1

theorem Kc_le : Kc ≤ 4.4527 := by
  unfold Kc c0
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have he := Real.exp_one_gt_d9
  have hpi2 : Real.pi ^ 2 < 3.1416 ^ 2 := by nlinarith
  have hc0 : (1 - Real.log 2 / 2) ^ 2 ≤ 0.42697 := by nlinarith
  have he2 : 2 / Real.exp 1 ≤ 0.73576 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
  nlinarith

/-- `2(c₀ + log(D/δ))/D³ − δ/D⁴ ≤ (c₀² + 2/e)/(δD²)`. -/
theorem aux_log {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D) :
    2 * (c0 + Real.log (D / δ)) / D ^ 3 - δ / D ^ 4 ≤ (c0 ^ 2 + 2 / Real.exp 1) / (δ * D ^ 2) := by
  set s := D / δ with hs
  have hs0 : 0 < s := div_pos hD hδ
  have hlog : Real.log s ≤ s / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos (x := s / Real.exp 1) (by positivity)
    rw [Real.log_div hs0.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    linarith
  have hkey : 2 * (c0 + Real.log s) / D ^ 3 - δ / D ^ 4 - (c0 ^ 2 + 2 / Real.exp 1) / (δ * D ^ 2) =
      -(c0 * D - δ) ^ 2 / (δ * D ^ 4) + 2 * (Real.log s - s / Real.exp 1) / D ^ 3 := by
    rw [hs]; field_simp; ring
  have h1 : -(c0 * D - δ) ^ 2 / (δ * D ^ 4) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (c0 * D - δ)]) (by positivity)
  have h2 : 2 * (Real.log s - s / Real.exp 1) / D ^ 3 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- The pointwise bound behind our Lemme 6. -/
theorem key_term {n l m δn : ℝ} (hnl : n ≠ l) (hnm : n ≠ m) (hlm : l ≠ m) (hδn : 0 ≤ δn) :
    δn / ((n - l) ^ 2 * (n - m) ^ 2) ≤ δn / (l - m) ^ 2 * (1 / (n - l) ^ 2 + 1 / (n - m) ^ 2) +
      (if (n - l) * (n - m) < 0 then 2 * δn / |l - m| ^ 3 * (1 / |n - l| + 1 / |n - m|) else 0) := by
  have hA : n - l ≠ 0 := sub_ne_zero.2 hnl
  have hB : n - m ≠ 0 := sub_ne_zero.2 hnm
  have hD : l - m ≠ 0 := sub_ne_zero.2 hlm
  have hid : δn / ((n - l) ^ 2 * (n - m) ^ 2) = δn / (l - m) ^ 2 * (1 / (n - l) ^ 2 + 1 / (n - m) ^ 2) +
      δn / (l - m) ^ 2 * (-2 / ((n - l) * (n - m))) := by
    field_simp; ring
  rw [hid]
  split_ifs with h
  · -- `|A| + |B| = |D|` and `−2/(AB) = (2/|D|)(1/|A| + 1/|B|)`.
    have habs : |n - l| + |n - m| = |l - m| := by
      rcases lt_or_gt_of_ne hA with h1 | h1
      · rw [abs_of_neg h1, abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]; ring
      · rw [abs_of_pos h1, abs_of_neg (by nlinarith), abs_of_neg (by nlinarith)]; ring
    have hab : (n - l) * (n - m) = -(|n - l| * |n - m|) := by
      rw [← abs_mul, abs_of_neg h]; ring
    have hA' : 0 < |n - l| := abs_pos.2 hA
    have hB' : 0 < |n - m| := abs_pos.2 hB
    have hD' : |l - m| ^ 2 = (l - m) ^ 2 := sq_abs _
    have : δn / (l - m) ^ 2 * (-2 / ((n - l) * (n - m))) =
        2 * δn / |l - m| ^ 3 * (1 / |n - l| + 1 / |n - m|) := by
      rw [hab, ← hD', ← habs]; field_simp; ring
    rw [this]
  · push Not at h
    have hpos : 0 < (n - l) * (n - m) := lt_of_le_of_ne h (mul_ne_zero hA hB).symm
    have : δn / (l - m) ^ 2 * (-2 / ((n - l) * (n - m))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (div_nonpos_of_nonpos_of_nonneg (by norm_num)
        hpos.le)
    linarith

/-- **Our Lemme 6**: `∑_{n ≠ l,m} δ_n/((n−l)²(n−m)²) ≤ K(1/δ_l + 1/δ_m)/(l−m)²`. -/
theorem lemma6 (S : Finset ℝ) {l m : ℝ} (hl : l ∈ S) (hm : m ∈ S) (hlm : l ≠ m) (δ : ℝ → ℝ)
    (hδ : ∀ y ∈ S, 0 < δ y) (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) :
    ∑ n ∈ (S.erase l).erase m, δ n / ((n - l) ^ 2 * (n - m) ^ 2) ≤
      Kc * (1 / δ l + 1 / δ m) / (l - m) ^ 2 := by
  set T := (S.erase l).erase m with hT
  have hTS : ∀ n ∈ T, n ∈ S ∧ n ≠ l ∧ n ≠ m := fun n hn => by
    simp only [hT, mem_erase] at hn; exact ⟨hn.2.2, hn.2.1, hn.1⟩
  have hδl := hδ l hl
  have hδm := hδ m hm
  have hD : 0 < |l - m| := abs_pos.2 (sub_ne_zero.2 hlm)
  have hD2 : (l - m) ^ 2 = |l - m| ^ 2 := (sq_abs _).symm
  -- termwise
  have h1 := sum_le_sum fun n (hn : n ∈ T) =>
    key_term (hTS n hn).2.1 (hTS n hn).2.2 hlm (hδ n (hTS n hn).1).le
  refine h1.trans ?_
  rw [sum_add_distrib]
  -- the square sums
  have hsqL : ∑ n ∈ T, δ n / (n - l) ^ 2 ≤ Real.pi ^ 2 / 3 / δ l - δ m / (l - m) ^ 2 := by
    have hmem : m ∈ S.erase l := mem_erase.2 ⟨hlm.symm, hm⟩
    have := Shan.spacing_two S hl δ hδ hsep
    rw [← sum_erase_add _ _ hmem] at this
    rw [show (m - l) ^ 2 = (l - m) ^ 2 by ring] at this
    linarith
  have hsqM : ∑ n ∈ T, δ n / (n - m) ^ 2 ≤ Real.pi ^ 2 / 3 / δ m - δ l / (l - m) ^ 2 := by
    have hmem : l ∈ S.erase m := mem_erase.2 ⟨hlm, hl⟩
    have hT' : T = (S.erase m).erase l := by rw [hT, erase_right_comm]
    have := Shan.spacing_two S hm δ hδ hsep
    rw [← sum_erase_add _ _ hmem] at this
    rw [hT']; linarith
  have hsq : ∑ n ∈ T, δ n / (l - m) ^ 2 * (1 / (n - l) ^ 2 + 1 / (n - m) ^ 2) =
      (∑ n ∈ T, δ n / (n - l) ^ 2 + ∑ n ∈ T, δ n / (n - m) ^ 2) / (l - m) ^ 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun n _ => by ring
  -- the in-between sums
  have hbetw : ∑ n ∈ T, (if (n - l) * (n - m) < 0 then
      2 * δ n / |l - m| ^ 3 * (1 / |n - l| + 1 / |n - m|) else 0) ≤
      2 / |l - m| ^ 3 * ((c0 + Real.log (|l - m| / δ l)) + (c0 + Real.log (|l - m| / δ m))) := by
    rw [← sum_filter]
    have hsub : T.filter (fun y => (y - l) * (y - m) < 0) =
        S.filter (fun y => (y - l) * (y - m) < 0) := by
      ext y; simp only [mem_filter, hT, mem_erase]
      constructor
      · rintro ⟨⟨_, _, hy⟩, h⟩; exact ⟨hy, h⟩
      · rintro ⟨hy, h⟩
        refine ⟨⟨?_, ?_, hy⟩, h⟩
        · rintro rfl; simp at h
        · rintro rfl; simp at h
    rw [hsub]
    have hA := between_abs S hl hm hlm δ hδ hsep
    have hB := between_abs S hm hl hlm.symm δ hδ hsep
    have hf : S.filter (fun y => (y - m) * (y - l) < 0) = S.filter (fun y => (y - l) * (y - m) < 0) :=
      filter_congr fun y _ => by rw [mul_comm]
    rw [hf, abs_sub_comm m l] at hB
    calc ∑ n ∈ S.filter (fun y => (y - l) * (y - m) < 0),
          2 * δ n / |l - m| ^ 3 * (1 / |n - l| + 1 / |n - m|)
        = 2 / |l - m| ^ 3 * (∑ n ∈ S.filter (fun y => (y - l) * (y - m) < 0), δ n / |n - l| +
            ∑ n ∈ S.filter (fun y => (y - l) * (y - m) < 0), δ n / |n - m|) := by
          rw [← sum_add_distrib, mul_sum]; refine sum_congr rfl fun n _ => by ring
      _ ≤ _ := by gcongr
  rw [hsq]
  have hpow : |l - m| ^ 4 = (l - m) ^ 2 * (l - m) ^ 2 := by rw [hD2]; ring
  have hauxl := aux_log hδl hD
  have hauxm := aux_log hδm hD
  -- assemble
  have hfin : (Real.pi ^ 2 / 3 / δ l - δ m / (l - m) ^ 2 + (Real.pi ^ 2 / 3 / δ m - δ l / (l - m) ^ 2)) /
      (l - m) ^ 2 + 2 / |l - m| ^ 3 * ((c0 + Real.log (|l - m| / δ l)) +
        (c0 + Real.log (|l - m| / δ m))) ≤ Kc * (1 / δ l + 1 / δ m) / (l - m) ^ 2 := by
    have e1 : (Real.pi ^ 2 / 3 / δ l - δ m / (l - m) ^ 2 + (Real.pi ^ 2 / 3 / δ m - δ l / (l - m) ^ 2)) /
        (l - m) ^ 2 + 2 / |l - m| ^ 3 * ((c0 + Real.log (|l - m| / δ l)) +
          (c0 + Real.log (|l - m| / δ m))) =
        Real.pi ^ 2 / 3 * (1 / δ l + 1 / δ m) / (l - m) ^ 2 +
        (2 * (c0 + Real.log (|l - m| / δ l)) / |l - m| ^ 3 - δ l / |l - m| ^ 4) +
        (2 * (c0 + Real.log (|l - m| / δ m)) / |l - m| ^ 3 - δ m / |l - m| ^ 4) := by
      rw [hpow]; field_simp; ring
    have e2 : Kc * (1 / δ l + 1 / δ m) / (l - m) ^ 2 =
        Real.pi ^ 2 / 3 * (1 / δ l + 1 / δ m) / (l - m) ^ 2 +
        (c0 ^ 2 + 2 / Real.exp 1) / (δ l * |l - m| ^ 2) +
        (c0 ^ 2 + 2 / Real.exp 1) / (δ m * |l - m| ^ 2) := by
      unfold Kc; rw [hD2]; field_simp; ring
    rw [e1, e2]; linarith
  refine le_trans ?_ hfin
  gcongr

/-! ### The bound `U ≤ 9.2 V` (Preissmann's Cauchy–Schwarz argument) -/

/-- `q(a, b) = 1/(a − b)²`, `q(a, a) = 0`. -/
noncomputable def qq (a b : ℝ) : ℝ := if a = b then 0 else 1 / (a - b) ^ 2

theorem qq_symm (a b : ℝ) : qq a b = qq b a := by
  unfold qq
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), show (b - a) ^ 2 = (a - b) ^ 2 by ring]

theorem qq_nonneg (a b : ℝ) : 0 ≤ qq a b := by unfold qq; split_ifs <;> positivity

/-- `U = ∑_{m ≠ n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(m − n)²`. -/
noncomputable def Uform (S : Finset ℝ) (δ t : ℝ → ℝ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S, δ m * √(δ m) * √(δ n) * t m * t n * qq m n

theorem Uform_le (S : Finset ℝ) (δ t : ℝ → ℝ) (hδ : ∀ y ∈ S, 0 < δ y)
    (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) (ht : ∀ y ∈ S, 0 ≤ t y) :
    Uform S δ t ≤ 9.2 * ∑ n ∈ S, t n ^ 2 := by
  set V := ∑ n ∈ S, t n ^ 2 with hV
  set U := Uform S δ t with hU
  set R : ℝ → ℝ := fun n => ∑ m ∈ S, δ m * √(δ m) * √(δ n) * t m * qq m n with hR
  have hUR : U = ∑ n ∈ S, t n * R n := by
    simp only [hU, Uform, hR, mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => by ring
  have hV0 : 0 ≤ V := sum_nonneg fun n _ => sq_nonneg _
  have hU0 : 0 ≤ U := by
    simp only [hU, Uform]
    refine sum_nonneg fun n hn => sum_nonneg fun m hm => ?_
    have := hδ m hm; have := ht m hm; have := ht n hn; have := qq_nonneg m n
    positivity
  -- Cauchy–Schwarz
  have hCS : U ^ 2 ≤ V * ∑ n ∈ S, R n ^ 2 := by
    rw [hUR]; exact sum_mul_sq_le_sq_mul_sq S t R
  -- expand `∑ R²`
  have hR2 : ∑ n ∈ S, R n ^ 2 = ∑ m ∈ S, ∑ l ∈ S, δ m * √(δ m) * (δ l * √(δ l)) * t m * t l *
      ∑ n ∈ S, δ n * (qq m n * qq l n) := by
    have hpt : ∀ n ∈ S, R n ^ 2 = ∑ m ∈ S, ∑ l ∈ S, δ m * √(δ m) * (δ l * √(δ l)) * t m * t l *
        (δ n * (qq m n * qq l n)) := by
      intro n hn
      rw [sq, hR]; simp only; rw [sum_mul_sum]
      refine sum_congr rfl fun m _ => sum_congr rfl fun l _ => ?_
      have : √(δ n) * √(δ n) = δ n := Real.mul_self_sqrt (hδ n hn).le
      linear_combination (δ m * √(δ m) * (δ l * √(δ l)) * t m * t l * (qq m n * qq l n)) * this
    rw [sum_congr rfl hpt, sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_sum]
  -- bound each inner sum
  have hW : ∀ m ∈ S, ∀ l ∈ S, ∑ n ∈ S, δ n * (qq m n * qq l n) ≤
      (if m = l then Real.pi ^ 4 / 45 / δ m ^ 3 else Kc * (1 / δ m + 1 / δ l) * qq m l) := by
    intro m hm l hl
    split_ifs with hml
    · subst hml
      have h4 := Shan.spacing_four S hm δ hδ hsep
      rw [← sum_erase_add _ _ hm]
      have hmm : δ m * (qq m m * qq m m) = 0 := by simp [qq]
      rw [hmm, add_zero]
      refine le_trans (le_of_eq (sum_congr rfl fun n hn => ?_)) h4
      have hne : n ≠ m := (mem_erase.1 hn).1
      simp only [qq, if_neg (Ne.symm hne)]
      rw [show (n - m) ^ 4 = (m - n) ^ 2 * (m - n) ^ 2 by ring]
      field_simp
    · have h6 := lemma6 S hm hl hml δ hδ hsep
      have hT : ∑ n ∈ S, δ n * (qq m n * qq l n) = ∑ n ∈ (S.erase m).erase l,
          δ n / ((n - m) ^ 2 * (n - l) ^ 2) := by
        rw [← sum_erase_add _ _ hm, ← sum_erase_add _ _ (mem_erase.2 ⟨Ne.symm hml, hl⟩)]
        have hz1 : δ m * (qq m m * qq l m) = 0 := by simp [qq]
        have hz2 : δ l * (qq m l * qq l l) = 0 := by simp [qq]
        rw [hz1, hz2, add_zero, add_zero]
        refine sum_congr rfl fun n hn => ?_
        have hn1 : n ≠ l := (mem_erase.1 hn).1
        have hn2 : n ≠ m := (mem_erase.1 (mem_erase.1 hn).2).1
        simp only [qq, if_neg (Ne.symm hn2), if_neg (Ne.symm hn1)]
        rw [show (n - m) ^ 2 = (m - n) ^ 2 by ring, show (n - l) ^ 2 = (l - n) ^ 2 by ring]
        field_simp
      rw [hT]
      refine h6.trans (le_of_eq ?_)
      simp only [qq, if_neg hml]; ring
  have hcoef : ∀ m ∈ S, ∀ l ∈ S, 0 ≤ δ m * √(δ m) * (δ l * √(δ l)) * t m * t l := by
    intro m hm l hl
    have := hδ m hm; have := hδ l hl; have := ht m hm; have := ht l hl
    positivity
  have hRbound : ∑ n ∈ S, R n ^ 2 ≤ Real.pi ^ 4 / 45 * V + 2 * Kc * U := by
    rw [hR2]
    calc ∑ m ∈ S, ∑ l ∈ S, δ m * √(δ m) * (δ l * √(δ l)) * t m * t l *
          ∑ n ∈ S, δ n * (qq m n * qq l n)
        ≤ ∑ m ∈ S, ∑ l ∈ S, δ m * √(δ m) * (δ l * √(δ l)) * t m * t l *
          (if m = l then Real.pi ^ 4 / 45 / δ m ^ 3 else Kc * (1 / δ m + 1 / δ l) * qq m l) :=
          sum_le_sum fun m hm => sum_le_sum fun l hl =>
            mul_le_mul_of_nonneg_left (hW m hm l hl) (hcoef m hm l hl)
      _ = Real.pi ^ 4 / 45 * V + 2 * Kc * U := by
          have hsplit : ∀ m ∈ S, ∀ l ∈ S, δ m * √(δ m) * (δ l * √(δ l)) * t m * t l *
              (if m = l then Real.pi ^ 4 / 45 / δ m ^ 3 else Kc * (1 / δ m + 1 / δ l) * qq m l) =
              (if m = l then Real.pi ^ 4 / 45 * t m ^ 2 else 0) +
                Kc * (√(δ m) * (δ l * √(δ l)) * t m * t l * qq m l +
                  δ m * √(δ m) * √(δ l) * t m * t l * qq m l) := by
            intro m hm l hl
            have hm0 := hδ m hm
            have hl0 := hδ l hl
            have hsm : √(δ m) * √(δ m) = δ m := Real.mul_self_sqrt hm0.le
            have hsl : √(δ l) * √(δ l) = δ l := Real.mul_self_sqrt hl0.le
            split_ifs with hml
            · subst hml
              have hqq : qq m m = 0 := by simp [qq]
              rw [hqq]
              field_simp
              rw [Real.sq_sqrt hm0.le]
              ring
            · simp only [zero_add]
              field_simp
          rw [sum_congr rfl fun m hm => sum_congr rfl fun l hl => hsplit m hm l hl]
          have hU1 : ∑ m ∈ S, ∑ l ∈ S, √(δ m) * (δ l * √(δ l)) * t m * t l * qq m l = U := by
            simp only [hU, Uform]
            refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
            rw [qq_symm]; ring
          have hU2 : ∑ m ∈ S, ∑ l ∈ S, δ m * √(δ m) * √(δ l) * t m * t l * qq m l = U := by
            simp only [hU, Uform]
            rw [sum_comm]
          have hA : ∑ m ∈ S, ∑ l ∈ S, (if m = l then Real.pi ^ 4 / 45 * t m ^ 2 else 0) =
              Real.pi ^ 4 / 45 * V := by
            rw [hV, mul_sum]
            exact sum_congr rfl fun m hm => by rw [sum_ite_eq, if_pos hm]
          simp only [sum_add_distrib, ← mul_sum]
          rw [hA, hU1, hU2]; ring
  -- solve the quadratic inequality
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hpi4 : Real.pi ^ 4 / 45 ≤ 2.1647 := by
    have : Real.pi ^ 4 < 3.1416 ^ 4 := by gcongr
    linarith
  have hK := Kc_le
  have hq : U ^ 2 ≤ V * (2.1647 * V + 8.9054 * U) := by
    refine hCS.trans (mul_le_mul_of_nonneg_left (hRbound.trans ?_) hV0)
    nlinarith
  by_contra hc
  push Not at hc
  nlinarith

/-! ### From eigenvalue bounds to the Hilbert inequality -/

/-- The bilinear form `∑_{n ≠ m} w̄_n w_m/(n − m)` over a finite set of reals. -/
noncomputable def hform (S : Finset ℝ) (w : ℝ → ℂ) : ℂ :=
  ∑ n ∈ S, ∑ m ∈ S, if n = m then 0 else starRingEnd ℂ (w n) * w m / ((n - m : ℝ) : ℂ)

/-- If every solution of `∑_m c_n c_m/(n−m) b_m = ν b_n` (`Re ν = 0`, `‖b‖ = 1`) has `|ν| ≤ C`,
then `|∑_{n≠m} w̄_n w_m/(n − m)| ≤ C ∑ |w_n|²/c_n²`. -/
theorem hform_le_of_eig (S : Finset ℝ) (c : ℝ → ℝ) (hc : ∀ x ∈ S, 0 < c x) {C : ℝ}
    (hbound : ∀ (b : S → ℂ) (ν : ℂ), ν.re = 0 →
      (∀ n : S, ∑ m : S, ((c n * c m * hk (fun i : S => (i : ℝ)) n m : ℝ) : ℂ) * b m = ν * b n) →
      ∑ n : S, ‖b n‖ ^ 2 = 1 → ‖ν‖ ≤ C)
    (w : ℝ → ℂ) : ‖hform S w‖ ≤ C * ∑ n ∈ S, ‖w n‖ ^ 2 / c n ^ 2 := by
  classical
  let x : S → ℝ := fun i => (i : ℝ)
  let r : S → S → ℝ := fun n m => c n * c m * hk x n m
  let A : Matrix S S ℂ := fun n m => Complex.I * (r n m : ℂ)
  have hr : ∀ n m, r m n = -r n m := fun n m => by simp only [r, hk_anti x n m]; ring
  have hA : A.IsHermitian := by
    ext n m
    rw [Matrix.conjTranspose_apply]
    show star (Complex.I * ((r m n : ℝ) : ℂ)) = Complex.I * ((r n m : ℝ) : ℂ)
    rw [hr n m]
    simp
  have hev : ∀ i, |hA.eigenvalues i| ≤ C := by
    intro i
    obtain ⟨heq, hnorm⟩ := eigenvector_spec hA i
    set b : S → ℂ := ⇑(hA.eigenvectorBasis i)
    set μ := hA.eigenvalues i
    have hb : ∀ n, ∑ m, ((r n m : ℝ) : ℂ) * b m = (-Complex.I * μ) * b n := by
      intro n
      have := congrFun heq n
      simp only [Matrix.mulVec, dotProduct, A, Pi.smul_apply, smul_eq_mul] at this
      have h2 : ∑ m, Complex.I * (r n m : ℂ) * b m = Complex.I * ∑ m, (r n m : ℂ) * b m := by
        rw [mul_sum]; refine sum_congr rfl fun m _ => by ring
      rw [h2] at this
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc ∑ m, (r n m : ℂ) * b m = -Complex.I * (Complex.I * ∑ m, (r n m : ℂ) * b m) := by
            rw [← mul_assoc, neg_mul, hI]; ring
        _ = _ := by rw [this]; ring
    have h := hbound b (-Complex.I * μ) (by simp) hb hnorm
    simpa [norm_mul] using h
  have hq := quad_form_le hA hev (fun n => w n / (c n : ℂ))
  have hc' : ∀ n : S, (c n : ℂ) ≠ 0 := fun n => by exact_mod_cast (hc n n.2).ne'
  have hlhs : star (fun n : S => w n / (c n : ℂ)) ⬝ᵥ (A *ᵥ fun n => w n / (c n : ℂ)) =
      Complex.I * hform S w := by
    simp only [dotProduct, Matrix.mulVec, A, Pi.star_apply, hform, mul_sum]
    rw [← sum_coe_sort S]
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_coe_sort S]
    refine sum_congr rfl fun m _ => ?_
    by_cases hnm : (n : ℝ) = m
    · have : n = m := Subtype.ext hnm
      subst this
      simp [r, hk_self]
    · rw [if_neg hnm]
      have hnm' : n ≠ m := fun h => hnm (by rw [h])
      simp only [r, x, hk, if_neg hnm']
      have hsub : ((n : ℝ) - m : ℂ) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast hnm
      simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
      have := hc' n
      have := hc' m
      push_cast
      field_simp
  have hrhs : ∑ n : S, ‖w n / (c n : ℂ)‖ ^ 2 = ∑ n ∈ S, ‖w n‖ ^ 2 / c n ^ 2 := by
    rw [← sum_coe_sort S]
    refine sum_congr rfl fun n _ => ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  rw [hlhs, norm_mul, Complex.norm_I, one_mul, hrhs] at hq
  exact hq

/-- Turning a function on `S` into one on `ℝ`. -/
noncomputable def extS (S : Finset ℝ) (f : S → ℝ) (y : ℝ) : ℝ := if h : y ∈ S then f ⟨y, h⟩ else 0

theorem sum_extS (S : Finset ℝ) (g : ℝ → ℝ → ℝ) (f : S → ℝ) :
    ∑ n : S, g n (f n) = ∑ n ∈ S, g n (extS S f n) := by
  rw [← sum_coe_sort S]
  refine sum_congr rfl fun n _ => ?_
  simp [extS, n.2]

/-- **The weighted Hilbert inequality on ℝ** (Montgomery–Vaughan, constant `4.66 < 3π/2`):
`|∑_{n≠m} w̄_n w_m/(n − m)| ≤ 4.66 ∑ |w_n|²/δ_n`. -/
theorem hilbert_weighted (S : Finset ℝ) (δ : ℝ → ℝ) (hδ : ∀ y ∈ S, 0 < δ y)
    (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) (w : ℝ → ℂ) :
    ‖hform S w‖ ≤ 4.66 * ∑ n ∈ S, ‖w n‖ ^ 2 / δ n := by
  have h := hform_le_of_eig S (fun y => √(δ y)) (fun y hy => Real.sqrt_pos.2 (hδ y hy))
    (C := 4.66) ?_ w
  · refine h.trans (le_of_eq ?_)
    congr 1; refine sum_congr rfl fun n hn => ?_
    rw [Real.sq_sqrt (hδ n hn).le]
  intro b ν hν hb hnorm
  have hx : Function.Injective (fun i : S => (i : ℝ)) := Subtype.val_injective
  have hid := eigen_identity hx (fun i : S => √(δ i)) b hν hb
  rw [hnorm, mul_one] at hid
  -- the two parts
  set t : S → ℝ := fun n => ‖b n‖
  have hsq : ∀ n : S, √(δ n) ^ 2 = δ n := fun n => Real.sq_sqrt (hδ n n.2).le
  have hT1 : ∑ l : S, ∑ n : S, √(δ l) ^ 2 * √(δ n) ^ 2 * hk (fun i : S => (i : ℝ)) n l ^ 2 *
      ‖b l‖ ^ 2 ≤ Real.pi ^ 2 / 3 := by
    calc _ ≤ ∑ l : S, ‖b l‖ ^ 2 * (Real.pi ^ 2 / 3) := by
          refine sum_le_sum fun l _ => ?_
          have hsp := Shan.spacing_two S l.2 δ hδ hsep
          have hδl := hδ l l.2
          have : ∑ n : S, √(δ l) ^ 2 * √(δ n) ^ 2 * hk (fun i : S => (i : ℝ)) n l ^ 2 * ‖b l‖ ^ 2 =
              ‖b l‖ ^ 2 * δ l * ∑ k ∈ S.erase l, δ k / (k - l) ^ 2 := by
            have e1 : ∑ k ∈ S.erase l, δ k / (k - l) ^ 2 = ∑ k ∈ S, δ k * qq k l := by
              rw [← sum_erase_add _ _ l.2]
              have hz : δ l * qq (l : ℝ) l = 0 := by simp [qq]
              rw [hz, add_zero]
              refine sum_congr rfl fun k hk => ?_
              have hne : k ≠ l := (mem_erase.1 hk).1
              simp only [qq, if_neg hne]; field_simp
            rw [e1, mul_sum]
            conv_rhs => rw [← Finset.sum_coe_sort S]
            refine sum_congr rfl fun n _ => ?_
            have hkq : hk (fun i : S => (i : ℝ)) n l ^ 2 = qq n l := by
              unfold hk qq
              by_cases h : n = l
              · subst h; simp
              · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]; field_simp
            rw [hkq, hsq, hsq]; ring
          rw [this]
          have h2 : δ l * ∑ k ∈ S.erase l, δ k / (k - l) ^ 2 ≤ Real.pi ^ 2 / 3 := by
            have := mul_le_mul_of_nonneg_left hsp hδl.le
            rwa [mul_div_cancel₀ _ hδl.ne'] at this
          have := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖b l‖)
          linarith
      _ = Real.pi ^ 2 / 3 := by rw [← sum_mul, hnorm, one_mul]
  have hT2 : ∑ l : S, ∑ m : S, √(δ l) * √(δ m) * hk (fun i : S => (i : ℝ)) l m ^ 2 *
      (√(δ l) ^ 2 + √(δ m) ^ 2) * (starRingEnd ℂ (b l) * b m).re ≤ 2 * 9.2 := by
    have hU := Uform_le S δ (extS S t) hδ hsep (fun y hy => by simp [extS, hy, t])
    have hV : ∑ n ∈ S, extS S t n ^ 2 = 1 := by
      rw [← hnorm, ← sum_coe_sort S]
      refine sum_congr rfl fun n _ => ?_
      simp [extS, n.2, t]
    rw [hV, mul_one] at hU
    have hle : ∀ l m : S, √(δ l) * √(δ m) * hk (fun i : S => (i : ℝ)) l m ^ 2 *
        (√(δ l) ^ 2 + √(δ m) ^ 2) * (starRingEnd ℂ (b l) * b m).re ≤
        (δ l * √(δ l) * √(δ m) + δ m * √(δ m) * √(δ l)) * t l * t m * qq l m := by
      intro l m
      have hre : (starRingEnd ℂ (b l) * b m).re ≤ t l * t m := by
        refine (Complex.re_le_norm _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_conj]
      have hkq : hk (fun i : S => (i : ℝ)) l m ^ 2 = qq l m := by
        unfold hk qq
        by_cases h : l = m
        · subst h; simp
        · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]; field_simp
      rw [hkq, hsq, hsq]
      have hpos : 0 ≤ √(δ l) * √(δ m) * qq l m * (δ l + δ m) := by
        have := hδ l l.2; have := hδ m m.2; have := qq_nonneg l m; positivity
      calc √(δ l) * √(δ m) * qq l m * (δ l + δ m) * (starRingEnd ℂ (b l) * b m).re
          ≤ √(δ l) * √(δ m) * qq l m * (δ l + δ m) * (t l * t m) :=
            mul_le_mul_of_nonneg_left hre hpos
        _ = _ := by ring
    calc _ ≤ ∑ l : S, ∑ m : S, (δ l * √(δ l) * √(δ m) + δ m * √(δ m) * √(δ l)) * t l * t m *
          qq l m := sum_le_sum fun l _ => sum_le_sum fun m _ => hle l m
      _ = 2 * Uform S δ (extS S t) := by
          have e1 : ∑ l : S, ∑ m : S, (δ l * √(δ l) * √(δ m) + δ m * √(δ m) * √(δ l)) * t l * t m *
              qq l m = ∑ l ∈ S, ∑ m ∈ S, (δ l * √(δ l) * √(δ m) + δ m * √(δ m) * √(δ l)) *
                extS S t l * extS S t m * qq l m := by
            rw [← sum_coe_sort S]
            refine sum_congr rfl fun l _ => ?_
            rw [← sum_coe_sort S]
            refine sum_congr rfl fun m _ => ?_
            simp [extS, l.2, m.2, t]
          rw [e1]
          simp only [Uform, add_mul, sum_add_distrib]
          have e2 : ∑ l ∈ S, ∑ m ∈ S, δ l * √(δ l) * √(δ m) * extS S t l * extS S t m * qq l m =
              ∑ n ∈ S, ∑ m ∈ S, δ m * √(δ m) * √(δ n) * extS S t m * extS S t n * qq m n := by
            rw [sum_comm]
          have e3 : ∑ l ∈ S, ∑ m ∈ S, δ m * √(δ m) * √(δ l) * extS S t l * extS S t m * qq l m =
              ∑ n ∈ S, ∑ m ∈ S, δ m * √(δ m) * √(δ n) * extS S t m * extS S t n * qq m n := by
            refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
            rw [qq_symm]; ring
          rw [e2, e3]; ring
      _ ≤ 2 * 9.2 := by linarith
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hν2 : ‖ν‖ ^ 2 ≤ 4.66 ^ 2 := by
    rw [hid]; nlinarith
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg ν]

theorem sum_hk_sq (S : Finset ℝ) (l : S) (f : ℝ → ℝ) :
    ∑ n : S, f n * hk (fun i : S => (i : ℝ)) n l ^ 2 = ∑ k ∈ S.erase l, f k / (k - l) ^ 2 := by
  have e1 : ∑ k ∈ S.erase l, f k / (k - l) ^ 2 = ∑ k ∈ S, f k * qq k l := by
    rw [← sum_erase_add _ _ l.2]
    have hz : f l * qq (l : ℝ) l = 0 := by simp [qq]
    rw [hz, add_zero]
    refine sum_congr rfl fun k hk => ?_
    have hne : k ≠ l := (mem_erase.1 hk).1
    simp only [qq, if_neg hne]; field_simp
  rw [e1]
  conv_rhs => rw [← Finset.sum_coe_sort S]
  refine sum_congr rfl fun n _ => ?_
  congr 1
  unfold hk qq
  by_cases h : n = l
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]; field_simp

/-- **The Hilbert inequality on ℝ for `δ`-spaced points** (Montgomery–Vaughan):
`|∑_{n≠m} w̄_n w_m/(n − m)| ≤ (π/δ) ∑ |w_n|²`. -/
theorem hilbert_uniform (S : Finset ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ₀ ≤ |y - z|) (w : ℝ → ℂ) :
    ‖hform S w‖ ≤ Real.pi / δ₀ * ∑ n ∈ S, ‖w n‖ ^ 2 := by
  have h := hform_le_of_eig S (fun _ => 1) (fun _ _ => one_pos) (C := Real.pi / δ₀) ?_ w
  · simpa using h
  intro b ν hν hb hnorm
  have hx : Function.Injective (fun i : S => (i : ℝ)) := Subtype.val_injective
  have hid := eigen_identity hx (fun _ : S => (1 : ℝ)) b hν hb
  rw [hnorm, mul_one] at hid
  simp only [one_pow, one_mul, mul_one] at hid
  -- `∑_n a_{nl}² ≤ π²/(3δ₀²)`
  have hrow : ∀ l : S, ∑ n : S, hk (fun i : S => (i : ℝ)) n l ^ 2 ≤ Real.pi ^ 2 / 3 / δ₀ ^ 2 := by
    intro l
    have h1 := sum_hk_sq S l (fun _ => 1)
    simp only [one_mul] at h1
    rw [h1]
    have hsp := Shan.spacing_two S l.2 (fun _ => δ₀) (fun _ _ => hδ₀) hsep
    have : ∑ k ∈ S.erase l, δ₀ / (k - l) ^ 2 = δ₀ * ∑ k ∈ S.erase l, 1 / (k - l) ^ 2 := by
      rw [mul_sum]; refine sum_congr rfl fun k _ => by ring
    rw [this] at hsp
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hsp hδ₀.le
    calc (∑ k ∈ S.erase l, 1 / (k - l) ^ 2) * δ₀ ^ 2 = δ₀ * (∑ k ∈ S.erase l, 1 / (k - l) ^ 2) * δ₀ := by
          ring
      _ ≤ Real.pi ^ 2 / 3 / δ₀ * δ₀ := this
      _ = Real.pi ^ 2 / 3 := by field_simp
  have hT1 : ∑ l : S, ∑ n : S, hk (fun i : S => (i : ℝ)) n l ^ 2 * ‖b l‖ ^ 2 ≤
      Real.pi ^ 2 / 3 / δ₀ ^ 2 := by
    calc _ = ∑ l : S, ‖b l‖ ^ 2 * ∑ n : S, hk (fun i : S => (i : ℝ)) n l ^ 2 := by
          refine sum_congr rfl fun l _ => ?_; rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
      _ ≤ ∑ l : S, ‖b l‖ ^ 2 * (Real.pi ^ 2 / 3 / δ₀ ^ 2) :=
          sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hrow l) (sq_nonneg _)
      _ = _ := by rw [← sum_mul, hnorm, one_mul]
  have hT2 : ∑ l : S, ∑ m : S, hk (fun i : S => (i : ℝ)) l m ^ 2 * (1 + 1) *
      (starRingEnd ℂ (b l) * b m).re ≤ 2 * (Real.pi ^ 2 / 3 / δ₀ ^ 2) := by
    have hpt : ∀ l m : S, hk (fun i : S => (i : ℝ)) l m ^ 2 * (1 + 1) * (starRingEnd ℂ (b l) * b m).re ≤
        hk (fun i : S => (i : ℝ)) l m ^ 2 * ‖b l‖ ^ 2 + hk (fun i : S => (i : ℝ)) m l ^ 2 * ‖b m‖ ^ 2 := by
      intro l m
      have hre : 2 * (starRingEnd ℂ (b l) * b m).re ≤ ‖b l‖ ^ 2 + ‖b m‖ ^ 2 := by
        have h1 : (starRingEnd ℂ (b l) * b m).re ≤ ‖b l‖ * ‖b m‖ := by
          refine (Complex.re_le_norm _).trans (le_of_eq ?_)
          rw [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖b l‖ - ‖b m‖)]
      rw [hk_anti _ l m, neg_sq]
      nlinarith [sq_nonneg (hk (fun i : S => (i : ℝ)) l m)]
    calc _ ≤ ∑ l : S, ∑ m : S, (hk (fun i : S => (i : ℝ)) l m ^ 2 * ‖b l‖ ^ 2 +
          hk (fun i : S => (i : ℝ)) m l ^ 2 * ‖b m‖ ^ 2) :=
          sum_le_sum fun l _ => sum_le_sum fun m _ => hpt l m
      _ = 2 * ∑ l : S, ∑ n : S, hk (fun i : S => (i : ℝ)) n l ^ 2 * ‖b l‖ ^ 2 := by
          simp only [sum_add_distrib]
          rw [sum_comm (f := fun l m => hk (fun i : S => (i : ℝ)) m l ^ 2 * ‖b m‖ ^ 2)]
          have : ∑ l : S, ∑ m : S, hk (fun i : S => (i : ℝ)) l m ^ 2 * ‖b l‖ ^ 2 =
              ∑ l : S, ∑ n : S, hk (fun i : S => (i : ℝ)) n l ^ 2 * ‖b l‖ ^ 2 :=
            sum_congr rfl fun l _ => sum_congr rfl fun n _ => by rw [hk_anti _ l n, neg_sq]
          rw [this]; ring
      _ ≤ _ := by linarith
  have hν2 : ‖ν‖ ^ 2 ≤ (Real.pi / δ₀) ^ 2 := by
    rw [hid, div_pow]
    have : Real.pi ^ 2 / δ₀ ^ 2 = 3 * (Real.pi ^ 2 / 3 / δ₀ ^ 2) := by ring
    rw [this]; linarith
  have hpos : 0 ≤ Real.pi / δ₀ := by positivity
  nlinarith [norm_nonneg ν, sq_nonneg (‖ν‖ - Real.pi / δ₀)]

end TernaryGoldbach.Prelim.Hilbert
