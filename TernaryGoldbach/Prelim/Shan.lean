import Mathlib

/-!
# Shan's spacing lemma

For a convex, non-increasing, non-negative `f` on `[1, ∞)` with `∑ f(j) < ∞`, and gaps `a₀ ≥ 1`,
`a₁, a₂, … > 0` with partial sums `λ_n = a₀ + ⋯ + a_n`:
`∑_{n < N} min(a_n, a_{n+1}) f(λ_n) ≤ ∑_{j ≥ 1} f(j)`.

This is the core of the spacing lemma `∑_{k ≠ l} δ_k/|λ_k − λ_l|^σ ≤ 2ζ(σ)/δ_l^{σ−1}` used in the
Montgomery–Vaughan weighted Hilbert inequality. We follow W. Yangjit, *On the Montgomery–Vaughan
weighted generalization of Hilbert's inequality*, arXiv:2203.14950, Lemmas 2.3–2.5 (an exposition of
Shan's method).
-/

open Finset

namespace TernaryGoldbach.Prelim.Shan

/-- The hypotheses on `f`. -/
structure Good (f : ℝ → ℝ) : Prop where
  convex : ConvexOn ℝ (Set.Ici 1) f
  anti : AntitoneOn f (Set.Ici 1)
  nonneg : ∀ x, 1 ≤ x → 0 ≤ f x
  summable : Summable fun j : ℕ => f (j + 1)

variable {f : ℝ → ℝ}

/-- The staircase potential `Φ(x) = ∑_{j ≤ ⌊x⌋} f(j) + {x} f(⌊x⌋ + 1)`. -/
noncomputable def Phi (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ range ⌊x⌋₊, f (j + 1) + Int.fract x * f (⌊x⌋₊ + 1)

theorem Phi_zero : Phi f 0 = 0 := by simp [Phi]

theorem Phi_le_tsum (hf : Good f) {x : ℝ} (_hx : 0 ≤ x) : Phi f x ≤ ∑' j : ℕ, f (j + 1) := by
  have hfr : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
  have hf1 : 0 ≤ f (⌊x⌋₊ + 1) := hf.nonneg _ (by have := Nat.cast_nonneg (α := ℝ) ⌊x⌋₊; linarith)
  calc Phi f x ≤ ∑ j ∈ range (⌊x⌋₊ + 1), f (j + 1) := by
        rw [Phi, sum_range_succ]
        have := mul_le_of_le_one_left hf1 hfr
        linarith
    _ ≤ _ := hf.summable.sum_le_tsum _ fun j _ => hf.nonneg _ (by
        have := Nat.cast_nonneg (α := ℝ) j; linarith)

/-- One step of Lemma 2.3: for `0 ≤ λ` and `a ≥ 1`, `a f(λ + a) ≤ Φ(λ + a) − Φ(λ)`. -/
theorem step (hf : Good f) {lam a : ℝ} (hlam : 0 ≤ lam) (ha : 1 ≤ a) :
    a * f (lam + a) ≤ Phi f (lam + a) - Phi f lam := by
  set μ := lam + a with hμ
  set m := ⌊μ⌋₊
  set k := ⌊lam⌋₊
  have hμ0 : 0 ≤ μ := by linarith
  have hμm : (m : ℝ) ≤ μ := Nat.floor_le hμ0
  have hμm1 : μ < m + 1 := Nat.lt_floor_add_one μ
  have hlk : (k : ℝ) ≤ lam := Nat.floor_le hlam
  have hlk1 : lam < k + 1 := Nat.lt_floor_add_one lam
  have hfμ : Int.fract μ = μ - m := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor hμ0]
  have hfl : Int.fract lam = lam - k := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor hlam]
  -- `m ≥ k + 1 ≥ 1`.
  have hmk : k + 1 ≤ m := by
    apply Nat.le_floor; push_cast; linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast le_trans (Nat.le_add_left 1 k) hmk
  -- (2.6) convexity between `m` and `m + 1`, (2.7) monotonicity.
  have h26 : f μ ≤ (1 - Int.fract μ) * f m + Int.fract μ * f (m + 1) := by
    have hfr0 := Int.fract_nonneg μ
    have hfr1 := Int.fract_lt_one μ
    have := hf.convex.2 (Set.mem_Ici.2 hm1) (Set.mem_Ici.2 (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1))
      (by linarith : (0 : ℝ) ≤ 1 - Int.fract μ) hfr0 (by ring)
    simp only [smul_eq_mul] at this
    have he : (1 - Int.fract μ) * (m : ℝ) + Int.fract μ * ((m : ℝ) + 1) = μ := by
      rw [hfμ]; ring
    rwa [he] at this
  have h27 : (a - 1) * f μ ≤ (a - 1) * f m :=
    mul_le_mul_of_nonneg_left (hf.anti (Set.mem_Ici.2 hm1) (Set.mem_Ici.2 (by linarith)) hμm)
      (by linarith)
  -- The sum over `k + 1 < j + 1 ≤ m`.
  have hsum : ((m : ℝ) - k - 1) * f m ≤ ∑ j ∈ Ico (k + 1) m, f (j + 1) := by
    have hcard : ((Ico (k + 1) m).card : ℝ) = m - k - 1 := by
      rw [Nat.card_Ico]; push_cast [Nat.cast_sub hmk]; ring
    rw [← hcard, ← nsmul_eq_mul]
    refine card_nsmul_le_sum _ _ _ fun j hj => ?_
    have hj' := mem_Ico.1 hj
    refine hf.anti (Set.mem_Ici.2 (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
      (Set.mem_Ici.2 hm1) ?_
    exact_mod_cast hj'.2
  have hk1 : (1 - Int.fract lam) * f m ≤ (1 - Int.fract lam) * f (k + 1) :=
    mul_le_mul_of_nonneg_left (hf.anti (Set.mem_Ici.2 (by
      have := Nat.cast_nonneg (α := ℝ) k; linarith)) (Set.mem_Ici.2 hm1) (by
      exact_mod_cast hmk)) (by linarith [Int.fract_lt_one lam])
  -- `Φ(μ) − Φ(λ)`.
  have hPhi : Phi f μ - Phi f lam = f (k + 1) + ∑ j ∈ Ico (k + 1) m, f (j + 1) +
      Int.fract μ * f (m + 1) - Int.fract lam * f (k + 1) := by
    simp only [Phi]
    have h1 : ∑ j ∈ range m, f (j + 1) = ∑ j ∈ range k, f (j + 1) + f (k + 1) +
        ∑ j ∈ Ico (k + 1) m, f (j + 1) := by
      rw [← sum_range_succ (fun j : ℕ => f (j + 1)) k, sum_range_add_sum_Ico _ hmk]
    rw [h1]; ring
  rw [hPhi]
  have ha' : a = (m - k - 1) + (1 - Int.fract lam) + Int.fract μ := by
    rw [hfμ, hfl]; ring
  have heq : (1 - Int.fract μ) * f m + (a - 1) * f m =
      ((m - k - 1) + (1 - Int.fract lam)) * f m := by rw [ha']; ring
  have hsplit : a * f μ = f μ + (a - 1) * f μ := by ring
  nlinarith [h26, h27, hsum, hk1, heq, hsplit]

/-- [Yangjit, Lemma 2.3]: if `a_n ≥ 1` for all `n < N`, then
`∑_{n<N} a_n f(a₀ + ⋯ + a_n) ≤ Φ(a₀ + ⋯ + a_{N−1})`. -/
theorem sum_le_Phi (hf : Good f) (a : ℕ → ℝ) (N : ℕ) (ha : ∀ n < N, 1 ≤ a n) :
    ∑ n ∈ range N, a n * f (∑ i ∈ range (n + 1), a i) ≤ Phi f (∑ i ∈ range N, a i) := by
  induction N with
  | zero => simp [Phi_zero]
  | succ N ih =>
    have hpos : 0 ≤ ∑ i ∈ range N, a i :=
      sum_nonneg fun i hi => by linarith [ha i (by have := mem_range.1 hi; omega)]
    have h := step hf hpos (ha N (by omega))
    rw [sum_range_succ, sum_range_succ (fun i => a i) N]
    have := ih fun n hn => ha n (by omega)
    linarith

theorem sum_le_tsum_of_one_le (hf : Good f) (a : ℕ → ℝ) (N : ℕ) (ha : ∀ n < N, 1 ≤ a n) :
    ∑ n ∈ range N, a n * f (∑ i ∈ range (n + 1), a i) ≤ ∑' j : ℕ, f (j + 1) := by
  refine (sum_le_Phi hf a N ha).trans (Phi_le_tsum hf ?_)
  exact sum_nonneg fun i hi => by linarith [ha i (mem_range.1 hi)]

/-- `λ_n = a₀ + ⋯ + a_n`. -/
noncomputable def lam (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range (n + 1), a i

/-- `F_N(a) = ∑_{n<N} min(a_n, a_{n+1}) f(λ_n)`. -/
noncomputable def FN (f : ℝ → ℝ) (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, min (a n) (a (n + 1)) * f (lam a n)

theorem lam_succ (a : ℕ → ℝ) (n : ℕ) : lam a (n + 1) = lam a n + a (n + 1) := by
  simp [lam, sum_range_succ _ (n + 1)]

theorem one_le_lam {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (h0 : 1 ≤ a 0) (n : ℕ) : 1 ≤ lam a n := by
  induction n with
  | zero => simpa [lam] using h0
  | succ n ih => rw [lam_succ]; linarith [hpos (n + 1)]

/-- [Yangjit, Lemma 2.4]: raising a gap that is smaller than its predecessor does not decrease
`F_N`. -/
theorem FN_le_update (hf : Good f) {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (h0 : 1 ≤ a 0) {ν : ℕ}
    (hν : 1 ≤ ν) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ a (ν - 1) - a ν) (N : ℕ) :
    FN f N a ≤ FN f N (Function.update a ν (a ν + ε)) := by
  set b := Function.update a ν (a ν + ε) with hb
  have hbν : b ν = a ν + ε := by simp [hb]
  have hbn : ∀ n, n ≠ ν → b n = a n := fun n hn => by simp [hb, hn]
  have hlam_lt : ∀ n, n < ν → lam b n = lam a n := by
    intro n hn
    refine sum_congr rfl fun i hi => hbn i ?_
    have := mem_range.1 hi; omega
  have hlam_ge : ∀ n, ν ≤ n → lam b n = lam a n + ε := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge n ν with h | h
      · have hn' : n + 1 = ν := by omega
        rw [lam_succ, lam_succ, hlam_lt n h, hn', hbν]; ring
      · rw [lam_succ, lam_succ, ih h, hbn (n + 1) (by omega)]; ring
  have hfa : ∀ n, 1 ≤ lam a n := one_le_lam hpos h0
  -- Below `ν`, the terms agree.
  have hlow : ∀ N, N ≤ ν - 1 → FN f N b = FN f N a := by
    intro N hN
    refine sum_congr rfl fun n hn => ?_
    have := mem_range.1 hn
    rw [hbn n (by omega), hbn (n + 1) (by omega), hlam_lt n (by omega)]
  -- The invariant `F_N(b) − F_N(a) ≥ ε f(λ_{N−1})` for `N ≥ ν`.
  have hinv : ∀ N, ν ≤ N → FN f N a + ε * f (lam a (N - 1)) ≤ FN f N b := by
    intro N hN
    induction N with
    | zero => omega
    | succ N ih =>
      rcases Nat.lt_or_ge N ν with h | h
      · -- `N + 1 = ν`: the new term is `n = ν − 1`.
        have hN : N = ν - 1 := by omega
        simp only [FN] at *
        rw [sum_range_succ, sum_range_succ]
        have hl := hlow N (by omega)
        rw [hl, hbn N (by omega), show N + 1 = ν by omega, hbν, hlam_lt N (by omega)]
        have hmin1 : min (a N) (a ν + ε) = a ν + ε := by
          rw [hN]; exact min_eq_right (by linarith)
        have hmin2 : min (a N) (a ν) = a ν := by
          rw [hN]; exact min_eq_right (by linarith)
        rw [hmin1, hmin2, ← hN]
        linarith
      · have ih := ih h
        simp only [FN] at *
        rw [sum_range_succ, sum_range_succ]
        -- The new term `n = N ≥ ν`.
        have hmin : min (a N) (a (N + 1)) ≤ min (b N) (b (N + 1)) := by
          rcases eq_or_ne N ν with hNν | hNν
          · rw [hNν, hbν, hbn (ν + 1) (by omega)]
            exact min_le_min (by linarith) le_rfl
          · rw [hbn N hNν, hbn (N + 1) (by omega)]
        have hmin0 : 0 ≤ min (a N) (a (N + 1)) := le_min (hpos N).le (hpos _).le
        have hfb : 0 ≤ f (lam a N + ε) := hf.nonneg _ (by linarith [hfa N])
        rw [hlam_ge N h]
        have hterm : min (a N) (a (N + 1)) * f (lam a N + ε) ≤
            min (b N) (b (N + 1)) * f (lam a N + ε) := mul_le_mul_of_nonneg_right hmin hfb
        -- Convexity: `min(a_N, a_{N+1})(f(λ_N + ε) − f(λ_N)) ≥ ε (f(λ_N) − f(λ_{N−1}))`.
        have hN1 : 1 ≤ N := le_trans hν h
        have hlamN : lam a N = lam a (N - 1) + a N := by
          have := lam_succ a (N - 1); rw [show N - 1 + 1 = N by omega] at this; exact this
        have hslope := hf.convex.slope_mono_adjacent (x := lam a (N - 1)) (y := lam a N)
          (z := lam a N + ε) (Set.mem_Ici.2 (hfa _)) (Set.mem_Ici.2 (by linarith [hfa N]))
          (by rw [hlamN]; linarith [hpos N]) (by linarith)
        have haN := hpos N
        have hdec : f (lam a N) - f (lam a (N - 1)) ≤ 0 := by
          have := hf.anti (Set.mem_Ici.2 (hfa (N - 1))) (Set.mem_Ici.2 (hfa N))
            (by rw [hlamN]; linarith)
          linarith
        rw [show lam a N - lam a (N - 1) = a N by linarith,
          show lam a N + ε - lam a N = ε by ring] at hslope
        rw [div_le_div_iff₀ haN hε] at hslope
        have hconv : ε * (f (lam a N) - f (lam a (N - 1))) ≤
            min (a N) (a (N + 1)) * (f (lam a N + ε) - f (lam a N)) := by
          have hm : min (a N) (a (N + 1)) ≤ a N := min_le_left _ _
          have : ε * (f (lam a N) - f (lam a (N - 1))) ≤ 0 := by nlinarith
          have h2 : 0 ≤ f (lam a N + ε) - f (lam a N) ∨ f (lam a N + ε) - f (lam a N) < 0 :=
            le_or_gt _ _
          rcases h2 with h2 | h2
          · nlinarith
          · -- `min · X ≥ a_N · X` for `X < 0`, and `a_N X ≥ ε (f λ_N − f λ_{N−1})`.
            have h3 : a N * (f (lam a N + ε) - f (lam a N)) ≤
                min (a N) (a (N + 1)) * (f (lam a N + ε) - f (lam a N)) := by nlinarith
            nlinarith
        rw [show N + 1 - 1 = N by omega]
        nlinarith [hterm, hconv, ih]
  rcases Nat.lt_or_ge N ν with h | h
  · rw [hlow N (by omega)]
  · have := hinv N h
    have : 0 ≤ ε * f (lam a (N - 1)) := mul_nonneg hε.le (hf.nonneg _ (hfa _))
    linarith

/-- The running maximum `ā_n = max(a₀, …, a_n)`. -/
noncomputable def amax (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | n + 1 => max (amax a n) (a (n + 1))

theorem amax_mono (a : ℕ → ℝ) : Monotone (amax a) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

theorem le_amax (a : ℕ → ℝ) (n : ℕ) : a n ≤ amax a n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_right _ _

/-- The sequence monotonized up to index `k`. -/
noncomputable def amon (a : ℕ → ℝ) (k : ℕ) (n : ℕ) : ℝ := if n ≤ k then amax a n else a n

theorem amon_succ (a : ℕ → ℝ) (k : ℕ) :
    amon a (k + 1) = Function.update (amon a k) (k + 1) (amax a (k + 1)) := by
  funext n
  rcases lt_trichotomy n (k + 1) with h | h | h
  · simp [amon, Function.update, show n ≤ k by omega, show n ≤ k + 1 by omega, h.ne]
  · subst h; simp [amon]
  · simp [amon, Function.update, show ¬ n ≤ k by omega, show ¬ n ≤ k + 1 by omega, h.ne']

/-- [Yangjit, Lemma 2.5]: `F_N(a) ≤ ∑_{j≥1} f(j)` when `a₀ ≥ 1` and all `a_n > 0`. -/
theorem FN_le_tsum (hf : Good f) {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (h0 : 1 ≤ a 0) (N : ℕ) :
    FN f N a ≤ ∑' j : ℕ, f (j + 1) := by
  have hamax_pos : ∀ n, 0 < amax a n := fun n => lt_of_lt_of_le (hpos n) (le_amax a n)
  have hmon_pos : ∀ k n, 0 < amon a k n := fun _ n => by
    unfold amon; split_ifs; exacts [hamax_pos n, hpos n]
  have hmon0 : ∀ k, 1 ≤ amon a k 0 := fun k => by simp [amon, amax, h0]
  -- `F_N(a) ≤ F_N(amon a k)` for all `k`.
  have hstep : ∀ k, FN f N a ≤ FN f N (amon a k) := by
    intro k
    induction k with
    | zero =>
      have : amon a 0 = a := by
        funext n; unfold amon; split_ifs with h
        · rw [Nat.le_zero.1 h]; rfl
        · rfl
      rw [this]
    | succ k ih =>
      refine ih.trans ?_
      rw [amon_succ]
      have hk : amon a k k = amax a k := by simp [amon]
      have hk1 : amon a k (k + 1) = a (k + 1) := by simp [amon]
      rcases le_or_gt (amax a k) (a (k + 1)) with h | h
      · have : amax a (k + 1) = amon a k (k + 1) := by
          rw [hk1]; exact max_eq_right h
        rw [this, Function.update_eq_self]
      · have hupd := FN_le_update hf (hmon_pos k) (hmon0 k) (ν := k + 1) (by omega)
          (ε := amax a k - a (k + 1)) (by linarith) (by rw [show k + 1 - 1 = k by omega, hk, hk1])
          N
        have : amon a k (k + 1) + (amax a k - a (k + 1)) = amax a (k + 1) := by
          rw [hk1]; simp only [amax]; rw [max_eq_left h.le]; ring
        rwa [this] at hupd
  refine (hstep N).trans (le_of_eq_of_le ?_ (sum_le_tsum_of_one_le hf (amax a) N fun n _ =>
    h0.trans (amax_mono a (Nat.zero_le n))))
  refine sum_congr rfl fun n hn => ?_
  have hn := mem_range.1 hn
  have h1 : amon a N n = amax a n := by simp [amon, show n ≤ N by omega]
  have h2 : amon a N (n + 1) = amax a (n + 1) := by simp [amon, show n + 1 ≤ N by omega]
  have h3 : lam (amon a N) n = ∑ i ∈ range (n + 1), amax a i :=
    sum_congr rfl fun i hi => by simp [amon, show i ≤ N by have := mem_range.1 hi; omega]
  rw [h1, h2, h3, min_eq_left (amax_mono a (Nat.le_succ n))]

/-! ### The spacing lemma for a finite set of points -/

/-- One side of [Yangjit, Lemma 2.2]: for a finite set `S ∋ l` with `0 < δ_y ≤ |y − z|`
(`y ≠ z ∈ S`), `∑_{k ∈ S, k > l} (δ_k/δ_l) f((k − l)/δ_l) ≤ ∑_{j ≥ 1} f(j)`. -/
theorem one_side (hf : Good f) (S : Finset ℝ) {l : ℝ} (hl : l ∈ S) (δ : ℝ → ℝ)
    (hδ : ∀ y ∈ S, 0 < δ y) (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) :
    ∑ k ∈ S.filter (l < ·), δ k / δ l * f ((k - l) / δ l) ≤ ∑' j : ℕ, f (j + 1) := by
  have htsum : 0 ≤ ∑' j : ℕ, f (j + 1) :=
    tsum_nonneg fun j => hf.nonneg _ (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  set T := S.filter (l < ·) with hT
  set N := T.card with hN
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · rw [Finset.card_eq_zero.1 hN0]; simpa using htsum
  have hδl := hδ l hl
  set e := T.orderEmbOfFin hN.symm
  have heT : ∀ i, e i ∈ T := fun i => T.orderEmbOfFin_mem hN.symm i
  have heS : ∀ i, e i ∈ S := fun i => (mem_filter.1 (heT i)).1
  have hel : ∀ i, l < e i := fun i => (mem_filter.1 (heT i)).2
  -- positions and gaps
  let pos : ℕ → ℝ := fun n => e ⟨min n (N - 1), by omega⟩
  let prev : ℕ → ℝ := fun n => if n = 0 then l else pos (n - 1)
  let a : ℕ → ℝ := fun n => (pos (min n (N - 1)) - prev (min n (N - 1))) / δ l
  have hpos_mono : ∀ m n, m < n → n < N → pos m < pos n := by
    intro m n hmn hn
    simp only [pos]
    apply e.strictMono
    simp only [Fin.mk_lt_mk]; omega
  have hgap_pos : ∀ m, m < N → 0 < pos m - prev m := by
    intro m hm
    simp only [prev]; split_ifs with h0
    · simp only [pos]; linarith [hel ⟨min m (N - 1), by omega⟩]
    · linarith [hpos_mono (m - 1) m (by omega) hm]
  have hprevS : ∀ m, prev m ∈ S := by
    intro m; simp only [prev]; split_ifs
    · exact hl
    · exact heS _
  have hprev_ne : ∀ m, m < N → prev m ≠ pos m := fun m hm => (ne_of_lt (by linarith [hgap_pos m hm]))
  have ha_pos : ∀ n, 0 < a n := fun n => div_pos (hgap_pos _ (by omega)) hδl
  have ha0 : 1 ≤ a 0 := by
    simp only [a, Nat.zero_min]
    rw [le_div_iff₀ hδl, one_mul]
    have h := hsep l hl (pos 0) (heS _) (hprev_ne 0 hNpos).symm
    simp only [prev, ite_true] at h ⊢
    rw [abs_sub_comm, abs_of_pos (by simp only [pos]; linarith [hel ⟨min 0 (N - 1), by omega⟩])] at h
    exact h
  -- `λ_n = (pos n − l)/δ_l` for `n < N`.
  have hlam : ∀ n, n < N → lam a n = (pos n - l) / δ l := by
    intro n hn
    induction n with
    | zero =>
      rw [lam, zero_add, sum_range_one]
      simp [a, prev]
    | succ n ih =>
      rw [lam_succ, ih (by omega)]
      simp only [a, show min (n + 1) (N - 1) = n + 1 by omega, prev, if_neg (Nat.succ_ne_zero n),
        show n + 1 - 1 = n by omega]
      field_simp; ring
  -- weights
  have hw : ∀ n, n < N → δ (pos n) / δ l ≤ min (a n) (a (n + 1)) := by
    intro n hn
    rw [div_le_iff₀ hδl, min_mul_of_nonneg _ _ hδl.le]
    have hposS : pos n ∈ S := heS _
    refine le_min ?_ ?_
    · simp only [a, show min n (N - 1) = n by omega]
      rw [div_mul_cancel₀ _ hδl.ne']
      have h := hsep (pos n) hposS (prev n) (hprevS n) (hprev_ne n hn)
      rwa [abs_of_pos (hgap_pos n hn)] at h
    · rcases Nat.lt_or_ge (n + 1) N with h1 | h1
      · simp only [a, show min (n + 1) (N - 1) = n + 1 by omega, prev, if_neg (Nat.succ_ne_zero n),
          show n + 1 - 1 = n by omega]
        rw [div_mul_cancel₀ _ hδl.ne']
        have hlt := hpos_mono n (n + 1) (by omega) h1
        have h := hsep (pos n) hposS (pos (n + 1)) (heS _) (ne_of_gt hlt)
        rwa [abs_sub_comm, abs_of_pos (by linarith)] at h
      · simp only [a, show min (n + 1) (N - 1) = n by omega]
        rw [div_mul_cancel₀ _ hδl.ne']
        have h := hsep (pos n) hposS (prev n) (hprevS n) (hprev_ne n hn)
        rwa [abs_of_pos (hgap_pos n hn)] at h
  -- reindex the sum
  have hsum : ∑ k ∈ T, δ k / δ l * f ((k - l) / δ l) =
      ∑ n ∈ range N, δ (pos n) / δ l * f (lam a n) := by
    rw [← T.image_orderEmbOfFin_univ hN.symm, sum_image fun i _ j _ h => e.injective h,
      ← Fin.sum_univ_eq_sum_range (fun n => δ (pos n) / δ l * f (lam a n)) N]
    refine sum_congr rfl fun i _ => ?_
    have hi : (⟨min (i : ℕ) (N - 1), by omega⟩ : Fin N) = i := by
      ext; simp only; omega
    simp only [pos, hi]
    rw [hlam i i.2]
    simp only [pos, hi]
  rw [hsum]
  refine le_trans ?_ (FN_le_tsum hf ha_pos ha0 N)
  refine sum_le_sum fun n hn => ?_
  have hn := mem_range.1 hn
  refine mul_le_mul_of_nonneg_right (hw n hn) (hf.nonneg _ ?_)
  exact one_le_lam ha_pos ha0 n

/-- [Yangjit, Lemma 2.2] for a finite set:
`∑_{k ∈ S, k ≠ l} (δ_k/δ_l) f(|k − l|/δ_l) ≤ 2 ∑_{j ≥ 1} f(j)`. -/
theorem spacing (hf : Good f) (S : Finset ℝ) {l : ℝ} (hl : l ∈ S) (δ : ℝ → ℝ)
    (hδ : ∀ y ∈ S, 0 < δ y) (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) :
    ∑ k ∈ S.erase l, δ k / δ l * f (|k - l| / δ l) ≤ 2 * ∑' j : ℕ, f (j + 1) := by
  have hright := one_side hf S hl δ hδ hsep
  -- the reflected set
  have hleft := one_side hf (S.image (fun y => -y)) (l := -l) (mem_image_of_mem _ hl)
    (fun y => δ (-y)) (fun y hy => by
      obtain ⟨y', hy', rfl⟩ := mem_image.1 hy; simpa using hδ y' hy')
    (fun y hy z hz hzy => by
      obtain ⟨y', hy', rfl⟩ := mem_image.1 hy
      obtain ⟨z', hz', rfl⟩ := mem_image.1 hz
      have := hsep y' hy' z' hz' (fun h => hzy (by rw [h]))
      simpa [abs_sub_comm, neg_neg, show -y' - -z' = -(y' - z') by ring, abs_neg] using this)
  have hsplit : S.erase l = S.filter (l < ·) ∪ S.filter (· < l) := by
    ext y; simp only [mem_erase, mem_union, mem_filter]
    constructor
    · rintro ⟨hne, hy⟩; rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl ⟨hy, h⟩
    · rintro (⟨hy, h⟩ | ⟨hy, h⟩)
      · exact ⟨ne_of_gt h, hy⟩
      · exact ⟨ne_of_lt h, hy⟩
  have hdisj : Disjoint (S.filter (l < ·)) (S.filter (· < l)) := by
    rw [disjoint_filter]; intro y _ h1 h2; linarith
  rw [hsplit, sum_union hdisj]
  have hR : ∑ k ∈ S.filter (l < ·), δ k / δ l * f (|k - l| / δ l) =
      ∑ k ∈ S.filter (l < ·), δ k / δ l * f ((k - l) / δ l) :=
    sum_congr rfl fun k hk => by rw [abs_of_pos (by linarith [(mem_filter.1 hk).2])]
  have hL : ∑ k ∈ S.filter (· < l), δ k / δ l * f (|k - l| / δ l) =
      ∑ k ∈ (S.image (fun y => -y)).filter (-l < ·), δ (-k) / δ (- -l) * f ((k - -l) / δ (- -l)) := by
    rw [filter_image, sum_image fun x _ y _ h => neg_injective h]
    · refine sum_congr ?_ fun k hk => ?_
      · ext y; simp only [mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
      · rw [neg_neg, neg_neg, abs_of_neg (by linarith [(mem_filter.1 hk).2])]; ring_nf
  rw [hR, hL]; linarith

/-! ### `f(x) = x^{-p}` -/

theorem good_inv_pow {p : ℕ} (hp : 2 ≤ p) : Good fun x : ℝ => (x ^ p)⁻¹ where
  convex := by
    have h := (convexOn_zpow (𝕜 := ℝ) (-(p : ℤ))).subset (fun x (hx : (1 : ℝ) ≤ x) =>
      (show (0 : ℝ) < x by linarith)) (convex_Ici 1)
    refine h.congr fun x _ => ?_
    simp [zpow_neg, zpow_natCast]
  anti := fun x hx y hy hxy => by
    have hx0 : (0 : ℝ) < x := by have := Set.mem_Ici.1 hx; linarith
    exact inv_anti₀ (pow_pos hx0 p) (pow_le_pow_left₀ hx0.le hxy p)
  nonneg := fun x hx => by have : (0 : ℝ) < x := by linarith
                           positivity
  summable := by
    have h := (Real.summable_one_div_nat_pow.2 (by omega : 1 < p))
    have h' := (summable_nat_add_iff 1).2 h
    refine h'.congr fun j => ?_
    push_cast; rw [one_div]

/-- `∑_{k ≠ l} δ_k/|k − l|^p ≤ 2 (∑_{j≥1} j^{-p}) / δ_l^{p−1}`. -/
theorem spacing_pow (p : ℕ) (hp : 2 ≤ p) (S : Finset ℝ) {l : ℝ} (hl : l ∈ S) (δ : ℝ → ℝ)
    (hδ : ∀ y ∈ S, 0 < δ y) (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) :
    ∑ k ∈ S.erase l, δ k / |k - l| ^ p ≤
      2 * (∑' j : ℕ, (((j : ℝ) + 1) ^ p)⁻¹) / δ l ^ (p - 1) := by
  have h := spacing (good_inv_pow hp) S hl δ hδ hsep
  have hδl := hδ l hl
  have hδp : 0 < δ l ^ (p - 1) := pow_pos hδl _
  rw [le_div_iff₀ hδp, sum_mul]
  refine le_of_eq_of_le (sum_congr rfl fun k hk => ?_) h
  have hk : k ≠ l := (mem_erase.1 hk).1
  have hkl : 0 < |k - l| := abs_pos.2 (sub_ne_zero.2 hk)
  have hp1 : p = (p - 1) + 1 := by omega
  rw [div_pow, inv_div]
  field_simp
  conv_rhs => rw [hp1, pow_succ]
  ring

/-- `∑_{j ≥ 1} j^{-2} = π²/6`. -/
theorem tsum_inv_sq : ∑' j : ℕ, (((j : ℝ) + 1) ^ 2)⁻¹ = Real.pi ^ 2 / 6 := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  simp only [sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Nat.cast_add, Nat.cast_one, one_div, inv_zero, sub_zero] at h
  exact h.tsum_eq

/-- `∑_{j ≥ 1} j^{-4} = π⁴/90`. -/
theorem tsum_inv_pow_four : ∑' j : ℕ, (((j : ℝ) + 1) ^ 4)⁻¹ = Real.pi ^ 4 / 90 := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_four
  simp only [sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Nat.cast_add, Nat.cast_one, one_div, inv_zero, sub_zero] at h
  exact h.tsum_eq

/-- **Spacing lemma, `σ = 2`**: `∑_{k ≠ l} δ_k/(k − l)² ≤ π²/(3δ_l)`. -/
theorem spacing_two (S : Finset ℝ) {l : ℝ} (hl : l ∈ S) (δ : ℝ → ℝ)
    (hδ : ∀ y ∈ S, 0 < δ y) (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) :
    ∑ k ∈ S.erase l, δ k / (k - l) ^ 2 ≤ Real.pi ^ 2 / 3 / δ l := by
  have h := spacing_pow 2 le_rfl S hl δ hδ hsep
  rw [tsum_inv_sq] at h
  simp only [sq_abs] at h
  convert h using 1; ring

/-- **Spacing lemma, `σ = 4`**: `∑_{k ≠ l} δ_k/(k − l)⁴ ≤ π⁴/(45δ_l³)`. -/
theorem spacing_four (S : Finset ℝ) {l : ℝ} (hl : l ∈ S) (δ : ℝ → ℝ)
    (hδ : ∀ y ∈ S, 0 < δ y) (hsep : ∀ y ∈ S, ∀ z ∈ S, z ≠ y → δ y ≤ |y - z|) :
    ∑ k ∈ S.erase l, δ k / (k - l) ^ 4 ≤ Real.pi ^ 4 / 45 / δ l ^ 3 := by
  have h := spacing_pow 4 (by norm_num) S hl δ hδ hsep
  rw [tsum_inv_pow_four] at h
  have h4 : ∀ k : ℝ, |k - l| ^ 4 = (k - l) ^ 4 := fun k => by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
  simp only [h4] at h
  convert h using 1; ring

end TernaryGoldbach.Prelim.Shan
