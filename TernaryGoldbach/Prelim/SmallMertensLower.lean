import TernaryGoldbach.Prelim.LogWalk

/-!
# [B, (2.13)] for `3 ≤ N ≤ 10⁴`, and `∑_{m≤X} Λ(m)/m − ψ(X)/(X+1) − log(X+2)` at `X = 10⁴`

Checked by the kernel (`scripts/gen_mertens_lower.py`). With `D = 10³⁰`, the walk keeps lower and
upper bounds for `D log n` (`LogWalk.incr_bounds`), `D ∑_{m≤n} Λ(m)/m` and `D ψ(n)`. `Λ(n+1)` comes
from trial division (`isPr`) and the table `PPL` of the proper prime powers `≤ 10002`, whose
completeness the kernel checks (`PPL_complete`). At every `3 ≤ N ≤ 10⁴` the walk checks
`D log(N+1) ≤ D ∑_{m≤N} Λ(m)/m + K₃₂` with `K₃₂ ≤ D log(3/√2)`.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim.MertWalk

open TernaryGoldbach.Prelim.LogWalk

/-! ### `Λ` on `n ≤ 10002` -/

/-- The proper prime powers `m = p^k ≤ 10002`, as `(m, p, k)`. -/
def PPL : List (ℕ × ℕ × ℕ) := [(4, 2, 2), (8, 2, 3), (9, 3, 2), (16, 2, 4), (25, 5, 2), (27, 3, 3), (32, 2, 5), (49, 7, 2), (64, 2, 6), (81, 3, 4), (121, 11, 2), (125, 5, 3), (128, 2, 7), (169, 13, 2), (243, 3, 5), (256, 2, 8), (289, 17, 2), (343, 7, 3), (361, 19, 2), (512, 2, 9), (529, 23, 2), (625, 5, 4), (729, 3, 6), (841, 29, 2), (961, 31, 2), (1024, 2, 10), (1331, 11, 3), (1369, 37, 2), (1681, 41, 2), (1849, 43, 2), (2048, 2, 11), (2187, 3, 7), (2197, 13, 3), (2209, 47, 2), (2401, 7, 4), (2809, 53, 2), (3125, 5, 5), (3481, 59, 2), (3721, 61, 2), (4096, 2, 12), (4489, 67, 2), (4913, 17, 3), (5041, 71, 2), (5329, 73, 2), (6241, 79, 2), (6561, 3, 8), (6859, 19, 3), (6889, 83, 2), (7921, 89, 2), (8192, 2, 13), (9409, 97, 2)]

def ppFind : List (ℕ × ℕ × ℕ) → ℕ → Option (ℕ × ℕ)
  | [], _ => none
  | (m', p, k) :: l, m => if m' = m then some (p, k) else ppFind l m

theorem ppFind_mem : ∀ {l : List (ℕ × ℕ × ℕ)} {m p k : ℕ}, ppFind l m = some (p, k) → (m, p, k) ∈ l
  | [], _, _, _, h => by simp [ppFind] at h
  | (m', p', k') :: l, m, p, k, h => by
    unfold ppFind at h
    split_ifs at h with hm
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hm
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ppFind_mem h)

theorem PPL_ok : PPL.all (fun e => isPr e.2.1 && e.2.1 ^ e.2.2 == e.1 && decide (2 ≤ e.2.2) &&
    decide (e.1 ≤ 10002)) = true := by
  decide +kernel

theorem PPL_complete_b : (List.range 101).all (fun p => (List.range 14).all (fun k =>
    !(isPr p && decide (2 ≤ k) && decide (p ^ k ≤ 10002)) || ppFind PPL (p ^ k) == some (p, k))) = true := by
  decide +kernel

theorem PPL_complete {p k : ℕ} (hp : p < 101) (hk : k < 14) (h1 : isPr p = true) (h2 : 2 ≤ k)
    (h3 : p ^ k ≤ 10002) : ppFind PPL (p ^ k) = some (p, k) := by
  have := List.all_eq_true.1 (List.all_eq_true.1 PPL_complete_b p (List.mem_range.2 hp)) k
    (List.mem_range.2 hk)
  simp only [h1, decide_eq_true h2, decide_eq_true h3, Bool.and_self, Bool.not_true,
    Bool.false_or, beq_iff_eq] at this
  exact this

theorem vM_of_mem {m p k : ℕ} (h : (m, p, k) ∈ PPL) :
    Λ m = Real.log m / k ∧ 2 ≤ k := by
  have h1 := List.all_eq_true.1 PPL_ok _ h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨hp, hpk⟩, hk⟩, hm⟩ := h1
  have hp' : p.Prime := (isPr_iff (by
    have : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    omega)).1 hp
  subst hpk
  refine ⟨?_, hk⟩
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp', Nat.cast_pow, Real.log_pow]
  have : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp

theorem vM_zero {m : ℕ} (hm : m ≤ 10002) (h1 : isPr m = false) (h2 : ppFind PPL m = none) :
    Λ m = 0 := by
  by_contra hne
  obtain ⟨p, k, hp, hk, rfl⟩ :=
    (isPrimePow_nat_iff _).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hne)
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    rw [pow_one] at h1 hm
    have := (isPr_iff (by omega)).2 hp
    rw [h1] at this; exact Bool.false_ne_true this
  · have hp2 := hp.two_le
    have hpp : p * p ≤ 10002 := by
      have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk2
      nlinarith
    have hp101 : p < 101 := by nlinarith
    have hk14 : k < 14 := by
      by_contra hk'
      have : 2 ^ 14 ≤ p ^ k :=
        (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hp2 k)
      omega
    have := PPL_complete hp101 hk14 ((isPr_iff (by omega)).2 hp) hk2 hm
    rw [h2] at this; cases this

/-- Bounds `(lo, hi)` for `D Λ(m)` from bounds `(Lo, Hi)` for `D log m`. -/
def lamB (m Lo Hi : ℕ) : ℕ × ℕ :=
  if isPr m then (Lo, Hi) else
    match ppFind PPL m with
    | some (_, k) => (Lo / k, Hi / k + 1)
    | none => (0, 0)

theorem lamB_spec {m Lo Hi : ℕ} (hm : m ≤ 10002) (h1 : (Lo : ℝ) ≤ 10 ^ 30 * Real.log m)
    (h2 : 10 ^ 30 * Real.log m ≤ Hi) :
    ((lamB m Lo Hi).1 : ℝ) ≤ 10 ^ 30 * Λ m ∧ 10 ^ 30 * Λ m ≤ (lamB m Lo Hi).2 := by
  unfold lamB
  split_ifs with hp
  · rw [ArithmeticFunction.vonMangoldt_apply_prime ((isPr_iff (by omega)).1 hp)]
    exact ⟨h1, h2⟩
  · split
    · rename_i p k hf
      obtain ⟨hΛ, hk⟩ := vM_of_mem (ppFind_mem hf)
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      obtain ⟨a1, -⟩ := floor_div_bounds Lo k (by omega)
      obtain ⟨-, b2⟩ := floor_div_bounds Hi k (by omega)
      rw [hΛ]
      have e : (10 : ℝ) ^ 30 * (Real.log m / k) = 10 ^ 30 * Real.log m / k := by ring
      rw [e]
      constructor
      · exact a1.trans (div_le_div_of_nonneg_right h1 hk0.le)
      · push_cast
        exact (div_le_div_of_nonneg_right h2 hk0.le).trans b2
    · rename_i hf
      rw [vM_zero hm (by simpa using hp) hf]
      simp

/-! ### The walk -/

/-- `K₃₂ ≤ 10³⁰ log(3/√2)`. -/
def K32 : ℕ := 752038698258164381699250953989

theorem incrLo_two : incrLo 2 = 405465108108164381699250953989 := by decide +kernel

theorem K32_le : (K32 : ℝ) ≤ 10 ^ 30 * Real.log (3 / √2) := by
  have h1 := (incr_bounds (n := 2) (by norm_num)).1
  rw [incrLo_two] at h1
  have h2 := Real.log_two_gt_d9
  have e : Real.log (3 / √2) = Real.log (1 + ((2 : ℕ) : ℝ)⁻¹) + Real.log 2 / 2 := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_sqrt (by norm_num)]
    have : Real.log 3 = Real.log (1 + ((2 : ℕ) : ℝ)⁻¹) + Real.log 2 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    rw [this]; ring
  rw [e]
  unfold K32
  push_cast at h1 ⊢
  linarith

structure MS where
  Llo : ℕ
  Lhi : ℕ
  Slo : ℕ
  Shi : ℕ
  Plo : ℕ
  Phi : ℕ
deriving DecidableEq

def mstep (n : ℕ) (s : MS) : MS :=
  let Llo := s.Llo + incrLo n
  let Lhi := s.Lhi + incrHi n
  let b := lamB (n + 1) Llo Lhi
  { Llo := Llo, Lhi := Lhi,
    Slo := s.Slo + b.1 / (n + 1), Shi := s.Shi + b.2 / (n + 1) + 1,
    Plo := s.Plo + b.1, Phi := s.Phi + b.2 }

/-- The walk, checking (2.13) at each `n ≥ 3`. -/
def walkM : ℕ → ℕ → MS → Option MS
  | _, 0, s => some s
  | n, len + 1, s =>
    if s.Llo + s.Lhi + s.Slo + s.Shi + s.Plo + s.Phi < 10 ^ 200 ∧
        (n < 3 ∨ s.Lhi + incrHi n ≤ s.Slo + K32) then
      walkM (n + 1) len (mstep n s) else none

noncomputable def Sm (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, (Λ m : ℝ) / m
noncomputable def Pm (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, (Λ m : ℝ)

/-- [B, (2.13)] at `N`. -/
def Ok (N : ℕ) : Prop := Real.log ((N : ℝ) + 1) - Real.log (3 / √2) ≤ Sm N

def Inv (n : ℕ) (s : MS) : Prop :=
  (s.Llo : ℝ) ≤ 10 ^ 30 * Real.log n ∧ 10 ^ 30 * Real.log n ≤ s.Lhi ∧
  (s.Slo : ℝ) ≤ 10 ^ 30 * Sm n ∧ 10 ^ 30 * Sm n ≤ s.Shi ∧
  (s.Plo : ℝ) ≤ 10 ^ 30 * Pm n ∧ 10 ^ 30 * Pm n ≤ s.Phi ∧
  ∀ N, 3 ≤ N → N < n → Ok N

theorem Inv_step {n : ℕ} (hn : 1 ≤ n) (hn' : n + 1 ≤ 10002) {s : MS} (h : Inv n s)
    (hchk : n < 3 ∨ s.Lhi + incrHi n ≤ s.Slo + K32) : Inv (n + 1) (mstep n s) := by
  obtain ⟨l1, l2, h1, h2, p1, p2, hok⟩ := h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i1, i2⟩ := incr_bounds hn
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
  set Lo := s.Llo + incrLo n with hLo
  set Hi := s.Lhi + incrHi n with hHi
  have hL1 : (Lo : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [hlog, hLo]; push_cast; linarith
  have hL2 : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ (Hi : ℝ) := by
    rw [hlog, hHi]; push_cast; linarith
  obtain ⟨b1, b2⟩ := lamB_spec hn' hL1 hL2
  set b := lamB (n + 1) Lo Hi with hb
  have hS : Sm (n + 1) = Sm n + Λ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
    rw [Sm, Sm, sum_Icc_succ_top (by omega)]
  have hP : Pm (n + 1) = Pm n + Λ (n + 1) := by
    rw [Pm, Pm, sum_Icc_succ_top (by omega)]
  have hm0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨f1, -⟩ := floor_div_bounds b.1 (n + 1) (by omega)
  obtain ⟨-, f2⟩ := floor_div_bounds b.2 (n + 1) (by omega)
  have e : (10 : ℝ) ^ 30 * (Sm n + Λ (n + 1) / ((n + 1 : ℕ) : ℝ)) =
      10 ^ 30 * Sm n + 10 ^ 30 * Λ (n + 1) / ((n + 1 : ℕ) : ℝ) := by ring
  have d1 : (b.1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 10 ^ 30 * Λ (n + 1) / ((n + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right b1 hm0.le
  have d2 : 10 ^ 30 * Λ (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ (b.2 : ℝ) / ((n + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right b2 hm0.le
  refine ⟨hL1, hL2, ?_, ?_, ?_, ?_, ?_⟩
  · show ((s.Slo + b.1 / (n + 1) : ℕ) : ℝ) ≤ _
    rw [hS, e, Nat.cast_add s.Slo]; linarith
  · show _ ≤ ((s.Shi + b.2 / (n + 1) + 1 : ℕ) : ℝ)
    rw [hS, e, Nat.cast_add (s.Shi + _) 1, Nat.cast_add s.Shi, Nat.cast_one]
    linarith
  · show ((s.Plo + b.1 : ℕ) : ℝ) ≤ _
    rw [hP, Nat.cast_add]; linarith
  · show _ ≤ ((s.Phi + b.2 : ℕ) : ℝ)
    rw [hP, Nat.cast_add]; linarith
  · intro N hN3 hNn
    rcases Nat.lt_or_ge N n with hlt | hge
    · exact hok N hN3 hlt
    · have hNe : N = n := by omega
      subst hNe
      rcases hchk with h3 | hc
      · omega
      · have hK := K32_le
        have hc' : (Hi : ℝ) ≤ (s.Slo : ℝ) + (K32 : ℝ) := by rw [hHi]; exact_mod_cast hc
        unfold Ok
        have e2 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        rw [← e2]
        nlinarith

theorem walkM_spec : ∀ (len n : ℕ) (s s' : MS), 1 ≤ n → n + len ≤ 10002 → Inv n s →
    walkM n len s = some s' → Inv (n + len) s' := by
  intro len
  induction len with
  | zero => intro n s s' _ _ h hw; simp only [walkM, Option.some.injEq] at hw; subst hw; simpa using h
  | succ len ih =>
    intro n s s' hn hl h hw
    rw [walkM] at hw
    split_ifs at hw with hc
    rw [show n + (len + 1) = n + 1 + len by ring]
    exact ih (n + 1) _ _ (by omega) (by omega) (Inv_step hn (by omega) h hc.2) hw

theorem Inv_one : Inv 1 ⟨0, 0, 0, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp [Sm]
  · simp [Sm]
  · simp [Pm]
  · simp [Pm]
  · intro N h3 h1; omega

theorem wk_1 : walkM 1 999 ⟨0, 0, 0, 0, 0, 0⟩ = some ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 6328751439663701156583023157498, 6328751439664056586956138765519, 996680912247156642253773724806936, 996680912247181667417464542895705⟩ := by decide +kernel
theorem wk_2 : walkM 1000 1000 ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 6328751439663701156583023157498, 6328751439664056586956138765519, 996680912247156642253773724806936, 996680912247181667417464542895705⟩ = some ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 7021871099532535974059735172738, 7021871099532904951149108939388, 1994451579978044801951795348274352, 1994451579978089220798516857754149⟩ := by decide +kernel
theorem wk_3 : walkM 2000 1000 ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 7021871099532535974059735172738, 7021871099532904951149108939388, 1994451579978044801951795348274352, 1994451579978089220798516857754149⟩ = some ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 7430419076770472324268411343838, 7430419076770848718560798028594, 3001094650045204119243658439914020, 3001094650045266782282185725238601⟩ := by decide +kernel
theorem wk_4 : walkM 3000 1000 ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 7430419076770472324268411343838, 7430419076770848718560798028594, 3001094650045204119243658439914020, 3001094650045266782282185725238601⟩ = some ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 7714661745821754309243046735662, 7714661745822135642927707327293, 3989678686968181797387321606889622, 3989678686968261625818132146084076⟩ := by decide +kernel
theorem wk_5 : walkM 4000 1000 ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 7714661745821754309243046735662, 7714661745822135642927707327293, 3989678686968181797387321606889622, 3989678686968261625818132146084076⟩ = some ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 7939925533972762325799802574038, 7939925533973147455870640158805, 4997959692237835723214400668158651, 4997959692237932535280727987177676⟩ := by decide +kernel
theorem wk_6 : walkM 5000 1000 ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 7939925533972762325799802574038, 7939925533973147455870640158805, 4997959692237835723214400668158651, 4997959692237932535280727987177676⟩ = some ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 8120581035057245645854328810430, 8120581035057633748488619101315, 5988114937097214731009734924780468, 5988114937097327830370720449713085⟩ := by decide +kernel
theorem wk_7 : walkM 6000 1000 ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 8120581035057245645854328810430, 8120581035057633748488619101315, 5988114937097214731009734924780468, 5988114937097327830370720449713085⟩ = some ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 8280779204946030482156989417016, 8280779204946421169802667782808, 7028069849520908904967332825859590, 7028069849521038781422055047786603⟩ := by decide +kernel
theorem wk_8 : walkM 7000 1000 ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 8280779204946030482156989417016, 8280779204946421169802667782808, 7028069849520908904967332825859590, 7028069849521038781422055047786603⟩ = some ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 8408706183284699847273431584248, 8408706183285092565745214416528, 7987287840744381140151313808315402, 7987287840744526241685825225541043⟩ := by decide +kernel
theorem wk_9 : walkM 8000 1000 ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 8408706183284699847273431584248, 8408706183285092565745214416528, 7987287840744381140151313808315402, 7987287840744526241685825225541043⟩ = some ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 8525965716658133546919647549250, 8525965716658528101195878409519, 8983205595785325312195521769869841, 8983205595785486003775956865421645⟩ := by decide +kernel
theorem wk_10 : walkM 9000 1000 ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 8525965716658133546919647549250, 8525965716658528101195878409519, 8983205595785325312195521769869841, 8983205595785486003775956865421645⟩ = some ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 8634639307925128720361629764850, 8634639307925524955577507951153, 10013396693262983521053440538486993, 10013396693263160145856910841316409⟩ := by decide +kernel
theorem wk_11 : walkM 10000 2 ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 8634639307925128720361629764850, 8634639307925524955577507951153, 10013396693262983521053440538486993, 10013396693263160145856910841316409⟩ = some ⟨9210540351978743748309293324591, 9210540351978885376958495173751, 8634639307925128720361629764850, 8634639307925524955577507951155, 10013396693262983521053440538486993, 10013396693263160145856910841316409⟩ := by decide +kernel

theorem inv_1 : Inv 1 ⟨0, 0, 0, 0, 0, 0⟩ := Inv_one
theorem inv_1000 : Inv 1000 ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 6328751439663701156583023157498, 6328751439664056586956138765519, 996680912247156642253773724806936, 996680912247181667417464542895705⟩ := walkM_spec 999 1 _ _ (by norm_num) (by norm_num) inv_1 wk_1
theorem inv_2000 : Inv 2000 ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 7021871099532535974059735172738, 7021871099532904951149108939388, 1994451579978044801951795348274352, 1994451579978089220798516857754149⟩ := walkM_spec 1000 1000 _ _ (by norm_num) (by norm_num) inv_1000 wk_2
theorem inv_3000 : Inv 3000 ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 7430419076770472324268411343838, 7430419076770848718560798028594, 3001094650045204119243658439914020, 3001094650045266782282185725238601⟩ := walkM_spec 1000 2000 _ _ (by norm_num) (by norm_num) inv_2000 wk_3
theorem inv_4000 : Inv 4000 ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 7714661745821754309243046735662, 7714661745822135642927707327293, 3989678686968181797387321606889622, 3989678686968261625818132146084076⟩ := walkM_spec 1000 3000 _ _ (by norm_num) (by norm_num) inv_3000 wk_4
theorem inv_5000 : Inv 5000 ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 7939925533972762325799802574038, 7939925533973147455870640158805, 4997959692237835723214400668158651, 4997959692237932535280727987177676⟩ := walkM_spec 1000 4000 _ _ (by norm_num) (by norm_num) inv_4000 wk_5
theorem inv_6000 : Inv 6000 ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 8120581035057245645854328810430, 8120581035057633748488619101315, 5988114937097214731009734924780468, 5988114937097327830370720449713085⟩ := walkM_spec 1000 5000 _ _ (by norm_num) (by norm_num) inv_5000 wk_6
theorem inv_7000 : Inv 7000 ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 8280779204946030482156989417016, 8280779204946421169802667782808, 7028069849520908904967332825859590, 7028069849521038781422055047786603⟩ := walkM_spec 1000 6000 _ _ (by norm_num) (by norm_num) inv_6000 wk_7
theorem inv_8000 : Inv 8000 ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 8408706183284699847273431584248, 8408706183285092565745214416528, 7987287840744381140151313808315402, 7987287840744526241685825225541043⟩ := walkM_spec 1000 7000 _ _ (by norm_num) (by norm_num) inv_7000 wk_8
theorem inv_9000 : Inv 9000 ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 8525965716658133546919647549250, 8525965716658528101195878409519, 8983205595785325312195521769869841, 8983205595785486003775956865421645⟩ := walkM_spec 1000 8000 _ _ (by norm_num) (by norm_num) inv_8000 wk_9
theorem inv_10000 : Inv 10000 ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 8634639307925128720361629764850, 8634639307925524955577507951153, 10013396693262983521053440538486993, 10013396693263160145856910841316409⟩ := walkM_spec 1000 9000 _ _ (by norm_num) (by norm_num) inv_9000 wk_10
theorem inv_10002 : Inv 10002 ⟨9210540351978743748309293324591, 9210540351978885376958495173751, 8634639307925128720361629764850, 8634639307925524955577507951155, 10013396693262983521053440538486993, 10013396693263160145856910841316409⟩ := walkM_spec 2 10000 _ _ (by norm_num) (by norm_num) inv_10000 wk_11

/-- **[B, (2.13)] for `3 ≤ N ≤ 10⁴`**, checked by the kernel. -/
theorem mertens_lower_le {N : ℕ} (h1 : 3 ≤ N) (h2 : N ≤ 10 ^ 4) :
    Real.log (N + 1) - Real.log (3 / √2) ≤ ∑ m ∈ Icc 1 N, (Λ m : ℝ) / m :=
  inv_10002.2.2.2.2.2.2 N h1 (by omega)

/-- `∑_{m≤X} Λ(m)/m − ψ(X)/(X+1) − log(X+2) ≥ −1.578` at `X = 10⁴` (value `−1.57714`). -/
theorem mertens_point_le :
    -1.578 ≤ ∑ m ∈ Icc 1 (10 ^ 4), (Λ m : ℝ) / m -
      (∑ m ∈ Icc 1 (10 ^ 4), (Λ m : ℝ)) / (10 ^ 4 + 1) - Real.log (10 ^ 4 + 2) := by
  obtain ⟨-, -, s1, -, -, p2, -⟩ := inv_10000
  obtain ⟨-, l2, -⟩ := inv_10002
  have eS : ∑ m ∈ Icc 1 (10 ^ 4), (Λ m : ℝ) / m = Sm 10000 := rfl
  have eP : ∑ m ∈ Icc 1 (10 ^ 4), (Λ m : ℝ) = Pm 10000 := rfl
  have eL : Real.log (10 ^ 4 + 2) = Real.log ((10002 : ℕ) : ℝ) := by norm_num
  rw [eS, eP, eL]
  dsimp only at s1 p2 l2
  push_cast at s1 p2 l2 ⊢
  have : Pm 10000 / 10001 ≤ (Pm 10000 * 10 ^ 30) / 10001 / 10 ^ 30 := by
    rw [mul_div_assoc, mul_comm, mul_div_assoc]; field_simp; rfl
  linarith

end TernaryGoldbach.Prelim.MertWalk
