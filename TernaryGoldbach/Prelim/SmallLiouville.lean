import TernaryGoldbach.Prelim.SmallPsi
import TernaryGoldbach.Prelim.Liouville

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# `|∑_{n ≤ k} λ(n)/n| log(k + 1) ≤ 0.99` for `1 ≤ k ≤ 10⁵`, checked by the kernel

`λ(n) = (−1)^{Ω(n)}`, with `Ω(n)` computed by trial division (`omTD`, proved correct). The kernel walks
`n = 1, …, 10⁵` keeping `P(k) = ∑_{n ≤ k, λ(n) = 1} ⌊10¹²/n⌋` and `Q(k)` (the same for `λ(n) = −1`),
so that `|10¹² ∑_{n ≤ k} λ(n)/n − (P(k) − Q(k))| ≤ k`, and checks
`100 (|P(k) − Q(k)| + k) u ≤ 99·10¹⁸` at every `k`, where `log(k + 1) < u/10⁶` on the chunk (`chkStep`).
The state `(P, Q)` is certified at the 105 chunk boundaries.
-/

open Finset ArithmeticFunction

namespace TernaryGoldbach.Prelim.SmallLiou

open TernaryGoldbach.Prelim (lam)
open TernaryGoldbach.Prelim.Small (chkStep log_lt_of_chk)

/-! ### `Ω` by trial division -/

/-- `Ω(m)` by trial division from `d` (`d = 2` or odd), or `none` when out of fuel. -/
def omTD : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | f + 1, m, d =>
    if m < 2 then some 0
    else if m < d * d then some 1
    else if m % d = 0 then (omTD f (m / d) d).map (· + 1)
    else omTD f m (if d = 2 then 3 else d + 2)

theorem omTD_spec : ∀ (f m d k : ℕ), 2 ≤ d → (d = 2 ∨ d % 2 = 1) →
    (∀ p, p.Prime → p ∣ m → d ≤ p) → omTD f m d = some k → cardFactors m = k := by
  intro f
  induction f with
  | zero => intro m d k _ _ _ h; simp [omTD] at h
  | succ f ih =>
    intro m d k hd hodd hinv h
    rw [omTD] at h
    split_ifs at h with h1 h2 h3 h4
    · cases h
      interval_cases m <;> simp
    · cases h
      have hm2 : 2 ≤ m := by omega
      have hp : m.Prime := by
        by_contra hnp
        have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
        have hle := hinv _ hmf (Nat.minFac_dvd m)
        have hsq := Nat.minFac_sq_le_self (by omega) hnp
        have : d * d ≤ m.minFac ^ 2 := by rw [sq]; exact Nat.mul_le_mul hle hle
        omega
      exact cardFactors_apply_prime hp
    · obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.1 h
      have hdm : d ∣ m := Nat.dvd_of_mod_eq_zero h3
      have hdp : d.Prime := by
        rw [Nat.prime_def_minFac]
        refine ⟨hd, ?_⟩
        have hmf := Nat.minFac_prime (show d ≠ 1 by omega)
        have h1' := hinv _ hmf ((Nat.minFac_dvd d).trans hdm)
        have h2' := Nat.minFac_le (show 0 < d by omega)
        omega
      have hq : m / d ≠ 0 := by
        have := Nat.div_pos (Nat.le_of_dvd (by omega) hdm) (by omega : 0 < d); omega
      have ih' := ih (m / d) d k' hd hodd (fun p hp hpd => hinv p hp (hpd.trans (Nat.div_dvd_of_dvd hdm))) hk'
      rw [← Nat.mul_div_cancel' hdm, cardFactors_mul (by omega) hq, cardFactors_apply_prime hdp, ih']
      ring
    · refine ih m 3 k (by norm_num) (by norm_num) ?_ h
      intro p hp hpm
      have hdp := hinv p hp hpm
      have hne : p ≠ d := fun e => h3 (Nat.mod_eq_zero_of_dvd (e ▸ hpm))
      omega
    · have h5 : d % 2 = 1 := by
        rcases hodd with h5 | h5
        · exact absurd h5 h4
        · exact h5
      refine ih m (d + 2) k (by omega) (Or.inr (by omega)) ?_ h
      intro p hp hpm
      have hdp := hinv p hp hpm
      have hne : p ≠ d := fun e => h3 (Nat.mod_eq_zero_of_dvd (e ▸ hpm))
      by_contra hlt
      have hp1 : p = d + 1 := by omega
      have hev : 2 ∣ p := by omega
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hev
      omega

/-- `λ(n) = 1` (`true`) or `−1` (`false`), by trial division. -/
def lamB (n : ℕ) : Option Bool := (omTD (n + 1) n 2).map (fun k => k % 2 == 0)

theorem lamB_spec {n : ℕ} (hn : 1 ≤ n) {b : Bool} (h : lamB n = some b) :
    lam n = if b then 1 else -1 := by
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
  have hΩ := omTD_spec _ n 2 k le_rfl (Or.inl rfl) (fun p hp _ => hp.two_le) hk
  have e : lam n = ((-1 : ℤ) ^ k : ℤ) := by
    rw [lam, intCoe_apply, liouville_apply (by omega), hΩ]
  rw [e]
  rcases Nat.even_or_odd k with he | ho
  · have : k % 2 = 0 := Nat.even_iff.1 he
    simp [this, he.neg_one_pow]
  · have : k % 2 = 1 := Nat.odd_iff.1 ho
    simp [this, ho.neg_one_pow]

theorem lam_eq_or {n : ℕ} (hn : 1 ≤ n) : lam n = 1 ∨ lam n = -1 := by
  rw [lam, intCoe_apply, liouville_apply (by omega)]
  rcases neg_one_pow_eq_or ℤ (cardFactors n) with h | h <;> simp [h]

/-! ### The walk -/

/-- `P(k) = ∑_{n ≤ k, λ(n) = 1} ⌊10¹²/n⌋`. -/
noncomputable def Pt (k : ℕ) : ℕ := ∑ m ∈ Icc 1 k, if lam m = 1 then 1000000000000 / m else 0

/-- `Q(k) = ∑_{n ≤ k, λ(n) ≠ 1} ⌊10¹²/n⌋`. -/
noncomputable def Qt (k : ℕ) : ℕ := ∑ m ∈ Icc 1 k, if lam m = 1 then 0 else 1000000000000 / m

theorem Pt_succ (k : ℕ) : Pt (k + 1) = Pt k + if lam (k + 1) = 1 then 1000000000000 / (k + 1) else 0 := by
  rw [Pt, Pt, sum_Icc_succ_top (by omega)]

theorem Qt_succ (k : ℕ) : Qt (k + 1) = Qt k + if lam (k + 1) = 1 then 0 else 1000000000000 / (k + 1) := by
  rw [Qt, Qt, sum_Icc_succ_top (by omega)]

/-- Processes `n + 1, …, n + len` from the state `(P, Q)` at `n`, checking each `k`. -/
def walk (u : ℕ) : ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | _, P, Q, 0 => some (P, Q)
  | n, P, Q, len + 1 =>
    match lamB (n + 1) with
    | none => none
    | some b =>
      if 100 * (((if b then P + 1000000000000 / (n + 1) else P) - (if b then Q else Q + 1000000000000 / (n + 1))) +
          ((if b then Q else Q + 1000000000000 / (n + 1)) - (if b then P + 1000000000000 / (n + 1) else P)) +
          (n + 1)) * u ≤ 99 * 10 ^ 18 then
        walk u (n + 1) (if b then P + 1000000000000 / (n + 1) else P)
          (if b then Q else Q + 1000000000000 / (n + 1)) len
      else none

theorem walk_spec (u : ℕ) : ∀ (len n : ℕ) (r : ℕ × ℕ), walk u n (Pt n) (Qt n) len = some r →
    r = (Pt (n + len), Qt (n + len)) ∧ ∀ k, n < k → k ≤ n + len →
      100 * ((Pt k - Qt k) + (Qt k - Pt k) + k) * u ≤ 99 * 10 ^ 18 := by
  intro len
  induction len with
  | zero => intro n r h; simp only [walk, Option.some.injEq] at h; exact ⟨h.symm, fun k h1 h2 => by omega⟩
  | succ len ih =>
    intro n r h
    rw [walk] at h
    rcases hb : lamB (n + 1) with _ | b
    · rw [hb] at h; simp at h
    rw [hb] at h
    simp only at h
    have hl := lamB_spec (by omega) hb
    have hP : Pt (n + 1) = if b then Pt n + 1000000000000 / (n + 1) else Pt n := by
      rw [Pt_succ]; cases b <;> simp [hl] <;> norm_num
    have hQ : Qt (n + 1) = if b then Qt n else Qt n + 1000000000000 / (n + 1) := by
      rw [Qt_succ]; cases b <;> simp [hl] <;> norm_num
    rw [← hP, ← hQ] at h
    split_ifs at h with hc
    obtain ⟨h1, h2⟩ := ih (n + 1) r h
    refine ⟨by rw [h1, show n + 1 + len = n + (len + 1) by omega], fun k hk1 hk2 => ?_⟩
    rcases Nat.eq_or_lt_of_le (show n + 1 ≤ k by omega) with e | e
    · rw [← e]; exact hc
    · exact h2 k e (by omega)

/-- `|10¹² ∑_{n ≤ k} λ(n)/n − (P(k) − Q(k))| ≤ k`. -/
theorem sum_approx (k : ℕ) :
    |1000000000000 * ∑ n ∈ Icc 1 k, lam n / n - ((Pt k : ℝ) - Qt k)| ≤ (k : ℝ) := by
  induction k with
  | zero => simp [Pt, Qt]
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega), Pt_succ, Qt_succ]
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hf1 : (((1000000000000 / (k + 1) : ℕ) : ℝ)) ≤ 1000000000000 / ((k : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := 1000000000000) (n := k + 1)
      push_cast at this; exact this
    have hf2 : 1000000000000 / ((k : ℝ) + 1) < (((1000000000000 / (k + 1) : ℕ) : ℝ)) + 1 := by
      rw [div_lt_iff₀ hk]
      have h2 := Nat.lt_mul_div_succ 1000000000000 (show 0 < k + 1 by omega)
      have := (Nat.cast_lt (α := ℝ)).2 h2
      push_cast at this
      linarith
    rcases lam_eq_or (show 1 ≤ k + 1 by omega) with hl | hl
    · rw [hl, if_pos rfl, if_pos rfl]
      rw [abs_le] at ih ⊢
      push_cast
      have e : (1000000000000 : ℝ) * (1 / ((k : ℝ) + 1)) = 1000000000000 / ((k : ℝ) + 1) := by ring
      constructor <;> linarith [ih.1, ih.2]
    · rw [hl, if_neg (by norm_num), if_neg (by norm_num)]
      rw [abs_le] at ih ⊢
      push_cast
      have e : (1000000000000 : ℝ) * (-1 / ((k : ℝ) + 1)) = -(1000000000000 / ((k : ℝ) + 1)) := by ring
      constructor <;> linarith [ih.1, ih.2]

theorem natAbs_cast (a b : ℕ) : (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (by
      have : (a : ℝ) ≤ b := by exact_mod_cast h
      linarith)]; ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (by
      have : (b : ℝ) ≤ a := by exact_mod_cast h
      linarith)]

/-- The bound at `k` from the check at `k`. -/
theorem bound_of_chk {k u B : ℕ} (hk : 1 ≤ k) (hkB : k + 1 ≤ B)
    (hc : 100 * ((Pt k - Qt k) + (Qt k - Pt k) + k) * u ≤ 99 * 10 ^ 18)
    (hu : chkStep u (10 ^ 6) 1 B = true) :
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 := by
  have hlB := log_lt_of_chk (by norm_num) (by omega) hu
  push_cast at hlB
  have hl : Real.log ((k : ℝ) + 1) ≤ Real.log B :=
    Real.log_le_log (by positivity) (by exact_mod_cast hkB)
  have hl0 : 0 ≤ Real.log ((k : ℝ) + 1) := by
    have h : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact Real.log_nonneg (by linarith)
  have ha := sum_approx k
  have hc' : (100 : ℝ) * ((((Pt k - Qt k) + (Qt k - Pt k) : ℕ) : ℝ) + k) * u ≤ 99 * 10 ^ 18 := by
    exact_mod_cast hc
  rw [natAbs_cast] at hc'
  set S := ∑ n ∈ Icc 1 k, lam n / n
  have hS : |S| * 10 ^ 12 ≤ |(Pt k : ℝ) - Qt k| + k := by
    have := abs_sub_abs_le_abs_sub (1000000000000 * S) ((Pt k : ℝ) - Qt k)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1000000000000)] at this
    linarith
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have h1 : |S| * Real.log ((k : ℝ) + 1) ≤ |S| * ((u : ℝ) / 10 ^ 6) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h2 : |S| * ((u : ℝ) / 10 ^ 6) ≤ (|(Pt k : ℝ) - Qt k| + k) / 10 ^ 12 * ((u : ℝ) / 10 ^ 6) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [le_div_iff₀ (by norm_num)]; exact hS
  have h3 : (|(Pt k : ℝ) - Qt k| + k) / 10 ^ 12 * ((u : ℝ) / 10 ^ 6) ≤ 0.99 := by
    have e : (|(Pt k : ℝ) - Qt k| + k) / 10 ^ 12 * ((u : ℝ) / 10 ^ 6) =
        100 * (|(Pt k : ℝ) - Qt k| + k) * u / (100 * 10 ^ 18) := by ring
    rw [e, div_le_iff₀ (by norm_num)]; linarith
  push_cast
  linarith

/-- One chunk: from the state at `n₀` to the state at `n₁`, with the check on `(n₀, n₁]`. -/
theorem chunk_ok {n₀ n₁ P₀ Q₀ P₁ Q₁ u : ℕ} (hw : walk u n₀ P₀ Q₀ (n₁ - n₀) = some (P₁, Q₁))
    (hu : chkStep u (10 ^ 6) 1 (n₁ + 1) = true) (h01 : n₀ ≤ n₁) (hs : Pt n₀ = P₀ ∧ Qt n₀ = Q₀) :
    (Pt n₁ = P₁ ∧ Qt n₁ = Q₁) ∧ ∀ k, n₀ < k → k ≤ n₁ →
      |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 := by
  rw [← hs.1, ← hs.2] at hw
  obtain ⟨h1, h2⟩ := walk_spec u _ _ _ hw
  rw [show n₀ + (n₁ - n₀) = n₁ by omega] at h1 h2
  simp only [Prod.mk.injEq] at h1
  exact ⟨⟨h1.1.symm, h1.2.symm⟩, fun k hk1 hk2 =>
    bound_of_chk (by omega) (by omega) (h2 k hk1 hk2) hu⟩

theorem w_0 : walk 693148 0 0 0 1 = some (1000000000000, 0) := by decide +kernel
theorem u_0 : chkStep 693148 (10 ^ 6) 1 2 = true := by decide +kernel
theorem w_1 : walk 1945911 1 1000000000000 0 5 = some (1416666666666, 1033333333333) := by decide +kernel
theorem u_1 : chkStep 1945911 (10 ^ 6) 1 7 = true := by decide +kernel
theorem w_2 : walk 2995733 6 1416666666666 1033333333333 13 = some (1828373015871, 1719366641268) := by decide +kernel
theorem u_2 : chkStep 2995733 (10 ^ 6) 1 20 = true := by decide +kernel
theorem w_3 : walk 4317489 19 1828373015871 1719366641268 55 = some (2477505067336, 2410517229857) := by decide +kernel
theorem u_3 : chkStep 4317489 (10 ^ 6) 1 75 = true := by decide +kernel
theorem w_4 : walk 6980077 74 2477505067336 2410517229857 1000 = some (3786133200820, 3770693215793) := by decide +kernel
theorem u_4 : chkStep 6980077 (10 ^ 6) 1 1075 = true := by decide +kernel
theorem w_5 : walk 7637717 1074 3786133200820 3770693215793 1000 = some (4116684851431, 4098006261995) := by decide +kernel
theorem u_5 : chkStep 7637717 (10 ^ 6) 1 2075 = true := by decide +kernel
theorem w_6 : walk 8031061 2074 4116684851431 4098006261995 1000 = some (4309788996379, 4298324236915) := by decide +kernel
theorem u_6 : chkStep 8031061 (10 ^ 6) 1 3075 = true := by decide +kernel
theorem w_7 : walk 8312627 3074 4309788996379 4298324236915 1000 = some (4448958589432, 4440760394837) := by decide +kernel
theorem u_7 : chkStep 8312627 (10 ^ 6) 1 4075 = true := by decide +kernel
theorem w_8 : walk 8532083 4074 4448958589432 4440760394837 1000 = some (4559288245479, 4549910695545) := by decide +kernel
theorem u_8 : chkStep 8532083 (10 ^ 6) 1 5075 = true := by decide +kernel
theorem w_9 : walk 8711938 5074 4559288245479 4549910695545 1000 = some (4649112566764, 4639958056690) := by decide +kernel
theorem u_9 : chkStep 8711938 (10 ^ 6) 1 6075 = true := by decide +kernel
theorem w_10 : walk 8864324 6074 4649112566764 4639958056690 1000 = some (4722345730546, 4719121980452) := by decide +kernel
theorem u_10 : chkStep 8864324 (10 ^ 6) 1 7075 = true := by decide +kernel
theorem w_11 : walk 8996529 7074 4722345730546 4719121980452 1000 = some (4792201999036, 4781479889320) := by decide +kernel
theorem u_11 : chkStep 8996529 (10 ^ 6) 1 8075 = true := by decide +kernel
theorem w_12 : walk 9113280 8074 4792201999036 4781479889320 1000 = some (4850174940652, 4840264281625) := by decide +kernel
theorem u_12 : chkStep 9113280 (10 ^ 6) 1 9075 = true := by decide +kernel
theorem w_13 : walk 9217813 9074 4850174940652 4840264281625 1000 = some (4899928051489, 4895050366783) := by decide +kernel
theorem u_13 : chkStep 9217813 (10 ^ 6) 1 10075 = true := by decide +kernel
theorem w_14 : walk 9312447 10074 4899928051489 4895050366783 1000 = some (4947131367342, 4942484739746) := by decide +kernel
theorem u_14 : chkStep 9312447 (10 ^ 6) 1 11075 = true := by decide +kernel
theorem w_15 : walk 9398893 11074 4947131367342 4942484739746 1000 = some (4991736503101, 4984330226063) := by decide +kernel
theorem u_15 : chkStep 9398893 (10 ^ 6) 1 12075 = true := by decide +kernel
theorem w_16 : walk 9478458 12074 4991736503101 4984330226063 1000 = some (5031701251877, 5023933454246) := by decide +kernel
theorem u_16 : chkStep 9478458 (10 ^ 6) 1 13075 = true := by decide +kernel
theorem w_17 : walk 9552156 13074 5031701251877 5023933454246 1000 = some (5068690747338, 5060644839353) := by decide +kernel
theorem u_17 : chkStep 9552156 (10 ^ 6) 1 14075 = true := by decide +kernel
theorem w_18 : walk 9620794 14074 5068690747338 5060644839353 1000 = some (5101973604045, 5096001907285) := by decide +kernel
theorem u_18 : chkStep 9620794 (10 ^ 6) 1 15075 = true := by decide +kernel
theorem w_19 : walk 9685022 15074 5101973604045 5096001907285 1000 = some (5132156739422, 5130048362262) := by decide +kernel
theorem u_19 : chkStep 9685022 (10 ^ 6) 1 16075 = true := by decide +kernel
theorem w_20 : walk 9745372 16074 5132156739422 5130048362262 1000 = some (5162575144609, 5159981913587) := by decide +kernel
theorem u_20 : chkStep 9745372 (10 ^ 6) 1 17075 = true := by decide +kernel
theorem w_21 : walk 9802286 17074 5162575144609 5159981913587 1000 = some (5191559891520, 5187913148863) := by decide +kernel
theorem u_21 : chkStep 9802286 (10 ^ 6) 1 18075 = true := by decide +kernel
theorem w_22 : walk 9856135 18074 5191559891520 5187913148863 1000 = some (5220186363161, 5213136936066) := by decide +kernel
theorem u_22 : chkStep 9856135 (10 ^ 6) 1 19075 = true := by decide +kernel
theorem w_23 : walk 9907232 19074 5220186363161 5213136936066 1000 = some (5245559241814, 5238862045318) := by decide +kernel
theorem u_23 : chkStep 9907232 (10 ^ 6) 1 20075 = true := by decide +kernel
theorem w_24 : walk 9955844 20074 5245559241814 5238862045318 1000 = some (5270401363267, 5262633349257) := by decide +kernel
theorem u_24 : chkStep 9955844 (10 ^ 6) 1 21075 = true := by decide +kernel
theorem w_25 : walk 10002202 21074 5270401363267 5262633349257 1000 = some (5292098974046, 5287295055345) := by decide +kernel
theorem u_25 : chkStep 10002202 (10 ^ 6) 1 22075 = true := by decide +kernel
theorem w_26 : walk 10046506 22074 5292098974046 5287295055345 1000 = some (5313905818360, 5309793226037) := by decide +kernel
theorem u_26 : chkStep 10046506 (10 ^ 6) 1 23075 = true := by decide +kernel
theorem w_27 : walk 10088930 23074 5313905818360 5309793226037 1000 = some (5334311877840, 5331812243416) := by decide +kernel
theorem u_27 : chkStep 10088930 (10 ^ 6) 1 24075 = true := by decide +kernel
theorem w_28 : walk 10129628 24074 5334311877840 5331812243416 1000 = some (5354810832011, 5352011493181) := by decide +kernel
theorem u_28 : chkStep 10129628 (10 ^ 6) 1 25075 = true := by decide +kernel
theorem w_29 : walk 10168733 25074 5354810832011 5352011493181 1000 = some (5374281191558, 5371647564906) := by decide +kernel
theorem u_29 : chkStep 10168733 (10 ^ 6) 1 26075 = true := by decide +kernel
theorem w_30 : walk 10206367 26074 5374281191558 5371647564906 1000 = some (5393251819111, 5390311437096) := by decide +kernel
theorem u_30 : chkStep 10206367 (10 ^ 6) 1 27075 = true := by decide +kernel
theorem w_31 : walk 10242636 27074 5393251819111 5390311437096 1000 = some (5411430367565, 5408402253677) := by decide +kernel
theorem u_31 : chkStep 10242636 (10 ^ 6) 1 28075 = true := by decide +kernel
theorem w_32 : walk 10277635 28074 5411430367565 5408402253677 1000 = some (5429420434689, 5425411996380) := by decide +kernel
theorem u_32 : chkStep 10277635 (10 ^ 6) 1 29075 = true := by decide +kernel
theorem w_33 : walk 10311451 29074 5429420434689 5425411996380 1000 = some (5446843094514, 5441805471354) := by decide +kernel
theorem u_33 : chkStep 10311451 (10 ^ 6) 1 30075 = true := by decide +kernel
theorem w_34 : walk 10344160 30074 5446843094514 5441805471354 1000 = some (5463781241090, 5457577234813) := by decide +kernel
theorem u_34 : chkStep 10344160 (10 ^ 6) 1 31075 = true := by decide +kernel
theorem w_35 : walk 10375833 31074 5463781241090 5457577234813 1000 = some (5479680107524, 5473352142636) := by decide +kernel
theorem u_35 : chkStep 10375833 (10 ^ 6) 1 32075 = true := by decide +kernel
theorem w_36 : walk 10406534 32074 5479680107524 5473352142636 1000 = some (5494294775455, 5489438745023) := by decide +kernel
theorem u_36 : chkStep 10406534 (10 ^ 6) 1 33075 = true := by decide +kernel
theorem w_37 : walk 10436320 33074 5494294775455 5489438745023 1000 = some (5508974644352, 5504545586863) := by decide +kernel
theorem u_37 : chkStep 10436320 (10 ^ 6) 1 34075 = true := by decide +kernel
theorem w_38 : walk 10465245 34074 5508974644352 5504545586863 1000 = some (5523462350542, 5518982946937) := by decide +kernel
theorem u_38 : chkStep 10465245 (10 ^ 6) 1 35075 = true := by decide +kernel
theorem w_39 : walk 10493356 35074 5523462350542 5518982946937 1000 = some (5537149188953, 5533407981859) := by decide +kernel
theorem u_39 : chkStep 10493356 (10 ^ 6) 1 36075 = true := by decide +kernel
theorem w_40 : walk 10520699 36074 5537149188953 5533407981859 1000 = some (5550606590439, 5547293737069) := by decide +kernel
theorem u_40 : chkStep 10520699 (10 ^ 6) 1 37075 = true := by decide +kernel
theorem w_41 : walk 10547314 37074 5550606590439 5547293737069 1000 = some (5563353626046, 5561162065934) := by decide +kernel
theorem u_41 : chkStep 10547314 (10 ^ 6) 1 38075 = true := by decide +kernel
theorem w_42 : walk 10573239 38074 5563353626046 5561162065934 1000 = some (5576261895179, 5574179109898) := by decide +kernel
theorem u_42 : chkStep 10573239 (10 ^ 6) 1 39075 = true := by decide +kernel
theorem w_43 : walk 10598509 39074 5576261895179 5574179109898 1000 = some (5589066966226, 5586644179844) := by decide +kernel
theorem u_43 : chkStep 10598509 (10 ^ 6) 1 40075 = true := by decide +kernel
theorem w_44 : walk 10623156 40074 5589066966226 5586644179844 1000 = some (5601266905480, 5599091509268) := by decide +kernel
theorem u_44 : chkStep 10623156 (10 ^ 6) 1 41075 = true := by decide +kernel
theorem w_45 : walk 10647210 41074 5601266905480 5599091509268 1000 = some (5612984691368, 5611428088355) := by decide +kernel
theorem u_45 : chkStep 10647210 (10 ^ 6) 1 42075 = true := by decide +kernel
theorem w_46 : walk 10670699 42074 5612984691368 5611428088355 1000 = some (5624633972869, 5623268124579) := by decide +kernel
theorem u_46 : chkStep 10670699 (10 ^ 6) 1 43075 = true := by decide +kernel
theorem w_47 : walk 10693649 43074 5624633972869 5623268124579 1000 = some (5636730230544, 5634122075650) := by decide +kernel
theorem u_47 : chkStep 10693649 (10 ^ 6) 1 44075 = true := by decide +kernel
theorem w_48 : walk 10716084 44074 5636730230544 5634122075650 1000 = some (5647862581724, 5645425016455) := by decide +kernel
theorem u_48 : chkStep 10716084 (10 ^ 6) 1 45075 = true := by decide +kernel
theorem w_49 : walk 10738027 45074 5647862581724 5645425016455 1000 = some (5659556067996, 5655674504912) := by decide +kernel
theorem u_49 : chkStep 10738027 (10 ^ 6) 1 46075 = true := by decide +kernel
theorem w_50 : walk 10759498 46074 5659556067996 5655674504912 1000 = some (5670805679098, 5665896694822) := by decide +kernel
theorem u_50 : chkStep 10759498 (10 ^ 6) 1 47075 = true := by decide +kernel
theorem w_51 : walk 10780519 47074 5670805679098 5665896694822 1000 = some (5681379189779, 5676343621535) := by decide +kernel
theorem u_51 : chkStep 10780519 (10 ^ 6) 1 48075 = true := by decide +kernel
theorem w_52 : walk 10801106 48074 5681379189779 5676343621535 1000 = some (5691944625633, 5686365845803) := by decide +kernel
theorem u_52 : chkStep 10801106 (10 ^ 6) 1 49075 = true := by decide +kernel
theorem w_53 : walk 10821278 49074 5691944625633 5686365845803 1000 = some (5701367450486, 5697115365300) := by decide +kernel
theorem u_53 : chkStep 10821278 (10 ^ 6) 1 50075 = true := by decide +kernel
theorem w_54 : walk 10841051 50074 5701367450486 5697115365300 1000 = some (5711410204514, 5706846065421) := by decide +kernel
theorem u_54 : chkStep 10841051 (10 ^ 6) 1 51075 = true := by decide +kernel
theorem w_55 : walk 10860441 51074 5711410204514 5706846065421 1000 = some (5720720127124, 5716926176744) := by decide +kernel
theorem u_55 : chkStep 10860441 (10 ^ 6) 1 52075 = true := by decide +kernel
theorem w_56 : walk 10879462 52074 5720720127124 5716926176744 1000 = some (5729984623961, 5726682880766) := by decide +kernel
theorem u_56 : chkStep 10879462 (10 ^ 6) 1 53075 = true := by decide +kernel
theorem w_57 : walk 10898128 53074 5729984623961 5726682880766 1000 = some (5739372858950, 5735960783758) := by decide +kernel
theorem u_57 : chkStep 10898128 (10 ^ 6) 1 54075 = true := by decide +kernel
theorem w_58 : walk 10916452 54074 5739372858950 5735960783758 1000 = some (5748627751702, 5745029979237) := by decide +kernel
theorem u_58 : chkStep 10916452 (10 ^ 6) 1 55075 = true := by decide +kernel
theorem w_59 : walk 10934446 55074 5748627751702 5745029979237 1000 = some (5757553236946, 5754098843115) := by decide +kernel
theorem u_59 : chkStep 10934446 (10 ^ 6) 1 56075 = true := by decide +kernel
theorem w_60 : walk 10952122 56074 5757553236946 5754098843115 1000 = some (5765685961012, 5763642386784) := by decide +kernel
theorem u_60 : chkStep 10952122 (10 ^ 6) 1 57075 = true := by decide +kernel
theorem w_61 : walk 10969492 57074 5765685961012 5763642386784 1000 = some (5774232127020, 5772465457376) := by decide +kernel
theorem u_61 : chkStep 10969492 (10 ^ 6) 1 58075 = true := by decide +kernel
theorem w_62 : walk 10986564 58074 5774232127020 5772465457376 1000 = some (5782428140501, 5781342133566) := by decide +kernel
theorem u_62 : chkStep 10986564 (10 ^ 6) 1 59075 = true := by decide +kernel
theorem w_63 : walk 11003350 59074 5782428140501 5781342133566 1000 = some (5790869351332, 5789687021711) := by decide +kernel
theorem u_63 : chkStep 11003350 (10 ^ 6) 1 60075 = true := by decide +kernel
theorem w_64 : walk 11019859 60074 5790869351332 5789687021711 1000 = some (5799075356816, 5797989987529) := by decide +kernel
theorem u_64 : chkStep 11019859 (10 ^ 6) 1 61075 = true := by decide +kernel
theorem w_65 : walk 11036100 61074 5799075356816 5797989987529 1000 = some (5807050197565, 5806255992421) := by decide +kernel
theorem u_65 : chkStep 11036100 (10 ^ 6) 1 62075 = true := by decide +kernel
theorem w_66 : walk 11052081 62074 5807050197565 5806255992421 1000 = some (5815217535194, 5814069945116) := by decide +kernel
theorem u_66 : chkStep 11052081 (10 ^ 6) 1 63075 = true := by decide +kernel
theorem w_67 : walk 11067811 63074 5815217535194 5814069945116 1000 = some (5822971500530, 5822045880723) := by decide +kernel
theorem u_67 : chkStep 11067811 (10 ^ 6) 1 64075 = true := by decide +kernel
theorem w_68 : walk 11083297 64074 5822971500530 5822045880723 1000 = some (5831441896136, 5829061783156) := by decide +kernel
theorem u_68 : chkStep 11083297 (10 ^ 6) 1 65075 = true := by decide +kernel
theorem w_69 : walk 11098547 65074 5831441896136 5829061783156 1000 = some (5839050880724, 5836702923974) := by decide +kernel
theorem u_69 : chkStep 11098547 (10 ^ 6) 1 66075 = true := by decide +kernel
theorem w_70 : walk 11113568 66074 5839050880724 5836702923974 1000 = some (5846968462380, 5843806390460) := by decide +kernel
theorem u_70 : chkStep 11113568 (10 ^ 6) 1 67075 = true := by decide +kernel
theorem w_71 : walk 11128366 67074 5846968462380 5843806390460 1000 = some (5853983479599, 5851590124485) := by decide +kernel
theorem u_71 : chkStep 11128366 (10 ^ 6) 1 68075 = true := by decide +kernel
theorem w_72 : walk 11142949 68074 5853983479599 5851590124485 1000 = some (5861682598316, 5858473943857) := by decide +kernel
theorem u_72 : chkStep 11142949 (10 ^ 6) 1 69075 = true := by decide +kernel
theorem w_73 : walk 11157322 69074 5861682598316 5858473943857 1000 = some (5868769148942, 5865760722274) := by decide +kernel
theorem u_73 : chkStep 11157322 (10 ^ 6) 1 70075 = true := by decide +kernel
theorem w_74 : walk 11171492 70074 5868769148942 5865760722274 1000 = some (5875896313568, 5872803218018) := by decide +kernel
theorem u_74 : chkStep 11171492 (10 ^ 6) 1 71075 = true := by decide +kernel
theorem w_75 : walk 11185464 71074 5875896313568 5872803218018 1000 = some (5882727623294, 5879943591401) := by decide +kernel
theorem u_75 : chkStep 11185464 (10 ^ 6) 1 72075 = true := by decide +kernel
theorem w_76 : walk 11199243 72074 5882727623294 5879943591401 1000 = some (5889329542111, 5887120834489) := by decide +kernel
theorem u_76 : chkStep 11199243 (10 ^ 6) 1 73075 = true := by decide +kernel
theorem w_77 : walk 11212834 73074 5889329542111 5887120834489 1000 = some (5896615747444, 5893426503484) := by decide +kernel
theorem u_77 : chkStep 11212834 (10 ^ 6) 1 74075 = true := by decide +kernel
theorem w_78 : walk 11226244 74074 5896615747444 5893426503484 1000 = some (5903186204361, 5900265656405) := by decide +kernel
theorem u_78 : chkStep 11226244 (10 ^ 6) 1 75075 = true := by decide +kernel
theorem w_79 : walk 11239476 75074 5903186204361 5900265656405 1000 = some (5909962036890, 5906721992846) := by decide +kernel
theorem u_79 : chkStep 11239476 (10 ^ 6) 1 76075 = true := by decide +kernel
theorem w_80 : walk 11252535 76074 5909962036890 5906721992846 1000 = some (5916779829389, 5912963563115) := by decide +kernel
theorem u_80 : chkStep 11252535 (10 ^ 6) 1 77075 = true := by decide +kernel
theorem w_81 : walk 11265426 77074 5916779829389 5912963563115 1000 = some (5923084697016, 5919549707470) := by decide +kernel
theorem u_81 : chkStep 11265426 (10 ^ 6) 1 78075 = true := by decide +kernel
theorem w_82 : walk 11278153 78074 5923084697016 5919549707470 1000 = some (5929677576686, 5925683774319) := by decide +kernel
theorem u_82 : chkStep 11278153 (10 ^ 6) 1 79075 = true := by decide +kernel
theorem w_83 : walk 11290720 79074 5929677576686 5925683774319 1000 = some (5935521257715, 5932407098070) := by decide +kernel
theorem u_83 : chkStep 11290720 (10 ^ 6) 1 80075 = true := by decide +kernel
theorem w_84 : walk 11303131 80074 5935521257715 5932407098070 1000 = some (5941640684728, 5938698704270) := by decide +kernel
theorem u_84 : chkStep 11303131 (10 ^ 6) 1 81075 = true := by decide +kernel
theorem w_85 : walk 11315390 81074 5941640684728 5938698704270 1000 = some (5947659991327, 5944938283513) := by decide +kernel
theorem u_85 : chkStep 11315390 (10 ^ 6) 1 82075 = true := by decide +kernel
theorem w_86 : walk 11327500 82074 5947659991327 5944938283513 1000 = some (5953581754962, 5951126943574) := by decide +kernel
theorem u_86 : chkStep 11327500 (10 ^ 6) 1 83075 = true := by decide +kernel
theorem w_87 : walk 11339466 83074 5953581754962 5951126943574 1000 = some (5959815687487, 5956858525534) := by decide +kernel
theorem u_87 : chkStep 11339466 (10 ^ 6) 1 84075 = true := by decide +kernel
theorem w_88 : walk 11351289 84074 5959815687487 5956858525534 1000 = some (5965869140879, 5962629104324) := by decide +kernel
theorem u_88 : chkStep 11351289 (10 ^ 6) 1 85075 = true := by decide +kernel
theorem w_89 : walk 11362975 85074 5965869140879 5962629104324 1000 = some (5971746416184, 5968437685630) := by decide +kernel
theorem u_89 : chkStep 11362975 (10 ^ 6) 1 86075 = true := by decide +kernel
theorem w_90 : walk 11374526 86074 5971746416184 5968437685630 1000 = some (5977255519983, 5974479455076) := by decide +kernel
theorem u_90 : chkStep 11374526 (10 ^ 6) 1 87075 = true := by decide +kernel
theorem w_91 : walk 11385945 87074 5977255519983 5974479455076 1000 = some (5982827797396, 5980326150329) := by decide +kernel
theorem u_91 : chkStep 11385945 (10 ^ 6) 1 88075 = true := by decide +kernel
theorem w_92 : walk 11397235 88074 5982827797396 5980326150329 1000 = some (5988314702858, 5986129295383) := by decide +kernel
theorem u_92 : chkStep 11397235 (10 ^ 6) 1 89075 = true := by decide +kernel
theorem w_93 : walk 11408399 89074 5988314702858 5986129295383 1000 = some (5993941043243, 5991666961955) := by decide +kernel
theorem u_93 : chkStep 11408399 (10 ^ 6) 1 90075 = true := by decide +kernel
theorem w_94 : walk 11419440 90074 5993941043243 5991666961955 1000 = some (5999527634157, 5997121117787) := by decide +kernel
theorem u_94 : chkStep 11419440 (10 ^ 6) 1 91075 = true := by decide +kernel
theorem w_95 : walk 11430360 91074 5999527634157 5997121117787 1000 = some (6004638452077, 6002930478434) := by decide +kernel
theorem u_95 : chkStep 11430360 (10 ^ 6) 1 92075 = true := by decide +kernel
theorem w_96 : walk 11441162 92074 6004638452077 6002930478434 1000 = some (6009877385589, 6008493760183) := by decide +kernel
theorem u_96 : chkStep 11441162 (10 ^ 6) 1 93075 = true := by decide +kernel
theorem w_97 : walk 11451849 93074 6009877385589 6008493760183 1000 = some (6015060107078, 6013997812007) := by decide +kernel
theorem u_97 : chkStep 11451849 (10 ^ 6) 1 94075 = true := by decide +kernel
theorem w_98 : walk 11462422 94074 6015060107078 6013997812007 1000 = some (6020219702028, 6019411989793) := by decide +kernel
theorem u_98 : chkStep 11462422 (10 ^ 6) 1 95075 = true := by decide +kernel
theorem w_99 : walk 11472885 95074 6020219702028 6019411989793 1000 = some (6025273064415, 6024821764304) := by decide +kernel
theorem u_99 : chkStep 11472885 (10 ^ 6) 1 96075 = true := by decide +kernel
theorem w_100 : walk 11483240 96074 6025273064415 6024821764304 1000 = some (6030377601779, 6030072019208) := by decide +kernel
theorem u_100 : chkStep 11483240 (10 ^ 6) 1 97075 = true := by decide +kernel
theorem w_101 : walk 11493489 97074 6030377601779 6030072019208 1000 = some (6035748635692, 6034949653808) := by decide +kernel
theorem u_101 : chkStep 11493489 (10 ^ 6) 1 98075 = true := by decide +kernel
theorem w_102 : walk 11503633 98074 6035748635692 6034949653808 1000 = some (6040992946174, 6039850041265) := by decide +kernel
theorem u_102 : chkStep 11503633 (10 ^ 6) 1 99075 = true := by decide +kernel
theorem w_103 : walk 11512936 99074 6040992946174 6039850041265 926 = some (6045774596579, 6044371484002) := by decide +kernel
theorem u_103 : chkStep 11512936 (10 ^ 6) 1 100001 = true := by decide +kernel

theorem s_0 : Pt 0 = 0 ∧ Qt 0 = 0 := by simp [Pt, Qt]

theorem c_0 : (Pt 1 = 1000000000000 ∧ Qt 1 = 0) ∧ ∀ k, 0 < k → k ≤ 1 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_0 u_0 (by norm_num) s_0
theorem c_1 : (Pt 6 = 1416666666666 ∧ Qt 6 = 1033333333333) ∧ ∀ k, 1 < k → k ≤ 6 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_1 u_1 (by norm_num) c_0.1
theorem c_2 : (Pt 19 = 1828373015871 ∧ Qt 19 = 1719366641268) ∧ ∀ k, 6 < k → k ≤ 19 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_2 u_2 (by norm_num) c_1.1
theorem c_3 : (Pt 74 = 2477505067336 ∧ Qt 74 = 2410517229857) ∧ ∀ k, 19 < k → k ≤ 74 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_3 u_3 (by norm_num) c_2.1
theorem c_4 : (Pt 1074 = 3786133200820 ∧ Qt 1074 = 3770693215793) ∧ ∀ k, 74 < k → k ≤ 1074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_4 u_4 (by norm_num) c_3.1
theorem c_5 : (Pt 2074 = 4116684851431 ∧ Qt 2074 = 4098006261995) ∧ ∀ k, 1074 < k → k ≤ 2074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_5 u_5 (by norm_num) c_4.1
theorem c_6 : (Pt 3074 = 4309788996379 ∧ Qt 3074 = 4298324236915) ∧ ∀ k, 2074 < k → k ≤ 3074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_6 u_6 (by norm_num) c_5.1
theorem c_7 : (Pt 4074 = 4448958589432 ∧ Qt 4074 = 4440760394837) ∧ ∀ k, 3074 < k → k ≤ 4074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_7 u_7 (by norm_num) c_6.1
theorem c_8 : (Pt 5074 = 4559288245479 ∧ Qt 5074 = 4549910695545) ∧ ∀ k, 4074 < k → k ≤ 5074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_8 u_8 (by norm_num) c_7.1
theorem c_9 : (Pt 6074 = 4649112566764 ∧ Qt 6074 = 4639958056690) ∧ ∀ k, 5074 < k → k ≤ 6074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_9 u_9 (by norm_num) c_8.1
theorem c_10 : (Pt 7074 = 4722345730546 ∧ Qt 7074 = 4719121980452) ∧ ∀ k, 6074 < k → k ≤ 7074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_10 u_10 (by norm_num) c_9.1
theorem c_11 : (Pt 8074 = 4792201999036 ∧ Qt 8074 = 4781479889320) ∧ ∀ k, 7074 < k → k ≤ 8074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_11 u_11 (by norm_num) c_10.1
theorem c_12 : (Pt 9074 = 4850174940652 ∧ Qt 9074 = 4840264281625) ∧ ∀ k, 8074 < k → k ≤ 9074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_12 u_12 (by norm_num) c_11.1
theorem c_13 : (Pt 10074 = 4899928051489 ∧ Qt 10074 = 4895050366783) ∧ ∀ k, 9074 < k → k ≤ 10074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_13 u_13 (by norm_num) c_12.1
theorem c_14 : (Pt 11074 = 4947131367342 ∧ Qt 11074 = 4942484739746) ∧ ∀ k, 10074 < k → k ≤ 11074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_14 u_14 (by norm_num) c_13.1
theorem c_15 : (Pt 12074 = 4991736503101 ∧ Qt 12074 = 4984330226063) ∧ ∀ k, 11074 < k → k ≤ 12074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_15 u_15 (by norm_num) c_14.1
theorem c_16 : (Pt 13074 = 5031701251877 ∧ Qt 13074 = 5023933454246) ∧ ∀ k, 12074 < k → k ≤ 13074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_16 u_16 (by norm_num) c_15.1
theorem c_17 : (Pt 14074 = 5068690747338 ∧ Qt 14074 = 5060644839353) ∧ ∀ k, 13074 < k → k ≤ 14074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_17 u_17 (by norm_num) c_16.1
theorem c_18 : (Pt 15074 = 5101973604045 ∧ Qt 15074 = 5096001907285) ∧ ∀ k, 14074 < k → k ≤ 15074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_18 u_18 (by norm_num) c_17.1
theorem c_19 : (Pt 16074 = 5132156739422 ∧ Qt 16074 = 5130048362262) ∧ ∀ k, 15074 < k → k ≤ 16074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_19 u_19 (by norm_num) c_18.1
theorem c_20 : (Pt 17074 = 5162575144609 ∧ Qt 17074 = 5159981913587) ∧ ∀ k, 16074 < k → k ≤ 17074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_20 u_20 (by norm_num) c_19.1
theorem c_21 : (Pt 18074 = 5191559891520 ∧ Qt 18074 = 5187913148863) ∧ ∀ k, 17074 < k → k ≤ 18074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_21 u_21 (by norm_num) c_20.1
theorem c_22 : (Pt 19074 = 5220186363161 ∧ Qt 19074 = 5213136936066) ∧ ∀ k, 18074 < k → k ≤ 19074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_22 u_22 (by norm_num) c_21.1
theorem c_23 : (Pt 20074 = 5245559241814 ∧ Qt 20074 = 5238862045318) ∧ ∀ k, 19074 < k → k ≤ 20074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_23 u_23 (by norm_num) c_22.1
theorem c_24 : (Pt 21074 = 5270401363267 ∧ Qt 21074 = 5262633349257) ∧ ∀ k, 20074 < k → k ≤ 21074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_24 u_24 (by norm_num) c_23.1
theorem c_25 : (Pt 22074 = 5292098974046 ∧ Qt 22074 = 5287295055345) ∧ ∀ k, 21074 < k → k ≤ 22074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_25 u_25 (by norm_num) c_24.1
theorem c_26 : (Pt 23074 = 5313905818360 ∧ Qt 23074 = 5309793226037) ∧ ∀ k, 22074 < k → k ≤ 23074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_26 u_26 (by norm_num) c_25.1
theorem c_27 : (Pt 24074 = 5334311877840 ∧ Qt 24074 = 5331812243416) ∧ ∀ k, 23074 < k → k ≤ 24074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_27 u_27 (by norm_num) c_26.1
theorem c_28 : (Pt 25074 = 5354810832011 ∧ Qt 25074 = 5352011493181) ∧ ∀ k, 24074 < k → k ≤ 25074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_28 u_28 (by norm_num) c_27.1
theorem c_29 : (Pt 26074 = 5374281191558 ∧ Qt 26074 = 5371647564906) ∧ ∀ k, 25074 < k → k ≤ 26074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_29 u_29 (by norm_num) c_28.1
theorem c_30 : (Pt 27074 = 5393251819111 ∧ Qt 27074 = 5390311437096) ∧ ∀ k, 26074 < k → k ≤ 27074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_30 u_30 (by norm_num) c_29.1
theorem c_31 : (Pt 28074 = 5411430367565 ∧ Qt 28074 = 5408402253677) ∧ ∀ k, 27074 < k → k ≤ 28074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_31 u_31 (by norm_num) c_30.1
theorem c_32 : (Pt 29074 = 5429420434689 ∧ Qt 29074 = 5425411996380) ∧ ∀ k, 28074 < k → k ≤ 29074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_32 u_32 (by norm_num) c_31.1
theorem c_33 : (Pt 30074 = 5446843094514 ∧ Qt 30074 = 5441805471354) ∧ ∀ k, 29074 < k → k ≤ 30074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_33 u_33 (by norm_num) c_32.1
theorem c_34 : (Pt 31074 = 5463781241090 ∧ Qt 31074 = 5457577234813) ∧ ∀ k, 30074 < k → k ≤ 31074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_34 u_34 (by norm_num) c_33.1
theorem c_35 : (Pt 32074 = 5479680107524 ∧ Qt 32074 = 5473352142636) ∧ ∀ k, 31074 < k → k ≤ 32074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_35 u_35 (by norm_num) c_34.1
theorem c_36 : (Pt 33074 = 5494294775455 ∧ Qt 33074 = 5489438745023) ∧ ∀ k, 32074 < k → k ≤ 33074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_36 u_36 (by norm_num) c_35.1
theorem c_37 : (Pt 34074 = 5508974644352 ∧ Qt 34074 = 5504545586863) ∧ ∀ k, 33074 < k → k ≤ 34074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_37 u_37 (by norm_num) c_36.1
theorem c_38 : (Pt 35074 = 5523462350542 ∧ Qt 35074 = 5518982946937) ∧ ∀ k, 34074 < k → k ≤ 35074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_38 u_38 (by norm_num) c_37.1
theorem c_39 : (Pt 36074 = 5537149188953 ∧ Qt 36074 = 5533407981859) ∧ ∀ k, 35074 < k → k ≤ 36074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_39 u_39 (by norm_num) c_38.1
theorem c_40 : (Pt 37074 = 5550606590439 ∧ Qt 37074 = 5547293737069) ∧ ∀ k, 36074 < k → k ≤ 37074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_40 u_40 (by norm_num) c_39.1
theorem c_41 : (Pt 38074 = 5563353626046 ∧ Qt 38074 = 5561162065934) ∧ ∀ k, 37074 < k → k ≤ 38074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_41 u_41 (by norm_num) c_40.1
theorem c_42 : (Pt 39074 = 5576261895179 ∧ Qt 39074 = 5574179109898) ∧ ∀ k, 38074 < k → k ≤ 39074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_42 u_42 (by norm_num) c_41.1
theorem c_43 : (Pt 40074 = 5589066966226 ∧ Qt 40074 = 5586644179844) ∧ ∀ k, 39074 < k → k ≤ 40074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_43 u_43 (by norm_num) c_42.1
theorem c_44 : (Pt 41074 = 5601266905480 ∧ Qt 41074 = 5599091509268) ∧ ∀ k, 40074 < k → k ≤ 41074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_44 u_44 (by norm_num) c_43.1
theorem c_45 : (Pt 42074 = 5612984691368 ∧ Qt 42074 = 5611428088355) ∧ ∀ k, 41074 < k → k ≤ 42074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_45 u_45 (by norm_num) c_44.1
theorem c_46 : (Pt 43074 = 5624633972869 ∧ Qt 43074 = 5623268124579) ∧ ∀ k, 42074 < k → k ≤ 43074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_46 u_46 (by norm_num) c_45.1
theorem c_47 : (Pt 44074 = 5636730230544 ∧ Qt 44074 = 5634122075650) ∧ ∀ k, 43074 < k → k ≤ 44074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_47 u_47 (by norm_num) c_46.1
theorem c_48 : (Pt 45074 = 5647862581724 ∧ Qt 45074 = 5645425016455) ∧ ∀ k, 44074 < k → k ≤ 45074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_48 u_48 (by norm_num) c_47.1
theorem c_49 : (Pt 46074 = 5659556067996 ∧ Qt 46074 = 5655674504912) ∧ ∀ k, 45074 < k → k ≤ 46074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_49 u_49 (by norm_num) c_48.1
theorem c_50 : (Pt 47074 = 5670805679098 ∧ Qt 47074 = 5665896694822) ∧ ∀ k, 46074 < k → k ≤ 47074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_50 u_50 (by norm_num) c_49.1
theorem c_51 : (Pt 48074 = 5681379189779 ∧ Qt 48074 = 5676343621535) ∧ ∀ k, 47074 < k → k ≤ 48074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_51 u_51 (by norm_num) c_50.1
theorem c_52 : (Pt 49074 = 5691944625633 ∧ Qt 49074 = 5686365845803) ∧ ∀ k, 48074 < k → k ≤ 49074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_52 u_52 (by norm_num) c_51.1
theorem c_53 : (Pt 50074 = 5701367450486 ∧ Qt 50074 = 5697115365300) ∧ ∀ k, 49074 < k → k ≤ 50074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_53 u_53 (by norm_num) c_52.1
theorem c_54 : (Pt 51074 = 5711410204514 ∧ Qt 51074 = 5706846065421) ∧ ∀ k, 50074 < k → k ≤ 51074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_54 u_54 (by norm_num) c_53.1
theorem c_55 : (Pt 52074 = 5720720127124 ∧ Qt 52074 = 5716926176744) ∧ ∀ k, 51074 < k → k ≤ 52074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_55 u_55 (by norm_num) c_54.1
theorem c_56 : (Pt 53074 = 5729984623961 ∧ Qt 53074 = 5726682880766) ∧ ∀ k, 52074 < k → k ≤ 53074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_56 u_56 (by norm_num) c_55.1
theorem c_57 : (Pt 54074 = 5739372858950 ∧ Qt 54074 = 5735960783758) ∧ ∀ k, 53074 < k → k ≤ 54074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_57 u_57 (by norm_num) c_56.1
theorem c_58 : (Pt 55074 = 5748627751702 ∧ Qt 55074 = 5745029979237) ∧ ∀ k, 54074 < k → k ≤ 55074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_58 u_58 (by norm_num) c_57.1
theorem c_59 : (Pt 56074 = 5757553236946 ∧ Qt 56074 = 5754098843115) ∧ ∀ k, 55074 < k → k ≤ 56074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_59 u_59 (by norm_num) c_58.1
theorem c_60 : (Pt 57074 = 5765685961012 ∧ Qt 57074 = 5763642386784) ∧ ∀ k, 56074 < k → k ≤ 57074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_60 u_60 (by norm_num) c_59.1
theorem c_61 : (Pt 58074 = 5774232127020 ∧ Qt 58074 = 5772465457376) ∧ ∀ k, 57074 < k → k ≤ 58074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_61 u_61 (by norm_num) c_60.1
theorem c_62 : (Pt 59074 = 5782428140501 ∧ Qt 59074 = 5781342133566) ∧ ∀ k, 58074 < k → k ≤ 59074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_62 u_62 (by norm_num) c_61.1
theorem c_63 : (Pt 60074 = 5790869351332 ∧ Qt 60074 = 5789687021711) ∧ ∀ k, 59074 < k → k ≤ 60074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_63 u_63 (by norm_num) c_62.1
theorem c_64 : (Pt 61074 = 5799075356816 ∧ Qt 61074 = 5797989987529) ∧ ∀ k, 60074 < k → k ≤ 61074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_64 u_64 (by norm_num) c_63.1
theorem c_65 : (Pt 62074 = 5807050197565 ∧ Qt 62074 = 5806255992421) ∧ ∀ k, 61074 < k → k ≤ 62074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_65 u_65 (by norm_num) c_64.1
theorem c_66 : (Pt 63074 = 5815217535194 ∧ Qt 63074 = 5814069945116) ∧ ∀ k, 62074 < k → k ≤ 63074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_66 u_66 (by norm_num) c_65.1
theorem c_67 : (Pt 64074 = 5822971500530 ∧ Qt 64074 = 5822045880723) ∧ ∀ k, 63074 < k → k ≤ 64074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_67 u_67 (by norm_num) c_66.1
theorem c_68 : (Pt 65074 = 5831441896136 ∧ Qt 65074 = 5829061783156) ∧ ∀ k, 64074 < k → k ≤ 65074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_68 u_68 (by norm_num) c_67.1
theorem c_69 : (Pt 66074 = 5839050880724 ∧ Qt 66074 = 5836702923974) ∧ ∀ k, 65074 < k → k ≤ 66074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_69 u_69 (by norm_num) c_68.1
theorem c_70 : (Pt 67074 = 5846968462380 ∧ Qt 67074 = 5843806390460) ∧ ∀ k, 66074 < k → k ≤ 67074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_70 u_70 (by norm_num) c_69.1
theorem c_71 : (Pt 68074 = 5853983479599 ∧ Qt 68074 = 5851590124485) ∧ ∀ k, 67074 < k → k ≤ 68074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_71 u_71 (by norm_num) c_70.1
theorem c_72 : (Pt 69074 = 5861682598316 ∧ Qt 69074 = 5858473943857) ∧ ∀ k, 68074 < k → k ≤ 69074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_72 u_72 (by norm_num) c_71.1
theorem c_73 : (Pt 70074 = 5868769148942 ∧ Qt 70074 = 5865760722274) ∧ ∀ k, 69074 < k → k ≤ 70074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_73 u_73 (by norm_num) c_72.1
theorem c_74 : (Pt 71074 = 5875896313568 ∧ Qt 71074 = 5872803218018) ∧ ∀ k, 70074 < k → k ≤ 71074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_74 u_74 (by norm_num) c_73.1
theorem c_75 : (Pt 72074 = 5882727623294 ∧ Qt 72074 = 5879943591401) ∧ ∀ k, 71074 < k → k ≤ 72074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_75 u_75 (by norm_num) c_74.1
theorem c_76 : (Pt 73074 = 5889329542111 ∧ Qt 73074 = 5887120834489) ∧ ∀ k, 72074 < k → k ≤ 73074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_76 u_76 (by norm_num) c_75.1
theorem c_77 : (Pt 74074 = 5896615747444 ∧ Qt 74074 = 5893426503484) ∧ ∀ k, 73074 < k → k ≤ 74074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_77 u_77 (by norm_num) c_76.1
theorem c_78 : (Pt 75074 = 5903186204361 ∧ Qt 75074 = 5900265656405) ∧ ∀ k, 74074 < k → k ≤ 75074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_78 u_78 (by norm_num) c_77.1
theorem c_79 : (Pt 76074 = 5909962036890 ∧ Qt 76074 = 5906721992846) ∧ ∀ k, 75074 < k → k ≤ 76074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_79 u_79 (by norm_num) c_78.1
theorem c_80 : (Pt 77074 = 5916779829389 ∧ Qt 77074 = 5912963563115) ∧ ∀ k, 76074 < k → k ≤ 77074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_80 u_80 (by norm_num) c_79.1
theorem c_81 : (Pt 78074 = 5923084697016 ∧ Qt 78074 = 5919549707470) ∧ ∀ k, 77074 < k → k ≤ 78074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_81 u_81 (by norm_num) c_80.1
theorem c_82 : (Pt 79074 = 5929677576686 ∧ Qt 79074 = 5925683774319) ∧ ∀ k, 78074 < k → k ≤ 79074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_82 u_82 (by norm_num) c_81.1
theorem c_83 : (Pt 80074 = 5935521257715 ∧ Qt 80074 = 5932407098070) ∧ ∀ k, 79074 < k → k ≤ 80074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_83 u_83 (by norm_num) c_82.1
theorem c_84 : (Pt 81074 = 5941640684728 ∧ Qt 81074 = 5938698704270) ∧ ∀ k, 80074 < k → k ≤ 81074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_84 u_84 (by norm_num) c_83.1
theorem c_85 : (Pt 82074 = 5947659991327 ∧ Qt 82074 = 5944938283513) ∧ ∀ k, 81074 < k → k ≤ 82074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_85 u_85 (by norm_num) c_84.1
theorem c_86 : (Pt 83074 = 5953581754962 ∧ Qt 83074 = 5951126943574) ∧ ∀ k, 82074 < k → k ≤ 83074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_86 u_86 (by norm_num) c_85.1
theorem c_87 : (Pt 84074 = 5959815687487 ∧ Qt 84074 = 5956858525534) ∧ ∀ k, 83074 < k → k ≤ 84074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_87 u_87 (by norm_num) c_86.1
theorem c_88 : (Pt 85074 = 5965869140879 ∧ Qt 85074 = 5962629104324) ∧ ∀ k, 84074 < k → k ≤ 85074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_88 u_88 (by norm_num) c_87.1
theorem c_89 : (Pt 86074 = 5971746416184 ∧ Qt 86074 = 5968437685630) ∧ ∀ k, 85074 < k → k ≤ 86074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_89 u_89 (by norm_num) c_88.1
theorem c_90 : (Pt 87074 = 5977255519983 ∧ Qt 87074 = 5974479455076) ∧ ∀ k, 86074 < k → k ≤ 87074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_90 u_90 (by norm_num) c_89.1
theorem c_91 : (Pt 88074 = 5982827797396 ∧ Qt 88074 = 5980326150329) ∧ ∀ k, 87074 < k → k ≤ 88074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_91 u_91 (by norm_num) c_90.1
theorem c_92 : (Pt 89074 = 5988314702858 ∧ Qt 89074 = 5986129295383) ∧ ∀ k, 88074 < k → k ≤ 89074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_92 u_92 (by norm_num) c_91.1
theorem c_93 : (Pt 90074 = 5993941043243 ∧ Qt 90074 = 5991666961955) ∧ ∀ k, 89074 < k → k ≤ 90074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_93 u_93 (by norm_num) c_92.1
theorem c_94 : (Pt 91074 = 5999527634157 ∧ Qt 91074 = 5997121117787) ∧ ∀ k, 90074 < k → k ≤ 91074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_94 u_94 (by norm_num) c_93.1
theorem c_95 : (Pt 92074 = 6004638452077 ∧ Qt 92074 = 6002930478434) ∧ ∀ k, 91074 < k → k ≤ 92074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_95 u_95 (by norm_num) c_94.1
theorem c_96 : (Pt 93074 = 6009877385589 ∧ Qt 93074 = 6008493760183) ∧ ∀ k, 92074 < k → k ≤ 93074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_96 u_96 (by norm_num) c_95.1
theorem c_97 : (Pt 94074 = 6015060107078 ∧ Qt 94074 = 6013997812007) ∧ ∀ k, 93074 < k → k ≤ 94074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_97 u_97 (by norm_num) c_96.1
theorem c_98 : (Pt 95074 = 6020219702028 ∧ Qt 95074 = 6019411989793) ∧ ∀ k, 94074 < k → k ≤ 95074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_98 u_98 (by norm_num) c_97.1
theorem c_99 : (Pt 96074 = 6025273064415 ∧ Qt 96074 = 6024821764304) ∧ ∀ k, 95074 < k → k ≤ 96074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_99 u_99 (by norm_num) c_98.1
theorem c_100 : (Pt 97074 = 6030377601779 ∧ Qt 97074 = 6030072019208) ∧ ∀ k, 96074 < k → k ≤ 97074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_100 u_100 (by norm_num) c_99.1
theorem c_101 : (Pt 98074 = 6035748635692 ∧ Qt 98074 = 6034949653808) ∧ ∀ k, 97074 < k → k ≤ 98074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_101 u_101 (by norm_num) c_100.1
theorem c_102 : (Pt 99074 = 6040992946174 ∧ Qt 99074 = 6039850041265) ∧ ∀ k, 98074 < k → k ≤ 99074 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_102 u_102 (by norm_num) c_101.1
theorem c_103 : (Pt 100000 = 6045774596579 ∧ Qt 100000 = 6044371484002) ∧ ∀ k, 99074 < k → k ≤ 100000 →
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 :=
  chunk_ok w_103 u_103 (by norm_num) c_102.1

/-- **`|∑_{n ≤ k} λ(n)/n| log(k + 1) ≤ 0.99` for `1 ≤ k ≤ 10⁵`** (kernel-checked). -/
theorem liouville_kernel (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 10 ^ 5) :
    |∑ n ∈ Icc 1 k, lam n / n| * Real.log (k + 1) ≤ 0.99 := by
  by_cases h0 : k ≤ 1
  · exact c_0.2 k (by omega) h0
  by_cases h1 : k ≤ 6
  · exact c_1.2 k (by omega) h1
  by_cases h2 : k ≤ 19
  · exact c_2.2 k (by omega) h2
  by_cases h3 : k ≤ 74
  · exact c_3.2 k (by omega) h3
  by_cases h4 : k ≤ 1074
  · exact c_4.2 k (by omega) h4
  by_cases h5 : k ≤ 2074
  · exact c_5.2 k (by omega) h5
  by_cases h6 : k ≤ 3074
  · exact c_6.2 k (by omega) h6
  by_cases h7 : k ≤ 4074
  · exact c_7.2 k (by omega) h7
  by_cases h8 : k ≤ 5074
  · exact c_8.2 k (by omega) h8
  by_cases h9 : k ≤ 6074
  · exact c_9.2 k (by omega) h9
  by_cases h10 : k ≤ 7074
  · exact c_10.2 k (by omega) h10
  by_cases h11 : k ≤ 8074
  · exact c_11.2 k (by omega) h11
  by_cases h12 : k ≤ 9074
  · exact c_12.2 k (by omega) h12
  by_cases h13 : k ≤ 10074
  · exact c_13.2 k (by omega) h13
  by_cases h14 : k ≤ 11074
  · exact c_14.2 k (by omega) h14
  by_cases h15 : k ≤ 12074
  · exact c_15.2 k (by omega) h15
  by_cases h16 : k ≤ 13074
  · exact c_16.2 k (by omega) h16
  by_cases h17 : k ≤ 14074
  · exact c_17.2 k (by omega) h17
  by_cases h18 : k ≤ 15074
  · exact c_18.2 k (by omega) h18
  by_cases h19 : k ≤ 16074
  · exact c_19.2 k (by omega) h19
  by_cases h20 : k ≤ 17074
  · exact c_20.2 k (by omega) h20
  by_cases h21 : k ≤ 18074
  · exact c_21.2 k (by omega) h21
  by_cases h22 : k ≤ 19074
  · exact c_22.2 k (by omega) h22
  by_cases h23 : k ≤ 20074
  · exact c_23.2 k (by omega) h23
  by_cases h24 : k ≤ 21074
  · exact c_24.2 k (by omega) h24
  by_cases h25 : k ≤ 22074
  · exact c_25.2 k (by omega) h25
  by_cases h26 : k ≤ 23074
  · exact c_26.2 k (by omega) h26
  by_cases h27 : k ≤ 24074
  · exact c_27.2 k (by omega) h27
  by_cases h28 : k ≤ 25074
  · exact c_28.2 k (by omega) h28
  by_cases h29 : k ≤ 26074
  · exact c_29.2 k (by omega) h29
  by_cases h30 : k ≤ 27074
  · exact c_30.2 k (by omega) h30
  by_cases h31 : k ≤ 28074
  · exact c_31.2 k (by omega) h31
  by_cases h32 : k ≤ 29074
  · exact c_32.2 k (by omega) h32
  by_cases h33 : k ≤ 30074
  · exact c_33.2 k (by omega) h33
  by_cases h34 : k ≤ 31074
  · exact c_34.2 k (by omega) h34
  by_cases h35 : k ≤ 32074
  · exact c_35.2 k (by omega) h35
  by_cases h36 : k ≤ 33074
  · exact c_36.2 k (by omega) h36
  by_cases h37 : k ≤ 34074
  · exact c_37.2 k (by omega) h37
  by_cases h38 : k ≤ 35074
  · exact c_38.2 k (by omega) h38
  by_cases h39 : k ≤ 36074
  · exact c_39.2 k (by omega) h39
  by_cases h40 : k ≤ 37074
  · exact c_40.2 k (by omega) h40
  by_cases h41 : k ≤ 38074
  · exact c_41.2 k (by omega) h41
  by_cases h42 : k ≤ 39074
  · exact c_42.2 k (by omega) h42
  by_cases h43 : k ≤ 40074
  · exact c_43.2 k (by omega) h43
  by_cases h44 : k ≤ 41074
  · exact c_44.2 k (by omega) h44
  by_cases h45 : k ≤ 42074
  · exact c_45.2 k (by omega) h45
  by_cases h46 : k ≤ 43074
  · exact c_46.2 k (by omega) h46
  by_cases h47 : k ≤ 44074
  · exact c_47.2 k (by omega) h47
  by_cases h48 : k ≤ 45074
  · exact c_48.2 k (by omega) h48
  by_cases h49 : k ≤ 46074
  · exact c_49.2 k (by omega) h49
  by_cases h50 : k ≤ 47074
  · exact c_50.2 k (by omega) h50
  by_cases h51 : k ≤ 48074
  · exact c_51.2 k (by omega) h51
  by_cases h52 : k ≤ 49074
  · exact c_52.2 k (by omega) h52
  by_cases h53 : k ≤ 50074
  · exact c_53.2 k (by omega) h53
  by_cases h54 : k ≤ 51074
  · exact c_54.2 k (by omega) h54
  by_cases h55 : k ≤ 52074
  · exact c_55.2 k (by omega) h55
  by_cases h56 : k ≤ 53074
  · exact c_56.2 k (by omega) h56
  by_cases h57 : k ≤ 54074
  · exact c_57.2 k (by omega) h57
  by_cases h58 : k ≤ 55074
  · exact c_58.2 k (by omega) h58
  by_cases h59 : k ≤ 56074
  · exact c_59.2 k (by omega) h59
  by_cases h60 : k ≤ 57074
  · exact c_60.2 k (by omega) h60
  by_cases h61 : k ≤ 58074
  · exact c_61.2 k (by omega) h61
  by_cases h62 : k ≤ 59074
  · exact c_62.2 k (by omega) h62
  by_cases h63 : k ≤ 60074
  · exact c_63.2 k (by omega) h63
  by_cases h64 : k ≤ 61074
  · exact c_64.2 k (by omega) h64
  by_cases h65 : k ≤ 62074
  · exact c_65.2 k (by omega) h65
  by_cases h66 : k ≤ 63074
  · exact c_66.2 k (by omega) h66
  by_cases h67 : k ≤ 64074
  · exact c_67.2 k (by omega) h67
  by_cases h68 : k ≤ 65074
  · exact c_68.2 k (by omega) h68
  by_cases h69 : k ≤ 66074
  · exact c_69.2 k (by omega) h69
  by_cases h70 : k ≤ 67074
  · exact c_70.2 k (by omega) h70
  by_cases h71 : k ≤ 68074
  · exact c_71.2 k (by omega) h71
  by_cases h72 : k ≤ 69074
  · exact c_72.2 k (by omega) h72
  by_cases h73 : k ≤ 70074
  · exact c_73.2 k (by omega) h73
  by_cases h74 : k ≤ 71074
  · exact c_74.2 k (by omega) h74
  by_cases h75 : k ≤ 72074
  · exact c_75.2 k (by omega) h75
  by_cases h76 : k ≤ 73074
  · exact c_76.2 k (by omega) h76
  by_cases h77 : k ≤ 74074
  · exact c_77.2 k (by omega) h77
  by_cases h78 : k ≤ 75074
  · exact c_78.2 k (by omega) h78
  by_cases h79 : k ≤ 76074
  · exact c_79.2 k (by omega) h79
  by_cases h80 : k ≤ 77074
  · exact c_80.2 k (by omega) h80
  by_cases h81 : k ≤ 78074
  · exact c_81.2 k (by omega) h81
  by_cases h82 : k ≤ 79074
  · exact c_82.2 k (by omega) h82
  by_cases h83 : k ≤ 80074
  · exact c_83.2 k (by omega) h83
  by_cases h84 : k ≤ 81074
  · exact c_84.2 k (by omega) h84
  by_cases h85 : k ≤ 82074
  · exact c_85.2 k (by omega) h85
  by_cases h86 : k ≤ 83074
  · exact c_86.2 k (by omega) h86
  by_cases h87 : k ≤ 84074
  · exact c_87.2 k (by omega) h87
  by_cases h88 : k ≤ 85074
  · exact c_88.2 k (by omega) h88
  by_cases h89 : k ≤ 86074
  · exact c_89.2 k (by omega) h89
  by_cases h90 : k ≤ 87074
  · exact c_90.2 k (by omega) h90
  by_cases h91 : k ≤ 88074
  · exact c_91.2 k (by omega) h91
  by_cases h92 : k ≤ 89074
  · exact c_92.2 k (by omega) h92
  by_cases h93 : k ≤ 90074
  · exact c_93.2 k (by omega) h93
  by_cases h94 : k ≤ 91074
  · exact c_94.2 k (by omega) h94
  by_cases h95 : k ≤ 92074
  · exact c_95.2 k (by omega) h95
  by_cases h96 : k ≤ 93074
  · exact c_96.2 k (by omega) h96
  by_cases h97 : k ≤ 94074
  · exact c_97.2 k (by omega) h97
  by_cases h98 : k ≤ 95074
  · exact c_98.2 k (by omega) h98
  by_cases h99 : k ≤ 96074
  · exact c_99.2 k (by omega) h99
  by_cases h100 : k ≤ 97074
  · exact c_100.2 k (by omega) h100
  by_cases h101 : k ≤ 98074
  · exact c_101.2 k (by omega) h101
  by_cases h102 : k ≤ 99074
  · exact c_102.2 k (by omega) h102
  exact c_103.2 k (by omega) (by omega)

end TernaryGoldbach.Prelim.SmallLiou
