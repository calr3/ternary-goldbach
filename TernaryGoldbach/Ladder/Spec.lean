import Mathlib.NumberTheory.Fermat
import TernaryGoldbach.Ladder.Check

/-!
# The prime ladder: correctness of the kernel check

`run_spec`: if `run n i₀ h = true`, then for each rung `i ∈ [i₀, i₀ + 32n)` with offset
`t = tOf h (i − i₀)` the candidate `c = cand (S·i) t` is prime to `3` and divides
`3^(2⁴⁴·S·i) + 3^(2⁴⁴·t)` (`Cert i t`). `prime_of_cert`: then `c` is prime. This is Proth's
theorem in Pocklington's form (`prime_of_dvd_pow_add_one`): every prime factor of `x^(2⁴⁴) + 1`
other than `2` is `≡ 1 (mod 2⁴⁵)` (Mathlib's `Nat.pow_pow_add_primeFactors_one_lt`), and
`c < (2⁴⁵ + 1)²`. `prime_of_runsOK` turns `RunsOK a n` into a prime in every window
`[(S·i − 2047)·2⁴⁵ + 1, S·i·2⁴⁵ + 1]`, `i ∈ [a, a + 4096n)`.
-/

namespace TernaryGoldbach.Ladder

/-- The offset of rung `j` in the packed hint `h`. -/
def tOf (h j : ℕ) : ℕ := (h >>> (11 * j)) &&& 2047

/-- The certificate checked for rung `i` with offset `t`. -/
def Cert (i t : ℕ) : Prop :=
  ¬ 3 ∣ cand (111616 * i) t ∧ cand (111616 * i) t ∣ 3 ^ (2 ^ 44 * (111616 * i)) + 3 ^ (2 ^ 44 * t)

theorem cand_eq (iS t : ℕ) : cand iS t = (iS - t) * 2 ^ 45 + 1 := rfl

theorem tOf_lt (h j : ℕ) : tOf h j < 2048 := Nat.lt_succ_of_le Nat.and_le_right

theorem tOf_zero (h : ℕ) : tOf h 0 = h &&& 2047 := by simp [tOf]

theorem tOf_shift (h j k : ℕ) : tOf (h >>> (11 * k)) j = tOf h (k + j) := by
  simp only [tOf, ← Nat.shiftRight_add, Nat.mul_add]

/-! ### Proth's criterion -/

/-- **Pocklington's criterion for `F = 2⁴⁵`**: an odd `c > 1` with `c < (2⁴⁵ + 1)²` that divides
`x^(2⁴⁴) + 1` is prime. -/
theorem prime_of_dvd_pow_add_one {c x : ℕ} (hodd : Odd c) (h1 : 1 < c)
    (hc : c < (2 ^ 45 + 1) ^ 2) (hd : c ∣ x ^ 2 ^ 44 + 1) : c.Prime := by
  by_contra hnp
  have hp : c.minFac.Prime := Nat.minFac_prime (by omega)
  have hpc : c.minFac ∣ c := Nat.minFac_dvd c
  have hsq : c.minFac ^ 2 ≤ c := Nat.minFac_sq_le_self (by omega) hnp
  have hp2 : c.minFac ≠ 2 := by
    intro h2
    rw [h2] at hpc
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpc)
  obtain ⟨k, hk⟩ := Nat.pow_pow_add_primeFactors_one_lt hp hp2 (hpc.trans hd)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, zero_mul, zero_add] at hk; exact absurd hk hp.one_lt.ne'
    · exact h0
  have hpge : 2 ^ 45 + 1 ≤ c.minFac := by rw [hk]; norm_num; omega
  have := Nat.pow_le_pow_left hpge 2
  omega

/-- A certified rung is prime. -/
theorem prime_of_cert {i t : ℕ} (hi : 1 ≤ i) (hiS : 111616 * i < 2 ^ 45) (ht : t < 2048)
    (h : Cert i t) : (cand (111616 * i) t).Prime := by
  obtain ⟨h3, hd⟩ := h
  set k := 111616 * i - t with hk
  have hkt : 111616 * i = k + t := by omega
  have hk1 : 1 ≤ k := by omega
  have hk45 : k < 2 ^ 45 := by omega
  rw [cand_eq] at h3 hd ⊢
  rw [← hk] at h3 hd ⊢
  have hcop : Nat.Coprime ((k * 2 ^ 45 + 1)) (3 ^ (2 ^ 44 * t)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  -- `D` stays a variable: the kernel must not evaluate `3 ^ 2 ^ 44`
  have hfac : ∀ D : ℕ, 3 ^ (D * (k + t)) + 3 ^ (D * t) = 3 ^ (D * t) * ((3 ^ k) ^ D + 1) := by
    intro D; rw [← pow_mul, Nat.mul_add, pow_add, mul_comm k D]; ring
  rw [hkt, hfac] at hd
  have hd' : k * 2 ^ 45 + 1 ∣ (3 ^ k) ^ 2 ^ 44 + 1 := hcop.dvd_of_dvd_mul_left hd
  have hpos : 0 < k * 2 ^ 45 := Nat.mul_pos hk1 (by positivity)
  have hlt : k * 2 ^ 45 + 1 < (2 ^ 45 + 1) ^ 2 := by
    have h1 : k * 2 ^ 45 < 2 ^ 45 * 2 ^ 45 := Nat.mul_lt_mul_of_pos_right hk45 (by positivity)
    generalize (2 : ℕ) ^ 45 = P at h1 ⊢
    nlinarith
  exact prime_of_dvd_pow_add_one ⟨k * 2 ^ 44, by ring⟩ (by omega) hlt hd'

/-! ### The loops -/

-- The loop equations are used with `rw`. A `simp` proof, or a direct definitional unfolding, can
-- make the kernel compare `Nat.add iS 111616` with `iS + 111616` by unfolding `Nat.add` on the
-- literal, which recurses `111616` levels deep.
theorem prodC_succ (n : ℕ) : prodC (n + 1) =
    fun iS h acc => prodC n (iS + 111616) (h >>> 11) (acc * cand iS (h &&& 2047)) := rfl

theorem prodC_dvd : ∀ (n iS h acc : ℕ), acc ∣ prodC n iS h acc ∧
    ∀ j < n, cand (iS + 111616 * j) (tOf h j) ∣ prodC n iS h acc := by
  intro n
  induction n with
  | zero => intro iS h acc; exact ⟨dvd_rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro iS h acc
    rw [prodC_succ]
    obtain ⟨h1, h2⟩ := ih (iS + 111616) (h >>> 11) (acc * cand iS (h &&& 2047))
    refine ⟨(dvd_mul_right acc _).trans h1, fun j hj => ?_⟩
    rcases j with _ | j
    · simpa [tOf_zero] using (dvd_mul_left _ acc).trans h1
    · have := h2 j (by omega)
      rw [show h >>> 11 = h >>> (11 * 1) by rfl, tOf_shift] at this
      rwa [show iS + 111616 + 111616 * j = iS + 111616 * (j + 1) by ring, add_comm 1 j] at this

theorem sqPow_zero (m x : ℕ) : sqPow m 0 x = x := rfl

theorem sqPow_succ (m f : ℕ) : sqPow m (f + 1) = fun x => sqPow m f (x * x % m) := rfl

theorem sqPow_modEq (m : ℕ) : ∀ f x, sqPow m f x ≡ x ^ 2 ^ f [MOD m] := by
  intro f
  induction f with
  | zero => intro x; rw [sqPow_zero, pow_zero, pow_one]
  | succ f ih =>
    intro x
    rw [sqPow_succ]
    refine (ih _).trans ?_
    rw [pow_succ', pow_mul, _root_.sq]
    exact ((Nat.mod_modEq _ m).pow _)

theorem powM_zero (m b e r : ℕ) : powM m 0 b e r = r := rfl

theorem powM_succ (m f b e r : ℕ) : powM m (f + 1) b e r =
    Bool.rec (powM m f (b * b % m) (e >>> 1) r) (powM m f (b * b % m) (e >>> 1) (r * b % m))
      (Nat.beq (e &&& 1) 1) := rfl

theorem powM_modEq (m : ℕ) : ∀ f b e r, e < 2 ^ f → powM m f b e r ≡ r * b ^ e [MOD m] := by
  intro f
  induction f with
  | zero =>
    intro b e r he
    have : e = 0 := by simpa using he
    subst this
    rw [powM_zero, pow_zero, mul_one]
  | succ f ih =>
    intro b e r he
    rw [powM_succ, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, pow_one]
    have he2 : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
    have hbb : (b * b % m) ^ (e / 2) ≡ b ^ (2 * (e / 2)) [MOD m] := by
      rw [pow_mul, _root_.sq]; exact (Nat.mod_modEq _ m).pow _
    rcases Nat.mod_two_eq_zero_or_one e with h0 | h0
    · rw [h0]
      refine (ih _ _ _ he2).trans ?_
      rw [show 2 * (e / 2) = e by omega] at hbb
      exact hbb.mul_left r
    · rw [h0]
      refine (ih _ _ _ he2).trans ?_
      calc r * b % m * (b * b % m) ^ (e / 2) ≡ r * b * b ^ (2 * (e / 2)) [MOD m] :=
            (Nat.mod_modEq _ m).mul hbb
        _ = r * b ^ e := by rw [mul_assoc, ← pow_succ', show 2 * (e / 2) + 1 = e by omega]

theorem chk_succ (M B A n iS U h : ℕ) : chk M B A (n + 1) iS U h =
    Bool.rec false (chk M B A n (iS + 111616) (U * A % M) (h >>> 11))
      (Nat.beq ((U + (B % cand iS (h &&& 2047)) ^ (h &&& 2047) % cand iS (h &&& 2047)) %
        cand iS (h &&& 2047)) 0) := rfl

theorem chk_spec {M B A : ℕ} (hB : B ≡ 3 ^ 2 ^ 44 [MOD M]) (hA : A ≡ 3 ^ (2 ^ 44 * 111616) [MOD M]) :
    ∀ n iS U h, U ≡ 3 ^ (2 ^ 44 * iS) [MOD M] →
      (∀ j < n, cand (iS + 111616 * j) (tOf h j) ∣ M) → chk M B A n iS U h = true →
      ∀ j < n, cand (iS + 111616 * j) (tOf h j) ∣
        3 ^ (2 ^ 44 * (iS + 111616 * j)) + 3 ^ (2 ^ 44 * tOf h j) := by
  intro n
  induction n with
  | zero => intro iS U h _ _ _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    intro iS U h hU hM hc j hj
    rw [chk_succ] at hc
    set t := h &&& 2047 with ht
    set c := cand iS t with hcdef
    cases htest : Nat.beq ((U + (B % c) ^ t % c) % c) 0 with
    | false => rw [htest] at hc; exact absurd hc (by simp)
    | true =>
      rw [htest] at hc
      rcases j with _ | j
      · -- the rung itself
        have hc0 : c ∣ M := by simpa [tOf_zero, ← ht, ← hcdef] using hM 0 (by omega)
        have hdvd : c ∣ U + (B % c) ^ t % c := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true htest)
        have h1 : U ≡ 3 ^ (2 ^ 44 * iS) [MOD c] := hU.of_dvd hc0
        have h2 : (B % c) ^ t % c ≡ 3 ^ (2 ^ 44 * t) [MOD c] := by
          refine (Nat.mod_modEq _ c).trans ?_
          rw [pow_mul]
          exact ((Nat.mod_modEq _ c).pow t).trans ((hB.of_dvd hc0).pow t)
        have := (Nat.modEq_zero_iff_dvd.2 hdvd).symm.trans (h1.add h2)
        simpa [tOf_zero, ← ht, ← hcdef] using (Nat.modEq_zero_iff_dvd.1 this.symm)
      · -- the later rungs
        have hU' : U * A % M ≡ 3 ^ (2 ^ 44 * (iS + 111616)) [MOD M] := by
          refine (Nat.mod_modEq _ M).trans ?_
          rw [Nat.mul_add, pow_add]
          exact hU.mul hA
        have hM' : ∀ j < n, cand (iS + 111616 + 111616 * j) (tOf (h >>> 11) j) ∣ M := by
          intro j hj
          have := hM (j + 1) (by omega)
          rw [show h >>> 11 = h >>> (11 * 1) by rfl, tOf_shift, add_comm 1 j]
          rwa [show iS + 111616 + 111616 * j = iS + 111616 * (j + 1) by ring]
        have := ih (iS + 111616) (U * A % M) (h >>> 11) hU' hM' hc j (by omega)
        rw [show h >>> 11 = h >>> (11 * 1) by rfl, tOf_shift, add_comm 1 j] at this
        rwa [show iS + 111616 + 111616 * j = iS + 111616 * (j + 1) by ring] at this

theorem blkWith_spec {P Q W C}
    (hP : ∀ n iS h acc, ∀ j < n, cand (iS + 111616 * j) (tOf h j) ∣ P n iS h acc)
    (hQ : ∀ m f x, Q m f x ≡ x ^ 2 ^ f [MOD m])
    (hW : ∀ m f b e r, e < 2 ^ f → W m f b e r ≡ r * b ^ e [MOD m])
    (hC : ∀ {M B A : ℕ}, B ≡ 3 ^ 2 ^ 44 [MOD M] → A ≡ 3 ^ (2 ^ 44 * 111616) [MOD M] →
      ∀ n iS U h, U ≡ 3 ^ (2 ^ 44 * iS) [MOD M] →
      (∀ j < n, cand (iS + 111616 * j) (tOf h j) ∣ M) → C M B A n iS U h = true →
      ∀ j < n, cand (iS + 111616 * j) (tOf h j) ∣
        3 ^ (2 ^ 44 * (iS + 111616 * j)) + 3 ^ (2 ^ 44 * tOf h j))
    {i0 h : ℕ} (hi : i0 < 2 ^ 28) (hb : blkWith P Q W C i0 h = true) :
    ∀ j < 32, Cert (i0 + j) (tOf h j) := by
  simp only [blkWith] at hb
  set iS := i0 * 111616 with hiS
  set M := P 32 iS h 1 with hMdef
  cases h3 : Nat.beq (M % 3) 0 with
  | true => rw [h3] at hb; exact absurd hb (by simp)
  | false =>
    rw [h3] at hb
    have hM3 : ¬ 3 ∣ M := fun hd => by
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      rw [hd] at h3
      exact absurd h3 (by decide)
    have hB : Q M 44 3 ≡ 3 ^ 2 ^ 44 [MOD M] := hQ M 44 3
    have hA : W M 17 (Q M 44 3) 111616 1 ≡ 3 ^ (2 ^ 44 * 111616) [MOD M] := by
      refine (hW M 17 _ _ 1 (by norm_num)).trans ?_
      rw [one_mul, pow_mul]
      exact hB.pow _
    have hU : W M 28 (W M 17 (Q M 44 3) 111616 1) i0 1 ≡ 3 ^ (2 ^ 44 * iS) [MOD M] := by
      refine (hW M 28 _ _ 1 hi).trans ?_
      rw [one_mul, hiS, show 2 ^ 44 * (i0 * 111616) = 2 ^ 44 * 111616 * i0 by ring, pow_mul]
      exact hA.pow _
    have hdvd := hP 32 iS h 1
    have hb' : C M (Q M 44 3) (W M 17 (Q M 44 3) 111616 1) 32 iS
        (W M 28 (W M 17 (Q M 44 3) 111616 1) i0 1) h = true := hb
    intro j hj
    have e : iS + 111616 * j = 111616 * (i0 + j) := by rw [hiS]; ring
    have hcM := hdvd j hj
    rw [e] at hcM
    refine ⟨fun h3c => hM3 (h3c.trans hcM), ?_⟩
    have := hC (M := M) (B := Q M 44 3) (A := W M 17 (Q M 44 3) 111616 1) hB hA 32 iS
      (W M 28 (W M 17 (Q M 44 3) 111616 1) i0 1) h hU hdvd hb' j hj
    rwa [e] at this

theorem blk_spec {i0 h : ℕ} (hi : i0 < 2 ^ 28) (hb : blk i0 h = true) :
    ∀ j < 32, Cert (i0 + j) (tOf h j) :=
  blkWith_spec (fun n iS h acc => (prodC_dvd n iS h acc).2) sqPow_modEq powM_modEq
    (fun hB hA => chk_spec hB hA) hi hb

theorem tOf_land {h j : ℕ} (hj : j < 32) : tOf (h &&& mask352) j = tOf h j := by
  rw [mask352_eq]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [tOf, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    show (2047 : ℕ) = 2 ^ 11 - 1 by norm_num]
  by_cases hb : b < 11
  · have : 11 * j + b < 352 := by omega
    simp [hb, this]
  · simp [hb]

theorem runWith_succ (b : ℕ → ℕ → Bool) (n i0 h : ℕ) : runWith b (n + 1) i0 h =
    Bool.rec false (runWith b n (i0 + 32) (h >>> 352)) (b i0 (h &&& mask352)) := rfl

theorem runWith_spec {b : ℕ → ℕ → Bool}
    (hb : ∀ {i0 h}, i0 < 2 ^ 28 → b i0 h = true → ∀ j < 32, Cert (i0 + j) (tOf h j)) :
    ∀ n i0 h, i0 + 32 * n ≤ 2 ^ 28 → runWith b n i0 h = true →
    ∀ j < 32 * n, Cert (i0 + j) (tOf h j) := by
  intro n
  induction n with
  | zero => intro i0 h _ _ j hj; exact absurd hj (by omega)
  | succ n ih =>
    intro i0 h hn hr j hj
    rw [runWith_succ] at hr
    cases hb0 : b i0 (h &&& mask352) with
    | false => rw [hb0] at hr; exact absurd hr (by simp)
    | true =>
      rw [hb0] at hr
      by_cases hj32 : j < 32
      · have := hb (by omega) hb0 j hj32
        rwa [tOf_land hj32] at this
      · have := ih (i0 + 32) (h >>> 352) (by omega) hr (j - 32) (by omega)
        rw [show h >>> 352 = h >>> (11 * 32) by rfl, tOf_shift,
          show 32 + (j - 32) = j by omega, show i0 + 32 + (j - 32) = i0 + j by omega] at this
        exact this

theorem run_spec : ∀ n i0 h, i0 + 32 * n ≤ 2 ^ 28 → run n i0 h = true →
    ∀ j < 32 * n, Cert (i0 + j) (tOf h j) :=
  runWith_spec blk_spec

/-- **Every window of `[a, a + 4096n)` contains a prime.** -/
theorem prime_of_runsOK {a n : ℕ} (h : RunsOK a n) (ha : 1 ≤ a) (hn : a + 4096 * n ≤ 2 ^ 28)
    (hS : 111616 * (a + 4096 * n) ≤ 2 ^ 45) {i : ℕ} (hi1 : a ≤ i) (hi2 : i < a + 4096 * n) :
    ∃ p, p.Prime ∧ (111616 * i - 2047) * 2 ^ 45 + 1 ≤ p ∧ p ≤ 111616 * i * 2 ^ 45 + 1 := by
  obtain ⟨hh, hr⟩ := h ((i - a) / 4096) (by omega)
  have hc := run_spec 128 _ hh (by omega) hr ((i - a) % 4096) (by omega)
  have hi : a + 4096 * ((i - a) / 4096) + (i - a) % 4096 = i := by omega
  rw [hi] at hc
  have ht := tOf_lt hh ((i - a) % 4096)
  have hiS : 111616 * i < 2 ^ 45 := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hi2 (by norm_num)) hS
  refine ⟨_, prime_of_cert (by omega) hiS ht hc, ?_, ?_⟩
  · rw [cand_eq]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1
  · rw [cand_eq]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) 1

end TernaryGoldbach.Ladder
