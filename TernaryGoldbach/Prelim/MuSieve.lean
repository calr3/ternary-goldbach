import TernaryGoldbach.Prelim.PsiSieve

/-!
# A packed sieve for `μ` in the kernel

A window `(n, n + W]` (`W ≤ 4096`) is laid out in 8-bit fields, field `i` for `n + 1 + i`. For each prime
`p < 10007`, one doubling-built pattern adds `⌊4 log₂ p⌋` to the fields of the multiples of `p`
(`acc`), one toggles bit 7 there (`par`, the parity of the number of such `p`), and one sets bit 7 at
the multiples of `p²` (`sq`). For `m < 10007²` with no `p² ∣ m`, `m` has at most one prime factor
`≥ 10007`, and it has one exactly when the field sum is below a threshold `t` (`lg_sum_lt`,
`lg_sum_ge`): the sum is `log₂` of the `p⁴`-product of the small prime factors, up to `9`. Adding
`128 − t` to every field puts that test in bit 7 (`fld_add`). So bit 7 of `pos`/`neg` is set exactly
where `μ = 1`/`μ = −1` (`winPN_spec`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.MuSieve
open TernaryGoldbach.Prelim.SieveTab (rep sub_mod_of_dvd nbits pcL pcL_spec)

/-! ### Periodic patterns with a predicate on the residue -/

theorem rep_spec_g {p W : ℕ} {g : ℕ → Prop} [DecidablePred g] : ∀ (f m len : ℕ), p ∣ len → 0 < len →
    (∀ i, m.testBit i = decide (i < len ∧ g (i % p))) →
    ∃ len', (W ≤ len' ∨ len' = len * 2 ^ f) ∧
      ∀ i, (rep m len W f).testBit i = decide (i < len' ∧ g (i % p)) := by
  intro f
  induction f with
  | zero => intro m len _ _ hm; exact ⟨len, Or.inr (by simp), by simpa [rep] using hm⟩
  | succ f ih =>
    intro m len hl hl0 hm
    unfold rep
    split_ifs with hW
    · exact ⟨len, Or.inl hW, hm⟩
    · obtain ⟨len', h2, h3⟩ := ih (m ||| (m <<< len)) (2 * len) (dvd_mul_of_dvd_right hl 2)
        (by omega) (fun i => by
          rw [Nat.testBit_or, Nat.testBit_shiftLeft, hm]
          by_cases h : i < len
          · have h' : ¬ len ≤ i := by omega
            simp [h, h', show i < 2 * len by omega]
          · push Not at h
            rw [hm, sub_mod_of_dvd hl h]
            have h1 : ¬ i < len := by omega
            by_cases h2 : i < 2 * len
            · simp [h1, h2, h, show i - len < len by omega]
            · simp [h1, h2, h, show ¬ i - len < len by omega])
      refine ⟨len', ?_, h3⟩
      rcases h2 with h2 | h2
      · exact Or.inl h2
      · right; rw [h2, pow_succ]; ring

/-- A pattern of period `per` on the bits `< L`, from the base `m < 2^per`, built by doubling. -/
def patt (m per L : ℕ) : ℕ := rep m per L 64 &&& ((1 <<< L) - 1)

theorem patt_spec {m per L : ℕ} (hper : 0 < per) (hm : m < 2 ^ per) (hL : L ≤ 2 ^ 64) (i : ℕ) :
    (patt m per L).testBit i = decide (i < L ∧ m.testBit (i % per)) := by
  obtain ⟨len', h1, h2⟩ := rep_spec_g (p := per) (W := L) (g := fun k => m.testBit k = true) 64 m per
    dvd_rfl hper (fun i => by
      by_cases hi : i < per
      · simp [hi, Nat.mod_eq_of_lt hi]
      · have : m.testBit i = false := Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [hi, this])
  unfold patt
  rw [Nat.testBit_and, h2, show (1 <<< L) - 1 = 2 ^ L - 1 by rw [Nat.one_shiftLeft],
    Nat.testBit_two_pow_sub_one]
  have hL' : L ≤ len' := by
    rcases h1 with h1 | h1
    · exact h1
    · rw [h1]; calc L ≤ 2 ^ 64 := hL
        _ ≤ per * 2 ^ 64 := Nat.le_mul_of_pos_left _ hper
  by_cases hi : i < L
  · simp [hi, show i < len' by omega]
  · simp [hi]

/-! ### 8-bit fields -/

/-- Field `i` of `x`. -/
def fld (x i : ℕ) : ℕ := (x >>> (8 * i)) % 256

theorem fld_lt (x i : ℕ) : fld x i < 256 := Nat.mod_lt _ (by norm_num)

theorem fld_eq_div (x i : ℕ) : fld x i = x / 256 ^ i % 256 := by
  unfold fld; rw [Nat.shiftRight_eq_div_pow, pow_mul]; norm_num

theorem testBit_fld (x i b : ℕ) : (fld x i).testBit b = (decide (b < 8) && x.testBit (8 * i + b)) := by
  unfold fld
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    add_comm]

theorem fld_eq_of_bits {x i v : ℕ} (hv : v < 256) (h : ∀ b < 8, x.testBit (8 * i + b) = v.testBit b) :
    fld x i = v := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld]
  by_cases hb : b < 8
  · simp [hb, h b hb]
  · have : v.testBit b = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hv (by rw [show (256 : ℕ) = 2 ^ 8 by norm_num]
                             exact Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hb, this]

/-- The base-256 value of the digits `c 0, …, c (W − 1)`. -/
def pack (c : ℕ → ℕ) (W : ℕ) : ℕ := ∑ i ∈ range W, c i * 256 ^ i

theorem pack_succ (c : ℕ → ℕ) (W : ℕ) : pack c (W + 1) = c 0 + 256 * pack (fun i => c (i + 1)) W := by
  unfold pack
  rw [sum_range_succ', mul_sum]
  simp only [pow_zero, mul_one, pow_succ]
  rw [add_comm]; congr 1
  exact sum_congr rfl fun i _ => by ring

theorem pack_lt {c : ℕ → ℕ} : ∀ {W : ℕ}, (∀ i < W, c i < 256) → pack c W < 256 ^ W
  | 0, _ => by simp [pack]
  | W + 1, h => by
    rw [pack_succ, pow_succ]
    have := pack_lt (c := fun i => c (i + 1)) (W := W) (fun i hi => h (i + 1) (by omega))
    have h0 := h 0 (by omega)
    nlinarith

theorem fld_pack {c : ℕ → ℕ} : ∀ {W : ℕ}, (∀ i < W, c i < 256) → ∀ j < W, fld (pack c W) j = c j
  | 0, _, j, hj => absurd hj (by omega)
  | W + 1, h, j, hj => by
    rw [pack_succ]
    have h0 := h 0 (by omega)
    rcases j with _ | j
    · simp only [fld, mul_zero, Nat.shiftRight_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    · have ih := fld_pack (c := fun i => c (i + 1)) (W := W) (fun i hi => h (i + 1) (by omega)) j (by omega)
      rw [fld_eq_div] at ih ⊢
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num),
        Nat.div_eq_of_lt h0, zero_add]
      exact ih

theorem eq_pack : ∀ {W x : ℕ}, x < 256 ^ W → x = pack (fld x) W
  | 0, x, h => by simp [pack] at h ⊢; omega
  | W + 1, x, h => by
    rw [pack_succ]
    have h1 : x / 256 < 256 ^ W := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h
    have ih := eq_pack h1
    have e : (fun i => fld x (i + 1)) = fld (x / 256) := by
      funext i; rw [fld_eq_div, fld_eq_div, pow_succ', ← Nat.div_div_eq_div_mul]
    rw [e, ← ih]
    simp only [fld, mul_zero, Nat.shiftRight_zero]
    omega

/-- `x` has fields `v i` below `W`, and nothing above. -/
def Pk (x W : ℕ) (v : ℕ → ℕ) : Prop := x < 256 ^ W ∧ ∀ i < W, fld x i = v i

theorem Pk_add {a b W : ℕ} {va vb : ℕ → ℕ} (ha : Pk a W va) (hb : Pk b W vb)
    (hs : ∀ i < W, va i + vb i < 256) : Pk (a + b) W (fun i => va i + vb i) := by
  have ea := eq_pack ha.1
  have eb := eq_pack hb.1
  have e : a + b = pack (fun i => fld a i + fld b i) W := by
    have e2 : pack (fld a) W + pack (fld b) W = pack (fun i => fld a i + fld b i) W := by
      unfold pack; rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [← e2, ← ea, ← eb]
  have hs' : ∀ i < W, fld a i + fld b i < 256 := fun i hi => by rw [ha.2 i hi, hb.2 i hi]; exact hs i hi
  refine ⟨by rw [e]; exact pack_lt hs', fun i hi => ?_⟩
  rw [e, fld_pack hs' i hi, ha.2 i hi, hb.2 i hi]

theorem Pk_zero (W : ℕ) : Pk 0 W (fun _ => 0) :=
  ⟨by positivity, fun i _ => by simp [fld]⟩

theorem Pk_mul {a W c : ℕ} {va : ℕ → ℕ} (ha : Pk a W va) (hc : ∀ i < W, c * va i < 256) :
    Pk (c * a) W (fun i => c * va i) := by
  induction c with
  | zero => simpa using Pk_zero W
  | succ c ih =>
    have ih' := ih (fun i hi => lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ c)) (hc i hi))
    have := Pk_add ih' ha (fun i hi => by have := hc i hi; rw [Nat.succ_mul] at this; exact this)
    simpa [Nat.succ_mul] using this

/-- From bits: `x < 2^(8W)` and its fields have bits `v`. -/
theorem Pk_of_bits {x W : ℕ} {v : ℕ → ℕ} (hx : x < 2 ^ (8 * W)) (hv : ∀ i < W, v i < 256)
    (h : ∀ i < W, ∀ b < 8, x.testBit (8 * i + b) = (v i).testBit b) : Pk x W v :=
  ⟨by rw [pow_mul] at hx; simpa using hx, fun i hi => fld_eq_of_bits (hv i hi) (h i hi)⟩

theorem lt_two_pow_of_bits {x B : ℕ} (h : ∀ k, B ≤ k → x.testBit k = false) : x < 2 ^ B :=
  Nat.lt_pow_two_of_testBit _ fun k hk => h k hk

theorem testBit_7_of_fld {x i : ℕ} : x.testBit (8 * i + 7) = decide (128 ≤ fld x i) := by
  have h := testBit_fld x i 7
  simp only [show (7 : ℕ) < 8 by norm_num, decide_true, Bool.true_and] at h
  rw [← h]
  have hl := fld_lt x i
  rw [Nat.testBit_eq_decide_div_mod_eq, show (2 : ℕ) ^ 7 = 128 by norm_num]
  by_cases h1 : 128 ≤ fld x i
  · have : fld x i / 128 = 1 := by omega
    simp [this, h1]
  · have : fld x i / 128 = 0 := by omega
    simp [this, h1]

/-! ### The window -/

def WM : ℕ := 4096

/-- `⌊log₂ p⁴⌋`. -/
def lgN (p : ℕ) : ℕ := Nat.log2 (p ^ 4)

/-- The patterns of `p`: `(p, ⌊4 log₂ p⌋ at multiples of p, bit 7 at multiples of p, bit 7 at
multiples of p² (or 0 when p² > 4096))`. -/
def mkRec (p : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (p, patt (lgN p) (8 * p) (8 * (WM + p)), patt (1 <<< 7) (8 * p) (8 * (WM + p)),
    if p * p ≤ WM then patt (1 <<< 7) (8 * (p * p)) (8 * (WM + p * p)) else 0)

/-- Shift a pattern of period `q` into the window `(n, n + W]`. -/
def piece (pt q n W : ℕ) : ℕ := (pt >>> (8 * ((n + 1) % q))) &&& ((1 <<< (8 * W)) - 1)

theorem testBit_mask (W k : ℕ) : ((1 <<< (8 * W)) - 1).testBit k = decide (k < 8 * W) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem piece_spec {m q n W : ℕ} (hm : m < 256) (hq : 0 < q) (hW : W ≤ WM) (hL : 8 * (WM + q) ≤ 2 ^ 64)
    {i b : ℕ} (hi : i < W) (hb : b < 8) :
    (piece (patt m (8 * q) (8 * (WM + q))) q n W).testBit (8 * i + b) =
      (decide ((n + 1 + i) % q = 0) && m.testBit b) := by
  have hm' : m < 2 ^ (8 * q) := lt_of_lt_of_le hm (by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ (8 * q) := Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold piece
  rw [Nat.testBit_and, testBit_mask, Nat.testBit_shiftRight, patt_spec (by omega) hm' hL]
  set r := (n + 1) % q with hr
  have hrq : r < q := Nat.mod_lt _ hq
  have e1 : 8 * r + (8 * i + b) = 8 * (r + i) + b := by ring
  rw [e1]
  have e2 : (8 * (r + i) + b) % (8 * q) = 8 * ((r + i) % q) + b := by
    rw [show 8 * (r + i) + b = b + 8 * (r + i) by ring, Nat.add_mod, Nat.mul_mod_mul_left,
      Nat.mod_eq_of_lt (show b < 8 * q by omega)]
    have : b + 8 * ((r + i) % q) < 8 * q := by have := Nat.mod_lt (r + i) hq; omega
    rw [Nat.mod_eq_of_lt this]; ring
  rw [e2]
  have e3 : (r + i) % q = (n + 1 + i) % q := by rw [hr, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [e3]
  have hlt : 8 * (r + i) + b < 8 * (WM + q) := by omega
  have hlt2 : 8 * i + b < 8 * W := by omega
  by_cases h0 : (n + 1 + i) % q = 0
  · simp [h0, hlt, hlt2]
  · have hbig : m.testBit (8 * ((n + 1 + i) % q) + b) = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hm (by
        calc 256 = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ (8 * ((n + 1 + i) % q) + b) := Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [h0, hbig]

theorem piece_lt (pt q n W : ℕ) : piece pt q n W < 2 ^ (8 * W) :=
  lt_two_pow_of_bits fun k hk => by unfold piece; rw [Nat.testBit_and, testBit_mask]; simp; omega

/-- One window: `(acc, par, sq)` over the patterns `rs`. -/
def winAcc (n W : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | [], s => s
  | (p, pl, pb, pq) :: rs, (acc, par, sq) =>
    let sq' := if pq = 0 then
        (let j := (p * p - (n + 1) % (p * p)) % (p * p)
         if j < W then sq ||| (1 <<< (8 * j + 7)) else sq)
      else sq ||| piece pq (p * p) n W
    winAcc n W rs (acc + piece pl p n W, par ^^^ piece pb p n W, sq')

/-- The sum of `⌊4 log₂ p⌋` over the `p ∈ ps` dividing `m`. -/
def lgSum (ps : List ℕ) (m : ℕ) : ℕ := ((ps.filter (· ∣ m)).map lgN).sum

/-- The number of `p ∈ ps` dividing `m`. -/
def dvdCount (ps : List ℕ) (m : ℕ) : ℕ := (ps.filter (· ∣ m)).length

theorem lgN_lt (p : ℕ) (hp : p < 10007) : lgN p < 256 := by
  unfold lgN
  have h1 : p ^ 4 < 2 ^ 256 := lt_of_lt_of_le (Nat.pow_lt_pow_left hp (by norm_num)) (by norm_num)
  rcases eq_or_ne (p ^ 4) 0 with h0 | h0
  · rw [h0]; simp
  · exact (Nat.log2_lt h0).2 h1

theorem winAcc_spec {n W : ℕ} (hW : W ≤ WM) : ∀ (ps : List ℕ) (acc par sq : ℕ) (va : ℕ → ℕ),
    (∀ p ∈ ps, 0 < p ∧ p < 10007) → Pk acc W va →
    (∀ i < W, va i + lgSum ps (n + 1 + i) < 256) →
    let r := winAcc n W (ps.map mkRec) (acc, par, sq)
    Pk r.1 W (fun i => va i + lgSum ps (n + 1 + i)) ∧
    (∀ i < W, r.2.1.testBit (8 * i + 7) =
      (par.testBit (8 * i + 7) ^^ decide (dvdCount ps (n + 1 + i) % 2 = 1))) ∧
    (∀ i < W, r.2.2.testBit (8 * i + 7) =
      (sq.testBit (8 * i + 7) || decide (∃ p ∈ ps, p * p ∣ n + 1 + i))) := by
  intro ps
  induction ps with
  | nil =>
    intro acc par sq va _ hacc _
    simp only [List.map_nil, winAcc]
    refine ⟨by simpa [lgSum] using hacc, fun i _ => by simp [dvdCount], fun i _ => by simp⟩
  | cons p ps ih =>
    intro acc par sq va hps hacc hs
    obtain ⟨hp0, hp1⟩ := hps p (by simp)
    have hL : 8 * (WM + p) ≤ 2 ^ 64 := by unfold WM; omega
    have hlg := lgN_lt p hp1
    -- the new accumulator
    have hpiece : Pk (piece (patt (lgN p) (8 * p) (8 * (WM + p))) p n W) W
        (fun i => if p ∣ n + 1 + i then lgN p else 0) := by
      refine Pk_of_bits (piece_lt _ _ _ _) (fun i _ => by split_ifs <;> omega) fun i hi b hb => ?_
      rw [piece_spec hlg hp0 hW hL hi hb]
      by_cases hd : p ∣ n + 1 + i
      · rw [if_pos hd, Nat.mod_eq_zero_of_dvd hd]; simp
      · have : ¬ (n + 1 + i) % p = 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
        rw [if_neg hd]; simp [this]
    have hsum : ∀ i, lgSum (p :: ps) (n + 1 + i) =
        (if p ∣ n + 1 + i then lgN p else 0) + lgSum ps (n + 1 + i) := by
      intro i; unfold lgSum; by_cases hd : p ∣ n + 1 + i <;> simp [List.filter_cons, hd]
    have hacc' := Pk_add hacc hpiece (fun i hi => by have := hs i hi; rw [hsum] at this; omega)
    have ih' := ih (acc + piece (patt (lgN p) (8 * p) (8 * (WM + p))) p n W)
      (par ^^^ piece (patt (1 <<< 7) (8 * p) (8 * (WM + p))) p n W)
      (if (if p * p ≤ WM then patt (1 <<< 7) (8 * (p * p)) (8 * (WM + p * p)) else 0) = 0 then
        (let j := (p * p - (n + 1) % (p * p)) % (p * p)
         if j < W then sq ||| (1 <<< (8 * j + 7)) else sq)
      else sq ||| piece (if p * p ≤ WM then patt (1 <<< 7) (8 * (p * p)) (8 * (WM + p * p)) else 0)
        (p * p) n W)
      _ (fun q hq => hps q (by simp [hq])) hacc'
      (fun i hi => by have := hs i hi; rw [hsum] at this; omega)
    simp only [List.map_cons, mkRec, winAcc] at ih' ⊢
    obtain ⟨i1, i2, i3⟩ := ih'
    refine ⟨?_, ?_, ?_⟩
    · convert i1 using 2; rw [hsum]; ring
    · intro i hi
      rw [i2 i hi, Nat.testBit_xor]
      have hb := piece_spec (m := 1 <<< 7) (q := p) (n := n) (by norm_num) hp0 hW hL hi (b := 7) (by norm_num)
      rw [hb]
      have hc : dvdCount (p :: ps) (n + 1 + i) =
          (if p ∣ n + 1 + i then 1 else 0) + dvdCount ps (n + 1 + i) := by
        unfold dvdCount; by_cases hd : p ∣ n + 1 + i <;> simp [List.filter_cons, hd]; omega
      rw [hc]
      have h7 : (1 <<< 7 : ℕ).testBit 7 = true := by decide
      by_cases hd : p ∣ n + 1 + i
      · have : (n + 1 + i) % p = 0 := Nat.mod_eq_zero_of_dvd hd
        simp only [this, h7, if_pos hd, decide_true, Bool.true_and]
        rcases Nat.mod_two_eq_zero_or_one (dvdCount ps (n + 1 + i)) with h | h <;>
          simp [h, Nat.add_mod, Bool.xor_assoc]
      · have : ¬ (n + 1 + i) % p = 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
        simp [this, hd]
    · intro i hi
      rw [i3 i hi]
      have hcase : (if (if p * p ≤ WM then patt (1 <<< 7) (8 * (p * p)) (8 * (WM + p * p)) else 0) = 0 then
          (let j := (p * p - (n + 1) % (p * p)) % (p * p)
           if j < W then sq ||| (1 <<< (8 * j + 7)) else sq)
          else sq ||| piece (if p * p ≤ WM then patt (1 <<< 7) (8 * (p * p)) (8 * (WM + p * p)) else 0)
            (p * p) n W).testBit (8 * i + 7) =
          (sq.testBit (8 * i + 7) || decide (p * p ∣ n + 1 + i)) := by
        have hpp : 0 < p * p := Nat.mul_pos hp0 hp0
        by_cases hsmall : p * p ≤ WM
        · have hne : patt (1 <<< 7) (8 * (p * p)) (8 * (WM + p * p)) ≠ 0 := by
            have h7 : (1 <<< 7 : ℕ).testBit 7 = true := by decide
            have h := patt_spec (m := 1 <<< 7) (per := 8 * (p * p)) (L := 8 * (WM + p * p)) (by omega)
              (lt_of_lt_of_le (by norm_num : (1 <<< 7 : ℕ) < 2 ^ 8) (Nat.pow_le_pow_right (by norm_num) (by omega)))
              (by unfold WM at hsmall ⊢; omega) 7
            rw [Nat.mod_eq_of_lt (show 7 < 8 * (p * p) by omega), h7] at h
            intro h0
            rw [h0, Nat.zero_testBit] at h
            have : 7 < 8 * (WM + p * p) := by unfold WM; omega
            simp [this] at h
          rw [if_pos hsmall, if_neg hne, Nat.testBit_or,
            piece_spec (by norm_num) hpp hW (by unfold WM at hsmall ⊢; omega) hi (by norm_num)]
          have h7 : (1 <<< 7 : ℕ).testBit 7 = true := by decide
          rw [h7, Bool.and_true]
          congr 1
        · rw [if_neg hsmall, if_pos rfl]
          simp only
          set j := (p * p - (n + 1) % (p * p)) % (p * p) with hj
          have hjiff : (p * p ∣ n + 1 + i) ↔ i = j := by
            have hiW : i < p * p := by unfold WM at hsmall hW; omega
            have hr := Nat.mod_lt (n + 1) hpp
            constructor
            · intro hd
              have h1 := Nat.mod_eq_zero_of_dvd hd
              rw [hj]
              have : (n + 1 + i) % (p * p) = ((n + 1) % (p * p) + i) % (p * p) := by
                rw [Nat.add_mod, Nat.add_mod_mod]
              rw [this] at h1
              rcases Nat.eq_zero_or_pos ((n + 1) % (p * p)) with h0 | h0
              · rw [h0, zero_add, Nat.mod_eq_of_lt hiW] at h1
                rw [h0, Nat.sub_zero, Nat.mod_self, h1]
              · have : (n + 1) % (p * p) + i = p * p := by
                  have h2 : (n + 1) % (p * p) + i < 2 * (p * p) := by omega
                  have h3 : 0 < (n + 1) % (p * p) + i := by omega
                  rcases Nat.lt_or_ge ((n + 1) % (p * p) + i) (p * p) with h4 | h4
                  · rw [Nat.mod_eq_of_lt h4] at h1; omega
                  · have : ((n + 1) % (p * p) + i) % (p * p) = (n + 1) % (p * p) + i - p * p := by
                      rw [Nat.mod_eq_sub_mod h4, Nat.mod_eq_of_lt (by omega)]
                    omega
                rw [Nat.mod_eq_of_lt (by omega)]; omega
            · intro hij
              apply Nat.dvd_of_mod_eq_zero
              rw [hij, hj, Nat.add_mod, Nat.mod_mod]
              rcases Nat.eq_zero_or_pos ((n + 1) % (p * p)) with h0 | h0
              · rw [h0]; simp
              · rw [Nat.mod_eq_of_lt (show p * p - (n + 1) % (p * p) < p * p by omega),
                  show (n + 1) % (p * p) + (p * p - (n + 1) % (p * p)) = p * p by omega, Nat.mod_self]
          split_ifs with hjW
          · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
            by_cases hij : i = j
            · subst hij; simp [hjiff.2 rfl]
            · have : ¬ p * p ∣ n + 1 + i := fun h => hij (hjiff.1 h)
              have h2 : ¬ 8 * j + 7 = 8 * i + 7 := by omega
              have h3 : ¬ j = i := fun h => hij h.symm
              simp [this, h2, h3]
          · have : ¬ p * p ∣ n + 1 + i := fun h => by have := hjiff.1 h; omega
            simp [this]
      rw [hcase]
      simp only [List.mem_cons, exists_eq_or_imp]
      rw [Bool.decide_or, Bool.or_assoc]

/-! ### The primes below `10007` -/

/-- Trial division by `2, …, 100` (`101² > 10006`). -/
def isPrimeM (n : ℕ) : Bool := 2 ≤ n && (List.range' 2 99).all (fun d => n < d * d || n % d != 0)

theorem isPrimeM_iff {n : ℕ} (hn : n ≤ 10006) : isPrimeM n = true ↔ n.Prime := by
  unfold isPrimeM
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hsq : Nat.minFac n * Nat.minFac n ≤ n := by
      have := Nat.minFac_sq_le_self (by omega) (fun hp => hne (Nat.Prime.minFac_eq hp)); nlinarith
    have hm2 := hmp.two_le
    have hm : Nat.minFac n ≤ 100 := by nlinarith
    rcases h (Nat.minFac n) ⟨hm2, by omega⟩ with h1 | h1
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro hp
    refine ⟨hp.two_le, fun d hd => ?_⟩
    by_cases hdd : n < d * d
    · exact Or.inl hdd
    · right
      intro h0
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h0
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · omega
      · subst h; nlinarith [hp.two_le]

/-- The primes below `10007`. -/
def PSm : List ℕ := (List.range 10007).filter isPrimeM

theorem mem_PSm {p : ℕ} : p ∈ PSm ↔ p < 10007 ∧ p.Prime := by
  unfold PSm
  rw [List.mem_filter, List.mem_range]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (isPrimeM_iff (by omega)).1 h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, (isPrimeM_iff (by omega)).2 h2⟩⟩

theorem PSm_nodup : PSm.Nodup := (List.nodup_range).filter _

/-! ### `μ` from the three tests -/

open ArithmeticFunction in
/-- For `1 ≤ m < 10007²` with no `p² ∣ m`, `p < 10007` prime: `m` is squarefree, and its prime factors
are the small ones `Sm` and at most one more, which exists exactly when `∏ Sm ≠ m`. -/
theorem mu_struct {m : ℕ} (hm1 : 1 ≤ m) (hm : m < 10007 ^ 2)
    (hsq : ∀ p, p.Prime → p < 10007 → ¬ p * p ∣ m) :
    let Sm := m.primeFactors.filter (· < 10007)
    let Lg := m.primeFactors.filter (fun p => ¬ p < 10007)
    Squarefree m ∧ (μ m : ℤ) = (-1) ^ (Sm.card + Lg.card) ∧ Lg.card ≤ 1 ∧
      (∏ p ∈ Sm, p) * (∏ p ∈ Lg, p) = m ∧ (Lg = ∅ ↔ ∏ p ∈ Sm, p = m) := by
  intro Sm Lg
  have hm0 : m ≠ 0 := by omega
  have hsf : Squarefree m := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hxp hxx
    by_cases hx1 : x < 10007
    · exact hsq x hxp hx1 hxx
    · have : 10007 ^ 2 ≤ x * x := by push Not at hx1; nlinarith
      have := Nat.le_of_dvd (by omega) hxx
      omega
  have hprod : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hsf
  have hsplit : (∏ p ∈ Sm, p) * (∏ p ∈ Lg, p) = m := by
    rw [← hprod]; exact Finset.prod_filter_mul_prod_filter_not _ _ (fun p => p)
  have hcard : m.primeFactors.card = Sm.card + Lg.card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have hmu : (μ m : ℤ) = (-1) ^ m.primeFactors.card := by
    rw [moebius_apply_of_squarefree hsf, cardFactors_apply]
    congr 1
    rw [Nat.primeFactors, List.toFinset_card_of_nodup (Squarefree.nodup_primeFactorsList hsf)]
  have hSpos : 0 < ∏ p ∈ Sm, p := Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos
  have hLge : 10007 ^ Lg.card ≤ ∏ p ∈ Lg, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => by have := (Finset.mem_filter.1 hp).2; omega
  have hLle : ∏ p ∈ Lg, p ≤ m := by
    rw [← hsplit]; exact Nat.le_mul_of_pos_left _ hSpos
  have hL1 : Lg.card ≤ 1 := by
    by_contra h
    have : 10007 ^ 2 ≤ 10007 ^ Lg.card := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨hsf, by rw [hmu, hcard], hL1, hsplit, ⟨fun h => by rw [← hsplit, h]; simp, fun h => ?_⟩⟩
  by_contra hne
  obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have h1 : 10007 ≤ ∏ p ∈ Lg, p := by
    have hdvd : q ∣ ∏ p ∈ Lg, p := Finset.dvd_prod_of_mem (fun p => p) hq
    have hpos : 0 < ∏ p ∈ Lg, p := Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos
    have := Nat.le_of_dvd hpos hdvd
    have hq2 := (Finset.mem_filter.1 hq).2
    omega
  rw [h] at hsplit
  have : m < m * ∏ p ∈ Lg, p := by nlinarith
  omega

theorem lgN_bounds {p : ℕ} (hp : 0 < p) : 2 ^ lgN p ≤ p ^ 4 ∧ p ^ 4 < 2 ^ (lgN p + 1) := by
  have h0 : p ^ 4 ≠ 0 := by positivity
  exact ⟨Nat.log2_self_le h0, (Nat.log2_lt h0).1 (Nat.lt_succ_self _)⟩

/-- `2^Σ ≤ (∏ S)⁴ ≤ 2^(Σ + |S|)` for a finset of positive integers. -/
theorem lgN_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) :
    2 ^ (∑ p ∈ S, lgN p) ≤ (∏ p ∈ S, p) ^ 4 ∧ (∏ p ∈ S, p) ^ 4 ≤ 2 ^ (∑ p ∈ S, lgN p + S.card) := by
  rw [← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  constructor
  · exact Finset.prod_le_prod' fun p hp => (lgN_bounds (hS p hp)).1
  · rw [show ∑ p ∈ S, lgN p + S.card = ∑ p ∈ S, (lgN p + 1) by rw [Finset.sum_add_distrib]; simp,
      ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun p hp => (lgN_bounds (hS p hp)).2.le

/-- The list sums are the finset sums over the small prime factors. -/
theorem PSm_filter_toFinset (m : ℕ) (hm : m ≠ 0) :
    (PSm.filter (· ∣ m)).toFinset = m.primeFactors.filter (· < 10007) := by
  ext p
  simp only [List.mem_toFinset, List.mem_filter, mem_PSm, decide_eq_true_eq, Finset.mem_filter,
    Nat.mem_primeFactors]
  tauto

theorem lgSum_eq (m : ℕ) (hm : m ≠ 0) : lgSum PSm m = ∑ p ∈ m.primeFactors.filter (· < 10007), lgN p := by
  rw [← PSm_filter_toFinset m hm, List.sum_toFinset _ (PSm_nodup.filter _)]
  rfl

theorem dvdCount_eq (m : ℕ) (hm : m ≠ 0) : dvdCount PSm m = (m.primeFactors.filter (· < 10007)).card := by
  rw [← PSm_filter_toFinset m hm, List.toFinset_card_of_nodup (PSm_nodup.filter _)]
  rfl

theorem sq_iff (m : ℕ) : (∃ p ∈ PSm, p * p ∣ m) ↔ ∃ p, p.Prime ∧ p < 10007 ∧ p * p ∣ m := by
  simp only [mem_PSm]; tauto

/-- **The threshold**: for `n < m ≤ n + W` with no small `p² ∣ m`, `2^(t + 26) ≤ (n+1)⁴` and
`(n + W)⁴ < 2^t 10007⁴`, the field sum is `≥ t` iff `m` has no prime factor `≥ 10007`. -/
theorem threshold {n W t m : ℕ} (h1 : n + 1 ≤ m) (h2 : m ≤ n + W) (hm10 : m < 10007 ^ 2)
    (ht1 : 2 ^ (t + 26) ≤ (n + 1) ^ 4) (ht2 : (n + W) ^ 4 < 2 ^ t * 10007 ^ 4)
    (hsq : ∀ p, p.Prime → p < 10007 → ¬ p * p ∣ m) :
    lgSum PSm m < 108 ∧
      (t ≤ lgSum PSm m ↔ m.primeFactors.filter (fun p => ¬ p < 10007) = ∅) := by
  have hm0 : m ≠ 0 := by omega
  have hm : m < 2 ^ 27 := by omega
  obtain ⟨-, -, -, hsplit, hiff⟩ := mu_struct (by omega) hm10 hsq
  set Sm := m.primeFactors.filter (· < 10007)
  set Lg := m.primeFactors.filter (fun p => ¬ p < 10007)
  rw [lgSum_eq m hm0]
  have hpos : ∀ p ∈ Sm, 0 < p := fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos
  obtain ⟨b1, b2⟩ := lgN_prod Sm hpos
  set Sg := ∑ p ∈ Sm, lgN p
  set s := ∏ p ∈ Sm, p
  have hs_le : s ≤ m := by
    rw [← hsplit]; exact Nat.le_mul_of_pos_right _ (Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos)
  have hm4 : m ^ 4 < 2 ^ 108 := by
    calc m ^ 4 < (2 ^ 27) ^ 4 := Nat.pow_lt_pow_left hm (by norm_num)
      _ = 2 ^ 108 := by norm_num
  have hcard : Sm.card ≤ 26 := by
    have : 2 ^ Sm.card ≤ s := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod' fun p hp =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
    by_contra h
    have : 2 ^ 27 ≤ 2 ^ Sm.card := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hS108 : Sg < 108 := by
    have : 2 ^ Sg < 2 ^ 108 := lt_of_le_of_lt b1 (lt_of_le_of_lt (Nat.pow_le_pow_left hs_le 4) hm4)
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  refine ⟨hS108, ⟨fun h => ?_, fun h => ?_⟩⟩
  · -- `t ≤ Σ` forces `Lg = ∅`
    by_contra hne
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hq1 : 10007 ≤ ∏ p ∈ Lg, p := by
      have hdvd : q ∣ ∏ p ∈ Lg, p := Finset.dvd_prod_of_mem (fun p => p) hq
      have hpos : 0 < ∏ p ∈ Lg, p := Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos
      have := Nat.le_of_dvd hpos hdvd
      have hq2 := (Finset.mem_filter.1 hq).2
      omega
    have hsm : s * 10007 ≤ m := by rw [← hsplit]; exact Nat.mul_le_mul_left _ hq1
    have h4 : s ^ 4 * 10007 ^ 4 ≤ (n + W) ^ 4 := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 4
    have h5 : 2 ^ t ≤ 2 ^ Sg := Nat.pow_le_pow_right (by norm_num) h
    have : s ^ 4 * 10007 ^ 4 < 2 ^ t * 10007 ^ 4 := lt_of_le_of_lt h4 ht2
    have : s ^ 4 < 2 ^ t := lt_of_mul_lt_mul_right this (by positivity)
    omega
  · -- `Lg = ∅`: `s = m`
    have hsm : s = m := hiff.1 h
    have h3 : 2 ^ (t + 26) ≤ 2 ^ (Sg + 26) := by
      calc 2 ^ (t + 26) ≤ (n + 1) ^ 4 := ht1
        _ ≤ m ^ 4 := Nat.pow_le_pow_left h1 4
        _ = s ^ 4 := by rw [hsm]
        _ ≤ 2 ^ (Sg + Sm.card) := b2
        _ ≤ 2 ^ (Sg + 26) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
    omega

theorem lgSum_lt {m : ℕ} (hm0 : m ≠ 0) (hm : m < 2 ^ 27) : lgSum PSm m < 108 := by
  rw [lgSum_eq m hm0]
  set Sm := m.primeFactors.filter (· < 10007)
  have hpos : ∀ p ∈ Sm, 0 < p := fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos
  have b1 := (lgN_prod Sm hpos).1
  have hdvd : ∏ p ∈ Sm, p ∣ m :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd m)
  have hle : ∏ p ∈ Sm, p ≤ m := Nat.le_of_dvd (by omega) hdvd
  have hm4 : m ^ 4 < 2 ^ 108 := by
    calc m ^ 4 < (2 ^ 27) ^ 4 := Nat.pow_lt_pow_left hm (by norm_num)
      _ = 2 ^ 108 := by norm_num
  have : 2 ^ (∑ p ∈ Sm, lgN p) < 2 ^ 108 := lt_of_le_of_lt b1 (lt_of_le_of_lt (Nat.pow_le_pow_left hle 4) hm4)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this

/-! ### The window counts -/

def recs : List (ℕ × ℕ × ℕ × ℕ) := PSm.map mkRec

def onesW (W : ℕ) : ℕ := patt 1 8 (8 * W)
def hib (W : ℕ) : ℕ := patt (1 <<< 7) 8 (8 * W)

theorem testBit_hib {W : ℕ} (hW : W ≤ WM) (k : ℕ) : (hib W).testBit k = decide (k < 8 * W ∧ k % 8 = 7) := by
  unfold hib
  rw [patt_spec (by norm_num) (by norm_num) (by unfold WM at hW; omega)]
  congr 1
  apply propext
  have : (1 <<< 7 : ℕ).testBit (k % 8) = decide (k % 8 = 7) := by
    have h8 := Nat.mod_lt k (show 0 < 8 by norm_num)
    interval_cases (k % 8) <;> decide
  rw [this]; simp

theorem Pk_onesW {W : ℕ} (hW : W ≤ WM) : Pk (onesW W) W (fun _ => 1) := by
  refine Pk_of_bits ?_ (fun _ _ => by norm_num) fun i hi b hb => ?_
  · exact lt_two_pow_of_bits fun k hk => by
      unfold onesW; rw [patt_spec (by norm_num) (by norm_num) (by unfold WM at hW; omega)]; simp; omega
  · unfold onesW
    rw [patt_spec (by norm_num) (by norm_num) (by unfold WM at hW; omega)]
    have : (8 * i + b) % 8 = b := by omega
    rw [this]
    have h1 : 8 * i + b < 8 * W := by omega
    simp only [h1, true_and, decide_eq_decide]
    interval_cases b <;> decide

/-- The counts of `μ = 1` and `μ = −1` on `(n, n + W]`, for the threshold `t`. -/
noncomputable def winPN (n W t : ℕ) : ℕ × ℕ :=
  let r := winAcc n W recs (0, 0, 0)
  let h := hib W
  let B0 := (r.1 + (128 - t) * onesW W) &&& h
  let sqf := h ^^^ (r.2.2 &&& h)
  let neg := sqf &&& (r.2.1 ^^^ (h ^^^ B0))
  (pcL 7 (sqf ^^^ neg), pcL 7 neg)

/-- The conditions on a window. -/
def WinOK (n W t : ℕ) : Prop :=
  1 ≤ W ∧ W ≤ WM ∧ n + W < 10007 ^ 2 ∧ t ≤ 128 ∧ 2 ^ (t + 26) ≤ (n + 1) ^ 4 ∧
    (n + W) ^ 4 < 2 ^ t * 10007 ^ 4

instance (n W t : ℕ) : Decidable (WinOK n W t) := by unfold WinOK; infer_instance

theorem nbits_stride {y W B : ℕ} (hB : 8 * W ≤ B) (hy : ∀ k, y.testBit k = true → k < 8 * W ∧ k % 8 = 7) :
    nbits B y = ((range W).filter (fun i => y.testBit (8 * i + 7) = true)).card := by
  unfold nbits
  rw [Finset.sum_boole]
  rw [← Finset.card_image_of_injective ((range W).filter (fun i => y.testBit (8 * i + 7) = true))
    (f := fun i => 8 * i + 7) (fun a b h => by simp only at h; omega)]
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hk, hb⟩
    obtain ⟨h1, h2⟩ := hy k hb
    exact ⟨k / 8, ⟨by omega, by rw [show 8 * (k / 8) + 7 = k by omega]; exact hb⟩, by omega⟩
  · rintro ⟨i, ⟨hi, hb⟩, rfl⟩
    exact ⟨by omega, hb⟩

set_option maxRecDepth 20000 in
open ArithmeticFunction in
/-- **The window**: the counts of `μ = 1` and `μ = −1` among `n + 1, …, n + W`. -/
theorem winPN_spec {n W t : ℕ} (hw : WinOK n W t) :
    (winPN n W t).1 = ((range W).filter (fun i => (μ (n + 1 + i) : ℤ) = 1)).card ∧
    (winPN n W t).2 = ((range W).filter (fun i => (μ (n + 1 + i) : ℤ) = -1)).card := by
  obtain ⟨hW1, hW, hn, ht, ht1, ht2⟩ := hw
  have hps : ∀ p ∈ PSm, 0 < p ∧ p < 10007 := fun p hp => ⟨(mem_PSm.1 hp).2.pos, (mem_PSm.1 hp).1⟩
  have hlg : ∀ i < W, lgSum PSm (n + 1 + i) < 108 := fun i hi =>
    lgSum_lt (by omega) (by omega)
  obtain ⟨a1, a2, a3⟩ := winAcc_spec (n := n) hW PSm 0 0 0 (fun _ => 0) hps (Pk_zero W)
    (fun i hi => by have := hlg i hi; omega)
  have hrec : recs = PSm.map mkRec := rfl
  unfold winPN
  rw [hrec]
  simp only [Nat.zero_testBit, Bool.false_xor, Bool.false_or] at a2 a3
  set r := winAcc n W (PSm.map mkRec) (0, 0, 0) with hr
  have a1' : Pk r.1 W (fun i => lgSum PSm (n + 1 + i)) := by simpa using a1
  have hones := Pk_mul (c := 128 - t) (Pk_onesW hW) (fun i hi => by omega)
  have hsum := Pk_add a1' hones (fun i hi => by have := hlg i hi; omega)
  -- the bits at `8 i + 7`
  have hB0 : ∀ i < W, (r.1 + (128 - t) * onesW W).testBit (8 * i + 7) =
      decide (t ≤ lgSum PSm (n + 1 + i)) := by
    intro i hi
    rw [testBit_7_of_fld, hsum.2 i hi]
    simp only [mul_one]
    exact decide_eq_decide.2 (by omega)
  set h := hib W
  have hh : ∀ k, h.testBit k = decide (k < 8 * W ∧ k % 8 = 7) := testBit_hib hW
  set B0 := (r.1 + (128 - t) * onesW W) &&& h
  set sqf := h ^^^ (r.2.2 &&& h)
  set neg := sqf &&& (r.2.1 ^^^ (h ^^^ B0))
  have hsqf : ∀ k, sqf.testBit k = true → k < 8 * W ∧ k % 8 = 7 := by
    intro k hk
    simp only [sqf, Nat.testBit_xor, Nat.testBit_and, hh] at hk
    by_contra hc
    simp [hc] at hk
  have hneg_sub : ∀ k, neg.testBit k = true → k < 8 * W ∧ k % 8 = 7 := by
    intro k hk; simp only [neg, Nat.testBit_and, Bool.and_eq_true] at hk; exact hsqf k hk.1
  have hpos_sub : ∀ k, (sqf ^^^ neg).testBit k = true → k < 8 * W ∧ k % 8 = 7 := by
    intro k hk
    simp only [neg, Nat.testBit_xor, Nat.testBit_and] at hk
    by_contra hc
    have : sqf.testBit k = false := by
      cases h' : sqf.testBit k
      · rfl
      · exact absurd (hsqf k h') hc
    simp [this] at hk
  -- bit `8 i + 7` in terms of `μ`
  have hbits : ∀ i < W, (sqf ^^^ neg).testBit (8 * i + 7) = decide ((μ (n + 1 + i) : ℤ) = 1) ∧
      neg.testBit (8 * i + 7) = decide ((μ (n + 1 + i) : ℤ) = -1) := by
    intro i hi
    set m := n + 1 + i with hm
    have hm0 : m ≠ 0 := by omega
    have hhi : h.testBit (8 * i + 7) = true := by rw [hh]; simp; omega
    have e1 : sqf.testBit (8 * i + 7) = !decide (∃ p ∈ PSm, p * p ∣ m) := by
      simp only [sqf, Nat.testBit_xor, Nat.testBit_and, hhi, a3 i hi, Bool.and_true]
      cases decide (∃ p ∈ PSm, p * p ∣ m) <;> rfl
    have e2 : B0.testBit (8 * i + 7) = decide (t ≤ lgSum PSm m) := by
      simp only [B0, Nat.testBit_and, hhi, Bool.and_true]; exact hB0 i hi
    have e3 : r.2.1.testBit (8 * i + 7) = decide (dvdCount PSm m % 2 = 1) := a2 i hi
    by_cases hsq : ∃ p ∈ PSm, p * p ∣ m
    · -- `μ m = 0`
      have hmu : μ m = 0 := by
        apply moebius_eq_zero_of_not_squarefree
        obtain ⟨p, hp, hpp⟩ := hsq
        rw [Nat.squarefree_iff_prime_squarefree]; push Not
        exact ⟨p, (mem_PSm.1 hp).2, hpp⟩
      have hs : sqf.testBit (8 * i + 7) = false := by rw [e1]; simp [hsq]
      simp only [neg, Nat.testBit_xor, Nat.testBit_and, hs, Bool.false_and, Bool.xor_false, hmu]
      simp
    · have hsq' : ∀ p, p.Prime → p < 10007 → ¬ p * p ∣ m := fun p hp hp1 hpp =>
        hsq ⟨p, mem_PSm.2 ⟨hp1, hp⟩, hpp⟩
      obtain ⟨_, hmu, hL1, -, hiff⟩ := mu_struct (by omega) (by omega) hsq'
      obtain ⟨-, hth⟩ := threshold (W := W) (by omega) (by omega) (by omega) ht1 ht2 hsq'
      have hs : sqf.testBit (8 * i + 7) = true := by rw [e1]; simp [hsq]
      rw [dvdCount_eq m hm0] at e3
      set a := (m.primeFactors.filter (· < 10007)).card
      set b := (m.primeFactors.filter (fun p => ¬ p < 10007)).card
      have hb : (t ≤ lgSum PSm m) ↔ b = 0 := by rw [hth]; exact Finset.card_eq_zero.symm
      have e2' : B0.testBit (8 * i + 7) = decide (b = 0) := by rw [e2]; exact decide_eq_decide.2 hb
      have hnegbit : neg.testBit (8 * i + 7) = decide ((a + b) % 2 = 1) := by
        simp only [neg, Nat.testBit_and, Nat.testBit_xor, hs, hhi, e2', e3, Bool.true_and]
        rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
          (interval_cases b <;> simp [ha, Nat.add_mod])
      have hmu' : (μ m : ℤ) = 1 ∨ (μ m : ℤ) = -1 := by
        rw [hmu]; rcases neg_one_pow_eq_or ℤ (a + b) with h' | h' <;> simp [h']
      have hmval : ((μ m : ℤ) = -1) ↔ (a + b) % 2 = 1 := by
        rw [hmu]
        constructor
        · intro h'; by_contra hc
          rw [show a + b = 2 * ((a + b) / 2) by omega, pow_mul] at h'; simp at h'
        · intro h'; rw [show a + b = 2 * ((a + b) / 2) + 1 by omega, pow_succ, pow_mul]; simp
      refine ⟨?_, ?_⟩
      · rw [Nat.testBit_xor, hs, hnegbit]
        rcases hmu' with h1 | h1
        · have : ¬ (a + b) % 2 = 1 := fun h' => by have := hmval.2 h'; omega
          simp [h1, this]
        · have : (a + b) % 2 = 1 := hmval.1 h1
          simp [h1, this]
      · rw [hnegbit]; exact decide_eq_decide.2 hmval.symm
  have hB : 8 * W ≤ 2 ^ (7 + 8) := by unfold WM at hW; omega
  refine ⟨(?_ : pcL 7 (sqf ^^^ neg) = _), (?_ : pcL 7 neg = _)⟩
  · rw [pcL_spec, nbits_stride hB hpos_sub]
    apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by have := (hbits i h1).1; rw [this] at h2; simpa using h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, by rw [(hbits i h1).1]; simpa using h2⟩⟩
  · rw [pcL_spec, nbits_stride hB hneg_sub]
    apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by have := (hbits i h1).2; rw [this] at h2; simpa using h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, by rw [(hbits i h1).2]; simpa using h2⟩⟩

/-! ### The chain of windows -/

/-- `M(k) = ∑_{n ≤ k} μ(n)` in `ℤ`. -/
def Mz (k : ℕ) : ℤ := ∑ i ∈ Icc 1 k, (μ i : ℤ)

theorem mu_cases_z (m : ℕ) : (μ m : ℤ) = 1 ∨ (μ m : ℤ) = -1 ∨ (μ m : ℤ) = 0 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := m)
  rcases abs_le.1 h with ⟨h1, h2⟩
  have : (μ m : ℤ) = -1 ∨ (μ m : ℤ) = 0 ∨ (μ m : ℤ) = 1 := by omega
  tauto

theorem Mz_sub (n k : ℕ) : Mz (n + k) - Mz n = ∑ i ∈ range k, (μ (n + 1 + i) : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ← ih, show n + (k + 1) = n + k + 1 by ring, Mz, Mz,
      sum_Icc_succ_top (by omega), show n + k + 1 = n + 1 + k by ring]
    unfold Mz; ring

theorem sum_mu_split (n k : ℕ) : ∑ i ∈ range k, (μ (n + 1 + i) : ℤ) =
    ((range k).filter (fun i => (μ (n + 1 + i) : ℤ) = 1)).card -
      ((range k).filter (fun i => (μ (n + 1 + i) : ℤ) = -1)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rcases mu_cases_z (n + 1 + i) with h | h | h <;> simp [h]

/-- **One window**: `M(n + W) = M(n) + P − N`, and `M(n) − N ≤ M(u) ≤ M(n) + P` on `(n, n + W]`. -/
theorem window_M {n W t : ℕ} (hw : WinOK n W t) :
    Mz (n + W) = Mz n + (winPN n W t).1 - (winPN n W t).2 ∧
      ∀ u, n < u → u ≤ n + W → Mz n - (winPN n W t).2 ≤ Mz u ∧ Mz u ≤ Mz n + (winPN n W t).1 := by
  obtain ⟨h1, h2⟩ := winPN_spec hw
  refine ⟨?_, fun u hu1 hu2 => ?_⟩
  · have := Mz_sub n W
    rw [sum_mu_split, ← h1, ← h2] at this
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
    have := Mz_sub n k
    rw [sum_mu_split] at this
    have c1 : ((range k).filter (fun i => (μ (n + 1 + i) : ℤ) = 1)).card ≤ (winPN n W t).1 := by
      rw [h1]; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    have c2 : ((range k).filter (fun i => (μ (n + 1 + i) : ℤ) = -1)).card ≤ (winPN n W t).2 := by
      rw [h2]; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    have c1' : (((range k).filter (fun i => (μ (n + 1 + i) : ℤ) = 1)).card : ℤ) ≤ (winPN n W t).1 := by
      exact_mod_cast c1
    have c2' : (((range k).filter (fun i => (μ (n + 1 + i) : ℤ) = -1)).card : ℤ) ≤ (winPN n W t).2 := by
      exact_mod_cast c2
    constructor <;> linarith [Nat.cast_nonneg (α := ℤ) ((range k).filter (fun i => (μ (n + 1 + i) : ℤ) = 1)).card,
      Nat.cast_nonneg (α := ℤ) ((range k).filter (fun i => (μ (n + 1 + i) : ℤ) = -1)).card]

/-- The check `10⁶ x² ≤ 326041 n`, that is `|x| ≤ 0.571 √n`. -/
def chkB (x : ℤ) (n : ℕ) : Bool := decide (10 ^ 6 * (x * x) ≤ 326041 * (n : ℤ))

/-- The chain: windows `(W, t)` from `n` with `M(n) = M`. -/
noncomputable def walkM : List (ℕ × ℕ) → ℕ → ℤ → Option (ℕ × ℤ)
  | [], n, M => some (n, M)
  | (W, t) :: ws, n, M =>
    if WinOK n W t then
      let pn := winPN n W t
      if chkB (M + pn.1) n && chkB (M - pn.2) n then walkM ws (n + W) (M + pn.1 - pn.2) else none
    else none

theorem chkB_of_between {a x b : ℤ} {n u : ℕ} (hnu : n ≤ u) (ha : chkB a n = true) (hb : chkB b n = true)
    (h1 : a ≤ x) (h2 : x ≤ b) : 10 ^ 6 * (x * x) ≤ 326041 * (u : ℤ) := by
  unfold chkB at ha hb
  simp only [decide_eq_true_eq] at ha hb
  have hnu' : (n : ℤ) ≤ u := by exact_mod_cast hnu
  have : x * x ≤ max (a * a) (b * b) := by
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  rcases le_total (a * a) (b * b) with h | h
  · rw [max_eq_right h] at this; nlinarith
  · rw [max_eq_left h] at this; nlinarith

/-- **The chain**: `M(n') = M'` and `|M(u)| ≤ 0.571 √u` on `(n, n']`. -/
theorem walkM_spec : ∀ (ws : List (ℕ × ℕ)) (n : ℕ) (M : ℤ) (n' : ℕ) (M' : ℤ),
    Mz n = M → walkM ws n M = some (n', M') →
    Mz n' = M' ∧ n ≤ n' ∧ ∀ u, n < u → u ≤ n' → 10 ^ 6 * (Mz u * Mz u) ≤ 326041 * (u : ℤ) := by
  intro ws
  induction ws with
  | nil =>
    intro n M n' M' hM h
    simp only [walkM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hM, le_rfl, fun u h1 h2 => by omega⟩
  | cons w ws ih =>
    obtain ⟨W, t⟩ := w
    intro n M n' M' hM h
    simp only [walkM] at h
    split_ifs at h with hw hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hM1, hrange⟩ := window_M hw
    obtain ⟨r1, r2, r3⟩ := ih (n + W) _ n' M' (by rw [hM1, hM]) h
    refine ⟨r1, by omega, fun u hu1 hu2 => ?_⟩
    rcases le_or_gt u (n + W) with hu | hu
    · obtain ⟨b1, b2⟩ := hrange u hu1 hu
      rw [hM] at b1 b2
      exact chkB_of_between hu1.le hc.2 hc.1 b1 b2
    · exact r3 u hu hu2

def resEqM : Option (ℕ × ℤ) → ℕ → ℤ → Bool
  | some (a, b), a', b' => a == a' && b == b'
  | none, _, _ => false

theorem resEqM_spec {r : Option (ℕ × ℤ)} {a : ℕ} {b : ℤ} (h : resEqM r a b = true) : r = some (a, b) := by
  match r, h with
  | some (a0, b0), h =>
    simp only [resEqM, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]

end TernaryGoldbach.Prelim.MuSieve
