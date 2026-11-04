import TernaryGoldbach.MinorArcs.T2Kernel
import TernaryGoldbach.Prelim.SmallMoebius
import TernaryGoldbach.MinorArcs.SmallG2

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]

/-!
# The kernel part of the `g₂` tail bound (`G2Tail.lean`)

With `X = 10⁴`, `K = 11815`, `m(k) = ∑_{n ≤ k} μ(n)/n`:
* `walkV` runs over `k < K`, keeping `10¹² m(k)` as `P(k) − Q(k)` (as in `SmallMoebius.lean`), lower and
  upper bounds `Plo`, `Phi` for `10²⁴ ∑_{j < k} m(j)² log(1 + 1/j)`, and for `k ≤ X` a trie
  `k ↦ (λ(k), w(k))` with `V(k) = cP + tail − Plo(k)` (an upper bound for
  `10²⁴ ∫_k^∞ m(⌊t⌋)²/t dt` once `Phi(K) ≤ cP`), `λ(k) = 2^{⌊log₂ V(k)/2⌋}` and `w(k) = ⌈V(k)/λ(k)⌉`;
  it also lists `den₁(a) = a ∏_{p ∣ a odd} (p + 1)` for `a ≤ X`;
* `outerC` sums over odd squarefree `d ≤ X` the quantity
  `⌈Λ_d Ξ_d/σ(d)²⌉`, `Λ_d = s_λ(d) + λ(1) (B_d − s₁(d))`, `Ξ_d = s_V(d) + w(1) (B_d − s₁(d))`, where
  `s₁ = ∑_{a ≤ X/d} H_d(a)`, `s_λ = ∑ H_d(a) λ(⌊X/(da)⌋)`, `s_V = ∑ H_d(a) w(⌊X/(da)⌋)` and
  `B_d = 2.47 σ(d)/d ≥ ∑_a H_d(a)`, all in fixed point (`H_d(a) = σ((a, d))/den₁(a)`).
-/

open Finset
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs.G2TailNum

open TernaryGoldbach.MinorArcs.T2K

def XX : ℕ := 10000
def KK : ℕ := 11815
def SH : ℕ := 10 ^ 20

def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `μ(k)` (as `0`, `1`, `2` = −1) and `den₁(k) = k ∏_{p ∣ k odd} (p + 1)`. -/
def muden (k : ℕ) : ℕ × ℕ :=
  let ps := oddPrimes k
  let r := ps.prod * (if k % 2 = 0 then 2 else 1)
  let m := if r = k then
    (if (ps.length + (if k % 2 = 0 then 1 else 0)) % 2 = 0 then 1 else 2) else 0
  (m, k * (ps.map (· + 1)).prod)

structure SV where
  P : ℕ
  Q : ℕ
  Plo : ℕ
  Phi : ℕ
  tv : Tr (ℕ × ℕ)
  dl : List ℕ

def cP : ℕ := 814940993196246650988643
def tailV : ℕ := 100001 * 10 ^ 15

def lam2 (v : ℕ) : ℕ := 2 ^ (Nat.log2 v / 2)

def termU (k P Q : ℕ) : ℕ := cdiv (((P - Q) + (Q - P) + k) ^ 2 * lhiN k) (lhiD k)
def termL (k P Q : ℕ) : ℕ := (((P - Q) + (Q - P)) - k) ^ 2 * lloN k / lloD k

def stepV (k : ℕ) (s : SV) : SV :=
  let md := muden k
  let P := if md.1 = 1 then s.P + 10 ^ 12 / k else s.P
  let Q := if md.1 = 2 then s.Q + 10 ^ 12 / k else s.Q
  let V := cP + tailV - s.Plo
  let lm := lam2 V
  let tv := if k ≤ XX then Tr.set (1, 0) 16 s.tv k (lm, cdiv V lm) else s.tv
  let dl := if k ≤ XX then md.2 :: s.dl else s.dl
  ⟨P, Q, s.Plo + termL k P Q, s.Phi + termU k P Q, tv, dl⟩

def walkV : ℕ → ℕ → SV → SV
  | 0, _, s => s
  | f + 1, k, s => walkV f (k + 1) (stepV k s)

/-- `σ((a, d))` from the primes of `d`. -/
def sgc (ps : List ℕ) (a : ℕ) : ℕ := ((ps.filter (fun p => a % p == 0)).map (· + 1)).prod

/-- Inner sums over `a = a₀, a₀ + 1, …` (list `L` of `den₁(a)`), grouped in blocks of constant
`k = ⌊X/(da)⌋`: state `(s₁, s_λ, s_V, pending block sum, k)`. -/
def innerC (tv : Tr (ℕ × ℕ)) (d : ℕ) (ps : List ℕ) :
    ℕ → ℕ → List ℕ → ℕ × ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | 0, _, _, (s1, sl, sv, bh, k) => let v := tv.get (1, 0) k; (s1, sl + bh * v.1, sv + bh * v.2)
  | _ + 1, _, [], (s1, sl, sv, bh, k) => let v := tv.get (1, 0) k; (s1, sl + bh * v.1, sv + bh * v.2)
  | f + 1, a, den :: L, (s1, sl, sv, bh, k) =>
    let sg := sgc ps a
    let lo := SH * sg / den
    let hi := cdiv (SH * sg) den
    let k' := XX / (d * a)
    if k' = k then innerC tv d ps f (a + 1) L (s1 + lo, sl, sv, bh + hi, k)
    else let v := tv.get (1, 0) k; innerC tv d ps f (a + 1) L (s1 + lo, sl + bh * v.1, sv + bh * v.2, hi, k')

def P1n : ℕ := 12338
def P1d : ℕ := 10000

/-- The term for odd `d`. -/
def termC (tv : Tr (ℕ × ℕ)) (dl : List ℕ) (d : ℕ) : ℕ :=
  let ps := oddPrimes d
  if ps.prod = d then
    let sg := (ps.map (· + 1)).prod
    let r := innerC tv d ps (XX / d) 1 dl (0, 0, 0, 0, XX / d)
    let B := cdiv (2 * P1n * sg * SH) (P1d * d)
    let tH := B - r.1
    let v1 := tv.get (1, 0) 1
    let Lam := r.2.1 + v1.1 * tH
    let Xi := r.2.2 + v1.2 * tH
    cdiv (Lam * Xi) (sg * sg)
  else 0

def outerC (tv : Tr (ℕ × ℕ)) (dl : List ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => outerC tv dl i + termC tv dl (2 * i + 1)

/-! ### `μ` and `den₁` -/

/-- `rad k = ∏_{p ∣ k} p` from the odd primes. -/
theorem rad_eq {k : ℕ} (hk : 0 < k) :
    (oddPrimes k).prod * (if k % 2 = 0 then 2 else 1) = ∏ p ∈ k.primeFactors, p := by
  have hnd := nodup_oddPrimes hk
  have h := List.prod_toFinset (fun p : ℕ => p) hnd
  rw [List.map_id'] at h
  rw [← h, toFinset_oddPrimes hk]
  by_cases he : k % 2 = 0
  · rw [if_pos he]
    have h2 : 2 ∈ k.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, Nat.dvd_of_mod_eq_zero he, by omega⟩
    rw [← prod_filter_mul_prod_filter_not k.primeFactors (· ≠ 2)]
    congr 1
    rw [show k.primeFactors.filter (fun p => ¬ p ≠ 2) = {2} by
      ext p; simp only [mem_filter, not_not, mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ h2, h⟩⟩, prod_singleton]
  · rw [if_neg he, mul_one, filter_true_of_mem]
    intro p hp h2
    subst h2
    exact he (Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors hp))

theorem squarefree_iff_rad {k : ℕ} (hk : 0 < k) : Squarefree k ↔ ∏ p ∈ k.primeFactors, p = k := by
  constructor
  · exact Nat.prod_primeFactors_of_squarefree
  · intro h
    rw [← h]
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      fun p hp => (Nat.prime_of_mem_primeFactors hp).prime.squarefree
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).2 hpq

theorem card_primeFactors_eq {k : ℕ} (hk : 0 < k) :
    k.primeFactors.card = (oddPrimes k).length + if k % 2 = 0 then 1 else 0 := by
  have hnd := nodup_oddPrimes hk
  rw [← List.toFinset_card_of_nodup hnd, toFinset_oddPrimes hk]
  by_cases he : k % 2 = 0
  · rw [if_pos he]
    have h2 : 2 ∈ k.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, Nat.dvd_of_mod_eq_zero he, by omega⟩
    have e : k.primeFactors = insert 2 (k.primeFactors.filter (· ≠ 2)) := by
      ext p; simp only [mem_insert, mem_filter]
      constructor
      · intro hp; by_cases h : p = 2
        · left; exact h
        · right; exact ⟨hp, h⟩
      · rintro (rfl | ⟨hp, -⟩)
        · exact h2
        · exact hp
    conv_lhs => rw [e]
    rw [card_insert_of_notMem (by simp)]
  · rw [if_neg he, add_zero, filter_true_of_mem]
    intro p hp h2
    subst h2
    exact he (Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors hp))

/-- The `μ` code of `muden`. -/
theorem muden_spec {k : ℕ} (hk : 0 < k) :
    ((muden k).1 = 1 → (μ k : ℝ) = 1) ∧ ((muden k).1 = 2 → (μ k : ℝ) = -1) ∧
      ((muden k).1 ≠ 1 → (muden k).1 ≠ 2 → (μ k : ℝ) = 0) := by
  unfold muden
  simp only
  rw [rad_eq hk]
  by_cases hr : ∏ p ∈ k.primeFactors, p = k
  · have hsq := (squarefree_iff_rad hk).2 hr
    have hc : ArithmeticFunction.cardFactors k = k.primeFactors.card := by
      rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors,
        List.toFinset_card_of_nodup hsq.nodup_primeFactorsList]
    have hmu : (μ k : ℝ) = (-1) ^ k.primeFactors.card := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, hc]; push_cast; rfl
    rw [if_pos hr, hmu, card_primeFactors_eq hk]
    rcases Nat.even_or_odd ((oddPrimes k).length + if k % 2 = 0 then 1 else 0) with h | h
    · have h0 : ((oddPrimes k).length + if k % 2 = 0 then 1 else 0) % 2 = 0 := Nat.even_iff.1 h
      rw [if_pos h0]
      exact ⟨fun _ => h.neg_one_pow, fun h' => absurd h' (by norm_num), fun h' => absurd rfl h'⟩
    · have h1 : ¬ ((oddPrimes k).length + if k % 2 = 0 then 1 else 0) % 2 = 0 := by
        have := Nat.odd_iff.1 h; omega
      rw [if_neg h1]
      exact ⟨fun h' => absurd h' (by norm_num), fun _ => h.neg_one_pow, fun _ h' => absurd rfl h'⟩
  · rw [if_neg hr]
    refine ⟨fun h => by omega, fun h => by omega, fun _ _ => ?_⟩
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun h => hr ((squarefree_iff_rad hk).1 h))]
    simp

/-! ### The `V` walk -/

open TernaryGoldbach.Prelim.SmallMoeb (Pt Qt sum_approx)

/-- `termL`, `termU` at `j` along the walk. -/
noncomputable def tL (j : ℕ) : ℕ := termL j (Pt j) (Qt j)
noncomputable def tU (j : ℕ) : ℕ := termU j (Pt j) (Qt j)

/-- `V(k) = cP + tail − ∑_{j < k} termL(j)`. -/
noncomputable def Vt (k : ℕ) : ℕ := cP + tailV - ∑ j ∈ Icc 1 (k - 1), tL j

/-- `den₁(a) = a ∏_{p ∣ a odd} (p + 1)`. -/
def den1 (a : ℕ) : ℕ := a * ((oddPrimes a).map (· + 1)).prod

/-- The state after `k`. -/
def VInv (k : ℕ) (s : SV) : Prop :=
  s.P = Pt k ∧ s.Q = Qt k ∧ s.Plo = ∑ j ∈ Icc 1 k, tL j ∧ s.Phi = ∑ j ∈ Icc 1 k, tU j ∧
  (∀ j, 1 ≤ j → j ≤ min k XX → s.tv.get (1, 0) j = (lam2 (Vt j), cdiv (Vt j) (lam2 (Vt j)))) ∧
  s.dl = ((List.range (min k XX)).map (fun i => den1 (i + 1))).reverse

theorem Pt_succ (k : ℕ) : Pt (k + 1) = Pt k + if (μ (k + 1) : ℝ) = 1 then 1000000000000 / (k + 1) else 0 := by
  unfold Pt; rw [sum_Icc_succ_top (by omega)]

theorem Qt_succ (k : ℕ) : Qt (k + 1) = Qt k + if (μ (k + 1) : ℝ) = -1 then 1000000000000 / (k + 1) else 0 := by
  unfold Qt; rw [sum_Icc_succ_top (by omega)]

theorem stepV_spec {k : ℕ} {s : SV} (h : VInv k s) : VInv (k + 1) (stepV (k + 1) s) := by
  obtain ⟨hP, hQ, hlo, hhi, htv, hdl⟩ := h
  obtain ⟨m1, m2, m0⟩ := muden_spec (k := k + 1) (by omega)
  have hP' : (if (muden (k + 1)).1 = 1 then s.P + 10 ^ 12 / (k + 1) else s.P) = Pt (k + 1) := by
    rw [Pt_succ, hP]
    by_cases h1 : (muden (k + 1)).1 = 1
    · rw [if_pos h1, if_pos (m1 h1)]; rfl
    · rw [if_neg h1, if_neg]; · simp
      by_cases h2 : (muden (k + 1)).1 = 2
      · rw [m2 h2]; norm_num
      · rw [m0 h1 h2]; norm_num
  have hQ' : (if (muden (k + 1)).1 = 2 then s.Q + 10 ^ 12 / (k + 1) else s.Q) = Qt (k + 1) := by
    rw [Qt_succ, hQ]
    by_cases h2 : (muden (k + 1)).1 = 2
    · rw [if_pos h2, if_pos (m2 h2)]; rfl
    · rw [if_neg h2, if_neg]; · simp
      by_cases h1 : (muden (k + 1)).1 = 1
      · rw [m1 h1]; norm_num
      · rw [m0 h1 h2]; norm_num
  unfold stepV
  simp only
  rw [hP', hQ']
  have hV : cP + tailV - s.Plo = Vt (k + 1) := by rw [hlo, Vt, Nat.add_sub_cancel]
  rw [hV]
  refine ⟨rfl, rfl, by rw [hlo, sum_Icc_succ_top (by omega)]; rfl,
    by rw [hhi, sum_Icc_succ_top (by omega)]; rfl, fun j hj1 hj2 => ?_, ?_⟩
  · by_cases hk : k + 1 ≤ XX
    · have hk' : k ≤ XX := Nat.le_of_succ_le hk
      rw [min_eq_left hk] at hj2
      have hfuel : 2 * (k + 1) + 1 < 2 ^ 16 := by
        have : k + 1 ≤ 10000 := hk
        calc 2 * (k + 1) + 1 ≤ 2 * 10000 + 1 := by omega
          _ < 2 ^ 16 := by norm_num
      rw [if_pos hk, Tr.get_set _ _ _ _ _ _ hfuel]
      by_cases hj : j = k + 1
      · rw [if_pos hj, hj]
      · rw [if_neg hj]; exact htv j hj1 (by rw [min_eq_left hk']; omega)
    · have hk' : XX ≤ k := Nat.le_of_lt_succ (not_le.1 hk)
      rw [min_eq_right (hk'.trans (Nat.le_succ k))] at hj2
      rw [if_neg hk]; exact htv j hj1 (by rw [min_eq_right hk']; exact hj2)
  · by_cases hk : k + 1 ≤ XX
    · show (if k + 1 ≤ XX then (muden (k + 1)).2 :: s.dl else s.dl) = _
      rw [if_pos hk, hdl, min_eq_left hk, min_eq_left (Nat.le_of_succ_le hk),
        List.range_succ, List.map_append, List.reverse_append]
      rfl
    · have hk' : XX ≤ k := Nat.le_of_lt_succ (not_le.1 hk)
      show (if k + 1 ≤ XX then (muden (k + 1)).2 :: s.dl else s.dl) = _
      rw [if_neg hk, hdl, min_eq_right hk', min_eq_right (hk'.trans (Nat.le_succ k))]

theorem walkV_spec : ∀ (f k : ℕ) (s : SV), VInv k s → VInv (k + f) (walkV f (k + 1) s) := by
  intro f
  induction f with
  | zero => intro k s h; simpa [walkV] using h
  | succ f ih =>
    intro k s h
    simp only [walkV]
    have := ih (k + 1) _ (stepV_spec h)
    rwa [show k + 1 + f = k + (f + 1) by omega] at this

theorem VInv_zero : VInv 0 ⟨0, 0, 0, 0, .nil, []⟩ := by
  refine ⟨by simp [Pt], by simp [Qt], by simp, by simp, fun j hj1 hj2 => by simp at hj2; omega, by simp⟩

/-- The final state of the `V` walk. -/
def sV : SV := walkV (KK - 1) 1 ⟨0, 0, 0, 0, .nil, []⟩

theorem sV_spec : VInv (KK - 1) sV := by
  have := walkV_spec (KK - 1) 0 _ VInv_zero
  rw [zero_add] at this
  exact this

/-! ### The inner and outer sums -/

/-- The value of an `innerC` state. -/
def val (tv : Tr (ℕ × ℕ)) (st : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (st.1, st.2.1 + st.2.2.2.1 * (tv.get (1, 0) st.2.2.2.2).1, st.2.2.1 + st.2.2.2.1 * (tv.get (1, 0) st.2.2.2.2).2)

theorem innerC_spec (tv : Tr (ℕ × ℕ)) (d : ℕ) (ps : List ℕ) : ∀ (f a : ℕ) (L : List ℕ)
    (st : ℕ × ℕ × ℕ × ℕ × ℕ), (∀ i < f, L[i]? = some (den1 (a + i))) →
    innerC tv d ps f a L st =
      ((val tv st).1 + ∑ i ∈ range f, SH * sgc ps (a + i) / den1 (a + i),
       (val tv st).2.1 + ∑ i ∈ range f, cdiv (SH * sgc ps (a + i)) (den1 (a + i)) *
          (tv.get (1, 0) (XX / (d * (a + i)))).1,
       (val tv st).2.2 + ∑ i ∈ range f, cdiv (SH * sgc ps (a + i)) (den1 (a + i)) *
          (tv.get (1, 0) (XX / (d * (a + i)))).2) := by
  intro f
  induction f with
  | zero =>
    intro a L st _
    obtain ⟨s1, sl, sv, bh, k⟩ := st
    simp [innerC, val]
  | succ f ih =>
    intro a L st hL
    obtain ⟨s1, sl, sv, bh, k⟩ := st
    rcases L with _ | ⟨den, L⟩
    · exact absurd (hL 0 (by omega)) (by simp)
    have hden : den = den1 a := by have := hL 0 (by omega); simpa using this
    have hL' : ∀ i < f, L[i]? = some (den1 (a + 1 + i)) := by
      intro i hi
      have := hL (i + 1) (by omega)
      simp only [List.getElem?_cons_succ] at this
      rw [this, show a + (i + 1) = a + 1 + i by omega]
    subst hden
    simp only [innerC]
    have e1a : ∑ i ∈ range (f + 1), SH * sgc ps (a + i) / den1 (a + i) =
        SH * sgc ps a / den1 a + ∑ i ∈ range f, SH * sgc ps (a + 1 + i) / den1 (a + 1 + i) := by
      rw [sum_range_succ', add_zero, add_comm]
      congr 1; exact sum_congr rfl fun i _ => by rw [show a + (i + 1) = a + 1 + i by omega]
    have e1b : ∑ i ∈ range (f + 1), cdiv (SH * sgc ps (a + i)) (den1 (a + i)) *
          (tv.get (1, 0) (XX / (d * (a + i)))).1 =
        cdiv (SH * sgc ps a) (den1 a) * (tv.get (1, 0) (XX / (d * a))).1 +
          ∑ i ∈ range f, cdiv (SH * sgc ps (a + 1 + i)) (den1 (a + 1 + i)) *
            (tv.get (1, 0) (XX / (d * (a + 1 + i)))).1 := by
      rw [sum_range_succ', add_zero, add_comm]
      congr 1; exact sum_congr rfl fun i _ => by rw [show a + (i + 1) = a + 1 + i by omega]
    have e1c : ∑ i ∈ range (f + 1), cdiv (SH * sgc ps (a + i)) (den1 (a + i)) *
          (tv.get (1, 0) (XX / (d * (a + i)))).2 =
        cdiv (SH * sgc ps a) (den1 a) * (tv.get (1, 0) (XX / (d * a))).2 +
          ∑ i ∈ range f, cdiv (SH * sgc ps (a + 1 + i)) (den1 (a + 1 + i)) *
            (tv.get (1, 0) (XX / (d * (a + 1 + i)))).2 := by
      rw [sum_range_succ', add_zero, add_comm]
      congr 1; exact sum_congr rfl fun i _ => by rw [show a + (i + 1) = a + 1 + i by omega]
    split_ifs with hk
    · rw [ih (a + 1) L _ hL', e1a, e1b, e1c, hk]
      simp only [val]
      refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))
    · rw [ih (a + 1) L _ hL', e1a, e1b, e1c]
      simp only [val]
      refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))

theorem outerC_eq (tv : Tr (ℕ × ℕ)) (dl : List ℕ) (n : ℕ) :
    outerC tv dl n = ∑ i ∈ range n, termC tv dl (2 * i + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [outerC, ih, sum_range_succ]

/-! ### The computation -/

def Macc : ℕ := 39974717715721261117728802693483729514802697639698853009160571

set_option maxHeartbeats 0 in
theorem tail_ok : (sV.Phi, outerC sV.tv sV.dl.reverse 5000) = (cP, Macc) := by
  unfold sV
  decide +kernel

end TernaryGoldbach.MinorArcs.G2TailNum
