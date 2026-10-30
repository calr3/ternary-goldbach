import TernaryGoldbach.MinorArcs.TypeII
import TernaryGoldbach.MinorArcs.S1Lemma

/-!
# Type II sums [B, §5.1]: the sum `S₁`

`S₁(U, W) = ∑_{max(U, x/2W) < m ≤ x/W, m odd} (∑_{d > U, d | m} μ(d))²` [B, (5.6)], `v = 2`.

* `S1_eq`: the reduction [B, (5.7)–(5.8)]: `S₁ = ∑_{s odd} ∑_{r₁, r₂} μ(r₁)μ(r₂) #{l}` via the
  change of variables `(m, d₁, d₂) ↔ (s, r₁, r₂, l)`, `d_i = r_i l`, `l = (d₁, d₂)`, `m = s r₁ r₂ l`;
* `integral_g2`: [B, (5.19)], `∫_{1/2}^1 g₂(uy) du = ∑ μ(r₁)μ(r₂)/(σ(r₁)σ(r₂)) (1 - max(1/2, r_i/y))`;
* `S1_bound`: **[B, (5.34)]** `S₁ ≤ (x/W) H₂(x/WU) + 1.27 ζ(3/2)³ x^{3/2}/(W^{3/2} U)`, from
  Lemma 5.1.1 (`lemma_5_1_1`) applied for each `s` with `y = S/s`, `z = x/(Ws)`.

Trusted inputs: `fsq_le` (via Lemma 5.1.1) and `T2_le` [B, (5.31) and the computation for
`16 ≤ S < 10⁵`], which rests on Lemma 5.1.2 and interval-arithmetic computations. (5.36) and (5.37)
are numerical ([B, (5.32)]) and are stated as trusted facts.
-/

open Real Finset MeasureTheory
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs
open TernaryGoldbach.Prelim

/-! ### The reduction (5.7)–(5.8) -/

/-- The `l`-range of [B, (5.8)] for `y = B/(Us)`, `z = B/s`. -/
theorem mem_lrange {B U : ℝ} (hB : 0 < B) (hU : 0 < U) {s r₁ r₂ l : ℕ} (hs : 1 ≤ s)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) :
    l ∈ Ioc ⌊aL (B / U / s) (B / s) r₁ r₂⌋₊ ⌊bL (B / s) r₁ r₂⌋₊ ↔
      U < r₁ * l ∧ U < r₂ * l ∧ B / 2 < s * r₁ * r₂ * l ∧ (s * r₁ * r₂ * l : ℝ) ≤ B := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : (0 : ℝ) < r₁ := by exact_mod_cast hr₁
  have h2 : (0 : ℝ) < r₂ := by exact_mod_cast hr₂
  have ha0 : 0 ≤ aL (B / U / s) (B / s) r₁ r₂ := by unfold aL; positivity
  have hb0 : 0 ≤ bL (B / s) r₁ r₂ := by unfold bL; positivity
  rw [mem_Ioc, Nat.floor_lt ha0, Nat.le_floor_iff hb0]
  have e1 : B / s / (B / U / s * r₁) = U / r₁ := by field_simp
  have e2 : B / s / (B / U / s * r₂) = U / r₂ := by field_simp
  simp only [aL, bL, max_lt_iff, e1, e2]
  rw [div_lt_iff₀ h1, div_lt_iff₀ h2, div_lt_iff₀ (by positivity), le_div_iff₀ (by positivity),
    le_div_iff₀ hs0, div_lt_iff₀ hs0]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨by linarith, by linarith⟩, by nlinarith⟩, by nlinarith⟩

/-- `S₁(U, W)` [B, (5.6)] with `v = 2`. -/
noncomputable def S1 (x U W : ℝ) : ℝ :=
  ∑ m ∈ Ioc ⌊max U (x / (2 * W))⌋₊ ⌊x / W⌋₊,
    if Odd m then (∑ d ∈ m.divisors.filter (fun d : ℕ => U < (d : ℝ)), (μ d : ℝ)) ^ 2 else 0

/-- The inner sum of [B, (5.8)] for fixed `s`, with `y = B/(Us)`, `z = B/s`, `B = x/W`. -/
noncomputable def innerS (B U : ℝ) (s : ℕ) : ℝ :=
  ∑ r₁ ∈ Icc 1 ⌊B / U / s⌋₊, ∑ r₂ ∈ Icc 1 ⌊B / U / s⌋₊,
    if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
      (μ r₁ : ℝ) * μ r₂ * cntSq (2 * (r₁ * r₂)) (aL (B / U / s) (B / s) r₁ r₂) (bL (B / s) r₁ r₂)
    else 0

theorem sum_eq_sum_ite_of_subset {J I : Finset ℕ} (h : J ⊆ I) (f : ℕ → ℝ) :
    ∑ x ∈ J, f x = ∑ x ∈ I, if x ∈ J then f x else 0 := by
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 h]

theorem moebius_mul_sq {r l : ℕ} (h : Squarefree (r * l)) : (μ (r * l) : ℝ) = μ r * μ l := by
  have hc := (Nat.squarefree_mul_iff.1 h).1
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]; push_cast; ring

/-- The left side of [B, (5.7)] as a sum over triples `(m, d₁, d₂)`. -/
theorem S1_eq_triples {x U W : ℝ} (hx : 0 < x) (hW : 0 < W) (hU : 0 < U) :
    S1 x U W = ∑ p ∈ (Icc 1 ⌊x / W⌋₊ ×ˢ Icc 1 ⌊x / W⌋₊ ×ˢ Icc 1 ⌊x / W⌋₊).filter
      (fun p : ℕ × ℕ × ℕ => Odd p.1 ∧ x / W / 2 < p.1 ∧ p.2.1 ∣ p.1 ∧ p.2.2 ∣ p.1 ∧
        U < p.2.1 ∧ U < p.2.2 ∧ Squarefree p.2.1 ∧ Squarefree p.2.2),
      (μ p.2.1 : ℝ) * μ p.2.2 := by
  rw [S1]
  have hx2 : x / (2 * W) = x / W / 2 := by field_simp
  rw [hx2]
  set B := x / W
  set I := Icc 1 ⌊B⌋₊
  rw [sum_filter, sum_product]
  simp only [sum_product]
  rw [sum_eq_sum_ite_of_subset (I := I)]
  swap
  · intro m hm; simp only [mem_Ioc, I, mem_Icc] at hm ⊢; omega
  refine sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
  have hDsum : ∑ d ∈ m.divisors.filter (fun d : ℕ => U < (d : ℝ)), (μ d : ℝ) =
      ∑ d ∈ I, if d ∣ m ∧ U < d then (μ d : ℝ) else 0 := by
    rw [← sum_filter]
    congr 1
    ext d
    simp only [mem_filter, Nat.mem_divisors, I, mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h1 hm1, (Nat.le_of_dvd hm1 h1).trans (mem_Icc.1 hm).2⟩, h1, h2⟩
    · rintro ⟨_, h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  rw [hDsum, sq, sum_mul_sum]
  by_cases hc : m ∈ Ioc ⌊max U (B / 2)⌋₊ ⌊B⌋₊ ∧ Odd m
  · rw [if_pos hc.1, if_pos hc.2]
    have hmB : B / 2 < m := by
      have := (Nat.floor_lt (le_max_of_le_left hU.le)).1 (mem_Ioc.1 hc.1).1
      exact lt_of_le_of_lt (le_max_right _ _) this
    refine sum_congr rfl fun d₁ _ => sum_congr rfl fun d₂ _ => ?_
    by_cases hs : Squarefree d₁ ∧ Squarefree d₂
    · rw [ite_zero_mul_ite_zero]
      have ho := hc.2
      exact if_congr (by tauto) rfl rfl
    · have : (μ d₁ : ℝ) * μ d₂ = 0 := by
        rcases not_and_or.1 hs with h | h <;>
          simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
      split_ifs <;> simp_all
  · rw [show ∀ t : ℝ, (if m ∈ Ioc ⌊max U (B / 2)⌋₊ ⌊B⌋₊ then (if Odd m then t else 0) else 0) = 0
      from fun t => by
        split_ifs with h1 h2
        · exact absurd ⟨h1, h2⟩ hc
        · rfl
        · rfl]
    symm
    refine sum_eq_zero fun d₁ _ => sum_eq_zero fun d₂ _ => if_neg ?_
    rintro ⟨ho, hmB, hd₁, -, hU₁, -⟩
    apply hc
    refine ⟨?_, ho⟩
    rw [mem_Ioc, Nat.floor_lt (le_max_of_le_left hU.le)]
    refine ⟨max_lt ?_ hmB, (mem_Icc.1 hm).2⟩
    exact lt_of_lt_of_le hU₁ (by exact_mod_cast Nat.le_of_dvd hm1 hd₁)

theorem mem_rrange {B U : ℝ} (hU : 0 < U) {s r₁ r₂ l : ℕ} (hs : 1 ≤ s) (hr₁ : 1 ≤ r₁)
    (h₂ : U < (r₂ : ℝ) * l) (hB : (s * r₁ * r₂ * l : ℝ) ≤ B) : r₁ ∈ Icc 1 ⌊B / U / s⌋₊ := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : (0 : ℝ) < r₁ := by exact_mod_cast hr₁
  refine mem_Icc.2 ⟨hr₁, Nat.le_floor ?_⟩
  rw [div_div, le_div_iff₀ (by positivity)]
  have : (s : ℝ) * r₁ * U ≤ s * r₁ * (r₂ * l) := by gcongr
  nlinarith

/-- The right side of [B, (5.8)] as a sum over quadruples `(s, r₁, r₂, l)`. -/
theorem sum_innerS_eq {B U : ℝ} (hB : 0 < B) (hU : 1 ≤ U) :
    ∑ s ∈ (Icc 1 ⌊B⌋₊).filter Odd, innerS B U s =
    ∑ q ∈ (Icc 1 ⌊B⌋₊ ×ˢ Icc 1 ⌊B⌋₊ ×ˢ Icc 1 ⌊B⌋₊ ×ˢ Icc 1 ⌊B⌋₊).filter
      (fun q : ℕ × ℕ × ℕ × ℕ => Odd q.1 ∧ Nat.Coprime q.2.1 q.2.2.1 ∧ Odd (q.2.1 * q.2.2.1) ∧
        Squarefree q.2.1 ∧ Squarefree q.2.2.1 ∧ Squarefree q.2.2.2 ∧
        Nat.Coprime q.2.2.2 (2 * (q.2.1 * q.2.2.1)) ∧
        U < (q.2.1 : ℝ) * q.2.2.2 ∧ U < (q.2.2.1 : ℝ) * q.2.2.2 ∧
        B / 2 < (q.1 : ℝ) * q.2.1 * q.2.2.1 * q.2.2.2 ∧ (q.1 * q.2.1 * q.2.2.1 * q.2.2.2 : ℝ) ≤ B),
      (μ q.2.1 : ℝ) * μ q.2.2.1 := by
  have hU0 : 0 < U := by linarith
  set I := Icc 1 ⌊B⌋₊
  rw [sum_filter, sum_filter, sum_product]
  refine sum_congr rfl fun s hs => ?_
  simp only [sum_product]
  have hs1 : 1 ≤ s := (mem_Icc.1 hs).1
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  by_cases ho : Odd s
  swap
  · rw [if_neg ho]; symm
    exact sum_eq_zero fun _ _ => sum_eq_zero fun _ _ => sum_eq_zero fun _ _ => if_neg (by tauto)
  rw [if_pos ho, innerS]
  have hJ : Icc 1 ⌊B / U / s⌋₊ ⊆ I := by
    refine Icc_subset_Icc le_rfl (Nat.floor_le_floor ?_)
    rw [div_div, div_le_iff₀ (by positivity)]
    have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    have : (1 : ℝ) ≤ U * s := by nlinarith
    nlinarith
  rw [sum_eq_sum_ite_of_subset hJ]
  refine sum_congr rfl fun r₁ hr₁ => ?_
  have h1 := (mem_Icc.1 hr₁).1
  by_cases hJ₁ : r₁ ∈ Icc 1 ⌊B / U / s⌋₊
  swap
  · rw [if_neg hJ₁]; symm
    refine sum_eq_zero fun r₂ hr₂ => sum_eq_zero fun l hl => if_neg ?_
    rintro ⟨-, -, -, -, -, -, -, -, hU₂, -, hB'⟩
    exact hJ₁ (mem_rrange hU0 hs1 h1 hU₂ hB')
  rw [if_pos hJ₁, sum_eq_sum_ite_of_subset hJ]
  refine sum_congr rfl fun r₂ hr₂ => ?_
  have h2 := (mem_Icc.1 hr₂).1
  have hL : Ioc ⌊aL (B / U / s) (B / s) r₁ r₂⌋₊ ⌊bL (B / s) r₁ r₂⌋₊ ⊆ I := by
    intro l hl
    have hl' := (mem_lrange hB hU0 hs1 h1 h2).1 hl
    have hl1 : 1 ≤ l := by have := (mem_Ioc.1 hl).1; omega
    refine mem_Icc.2 ⟨hl1, Nat.le_floor ?_⟩
    have : (l : ℝ) ≤ s * r₁ * r₂ * l := by
      have : (1 : ℝ) ≤ s * r₁ * r₂ := by
        have : (1 : ℕ) ≤ s * r₁ * r₂ := Nat.one_le_iff_ne_zero.2 (by positivity)
        exact_mod_cast this
      nlinarith [show (0 : ℝ) ≤ l from Nat.cast_nonneg l]
    linarith [hl'.2.2.2]
  by_cases hJ₂ : r₂ ∈ Icc 1 ⌊B / U / s⌋₊
  swap
  · rw [if_neg hJ₂]; symm
    refine sum_eq_zero fun l hl => if_neg ?_
    rintro ⟨-, -, -, -, -, -, -, hU₁, -, -, hB'⟩
    refine hJ₂ (mem_rrange hU0 hs1 h2 hU₁ ?_)
    calc (s * r₂ * r₁ * l : ℝ) = s * r₁ * r₂ * l := by ring
      _ ≤ B := hB'
  rw [if_pos hJ₂, cntSq, sum_eq_sum_ite_of_subset hL]
  by_cases hg : Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂)
  swap
  · rw [if_neg hg]; symm
    exact sum_eq_zero fun l _ => if_neg (by tauto)
  rw [if_pos hg, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  have hmem := mem_lrange (l := l) hB hU0 hs1 h1 h2
  by_cases hs : Squarefree r₁ ∧ Squarefree r₂
  · by_cases hl' : l ∈ Ioc ⌊aL (B / U / s) (B / s) r₁ r₂⌋₊ ⌊bL (B / s) r₁ r₂⌋₊
    · have := hmem.1 hl'
      rw [if_pos hl']
      by_cases hc : Squarefree l ∧ Nat.Coprime l (2 * (r₁ * r₂))
      · rw [if_pos hc, mul_one, if_pos]
        exact ⟨ho, hg.1, hg.2, hs.1, hs.2, hc.1, hc.2, this.1, this.2.1, this.2.2.1, this.2.2.2⟩
      · rw [if_neg hc, mul_zero, if_neg]
        rintro ⟨-, -, -, -, -, h5, h6, -⟩; exact hc ⟨h5, h6⟩
    · rw [if_neg hl', mul_zero, if_neg]
      rintro ⟨-, -, -, -, -, -, -, h7, h8, h9, h10⟩; exact hl' (hmem.2 ⟨h7, h8, h9, h10⟩)
  · have : (μ r₁ : ℝ) * μ r₂ = 0 := by
      rcases not_and_or.1 hs with h | h <;>
        simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    rw [this, zero_mul]
    split_ifs <;> simp_all

/-- The change of variables `(s, r₁, r₂, l) ↦ (s r₁ r₂ l, r₁ l, r₂ l)` between (5.7) and (5.8). -/
theorem quads_eq_triples {B U : ℝ} (hB : 0 < B) (hU : 0 < U) :
    ∑ q ∈ (Icc 1 ⌊B⌋₊ ×ˢ Icc 1 ⌊B⌋₊ ×ˢ Icc 1 ⌊B⌋₊ ×ˢ Icc 1 ⌊B⌋₊).filter
      (fun q : ℕ × ℕ × ℕ × ℕ => Odd q.1 ∧ Nat.Coprime q.2.1 q.2.2.1 ∧ Odd (q.2.1 * q.2.2.1) ∧
        Squarefree q.2.1 ∧ Squarefree q.2.2.1 ∧ Squarefree q.2.2.2 ∧
        Nat.Coprime q.2.2.2 (2 * (q.2.1 * q.2.2.1)) ∧
        U < (q.2.1 : ℝ) * q.2.2.2 ∧ U < (q.2.2.1 : ℝ) * q.2.2.2 ∧
        B / 2 < (q.1 : ℝ) * q.2.1 * q.2.2.1 * q.2.2.2 ∧ (q.1 * q.2.1 * q.2.2.1 * q.2.2.2 : ℝ) ≤ B),
      (μ q.2.1 : ℝ) * μ q.2.2.1 =
    ∑ p ∈ (Icc 1 ⌊B⌋₊ ×ˢ Icc 1 ⌊B⌋₊ ×ˢ Icc 1 ⌊B⌋₊).filter
      (fun p : ℕ × ℕ × ℕ => Odd p.1 ∧ B / 2 < p.1 ∧ p.2.1 ∣ p.1 ∧ p.2.2 ∣ p.1 ∧
        U < p.2.1 ∧ U < p.2.2 ∧ Squarefree p.2.1 ∧ Squarefree p.2.2),
      (μ p.2.1 : ℝ) * μ p.2.2 := by
  refine sum_nbij' (fun q => (q.1 * q.2.1 * q.2.2.1 * q.2.2.2, q.2.1 * q.2.2.2, q.2.2.1 * q.2.2.2))
    (fun p => (p.1 / Nat.lcm p.2.1 p.2.2, p.2.1 / Nat.gcd p.2.1 p.2.2,
      p.2.2 / Nat.gcd p.2.1 p.2.2, Nat.gcd p.2.1 p.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨s, r₁, r₂, l⟩ hq
    simp only [mem_filter, mem_product, mem_Icc] at hq ⊢
    obtain ⟨⟨⟨hs1, -⟩, ⟨hr₁, -⟩, ⟨hr₂, -⟩, ⟨hl1, -⟩⟩, ho, hcop, hodd, hsq₁, hsq₂, hsql, hcl,
      hU₁, hU₂, hB₁, hB₂⟩ := hq
    have hm1 : 1 ≤ s * r₁ * r₂ * l := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hmN : s * r₁ * r₂ * l ≤ ⌊B⌋₊ := Nat.le_floor (by push_cast; exact hB₂)
    have hd₁ : r₁ * l ∣ s * r₁ * r₂ * l := ⟨s * r₂, by ring⟩
    have hd₂ : r₂ * l ∣ s * r₁ * r₂ * l := ⟨s * r₁, by ring⟩
    have hlo : Odd l := Nat.coprime_two_right.1 (hcl.coprime_dvd_right (dvd_mul_right 2 _))
    have hc₁ : Nat.Coprime r₁ l :=
      (hcl.coprime_dvd_right (Dvd.intro_left _ (by ring : 2 * r₂ * r₁ = 2 * (r₁ * r₂)))).symm
    have hc₂ : Nat.Coprime r₂ l :=
      (hcl.coprime_dvd_right (Dvd.intro_left _ (by ring : 2 * r₁ * r₂ = 2 * (r₁ * r₂)))).symm
    refine ⟨⟨⟨hm1, hmN⟩, ⟨Nat.one_le_iff_ne_zero.2 (by positivity),
      (Nat.le_of_dvd (by omega) hd₁).trans hmN⟩, ⟨Nat.one_le_iff_ne_zero.2 (by positivity),
      (Nat.le_of_dvd (by omega) hd₂).trans hmN⟩⟩, ?_, by push_cast; exact hB₁, hd₁, hd₂,
      by push_cast; exact hU₁, by push_cast; exact hU₂,
      Nat.squarefree_mul_iff.2 ⟨hc₁, hsq₁, hsql⟩, Nat.squarefree_mul_iff.2 ⟨hc₂, hsq₂, hsql⟩⟩
    rw [mul_assoc s, mul_assoc s]
    exact Nat.odd_mul.2 ⟨ho, Nat.odd_mul.2 ⟨hodd, hlo⟩⟩ |>.of_dvd_nat (by
      rw [← mul_assoc s, ← mul_assoc s, mul_assoc (s * r₁)])
  · rintro ⟨m, d₁, d₂⟩ hp
    simp only [mem_filter, mem_product, mem_Icc] at hp ⊢
    obtain ⟨⟨⟨hm1, hmN⟩, ⟨hd₁1, hd₁N⟩, ⟨hd₂1, hd₂N⟩⟩, ho, hB₁, hd₁, hd₂, hU₁, hU₂, hsq₁, hsq₂⟩ := hp
    have hg : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left _ hd₁1
    obtain ⟨r₁, hr₁⟩ := Nat.gcd_dvd_left d₁ d₂
    obtain ⟨r₂, hr₂⟩ := Nat.gcd_dvd_right d₁ d₂
    set g := Nat.gcd d₁ d₂ with hgdef
    have hcop : Nat.Coprime r₁ r₂ := by
      have := Nat.coprime_div_gcd_div_gcd (m := d₁) (n := d₂) hg
      rwa [← hgdef, hr₁, hr₂, Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg] at this
    clear_value g
    subst hr₁ hr₂
    rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg, Nat.lcm_mul_left,
      hcop.lcm_eq_mul]
    obtain ⟨s, rfl⟩ : g * (r₁ * r₂) ∣ m := by
      rw [← hcop.lcm_eq_mul, ← Nat.lcm_mul_left]; exact Nat.lcm_dvd hd₁ hd₂
    have hL0 : 0 < g * (r₁ * r₂) := by
      rcases Nat.eq_zero_or_pos (g * (r₁ * r₂)) with h | h
      · rw [h, zero_mul] at hm1; omega
      · exact h
    rw [Nat.mul_div_cancel_left _ hL0]
    have hr₁0 : 0 < r₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hd₁1)
    have hr₂0 : 0 < r₂ := Nat.pos_of_ne_zero (by rintro rfl; simp at hd₂1)
    have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hm1)
    have hsN : s ≤ ⌊B⌋₊ := le_trans (Nat.le_mul_of_pos_left s hL0) hmN
    have hsq₁' := Nat.squarefree_mul_iff.1 hsq₁
    have hsq₂' := Nat.squarefree_mul_iff.1 hsq₂
    have hodd' := Nat.odd_mul.1 ho
    have hgo := (Nat.odd_mul.1 hodd'.1).1
    have hro := (Nat.odd_mul.1 hodd'.1).2
    have hmeq : ((g * (r₁ * r₂) * s : ℕ) : ℝ) = (s : ℝ) * r₁ * r₂ * g := by push_cast; ring
    refine ⟨⟨⟨hs0, hsN⟩, ⟨hr₁0, le_trans (Nat.le_mul_of_pos_left _ hg) hd₁N⟩,
      ⟨hr₂0, le_trans (Nat.le_mul_of_pos_left _ hg) hd₂N⟩, ⟨hg, ?_⟩⟩, hodd'.2, hcop, hro,
      hsq₁'.2.2, hsq₂'.2.2, hsq₁'.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (Nat.le_mul_of_pos_right _ hr₁0) hd₁N
    · refine Nat.Coprime.mul_right (Nat.coprime_two_right.2 hgo) ?_
      exact Nat.Coprime.mul_right hsq₁'.1 hsq₂'.1
    · push_cast at hU₁; linarith
    · push_cast at hU₂; linarith
    · rw [← hmeq]; exact hB₁
    · rw [← hmeq]; exact (Nat.cast_le.2 hmN).trans (Nat.floor_le hB.le)
  · rintro ⟨s, r₁, r₂, l⟩ hq
    simp only [mem_filter, mem_product, mem_Icc] at hq
    obtain ⟨⟨-, ⟨hr₁, -⟩, ⟨hr₂, -⟩, ⟨hl1, -⟩⟩, -, hcop, -⟩ := hq
    have hl0 : 0 < l := hl1
    simp only [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul, Nat.lcm_mul_right, hcop.lcm_eq_mul,
      Nat.mul_div_cancel _ hl0]
    rw [show s * r₁ * r₂ * l = s * (r₁ * r₂ * l) by ring,
      Nat.mul_div_cancel _ (Nat.mul_pos (Nat.mul_pos hr₁ hr₂) hl0)]
  · rintro ⟨m, d₁, d₂⟩ hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨-, ⟨hd₁1, -⟩, -⟩, -, -, hd₁, hd₂, -⟩ := hp
    have hg : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left _ hd₁1
    simp only [Prod.mk.injEq]
    refine ⟨?_, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)⟩
    have hL : d₁ / Nat.gcd d₁ d₂ * (d₂ / Nat.gcd d₁ d₂) * Nat.gcd d₁ d₂ = Nat.lcm d₁ d₂ := by
      rw [mul_right_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), Nat.lcm,
        Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
    rw [show ∀ a b c e : ℕ, a * b * c * e = a * (b * c * e) from fun a b c e => by ring, hL,
      Nat.div_mul_cancel (Nat.lcm_dvd hd₁ hd₂)]
  · rintro ⟨s, r₁, r₂, l⟩ hq
    simp only [mem_filter, mem_product, mem_Icc] at hq
    obtain ⟨-, -, -, -, -, -, hsql, hcl, -⟩ := hq
    have hc₁ : Nat.Coprime r₁ l :=
      (hcl.coprime_dvd_right (Dvd.intro_left _ (by ring : 2 * r₂ * r₁ = 2 * (r₁ * r₂)))).symm
    have hc₂ : Nat.Coprime r₂ l :=
      (hcl.coprime_dvd_right (Dvd.intro_left _ (by ring : 2 * r₁ * r₂ = 2 * (r₁ * r₂)))).symm
    simp only
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc₁,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc₂]
    have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsql
    push_cast
    have h' : ((μ l : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast this
    linear_combination (-(μ r₁ : ℝ) * μ r₂) * h'


/-- **The reduction [B, (5.7)–(5.8)]**: `S₁(U, W) = ∑_{s ≤ x/W odd} innerS(x/W, U, s)`. -/
theorem S1_eq {x U W : ℝ} (hx : 0 < x) (hW : 0 < W) (hU : 1 ≤ U) :
    S1 x U W = ∑ s ∈ (Icc 1 ⌊x / W⌋₊).filter Odd, innerS (x / W) U s := by
  rw [S1_eq_triples hx hW (by linarith), sum_innerS_eq (div_pos hx hW) hU,
    quads_eq_triples (div_pos hx hW) (by linarith)]

/-! ### The main term (5.19) -/

theorem integral_ite_le {M : ℝ} (hM : M ≤ 1) :
    ∫ u in (1 / 2 : ℝ)..1, (if M ≤ u then (1 : ℝ) else 0) = 1 - max (1 / 2) M := by
  have : (fun u : ℝ => if M ≤ u then (1 : ℝ) else 0) = (Set.Ici M).indicator 1 := by
    ext u; simp [Set.indicator, Set.mem_Ici]
  rw [this, intervalIntegral.integral_of_le (by norm_num), integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one]
  rcases le_or_gt M (1 / 2) with h | h
  · rw [max_eq_left h, measureReal_def, Measure.restrict_apply_univ,
      show Set.Ici M ∩ Set.Ioc (1 / 2 : ℝ) 1 = Set.Ioc (1 / 2 : ℝ) 1 from
        Set.inter_eq_right.2 (fun u (hu : u ∈ Set.Ioc (1 / 2 : ℝ) 1) => le_trans h hu.1.le),
      Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]
  · rw [max_eq_right h.le, show Set.Ici M ∩ Set.Ioc (1 / 2 : ℝ) 1 = Set.Icc M 1 by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩,
      measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]

/-- `g₂(t)` [B, Lemma 5.1.2]. -/
noncomputable def g2 (t : ℝ) : ℝ :=
  ∑ r₁ ∈ Icc 1 ⌊t⌋₊, ∑ r₂ ∈ Icc 1 ⌊t⌋₊,
    if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
      (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0

theorem monotone_ite_le (M : ℝ) : Monotone fun u : ℝ => if M ≤ u then (1 : ℝ) else 0 := by
  intro u v huv
  simp only
  split_ifs with h1 h2 <;> first | exact absurd (h1.trans huv) h2 | rfl | norm_num

/-- [B, (5.19)]: `∫_{1/2}^1 g₂(uy) du = ∑_{r₁,r₂ ≤ y} … (1 - max(1/2, r₁/y, r₂/y))`. -/
theorem integral_g2 {y : ℝ} (hy : 0 < y) :
    ∫ u in (1 / 2 : ℝ)..1, g2 (u * y) =
      ∑ r₁ ∈ Icc 1 ⌊y⌋₊, ∑ r₂ ∈ Icc 1 ⌊y⌋₊,
        (if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
          (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0) * wM y r₁ r₂ := by
  set c : ℕ → ℕ → ℝ := fun r₁ r₂ => if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
    (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0
  have hpt : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) 1, g2 (u * y) = ∑ r₁ ∈ Icc 1 ⌊y⌋₊, ∑ r₂ ∈ Icc 1 ⌊y⌋₊,
      c r₁ r₂ * (if max ((r₁ : ℝ) / y) (r₂ / y) ≤ u then 1 else 0) := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hfilt : Icc 1 ⌊u * y⌋₊ = (Icc 1 ⌊y⌋₊).filter (fun r : ℕ => (r : ℝ) ≤ u * y) := by
      ext r
      simp only [mem_Icc, mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        have h3 : (r : ℝ) ≤ u * y := (Nat.cast_le.2 h2).trans (Nat.floor_le (by nlinarith [hu.1]))
        exact ⟨⟨h1, Nat.le_floor (h3.trans (by nlinarith [hu.2]))⟩, h3⟩
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, Nat.le_floor h3⟩
    have hmax : ∀ r₁ r₂ : ℕ, max ((r₁ : ℝ) / y) (r₂ / y) ≤ u ↔
        (r₁ : ℝ) ≤ u * y ∧ (r₂ : ℝ) ≤ u * y := by
      intro r₁ r₂; rw [max_le_iff, div_le_iff₀ hy, div_le_iff₀ hy]
    rw [g2, hfilt, sum_filter]
    refine sum_congr rfl fun r₁ _ => ?_
    rw [sum_filter]
    simp only [hmax]
    by_cases h1 : (r₁ : ℝ) ≤ u * y
    · rw [if_pos h1]
      refine sum_congr rfl fun r₂ _ => ?_
      by_cases h2 : (r₂ : ℝ) ≤ u * y
      · simp [h1, h2, c]
      · simp [h2]
    · rw [if_neg h1]; symm
      exact sum_eq_zero fun r₂ _ => by simp [h1]
  have hint : ∀ r₁ r₂, IntervalIntegrable
      (fun u : ℝ => c r₁ r₂ * (if max ((r₁ : ℝ) / y) (r₂ / y) ≤ u then 1 else 0))
      volume (1 / 2) 1 := fun r₁ r₂ =>
    ((monotone_ite_le _).intervalIntegrable).const_mul _
  have hint2 : ∀ r₁, IntervalIntegrable (fun u : ℝ => ∑ r₂ ∈ Icc 1 ⌊y⌋₊,
      c r₁ r₂ * (if max ((r₁ : ℝ) / y) (r₂ / y) ≤ u then 1 else 0)) volume (1 / 2) 1 := by
    intro r₁
    have := IntervalIntegrable.sum (Icc 1 ⌊y⌋₊) (fun r₂ _ => hint r₁ r₂)
    convert this using 1; ext u; simp [Finset.sum_apply]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finset_sum
    (fun r₁ _ => hint2 r₁)]
  refine sum_congr rfl fun r₁ hr₁ => ?_
  rw [intervalIntegral.integral_finset_sum (fun r₂ _ => hint r₁ r₂)]
  refine sum_congr rfl fun r₂ hr₂ => ?_
  rw [intervalIntegral.integral_const_mul, integral_ite_le, wM]
  have h1 : (r₁ : ℝ) ≤ y := (Nat.cast_le.2 (mem_Icc.1 hr₁).2).trans (Nat.floor_le hy.le)
  have h2 : (r₂ : ℝ) ≤ y := (Nat.cast_le.2 (mem_Icc.1 hr₂).2).trans (Nat.floor_le hy.le)
  exact max_le ((div_le_one hy).2 h1) ((div_le_one hy).2 h2)


/-! ### The triple sum and `H₂` -/

/-- The triple sum `T₂(S) = ∑_{s ≤ S odd} (1/s) ∫_{1/2}^1 g₂(uS/s) du` [B, (5.28)]. -/
noncomputable def T2 (S : ℝ) : ℝ :=
  ∑ s ∈ Icc 1 ⌊S⌋₊, if Odd s then (1 / s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, g2 (u * S / s) else 0

/-- `H₂(S)` [B, (5.35)]: `(4/π²) max(T₂(S), 0)` for `S < 16`, `0.15107` for `S ≥ 16`. (The book uses
its computable upper bound `G₂(S)` in place of `T₂(S)`; `G₂ ≥ T₂` and `G₂ ≥ 0`, so `G₂ ≥ max(T₂, 0)`
and the book's statements (5.36), (5.37) about `H₂` remain valid for ours.) -/
noncomputable def H2 (S : ℝ) : ℝ := if S < 16 then 4 / π ^ 2 * max (T2 S) 0 else 0.15107

theorem H2_nonneg (S : ℝ) : 0 ≤ H2 S := by
  unfold H2; split_ifs
  · have := le_max_right (T2 S) 0; positivity
  · norm_num

/-- **Trusted** [B, (5.31) and p. 92]: `T₂(S) ≤ 0.37273` for `S ≥ 16`. For `S ≥ 10⁵` this follows
from Lemma 5.1.2 (whose range `x ≤ 10⁶` is an interval-arithmetic computation) and the numerics
after (5.30); for `16 ≤ S < 10⁵` it is a direct computation. -/
theorem T2_le {S : ℝ} (hS : 16 ≤ S) : T2 S ≤ 0.37273 := by
  sorry

/-- **[B, (5.36)]** (trusted; numerical, from [B, (5.32)]). -/
theorem integral_H2_le {T : ℝ} (hT : 1 ≤ T) :
    ∫ S in (1 : ℝ)..T, H2 S / S ≤ 0.15107 * Real.log T := by
  sorry

/-- `S ↦ H₂(S)/S` is integrable on `[1, T]`. **TODO (provable, not a computation)**: `H₂` is
bounded (`H2_nonneg`, `H2_le`) and measurable (`g₂` is a step function, so `S ↦ ∫ g₂(uS/s) du`
is measurable). -/
theorem intervalIntegrable_H2_div (T : ℝ) :
    IntervalIntegrable (fun S => H2 S / S) MeasureTheory.volume 1 T := by
  sorry

/-- **[B, (5.37)]** (trusted; numerical: `T₂(S) ≤ 1/2` for `S < 16`). -/
theorem H2_le (S : ℝ) : H2 S ≤ 2 / π ^ 2 := by
  sorry

theorem H2_ge {S : ℝ} : 4 / π ^ 2 * T2 S ≤ H2 S := by
  unfold H2
  split_ifs with h
  · have := le_max_left (T2 S) 0; have : (0 : ℝ) < 4 / π ^ 2 := by positivity
    nlinarith
  · have h1 := T2_le (not_lt.1 h)
    have hpi : (3.141592 : ℝ) < π := Real.pi_gt_d6
    have hpi2 : (9.8696 : ℝ) < π ^ 2 := by nlinarith
    calc 4 / π ^ 2 * T2 S ≤ 4 / π ^ 2 * 0.37273 := by gcongr
      _ ≤ 0.15107 := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith

/-- `(1 + 1/√2)(1 - 2^{-3/2})³ ≤ 1`. -/
theorem const_S1_le : (1 + 1 / √2) * (1 - 2 ^ (-(3 / 2) : ℝ)) ^ 3 ≤ 1 := by
  have h2 : (1.414 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2' : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have ha : (2 : ℝ) ^ (-(3 / 2) : ℝ) = 1 / (2 * √2) := by
    rw [rpow_neg (by norm_num), rpow_three_halves 2 (by norm_num), one_div]
  rw [ha]
  have hb : 0.3533 ≤ 1 / (2 * √2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have hb' : 1 / (2 * √2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hc : 1 + 1 / √2 ≤ 1.7073 := by
    have : 1 / √2 ≤ 0.7073 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hd : (1 - 1 / (2 * √2)) ^ 3 ≤ 0.6467 ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have he : 0 ≤ (1 - 1 / (2 * √2)) ^ 3 := pow_nonneg (by linarith) 3
  calc (1 + 1 / √2) * (1 - 1 / (2 * √2)) ^ 3 ≤ 1.7073 * 0.6467 ^ 3 := by
        gcongr
    _ ≤ 1 := by norm_num

/-- The inner sum of (5.8) splits as the main term of (5.10) plus the sum bounded in
Lemma 5.1.1. -/
theorem innerS_sub {B U : ℝ} (s : ℕ) :
    innerS B U s - 4 * (B / s) / π ^ 2 * ∑ r₁ ∈ Icc 1 ⌊B / U / s⌋₊, ∑ r₂ ∈ Icc 1 ⌊B / U / s⌋₊,
        (if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
          (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0) * wM (B / U / s) r₁ r₂ =
      ∑ r₁ ∈ Icc 1 ⌊B / U / s⌋₊, ∑ r₂ ∈ Icc 1 ⌊B / U / s⌋₊,
        (if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
          (μ r₁ : ℝ) * μ r₂ * (cntSq (2 * (r₁ * r₂)) (aL (B / U / s) (B / s) r₁ r₂)
            (bL (B / s) r₁ r₂) - 4 * (B / s) / π ^ 2 / ((σ 1 r₁ : ℝ) * σ 1 r₂) *
              wM (B / U / s) r₁ r₂) else 0) := by
  rw [innerS, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun r₁ _ => ?_
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun r₂ _ => ?_
  split_ifs
  · ring
  · ring

/-- **[B, (5.34)]**: for `x, W > 0` and `U ≥ 1`,
`S₁(U, W) ≤ (x/W) H₂(x/(WU)) + 1.27 ζ(3/2)³ x^{3/2}/(W^{3/2} U)`. -/
theorem S1_bound {x U W : ℝ} (hx : 0 < x) (hW : 0 < W) (hU : 1 ≤ U) :
    S1 x U W ≤ x / W * H2 (x / (W * U)) +
      1.27 * (riemannZeta (3 / 2)).re ^ 3 * x ^ (3 / 2 : ℝ) / (W ^ (3 / 2 : ℝ) * U) := by
  have hU0 : 0 < U := by linarith
  have hB : 0 < x / W := div_pos hx hW
  set B := x / W with hBdef
  set S := B / U with hSdef
  have hS : x / (W * U) = S := by rw [hSdef, hBdef, div_div]
  rw [hS, S1_eq hx hW hU]
  set ζ := (riemannZeta (3 / 2)).re
  set c : ℝ := 1 - 2 ^ (-(3 / 2) : ℝ)
  set E := 1.27 * (1 + 1 / √2) * (c * ζ) ^ 2
  set main : ℕ → ℝ := fun s => 4 * (B / s) / π ^ 2 * ∑ r₁ ∈ Icc 1 ⌊B / U / s⌋₊,
    ∑ r₂ ∈ Icc 1 ⌊B / U / s⌋₊, (if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
      (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0) * wM (B / U / s) r₁ r₂
  set I := Icc 1 ⌊B⌋₊
  -- Each inner sum is its main term plus an error.
  have hs_err : ∀ s ∈ I.filter Odd, innerS B U s ≤ main s + E * (B / U / s) * √(B / s) := by
    intro s hs
    have hs1 : 1 ≤ s := (mem_Icc.1 (mem_filter.1 hs).1).1
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
    have h := lemma_5_1_1 (y := B / U / s) (z := B / s) (by positivity) (by positivity)
    rw [← innerS_sub] at h
    have := (abs_le.1 h).2
    simp only [main, E, c, ζ]; linarith
  have hmain : ∑ s ∈ I.filter Odd, main s = 4 * B / π ^ 2 * T2 S := by
    have hsub : (Icc 1 ⌊S⌋₊).filter Odd ⊆ I.filter Odd := by
      refine filter_subset_filter _ (Icc_subset_Icc le_rfl (Nat.floor_le_floor ?_))
      rw [hSdef, div_le_iff₀ hU0]; nlinarith
    rw [← sum_subset hsub]
    · rw [T2, ← sum_filter, mul_sum]
      refine sum_congr rfl fun s hs => ?_
      have hs1 : 1 ≤ s := (mem_Icc.1 (mem_filter.1 hs).1).1
      have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
      have hy : 0 < B / U / s := by positivity
      simp only [main]
      rw [show (fun u : ℝ => g2 (u * S / s)) = fun u => g2 (u * (B / U / s)) by
        ext u; rw [hSdef, mul_div_assoc], integral_g2 hy]
      field_simp
    · intro s hs hs'
      have hs1 : 1 ≤ s := (mem_Icc.1 (mem_filter.1 hs).1).1
      have hlt : S < s := by
        by_contra h; push Not at h
        exact hs' (mem_filter.2 ⟨mem_Icc.2 ⟨hs1, Nat.le_floor h⟩, (mem_filter.1 hs).2⟩)
      have hy : ⌊B / U / s⌋₊ = 0 := by
        rw [Nat.floor_eq_zero, ← hSdef, div_lt_one (by positivity)]; exact hlt
      simp only [main, hy]; simp
  have herr : ∑ s ∈ I.filter Odd, E * (B / U / s) * √(B / s) ≤ E * (B / U) * √B * (c * ζ) := by
    have hE : 0 ≤ E := by positivity
    calc ∑ s ∈ I.filter Odd, E * (B / U / s) * √(B / s)
        = E * (B / U) * √B * ∑ s ∈ I.filter Odd, 1 / (s : ℝ) ^ (3 / 2 : ℝ) := by
          rw [mul_sum]
          refine sum_congr rfl fun s hs => ?_
          have hs0 : (0 : ℝ) < s := by exact_mod_cast (mem_Icc.1 (mem_filter.1 hs).1).1
          rw [rpow_three_halves _ hs0.le, sqrt_div' _ hs0.le]
          have : 0 < √(s : ℝ) := sqrt_pos.2 hs0
          field_simp
      _ ≤ E * (B / U) * √B * (c * ζ) := by
          gcongr
          exact sum_odd_rpow_le_zeta _
  have hζ : 0 ≤ ζ := zeta_three_halves_nonneg
  have hc : 0 ≤ c := one_sub_two_rpow_pos.le
  have hconst : E * (c * ζ) ≤ 1.27 * ζ ^ 3 := by
    have := const_S1_le
    calc E * (c * ζ) = 1.27 * ((1 + 1 / √2) * c ^ 3) * ζ ^ 3 := by simp only [E]; ring
      _ ≤ 1.27 * 1 * ζ ^ 3 := by gcongr
      _ = 1.27 * ζ ^ 3 := by ring
  have hpow : x ^ (3 / 2 : ℝ) / (W ^ (3 / 2 : ℝ) * U) = B / U * √B := by
    rw [← div_div, ← div_rpow hx.le hW.le, ← hBdef, rpow_three_halves _ hB.le]; ring
  calc ∑ s ∈ I.filter Odd, innerS B U s
      ≤ ∑ s ∈ I.filter Odd, (main s + E * (B / U / s) * √(B / s)) := sum_le_sum hs_err
    _ = 4 * B / π ^ 2 * T2 S + ∑ s ∈ I.filter Odd, E * (B / U / s) * √(B / s) := by
        rw [sum_add_distrib, hmain]
    _ ≤ B * H2 S + 1.27 * ζ ^ 3 * x ^ (3 / 2 : ℝ) / (W ^ (3 / 2 : ℝ) * U) := by
        have h1 : 4 * B / π ^ 2 * T2 S ≤ B * H2 S := by
          have := H2_ge (S := S)
          calc 4 * B / π ^ 2 * T2 S = B * (4 / π ^ 2 * T2 S) := by ring
            _ ≤ B * H2 S := by gcongr
        have h2 : E * (B / U) * √B * (c * ζ) ≤ 1.27 * ζ ^ 3 * x ^ (3 / 2 : ℝ) /
            (W ^ (3 / 2 : ℝ) * U) := by
          rw [mul_div_assoc, hpow]
          have : 0 ≤ B / U * √B := by positivity
          calc E * (B / U) * √B * (c * ζ) = E * (c * ζ) * (B / U * √B) := by ring
            _ ≤ 1.27 * ζ ^ 3 * (B / U * √B) := by gcongr
        linarith

end TernaryGoldbach.MinorArcs
