import TernaryGoldbach.MinorArcs.LargeSieveArcs
import TernaryGoldbach.MinorArcs.Plancherel
import TernaryGoldbach.MinorArcs.LSQuot6

/-!
# Proof of [H, Prop. 12.1.2] and [H, Cor. 12.2.5]

`prop_12_1_2`: for `aₙ` supported on primes `> √x` (in `ℓ¹`), `δ₀ ≥ 2`, `Q₀ ≥ 1`,
`δ₀Q₀² ≤ x/2`, `Q = √(x/2δ₀)`, and `C` with `G_q(2Q₀/sq) ≤ C G_q(2Q/sq)` for even `q ≤ 2Q₀`,
`1 ≤ s ≤ 2Q₀/q`:  `∫_{𝔐_{δ₀,Q₀}} |S|² ≤ C Σ |aₙ|²`.

Proof ([H, §12.1], [Bom74, Thm. 7A]):
1. `∫_{(0,1] ∩ 𝔐_{Q₀}} |S|² ≤ ∫_ℝ F_{Q₀}` (`integral_majorArcs_le`), where
   `F_R(β) = Σ_{q̃ ≤ 2R, |β| < w_q(R)} Σ_{b mod q}^* |S(b/q + β)|²`;
2. `∫_ℝ F_Q ≤ ∫_0^1 |S|² = Σ |aₙ|²` (`sum_arcs_le_integral`, Plancherel);
3. pointwise `F_{Q₀}(β) ≤ C F_Q(β)`: by Bombieri's identity (`totient_mul_sum_units_lift`) and
   `weight_sum`, a character of conductor `c` has weight `(c/φ(c)) κ_c G_{c̃}(m_R(β)/c̃)` in
   `F_R(β)`, with `m_R(β)` the largest `n ≤ 2R` with `n|β|x < δ₀R`; then use `hC` with
   `s = 2Q₀/m_{Q₀}(β)` and `⌊m_{Q₀} Q/Q₀⌋ ≤ m_Q`.

**Change from [H]:** we assume `δ₀ ≥ 2` (not `δ₀ ≥ 1`): the proof needs every prime `n > √x` to be
coprime to every modulus `q ≤ 2Q = √(2x/δ₀)`, which needs `2Q ≤ √x`.  [H] applies the result with
`δ₀ = 8`.
-/

open MeasureTheory Set Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs)
open TernaryGoldbach (expTsum)

/-! ## The function `|S|²` -/

theorem expTsum_periodic (a : ℕ → ℂ) : Function.Periodic (expTsum a) 1 := by
  intro α
  unfold expTsum
  refine tsum_congr fun n => ?_
  rw [mul_add, mul_one, TernaryGoldbach.e_add]
  have : TernaryGoldbach.e (n : ℝ) = 1 := (TernaryGoldbach.e_eq_one_iff _).2 ⟨n, by simp⟩
  rw [this, mul_one]

/-! ## Monotonicity of `G_q` -/

theorem Gq_nonneg (q : ℕ) (R : ℝ) : 0 ≤ Gq q R :=
  Finset.sum_nonneg fun r _ => by positivity

theorem Gq_mono {q : ℕ} {R R' : ℝ} (h : ⌊R⌋₊ ≤ ⌊R'⌋₊) : Gq q R ≤ Gq q R' := by
  unfold Gq
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => by positivity
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_Icc] at hr ⊢
  exact ⟨⟨hr.1.1, hr.1.2.trans h⟩, hr.2⟩

theorem Gq_eq_zero {q : ℕ} {R : ℝ} (h : R < 1) : Gq q R = 0 := by
  unfold Gq
  rw [Finset.sum_eq_zero]
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_Icc] at hr
  have : ⌊R⌋₊ = 0 := Nat.floor_eq_zero.2 h
  omega

theorem one_le_Gq_two {R : ℝ} (hR : 1 ≤ R) : 1 ≤ Gq 2 R := by
  unfold Gq
  have h1 : 1 ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r 2) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast hR)⟩, Nat.coprime_one_left 2⟩
  refine le_trans ?_ (Finset.single_le_sum (fun r _ => by positivity) h1)
  simp

/-! ## The moduli active at `β` -/

/-- `m_R(β)`: the largest `n ≤ 2R` with `n|β|x < δ₀R`. -/
noncomputable def mR (δ₀ R x β : ℝ) : ℕ :=
  Nat.findGreatest (fun n : ℕ => (n : ℝ) * |β| * x < δ₀ * R) ⌊2 * R⌋₊

theorem mR_le (δ₀ R x β : ℝ) : mR δ₀ R x β ≤ ⌊2 * R⌋₊ := Nat.findGreatest_le _

theorem mR_spec {δ₀ R x β : ℝ} (h : mR δ₀ R x β ≠ 0) :
    ((mR δ₀ R x β : ℕ) : ℝ) * |β| * x < δ₀ * R := Nat.findGreatest_of_ne_zero rfl h

/-- `q` is active at `β` (`q̃ ≤ 2R`, `|β| < w_q`) iff `q̃ ≤ m_R(β)`. -/
theorem active_iff {δ₀ R x β : ℝ} (hx : 0 < x) {q : ℕ} (hq : 1 ≤ q) :
    ((qt q : ℝ) ≤ 2 * R ∧ |β| < wrad δ₀ R x q) ↔ qt q ≤ mR δ₀ R x β := by
  have hqt : (0 : ℝ) < qt q := by have := two_le_qt hq; exact_mod_cast (by omega : 0 < qt q)
  have hw : |β| < wrad δ₀ R x q ↔ (qt q : ℝ) * |β| * x < δ₀ * R := by
    unfold wrad; rw [lt_div_iff₀ (by positivity)]; constructor <;> intro h <;> linarith
  rw [hw]
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.le_findGreatest (Nat.le_floor h1) h2
  · intro h
    have hm0 : mR δ₀ R x β ≠ 0 := by have := two_le_qt hq; omega
    have hP := mR_spec hm0
    have hmle := mR_le δ₀ R x β
    have hR : ((mR δ₀ R x β : ℕ) : ℝ) ≤ 2 * R := by
      have h2R : (0 : ℝ) ≤ 2 * R := by
        by_contra hneg; push Not at hneg
        have : ⌊2 * R⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
        omega
      exact le_trans (by exact_mod_cast hmle) (Nat.floor_le h2R)
    have hqr : (qt q : ℝ) ≤ mR δ₀ R x β := by exact_mod_cast h
    refine ⟨hqr.trans hR, lt_of_le_of_lt ?_ hP⟩
    have : 0 ≤ |β| * x := by positivity
    nlinarith

theorem Qset_filter_eq {δ₀ R x β : ℝ} (hx : 0 < x) :
    (Qset R).filter (fun q => |β| < wrad δ₀ R x q) =
      (Finset.Icc 1 ⌊((mR δ₀ R x β : ℕ) : ℝ)⌋₊).filter (fun q => (qt q : ℝ) ≤ (mR δ₀ R x β : ℕ)) := by
  ext q
  simp only [Qset, Finset.mem_filter, Finset.mem_Icc, Nat.floor_natCast]
  constructor
  · rintro ⟨⟨⟨hq1, -⟩, hqR⟩, hβ⟩
    have h := (active_iff hx hq1).1 ⟨hqR, hβ⟩
    exact ⟨⟨hq1, (qt_ge q).trans h⟩, by exact_mod_cast h⟩
  · rintro ⟨⟨hq1, -⟩, hqm⟩
    have h : qt q ≤ mR δ₀ R x β := by exact_mod_cast hqm
    obtain ⟨hqR, hβ⟩ := (active_iff hx hq1).2 h
    exact ⟨⟨⟨hq1, ((qt_ge q).trans h).trans (mR_le δ₀ R x β)⟩, hqR⟩, hβ⟩

/-! ## Sums over residues -/

theorem sum_Bset_eq_units {q : ℕ} [NeZero q] (F : ℝ → ℝ) (β : ℝ) :
    ∑ b ∈ Bset q, F ((b : ℝ) / q + β) =
      ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit, F ((b.val : ℝ) / q + β) := by
  rw [Finset.sum_filter, TernaryGoldbach.sum_zmod_eq_sum_range, Bset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcq := Finset.mem_range.1 hc
  rw [ZMod.val_cast_of_lt hcq]
  congr 1
  exact propext (ZMod.isUnit_iff_coprime c q).symm

/-! ## The arc function `F_R` and its character expansion -/

/-- `F_R(β) = Σ_{q̃ ≤ 2R, |β| < w_q} Σ_{b mod q}^* |S(b/q + β)|²`. -/
noncomputable def Farc (a : ℕ → ℂ) (δ₀ R x β : ℝ) : ℝ :=
  ∑ q ∈ Qset R, if |β| < wrad δ₀ R x q then ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 else 0

/-- **Character expansion of `F_R(β)`**: for `L` divisible by all `q ∈ Qset R` and `aₙ` supported
on `n` coprime to `L`, `F_R(β) = Σ_{Ψ mod L} |S_{Ψ⁻¹}(β)|² (c/φ(c)) κ_c G_{c̃}(m_R(β)/c̃)`,
`c = cond Ψ`. -/
theorem Farc_eq {L : ℕ} [NeZero L] {a : ℕ → ℂ} {δ₀ R x β : ℝ} (hx : 0 < x)
    (hqL : ∀ q ∈ Qset R, q ∣ L) (ha : Summable fun n => ‖a n‖)
    (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n L) :
    Farc a δ₀ R x β = ∑ Ψ : DirichletCharacter ℂ L, ‖Schar Ψ⁻¹ a β‖ ^ 2 *
      (Ψ.conductor / Ψ.conductor.totient *
        (kap Ψ.conductor * Gq (qt Ψ.conductor) ((mR δ₀ R x β : ℕ) / qt Ψ.conductor))) := by
  classical
  have hT : ∀ q ∈ Qset R, ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 =
      ∑ Ψ : DirichletCharacter ℂ L,
        (if Ψ.conductor ∣ q then TernaryGoldbach.wq q Ψ.conductor else 0) / q.totient *
          ‖Schar Ψ⁻¹ a β‖ ^ 2 := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.1 (Finset.mem_filter.1 hq).1).1
    have : NeZero q := ⟨by omega⟩
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
    rw [sum_Bset_eq_units (fun t => ‖expTsum a t‖ ^ 2) β]
    have key := totient_mul_sum_units_lift (hqL q hq) ha hcop β
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← key]
    field_simp
  unfold Farc
  rw [Finset.sum_congr rfl fun q hq => by rw [hT q hq], ← Finset.sum_filter, Qset_filter_eq hx,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun Ψ _ => ?_
  have hc1 : 1 ≤ Ψ.conductor := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero Ψ)
  rw [← weight_sum Ψ.conductor hc1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

theorem even_qt (q : ℕ) : Even (qt q) := by
  unfold qt; split_ifs with h
  · exact h
  · exact even_two_mul q

/-- **The key comparison of weights**: `G_{c̃}(m_{Q₀}(β)/c̃) ≤ C G_{c̃}(m_Q(β)/c̃)`. -/
theorem Gq_mR_le {δ₀ Q₀ Q x β C : ℝ} (hx : 0 < x) (hQ₀ : 1 ≤ Q₀) (hQQ : Q₀ ≤ Q) (hC0 : 0 ≤ C)
    (hC : ∀ q : ℕ, 1 ≤ q → Even q → (q : ℝ) ≤ 2 * Q₀ → ∀ s : ℝ, 1 ≤ s → s ≤ 2 * Q₀ / q →
      Gq q (2 * Q₀ / (s * q)) ≤ C * Gq q (2 * Q / (s * q))) (c : ℕ) (hc : 1 ≤ c) :
    Gq (qt c) ((mR δ₀ Q₀ x β : ℕ) / qt c) ≤ C * Gq (qt c) ((mR δ₀ Q x β : ℕ) / qt c) := by
  set m₀ := mR δ₀ Q₀ x β
  set mQ := mR δ₀ Q x β
  set ct := qt c
  have hct : 2 ≤ ct := two_le_qt hc
  have hctr : (0 : ℝ) < ct := by exact_mod_cast (by omega : 0 < ct)
  rcases lt_or_ge m₀ ct with hlt | hge
  · rw [Gq_eq_zero]
    · exact mul_nonneg hC0 (Gq_nonneg _ _)
    · rw [div_lt_one hctr]; exact_mod_cast hlt
  have hm0 : m₀ ≠ 0 := by omega
  have hm0r : (0 : ℝ) < m₀ := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hm2Q₀ : (m₀ : ℝ) ≤ 2 * Q₀ :=
    le_trans (by exact_mod_cast mR_le δ₀ Q₀ x β) (Nat.floor_le (by linarith))
  have hQ₀0 : (0 : ℝ) < Q₀ := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  set s := 2 * Q₀ / m₀
  have hs1 : 1 ≤ s := by rw [le_div_iff₀ hm0r]; linarith
  have hsct : s ≤ 2 * Q₀ / ct := div_le_div_of_nonneg_left (by linarith) hctr (by exact_mod_cast hge)
  have h := hC ct (by omega) (even_qt c) (le_trans (by exact_mod_cast hge) hm2Q₀) s hs1 hsct
  have e1 : 2 * Q₀ / (s * ct) = m₀ / ct := by simp only [s]; field_simp
  have e2 : 2 * Q / (s * ct) = m₀ * Q / Q₀ / ct := by simp only [s]; field_simp
  rw [e1, e2] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Gq_mono ?_) hC0)
  -- `⌊m₀Q/Q₀⌋ ≤ m_Q`
  have hn : ⌊(m₀ : ℝ) * Q / Q₀⌋₊ ≤ mQ := by
    apply Nat.le_findGreatest
    · apply Nat.le_floor
      refine le_trans (Nat.floor_le (by positivity)) ?_
      rw [div_le_iff₀ hQ₀0]; nlinarith
    · have hP := mR_spec hm0
      have hfl : (⌊(m₀ : ℝ) * Q / Q₀⌋₊ : ℝ) ≤ m₀ * Q / Q₀ := Nat.floor_le (by positivity)
      have hb : 0 ≤ |β| * x := by positivity
      calc (⌊(m₀ : ℝ) * Q / Q₀⌋₊ : ℝ) * |β| * x ≤ m₀ * Q / Q₀ * |β| * x := by
            rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hfl hb
        _ = Q / Q₀ * ((m₀ : ℝ) * |β| * x) := by ring
        _ < Q / Q₀ * (δ₀ * Q₀) := by
            exact mul_lt_mul_of_pos_left hP (by positivity)
        _ = δ₀ * Q := by field_simp
  rw [Nat.floor_div_natCast, Nat.floor_div_eq_div]
  exact Nat.div_le_div_right hn

theorem kap_nonneg (c : ℕ) : 0 ≤ kap c := by unfold kap; split_ifs <;> norm_num

/-- **Pointwise**: `F_{Q₀}(β) ≤ C F_Q(β)`. -/
theorem Farc_le {L : ℕ} [NeZero L] {a : ℕ → ℂ} {δ₀ Q₀ Q x β C : ℝ} (hx : 0 < x) (hQ₀ : 1 ≤ Q₀)
    (hQQ : Q₀ ≤ Q) (hC0 : 0 ≤ C)
    (hC : ∀ q : ℕ, 1 ≤ q → Even q → (q : ℝ) ≤ 2 * Q₀ → ∀ s : ℝ, 1 ≤ s → s ≤ 2 * Q₀ / q →
      Gq q (2 * Q₀ / (s * q)) ≤ C * Gq q (2 * Q / (s * q)))
    (hqL₀ : ∀ q ∈ Qset Q₀, q ∣ L) (hqL : ∀ q ∈ Qset Q, q ∣ L) (ha : Summable fun n => ‖a n‖)
    (hcop : ∀ n, a n ≠ 0 → Nat.Coprime n L) :
    Farc a δ₀ Q₀ x β ≤ C * Farc a δ₀ Q x β := by
  rw [Farc_eq hx hqL₀ ha hcop, Farc_eq hx hqL ha hcop, Finset.mul_sum]
  refine Finset.sum_le_sum fun Ψ _ => ?_
  have hc1 : 1 ≤ Ψ.conductor := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero Ψ)
  have hG := Gq_mR_le (δ₀ := δ₀) (x := x) (β := β) hx hQ₀ hQQ hC0 hC Ψ.conductor hc1
  have h1 : 0 ≤ ‖Schar Ψ⁻¹ a β‖ ^ 2 := by positivity
  have h2 : 0 ≤ (Ψ.conductor : ℝ) / Ψ.conductor.totient := by positivity
  have h3 := kap_nonneg Ψ.conductor
  calc ‖Schar Ψ⁻¹ a β‖ ^ 2 * (Ψ.conductor / Ψ.conductor.totient *
        (kap Ψ.conductor * Gq (qt Ψ.conductor) ((mR δ₀ Q₀ x β : ℕ) / qt Ψ.conductor)))
      ≤ ‖Schar Ψ⁻¹ a β‖ ^ 2 * (Ψ.conductor / Ψ.conductor.totient *
        (kap Ψ.conductor * (C * Gq (qt Ψ.conductor) ((mR δ₀ Q x β : ℕ) / qt Ψ.conductor)))) := by
        gcongr
    _ = _ := by ring

/-! ## From arcs to `∫ F_R` -/

theorem setIntegral_Ioo_translate {g : ℝ → ℝ} (c w : ℝ) :
    ∫ y in Ioo (c - w) (c + w), g y = ∫ β, (if |β| < w then g (c + β) else 0) := by
  rw [← integral_indicator measurableSet_Ioo, ← integral_add_left_eq_self _ c]
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  simp only [indicator, Set.mem_Ioo, abs_lt]
  congr 1
  apply propext; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem integrable_ite_abs_lt {T : ℝ → ℝ} (hT : Continuous T) (w : ℝ) :
    Integrable fun β => if |β| < w then T β else 0 := by
  have : (fun β => if |β| < w then T β else 0) = (Ioo (-w) w).indicator T := by
    funext β; simp only [indicator, Set.mem_Ioo, abs_lt]
  rw [this, integrable_indicator_iff measurableSet_Ioo]
  exact (hT.integrableOn_Icc (a := -w) (b := w)).mono_set Ioo_subset_Icc_self

theorem continuous_T {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) (q : ℕ) :
    Continuous fun β : ℝ => ∑ b ∈ Bset q, ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 :=
  continuous_finset_sum _ fun _ _ =>
    ((TernaryGoldbach.continuous_expTsum ha).comp (continuous_const.add continuous_id)).norm.pow 2

theorem integrable_Farc {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) (δ₀ R x : ℝ) :
    Integrable fun β => Farc a δ₀ R x β :=
  integrable_finset_sum _ fun q _ => integrable_ite_abs_lt (continuous_T ha q) _

/-- `Σ_{q,b} ∫_{J_{q,b}} |S|² = ∫_ℝ F_R`. -/
theorem sum_arcs_eq_integral_Farc {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) (δ₀ R x : ℝ) :
    ∑ q ∈ Qset R, ∑ b ∈ Bset q, ∫ y in arc δ₀ R x q b, ‖expTsum a y‖ ^ 2 =
      ∫ β, Farc a δ₀ R x β := by
  unfold Farc
  rw [integral_finset_sum _ fun q _ => integrable_ite_abs_lt (continuous_T ha q) _]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [arc, setIntegral_Ioo_translate]
  have hint : ∀ b ∈ Bset q, Integrable fun β =>
      if |β| < wrad δ₀ R x q then ‖expTsum a ((b : ℝ) / q + β)‖ ^ 2 else 0 := fun b _ =>
    integrable_ite_abs_lt (((TernaryGoldbach.continuous_expTsum ha).comp
      (continuous_const.add continuous_id)).norm.pow 2) _
  rw [← integral_finset_sum _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  simp only
  split_ifs <;> simp

/-! ## The proposition -/

/-- **[H, Prop. 12.1.2]** (with `δ₀ ≥ 2`, see the module docstring).  Let `aₙ` be supported on
primes `> √x`, in `ℓ¹`; `δ₀ ≥ 2`, `Q₀ ≥ 1`, `δ₀Q₀² ≤ x/2`, `Q = √(x/2δ₀)`.  If
`G_q(2Q₀/sq) ≤ C G_q(2Q/sq)` for every even `q ≤ 2Q₀` and `1 ≤ s ≤ 2Q₀/q`, then
`∫_{𝔐_{δ₀,Q₀}} |S(α)|² dα ≤ C Σ |aₙ|²`. -/
theorem prop_12_1_2 {x δ₀ Q₀ C : ℝ} {a : ℕ → ℂ} (ha : PrimeSupported x a)
    (hδ₀ : 2 ≤ δ₀) (hQ₀ : 1 ≤ Q₀) (hx : δ₀ * Q₀ ^ 2 ≤ x / 2)
    (hC : ∀ q : ℕ, 1 ≤ q → Even q → (q : ℝ) ≤ 2 * Q₀ → ∀ s : ℝ, 1 ≤ s → s ≤ 2 * Q₀ / q →
      Gq q (2 * Q₀ / (s * q)) ≤ C * Gq q (2 * √(x / (2 * δ₀)) / (s * q))) :
    ∫ α in Ioc (0 : ℝ) 1 ∩ majorArcs δ₀ Q₀ x, ‖expTsum a α‖ ^ 2 ≤ C * ∑' n, ‖a n‖ ^ 2 := by
  obtain ⟨hsupp, hsum⟩ := ha
  set Q := √(x / (2 * δ₀)) with hQdef
  have hx0 : 0 < x := by nlinarith
  have hδ0 : 0 < δ₀ := by linarith
  have hQsq : Q ^ 2 = x / (2 * δ₀) := Real.sq_sqrt (by positivity)
  have hQ0 : 0 < Q := Real.sqrt_pos.2 (by positivity)
  have hδQ2 : δ₀ * Q ^ 2 = x / 2 := by rw [hQsq]; field_simp
  have hQ₀Q : Q₀ ≤ Q := by
    rw [hQdef]; apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hδx : δ₀ ≤ x / 2 := by
    have : δ₀ * 1 ≤ δ₀ * Q₀ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hδ0.le
    linarith
  have hδQ : δ₀ * Q ≤ x := by
    have hsq : (δ₀ * Q) ^ 2 ≤ x ^ 2 := by
      rw [mul_pow, hQsq]
      rw [show δ₀ ^ 2 * (x / (2 * δ₀)) = δ₀ * x / 2 by field_simp]
      nlinarith
    nlinarith [mul_pos hδ0 hQ0]
  have h2Q : 2 * Q ≤ √x := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, hQsq]
    rw [show (2 : ℝ) ^ 2 * (x / (2 * δ₀)) = 2 * x / δ₀ by field_simp, div_le_iff₀ hδ0]
    nlinarith
  -- the common modulus
  set L := ∏ q ∈ Finset.Icc 1 ⌊2 * Q⌋₊, q with hL
  have hL0 : L ≠ 0 := Finset.prod_ne_zero_iff.2 fun q hq => by
    have := (Finset.mem_Icc.1 hq).1; omega
  have : NeZero L := ⟨hL0⟩
  have hqL : ∀ R, R ≤ Q → ∀ q ∈ Qset R, q ∣ L := by
    intro R hR q hq
    apply Finset.dvd_prod_of_mem
    obtain ⟨hq1, -⟩ := Finset.mem_filter.1 hq
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hq1
    exact Finset.mem_Icc.2 ⟨h1, h2.trans (Nat.floor_le_floor (by linarith))⟩
  have hcop : ∀ n, a n ≠ 0 → Nat.Coprime n L := by
    intro n hn
    obtain ⟨hp, hnx⟩ := hsupp n hn
    refine Nat.Coprime.prod_right fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.1 hq
    refine (Nat.coprime_or_dvd_of_prime hp q).resolve_right fun hdvd => ?_
    have hle := Nat.le_of_dvd (by omega) hdvd
    have : (q : ℝ) ≤ 2 * Q := le_trans (by exact_mod_cast hq2) (Nat.floor_le (by positivity))
    have : (n : ℝ) ≤ q := by exact_mod_cast hle
    linarith
  -- `C ≥ 0`
  have hC0 : 0 ≤ C := by
    have h := hC 2 (by norm_num) even_two (by push_cast; linarith) 1 le_rfl (by
      rw [le_div_iff₀ (by norm_num)]; push_cast; linarith)
    have e1 : 2 * Q₀ / (1 * ((2 : ℕ) : ℝ)) = Q₀ := by push_cast; ring
    rw [e1] at h
    have hG1 := one_le_Gq_two hQ₀
    have hGQ := Gq_nonneg 2 (2 * Q / (1 * ((2 : ℕ) : ℝ)))
    by_contra hneg; push Not at hneg
    nlinarith
  -- the chain
  set g : ℝ → ℝ := fun α => ‖expTsum a α‖ ^ 2
  have hg : Continuous g := (TernaryGoldbach.continuous_expTsum hsum).norm.pow 2
  have hper : Function.Periodic g 1 := fun α => by simp only [g, expTsum_periodic a α]
  have hg0 : ∀ α, 0 ≤ g α := fun α => by positivity
  have hδQ₀ : δ₀ * Q₀ ≤ x := by nlinarith
  calc ∫ α in Ioc (0 : ℝ) 1 ∩ majorArcs δ₀ Q₀ x, ‖expTsum a α‖ ^ 2
      ≤ ∑ q ∈ Qset Q₀, ∑ b ∈ Bset q, ∫ y in arc δ₀ Q₀ x q b, g y :=
        integral_majorArcs_le hg hper hg0 hx0 (by positivity) hδQ₀
    _ = ∫ β, Farc a δ₀ Q₀ x β := sum_arcs_eq_integral_Farc hsum δ₀ Q₀ x
    _ ≤ ∫ β, C * Farc a δ₀ Q x β :=
        integral_mono (integrable_Farc hsum _ _ _) ((integrable_Farc hsum _ _ _).const_mul C)
          fun β => Farc_le hx0 hQ₀ hQ₀Q hC0 hC (hqL Q₀ hQ₀Q) (hqL Q le_rfl) hsum hcop
    _ = C * ∑ q ∈ Qset Q, ∑ b ∈ Bset q, ∫ y in arc δ₀ Q x q b, g y := by
        rw [integral_const_mul, sum_arcs_eq_integral_Farc hsum δ₀ Q x]
    _ ≤ C * ∫ α in Ioc (0 : ℝ) 1, g α :=
        mul_le_mul_of_nonneg_left (sum_arcs_le_integral hg hper hg0 hx0 hδ0 hQ0 hδQ2.le hδQ) hC0
    _ = C * ∑' n, ‖a n‖ ^ 2 := by rw [TernaryGoldbach.setIntegral_norm_sq_expTsum hsum]

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **[H, Cor. 12.2.5, (12.42)]** (with `δ₀ ≥ 2`).  Let `Q₀ ≥ 10⁵`, `δ₀ ≥ 2`,
`(20000 Q₀)² ≤ x/2δ₀`, `Q = √(x/2δ₀)`, `2Q₀ ≤ (2Q)^{0.6}`.  Then
`∫_{𝔐_{δ₀,Q₀}} |S|² ≤ (log 2Q₀ + 2)/(log 2Q + c_E) Σ|aₙ|²`. -/
theorem cor_12_2_5 {x δ₀ Q₀ : ℝ} {a : ℕ → ℂ} (ha : PrimeSupported x a)
    (hQ₀ : 1e5 ≤ Q₀) (hδ₀ : 2 ≤ δ₀) (hx : (20000 * Q₀) ^ 2 ≤ x / (2 * δ₀))
    (hρ : 2 * Q₀ ≤ (2 * √(x / (2 * δ₀))) ^ (0.6 : ℝ)) :
    ∫ α in Ioc (0 : ℝ) 1 ∩ majorArcs δ₀ Q₀ x, ‖expTsum a α‖ ^ 2 ≤
      (Real.log (2 * Q₀) + 2) / (Real.log (2 * √(x / (2 * δ₀))) + cE) * ∑' n, ‖a n‖ ^ 2 := by
  set Q := √(x / (2 * δ₀)) with hQdef
  have hQ0 : 0 ≤ x / (2 * δ₀) := le_trans (by positivity) hx
  have hQ : 20000 * Q₀ ≤ Q := by
    rw [hQdef]; exact Real.le_sqrt_of_sq_le hx
  refine prop_12_1_2 ha hδ₀ (by linarith) ?_ fun q hq _ hq2 s hs hsq => ?_
  · have h1 : Q₀ ^ 2 ≤ x / (2 * δ₀) := le_trans (by nlinarith) hx
    have h2 : δ₀ * Q₀ ^ 2 ≤ δ₀ * (x / (2 * δ₀)) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : δ₀ * (x / (2 * δ₀)) = x / 2 := by field_simp
    linarith
  · have h2Q₀ : (0 : ℝ) < 2 * Q₀ := by linarith
    have hlog : Real.log (2 * Q₀) ≤ 0.6 * Real.log (2 * Q) := by
      have := Real.log_le_log h2Q₀ hρ
      rwa [Real.log_rpow (by nlinarith)] at this
    exact prop_12_2_4 (by linarith) (by linarith) hlog hq hq2 hs hsq

end TernaryGoldbach.MinorArcs
