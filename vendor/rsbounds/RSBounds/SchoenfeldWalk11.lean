import RSBounds.SchoenfeldPrimeWalk
import RSBounds.Schoenfeld1976Targets

/-!
# The walk below 1500, for Theorem 11

Schoenfeld's Theorem 11 asks for `|ψ(x) − x| < x ε₀(x)` from `x = 17`, `|θ(x) − x| < x ε₀(x)`
from `x = 101`, and `ψ(x) − x < x ε₀(x)` from `x = 1`. Below 1500 this is checked with the walk of
`SchoenfeldPrimeWalk`, cut into blocks `[a, b)` on which `ε₀ ≥ E` for an explicit rational `E`
and the walk's thresholds are at most `a E`.

The lower bound for `ε₀` needs no exponential bounds: with `X = √(log x / K)`, `K = 9.645908801`,
`ε₀(x) = √(8/(17π)) √X e^{−X} ≥ 0.387 · s · w` on `[a, b]` once `K s⁴ ≤ log a`,
`log b ≤ K u²` and `u ≤ log(1/w)`, and these follow from the integer logarithm enclosures
`logLo`, `logHi` (`epsOk`, checked by the kernel).
-/

open Real

namespace TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk

local notation "ε₀" => Goals.Schoenfeld1976.epsilon0

/-- A stretch of the walk with fixed thresholds. -/
def SegH (A B : ℕ) (r : Req) (sA sB : WS) : Prop :=
  Inv A sA → Inv B sB ∧ ∀ n, A ≤ n → n < B → Holds n r

theorem segH_of {A L : ℕ} (r : Req) {sA sB : WS} (hA : 1 ≤ A) (hB : A + L < 1163 * 1163)
    (h : walk A L r sA = some sB) : SegH A (A + L) r sA sB := fun hinv =>
  walk_spec L A r sA sB hA hB hinv h

/-- `√(8/(17π)) ≥ 0.387`. -/
theorem coeff_ge : (0.387 : ℝ) ≤ Real.sqrt (8 / (17 * Real.pi)) := by
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d4]

theorem eps_ge {a b x s u w : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) (hw : 0 ≤ w) (ha : 0 < a)
    (hxa : a ≤ x) (hxb : x ≤ b)
    (h1 : 9.645908801 * s ^ 4 ≤ Real.log a) (h2 : Real.log b ≤ 9.645908801 * u ^ 2)
    (h3 : w ≤ Real.exp (-u)) : 0.387 * s * w ≤ ε₀ x := by
  unfold Goals.Schoenfeld1976.epsilon0 Goals.Schoenfeld1976.X
  have hx0 : 0 < x := lt_of_lt_of_le ha hxa
  have hK : (0 : ℝ) < 9.645908801 := by norm_num
  have hlx : Real.log a ≤ Real.log x := Real.log_le_log ha hxa
  have hlb : Real.log x ≤ Real.log b := Real.log_le_log hx0 hxb
  set X := Real.sqrt (Real.log x / 9.645908801) with hX
  have hs2 : s ^ 2 ≤ X := by
    rw [hX]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hK]
    nlinarith
  have hsX : s ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hs2
  have hXu : X ≤ u := by
    calc X ≤ Real.sqrt (u ^ 2) := Real.sqrt_le_sqrt (by rw [div_le_iff₀ hK]; nlinarith)
      _ = u := Real.sqrt_sq hu
  have he : w ≤ Real.exp (-X) := h3.trans (Real.exp_le_exp.mpr (by linarith))
  have h4 := mul_le_mul coeff_ge hsX hs (Real.sqrt_nonneg _)
  exact mul_le_mul h4 he hw (by positivity)

/-- `ε₀ ≥ 0.387 · (sn/sd) · (wn/wd)` on `[an/ad, bn/bd]`, via `logLo`, `logHi`. -/
def epsOk (an ad bn bd sn sd un ud wn wd : ℕ) : Bool :=
  decide (2 ≤ an) && decide (an < 1163 * 1163) && decide (2 ≤ ad) && decide (ad < 1163 * 1163) &&
  decide (2 ≤ bn) && decide (bn < 1163 * 1163) && decide (2 ≤ bd) && decide (bd < 1163 * 1163) &&
  decide (2 ≤ wn) && decide (wn < 1163 * 1163) && decide (2 ≤ wd) && decide (wd < 1163 * 1163) &&
  decide (0 < sd) && decide (0 < ud) && decide (ad < an) &&
  decide (9645908801 * sn ^ 4 * D + 1000000000 * sd ^ 4 * logHi ad ≤
    1000000000 * sd ^ 4 * logLo an) &&
  decide (1000000000 * ud ^ 2 * logHi bn ≤ 9645908801 * un ^ 2 * D + 1000000000 * ud ^ 2 * logLo bd) &&
  decide (ud * logHi wn + un * D ≤ ud * logLo wd)

theorem log_bounds' {m : ℕ} (h2 : 2 ≤ m) (h : m < 1163 * 1163) :
    (logLo m : ℝ) ≤ (D : ℝ) * Real.log m ∧ (D : ℝ) * Real.log m ≤ (logHi m : ℝ) :=
  log_bounds h2 (by norm_num at h ⊢; omega)

theorem epsOk_spec {an ad bn bd sn sd un ud wn wd : ℕ}
    (h : epsOk an ad bn bd sn sd un ud wn wd = true) {x : ℝ}
    (hxa : (an : ℝ) / ad ≤ x) (hxb : x ≤ (bn : ℝ) / bd) :
    0.387 * ((sn : ℝ) / sd) * ((wn : ℝ) / wd) ≤ ε₀ x := by
  simp only [epsOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨ha2, ha, had2, had, hb2, hb, hbd2, hbd, hwn2, hwn, hwd2, hwd, hsd, hud, -, c1, c2, c3⟩ :=
    h
  have hD : (0 : ℝ) < D := by norm_num [D]
  obtain ⟨la1, la2⟩ := log_bounds' ha2 ha
  obtain ⟨lad1, lad2⟩ := log_bounds' had2 had
  obtain ⟨lb1, lb2⟩ := log_bounds' hb2 hb
  obtain ⟨lbd1, lbd2⟩ := log_bounds' hbd2 hbd
  obtain ⟨lw1, lw2⟩ := log_bounds' hwn2 hwn
  obtain ⟨lwd1, lwd2⟩ := log_bounds' hwd2 hwd
  have hadR : (0 : ℝ) < ad := by exact_mod_cast (by omega : 0 < ad)
  have hanR : (0 : ℝ) < an := by exact_mod_cast (by omega : 0 < an)
  have hbdR : (0 : ℝ) < bd := by exact_mod_cast (by omega : 0 < bd)
  have hbnR : (0 : ℝ) < bn := by exact_mod_cast (by omega : 0 < bn)
  have hwnR : (0 : ℝ) < wn := by exact_mod_cast (by omega : 0 < wn)
  have hwdR : (0 : ℝ) < wd := by exact_mod_cast (by omega : 0 < wd)
  have hsdR : (0 : ℝ) < sd := by exact_mod_cast hsd
  have hudR : (0 : ℝ) < ud := by exact_mod_cast hud
  have c1' : (9645908801 : ℝ) * sn ^ 4 * D + 1000000000 * sd ^ 4 * logHi ad ≤
      1000000000 * sd ^ 4 * logLo an := by exact_mod_cast c1
  have c2' : (1000000000 : ℝ) * ud ^ 2 * logHi bn ≤
      9645908801 * un ^ 2 * D + 1000000000 * ud ^ 2 * logLo bd := by exact_mod_cast c2
  have c3' : (ud : ℝ) * logHi wn + un * D ≤ ud * logLo wd := by exact_mod_cast c3
  have hla : Real.log ((an : ℝ) / ad) = Real.log an - Real.log ad :=
    Real.log_div hanR.ne' hadR.ne'
  have hlb : Real.log ((bn : ℝ) / bd) = Real.log bn - Real.log bd :=
    Real.log_div hbnR.ne' hbdR.ne'
  have hsd4 : (0 : ℝ) < sd ^ 4 := by positivity
  have hud2 : (0 : ℝ) < ud ^ 2 := by positivity
  apply eps_ge (a := (an : ℝ) / ad) (b := (bn : ℝ) / bd) (u := (un : ℝ) / ud) (by positivity)
    (by positivity) (by positivity) (by positivity) hxa hxb
  · rw [hla]
    have e1 := mul_le_mul_of_nonneg_left la1 (by positivity : (0 : ℝ) ≤ 1000000000 * sd ^ 4)
    have e2 := mul_le_mul_of_nonneg_left lad2 (by positivity : (0 : ℝ) ≤ 1000000000 * sd ^ 4)
    have h5 : D * ((9645908801 : ℝ) * sn ^ 4) ≤
        D * (1000000000 * sd ^ 4 * (Real.log an - Real.log ad)) := by linarith
    have h6 := le_of_mul_le_mul_left h5 hD
    have hq : ((sn : ℝ) / sd) ^ 4 * sd ^ 4 = sn ^ 4 := by field_simp
    have h7 : (9.645908801 * ((sn : ℝ) / sd) ^ 4) * sd ^ 4 ≤
        (Real.log an - Real.log ad) * sd ^ 4 := by
      rw [mul_assoc, hq]; linarith
    exact le_of_mul_le_mul_right h7 hsd4
  · rw [hlb]
    have e1 := mul_le_mul_of_nonneg_left lb2 (by positivity : (0 : ℝ) ≤ 1000000000 * ud ^ 2)
    have e2 := mul_le_mul_of_nonneg_left lbd1 (by positivity : (0 : ℝ) ≤ 1000000000 * ud ^ 2)
    have h5 : D * ((1000000000 : ℝ) * ud ^ 2 * (Real.log bn - Real.log bd)) ≤
        D * (9645908801 * un ^ 2) := by linarith
    have h6 := le_of_mul_le_mul_left h5 hD
    have hq : ((un : ℝ) / ud) ^ 2 * ud ^ 2 = un ^ 2 := by field_simp
    have h7 : (Real.log bn - Real.log bd) * ud ^ 2 ≤
        (9.645908801 * ((un : ℝ) / ud) ^ 2) * ud ^ 2 := by
      rw [mul_assoc, hq]; linarith
    exact le_of_mul_le_mul_right h7 hud2
  · have hu : (un : ℝ) / ud ≤ Real.log wd - Real.log wn := by
      rw [div_le_iff₀ hudR]
      have e1 := mul_le_mul_of_nonneg_left lw2 (by positivity : (0 : ℝ) ≤ ud)
      have e2 := mul_le_mul_of_nonneg_left lwd1 (by positivity : (0 : ℝ) ≤ ud)
      have h5 : D * (un : ℝ) ≤ D * ((Real.log wd - Real.log wn) * ud) := by linarith
      exact le_of_mul_le_mul_left h5 hD
    calc (wn : ℝ) / wd = Real.exp (-(Real.log wd - Real.log wn)) := by
          rw [neg_sub, Real.exp_sub, Real.exp_log hwnR, Real.exp_log hwdR]
      _ ≤ Real.exp (-((un : ℝ) / ud)) := Real.exp_le_exp.mpr (by linarith)

theorem epsOk_pos {an ad bn bd sn sd un ud wn wd : ℕ}
    (h : epsOk an ad bn bd sn sd un ud wn wd = true) : 0 < ad ∧ 0 < bd ∧ 0 < sd ∧ 0 < wd := by
  simp only [epsOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, had2, -, -, -, hbd2, -, -, -, hwd2, -, hsd, -⟩ := h
  exact ⟨by omega, by omega, hsd, by omega⟩

/-- The threshold `t / D` is at most `(an/ad) · 0.387 · (sn/sd) · (wn/wd)`. -/
def thrOk (an ad t sn sd wn wd : ℕ) : Bool :=
  decide (t * (1000 * sd * wd) * ad ≤ D * an * (387 * sn * wn))

theorem thrOk_spec {an ad t sn sd wn wd : ℕ} (h : thrOk an ad t sn sd wn wd = true)
    (had : 0 < ad) (hsd : 0 < sd) (hwd : 0 < wd) :
    (t : ℝ) / D ≤ (an : ℝ) / ad * (0.387 * ((sn : ℝ) / sd) * ((wn : ℝ) / wd)) := by
  simp only [thrOk, decide_eq_true_eq] at h
  have h' : (t : ℝ) * (1000 * sd * wd) * ad ≤ D * an * (387 * sn * wn) := by exact_mod_cast h
  have hD : (0 : ℝ) < D := by norm_num [D]
  have hadR : (0 : ℝ) < ad := by exact_mod_cast had
  have hsdR : (0 : ℝ) < sd := by exact_mod_cast hsd
  have hwdR : (0 : ℝ) < wd := by exact_mod_cast hwd
  rw [div_le_iff₀ hD]
  rw [show (an : ℝ) / ad * (0.387 * ((sn : ℝ) / sd) * ((wn : ℝ) / wd)) * D =
    D * an * (387 * sn * wn) / (1000 * sd * wd * ad) by field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- A block `[A, B)` of integers: `ψ`, from the walk's thresholds. -/
theorem block_psi {A B : ℕ} {r : Req} (hseg : ∀ n, A ≤ n → n < B → Holds n r)
    {sn sd un ud wn wd : ℕ} (he : epsOk (2 * A) 2 (2 * B) 2 sn sd un ud wn wd = true)
    (hu : thrOk (2 * A) 2 r.psUp sn sd wn wd = true)
    (hl : thrOk (2 * A) 2 r.psLo sn sd wn wd = true) :
    ∀ x : ℝ, (A : ℝ) ≤ x → x < B → |Chebyshev.psi x - x| < x * ε₀ x := by
  intro x hxa hxb
  obtain ⟨-, -, hsd, hwd⟩ := epsOk_pos he
  have h2 (k : ℕ) : ((2 * k : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = k := by push_cast; ring
  have hE := epsOk_spec he (x := x) (by rw [h2]; exact hxa) (by rw [h2]; exact hxb.le)
  have tu := thrOk_spec hu (by norm_num) hsd hwd
  have tl := thrOk_spec hl (by norm_num) hsd hwd
  rw [h2] at tu tl
  set E := 0.387 * ((sn : ℝ) / sd) * ((wn : ℝ) / wd)
  have hE0 : 0 ≤ E := by positivity
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg A) hxa
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hAn : A ≤ ⌊x⌋₊ := Nat.le_floor hxa
  have hnB : ⌊x⌋₊ < B := (Nat.floor_lt hx0).mpr hxb
  obtain ⟨-, -, p1, p2⟩ := hseg _ hAn hnB x hnx (Nat.lt_floor_add_one x)
  have hAE : (A : ℝ) * E ≤ x * ε₀ x :=
    (mul_le_mul_of_nonneg_right hxa hE0).trans (mul_le_mul_of_nonneg_left hE hx0)
  rw [abs_lt]
  constructor <;> linarith

/-- A block `[A, B)` of integers: `θ`, from the walk's thresholds. -/
theorem block_theta {A B : ℕ} {r : Req} (hseg : ∀ n, A ≤ n → n < B → Holds n r)
    {sn sd un ud wn wd : ℕ} (he : epsOk (2 * A) 2 (2 * B) 2 sn sd un ud wn wd = true)
    (hu : thrOk (2 * A) 2 r.thUp sn sd wn wd = true)
    (hl : thrOk (2 * A) 2 r.thLo sn sd wn wd = true) :
    ∀ x : ℝ, (A : ℝ) ≤ x → x < B → |Chebyshev.theta x - x| < x * ε₀ x := by
  intro x hxa hxb
  obtain ⟨-, -, hsd, hwd⟩ := epsOk_pos he
  have h2 (k : ℕ) : ((2 * k : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = k := by push_cast; ring
  have hE := epsOk_spec he (x := x) (by rw [h2]; exact hxa) (by rw [h2]; exact hxb.le)
  have tu := thrOk_spec hu (by norm_num) hsd hwd
  have tl := thrOk_spec hl (by norm_num) hsd hwd
  rw [h2] at tu tl
  set E := 0.387 * ((sn : ℝ) / sd) * ((wn : ℝ) / wd)
  have hE0 : 0 ≤ E := by positivity
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg A) hxa
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hAn : A ≤ ⌊x⌋₊ := Nat.le_floor hxa
  have hnB : ⌊x⌋₊ < B := (Nat.floor_lt hx0).mpr hxb
  obtain ⟨p1, p2, -, -⟩ := hseg _ hAn hnB x hnx (Nat.lt_floor_add_one x)
  have hAE : (A : ℝ) * E ≤ x * ε₀ x :=
    (mul_le_mul_of_nonneg_right hxa hE0).trans (mul_le_mul_of_nonneg_left hE hx0)
  rw [abs_lt]
  constructor <;> linarith

/-- A sub-block `[an/ad, bn/bd) ⊆ [n, n+1)`: `ψ`, from the enclosure of `ψ(n)`. -/
theorem sub_psi {n : ℕ} {s : WS} (hI : Inv n s) {an ad bn bd sn sd un ud wn wd : ℕ}
    (he : epsOk an ad bn bd sn sd un ud wn wd = true)
    (hn1 : n * ad ≤ an) (hn2 : bn ≤ (n + 1) * bd)
    (hu : s.Phi * ad * (1000 * sd * wd) < D * an * (1000 * sd * wd + 387 * sn * wn))
    (hl : bn * ad * (1000 * sd * wd) * D ≤
      bd * (s.Plo * ad * (1000 * sd * wd) + D * an * (387 * sn * wn))) :
    ∀ x : ℝ, (an : ℝ) / ad ≤ x → x < (bn : ℝ) / bd → |Chebyshev.psi x - x| < x * ε₀ x := by
  intro x hxa hxb
  obtain ⟨had, hbd, hsd, hwd⟩ := epsOk_pos he
  have hE := epsOk_spec he hxa hxb.le
  set E := 0.387 * ((sn : ℝ) / sd) * ((wn : ℝ) / wd) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hD : (0 : ℝ) < D := by norm_num [D]
  have hadR : (0 : ℝ) < ad := by exact_mod_cast had
  have hbdR : (0 : ℝ) < bd := by exact_mod_cast hbd
  have hsdR : (0 : ℝ) < sd := by exact_mod_cast hsd
  have hwdR : (0 : ℝ) < wd := by exact_mod_cast hwd
  have hn1' : (n : ℝ) ≤ x := by
    have : (n : ℝ) * ad ≤ an := by exact_mod_cast hn1
    exact le_trans (by rw [le_div_iff₀ hadR]; exact this) hxa
  have hn2' : x < n + 1 := by
    have : (bn : ℝ) ≤ (n + 1) * bd := by exact_mod_cast hn2
    exact lt_of_lt_of_le hxb (by rw [div_le_iff₀ hbdR]; exact this)
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg n) hn1'
  have hfl : ⌊x⌋₊ = n := (Nat.floor_eq_iff hx0).mpr ⟨hn1', hn2'⟩
  have hpsi : Chebyshev.psi x = Chebyshev.psi n := by
    rw [Chebyshev.psi_eq_psi_coe_floor, hfl]
  obtain ⟨-, -, q1, q2⟩ := hI
  have hu' : (s.Phi : ℝ) * ad * (1000 * sd * wd) < D * an * (1000 * sd * wd + 387 * sn * wn) := by
    exact_mod_cast hu
  have hl' : (bn : ℝ) * ad * (1000 * sd * wd) * D ≤
      bd * (s.Plo * ad * (1000 * sd * wd) + D * an * (387 * sn * wn)) := by exact_mod_cast hl
  -- with a = an/ad, b = bn/bd: D ψ(n) ≤ Phi < D a (1 + E) and D b ≤ Plo + D a E ≤ D ψ(n) + D a E
  have hEe : E * (1000 * sd * wd) = 387 * sn * wn := by
    rw [hEdef]; field_simp; ring
  have hup : Chebyshev.psi n < (an : ℝ) / ad * (1 + E) := by
    have h5 : (D : ℝ) * Chebyshev.psi n * ad * (1000 * sd * wd) <
        D * an * ((1 + E) * (1000 * sd * wd)) := by
      rw [add_mul, one_mul, hEe]
      have := mul_le_mul_of_nonneg_right q2 (by positivity : (0 : ℝ) ≤ ad * (1000 * sd * wd))
      linarith
    have h6 : Chebyshev.psi n * ad < an * (1 + E) := by
      have h7 : (D * (1000 * sd * wd)) * (Chebyshev.psi n * ad) <
          (D * (1000 * sd * wd)) * (an * (1 + E)) := by linarith
      exact lt_of_mul_lt_mul_left h7 (by positivity)
    rw [div_mul_eq_mul_div, lt_div_iff₀ hadR]
    linarith
  have hlo : (bn : ℝ) / bd ≤ Chebyshev.psi n + (an : ℝ) / ad * E := by
    have h5 : (D : ℝ) * (1000 * sd * wd) * (bn * ad) ≤
        (D * (1000 * sd * wd)) * (bd * (Chebyshev.psi n * ad + an * E)) := by
      have h8 : (s.Plo : ℝ) * ad * (1000 * sd * wd) ≤
          D * Chebyshev.psi n * ad * (1000 * sd * wd) := by
        have := mul_le_mul_of_nonneg_right q1 (by positivity : (0 : ℝ) ≤ ad * (1000 * sd * wd))
        linarith
      have h9 : (D : ℝ) * an * (387 * sn * wn) = D * an * E * (1000 * sd * wd) := by
        rw [mul_assoc (D * an : ℝ) E, hEe]
      nlinarith
    have h6 : (bn : ℝ) * ad ≤ bd * (Chebyshev.psi n * ad + an * E) :=
      le_of_mul_le_mul_left h5 (by positivity)
    rw [div_le_iff₀ hbdR]
    have : Chebyshev.psi n + (an : ℝ) / ad * E = (Chebyshev.psi n * ad + an * E) / ad := by
      field_simp
    rw [this, div_mul_eq_mul_div, le_div_iff₀ hadR]
    linarith
  have hxa' : (an : ℝ) / ad * E ≤ x * ε₀ x :=
    (mul_le_mul_of_nonneg_right hxa hE0).trans (mul_le_mul_of_nonneg_left hE hx0)
  rw [hpsi, abs_lt]
  constructor
  · linarith
  · nlinarith

end TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk
