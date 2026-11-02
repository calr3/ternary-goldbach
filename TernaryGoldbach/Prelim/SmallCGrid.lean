import TernaryGoldbach.Prelim.LogWalk

/-!
# `y ∑_{u ≤ 3000} |μ(u)|/u² β(y, u) ≤ 2.8` on `[2.8, 80)`, checked by the kernel

Ramaré's optimisation of `ρ(U, y)` for [H, (2.22)] (`LiouvilleBound.lean`). Since `β(·, u)` is
antitone, `y ∑ … ≤ b G(a)` for `a ≤ y ≤ b`. 17 intervals `[a, b]` (`a = A/1000`, `GT`) cover
`[2.8, 80)` (`C_cover`), and `b G(a) ≤ 2.8` on each (`grid_ok`).

A kernel walk over `u ≤ 3000` (`scripts/gen_c_grid.py`) keeps an upper bound for `10³⁰ log u`
(`LogWalk.incr_bounds`). For every grid point it accumulates upper bounds for
`10¹⁵ |μ(u)|/u² β(a, u)` (`tm_spec`), with squarefreeness by trial division (`sqf`).
-/

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- `β(a, u) = min(5/3, 0.99/(a − 2 log u))` if `2 log u < a`, else `5/3`. -/
noncomputable def betaf (a : ℝ) (u : ℕ) : ℝ :=
  if 2 * Real.log u < a then min (5 / 3) (0.99 / (a - 2 * Real.log u)) else 5 / 3

/-- The grid sum `G(a)`. -/
noncomputable def Gs (a : ℝ) : ℝ :=
  ∑ u ∈ Icc 1 3000, |(μ u : ℝ)| / (u * u : ℕ) * betaf a u + 5 / 3 / (3000 + 1 / 2)

namespace CGrid

open TernaryGoldbach.Prelim.LogWalk

theorem betaf_nonneg' (a : ℝ) (u : ℕ) : 0 ≤ betaf a u := by
  unfold betaf; split_ifs with h
  · exact le_min (by norm_num) (div_nonneg (by norm_num) (by linarith))
  · norm_num

/-- Trial division by the squares `d²`, `2 ≤ d ≤ 55`. -/
def sqf (v : ℕ) : Bool := (List.range' 2 54).all (fun d => v % (d * d) != 0)

theorem moebius_zero_of_sqf {v : ℕ} (h : sqf v = false) : μ v = 0 := by
  have hn : ¬ (∀ d ∈ List.range' 2 54, v % (d * d) ≠ 0) := by
    intro hall
    have : sqf v = true := by
      unfold sqf; rw [List.all_eq_true]; intro d hd; simpa using hall d hd
    rw [h] at this; exact Bool.false_ne_true this
  push_neg at hn
  obtain ⟨d, hd, hmod⟩ := hn
  rw [List.mem_range'_1] at hd
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  have := hsq d (Nat.dvd_of_mod_eq_zero hmod)
  rw [Nat.isUnit_iff] at this
  omega

/-- `⌈x/y⌉`. -/
def cdiv (x y : ℕ) : ℕ := (x + y - 1) / y

theorem cdiv_ge (x y : ℕ) (hy : 0 < y) : (x : ℝ) / y ≤ (cdiv x y : ℝ) := by
  unfold cdiv
  have h1 := Nat.div_add_mod (x + y - 1) y
  have h2 := Nat.mod_lt (x + y - 1) hy
  have h3 : x ≤ y * ((x + y - 1) / y) := by omega
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  rw [div_le_iff₀ hy']
  have : (x : ℝ) ≤ (y : ℝ) * (((x + y - 1) / y : ℕ) : ℝ) := by exact_mod_cast h3
  linarith

def c5 (v : ℕ) : ℕ := cdiv (5 * 10 ^ 15) (3 * v * v)

/-- An upper bound for `10¹⁵ β(A/1000, v)/v²`, given `10³⁰ log v ≤ Lh`. -/
def bup (A Lh v : ℕ) : ℕ :=
  if 2000 * Lh < A * 10 ^ 30 then
    min (c5 v) (cdiv (990 * 10 ^ 30 * 10 ^ 15) ((A * 10 ^ 30 - 2000 * Lh) * v * v))
  else c5 v

def tm (A Lh v : ℕ) : ℕ := if sqf v then bup A Lh v else 0

theorem bup_spec {A Lh v : ℕ} (hv : 1 ≤ v) (hL : 10 ^ 30 * Real.log v ≤ Lh) :
    10 ^ 15 * (betaf ((A : ℝ) / 1000) v / (v * v : ℕ)) ≤ bup A Lh v := by
  have hvv : (0 : ℝ) < ((v * v : ℕ) : ℝ) := by
    have : 0 < v * v := Nat.mul_pos hv hv
    exact_mod_cast this
  have hb0 := betaf_nonneg' ((A : ℝ) / 1000) v
  have h5 : 10 ^ 15 * (betaf ((A : ℝ) / 1000) v / (v * v : ℕ)) ≤ c5 v := by
    have hb5 : betaf ((A : ℝ) / 1000) v ≤ 5 / 3 := by
      unfold betaf; split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    have hc := cdiv_ge (5 * 10 ^ 15) (3 * v * v) (by positivity)
    have e : ((5 * 10 ^ 15 : ℕ) : ℝ) / ((3 * v * v : ℕ) : ℝ) =
        10 ^ 15 * (5 / 3 / ((v * v : ℕ) : ℝ)) := by
      push_cast; field_simp; ring
    rw [e] at hc
    unfold c5
    calc 10 ^ 15 * (betaf ((A : ℝ) / 1000) v / (v * v : ℕ))
        ≤ 10 ^ 15 * (5 / 3 / ((v * v : ℕ) : ℝ)) := by gcongr
      _ ≤ _ := hc
  unfold bup
  split_ifs with hc
  · rw [Nat.cast_min]
    refine le_min h5 ?_
    have hlog : 2 * Real.log v < (A : ℝ) / 1000 := by
      have : (2000 * Lh : ℝ) < A * 10 ^ 30 := by exact_mod_cast hc
      have hLh : (Lh : ℝ) ≥ 10 ^ 30 * Real.log v := hL
      rw [lt_div_iff₀ (by norm_num)]; nlinarith
    have hden : (0 : ℝ) < (A : ℝ) * 10 ^ 30 - 2000 * Lh := by
      have : (2000 * Lh : ℝ) < A * 10 ^ 30 := by exact_mod_cast hc
      linarith
    have hb : betaf ((A : ℝ) / 1000) v ≤ 990 * 10 ^ 30 / ((A : ℝ) * 10 ^ 30 - 2000 * Lh) := by
      unfold betaf
      rw [if_pos hlog]
      refine (min_le_right _ _).trans ?_
      rw [div_le_div_iff₀ (by linarith) hden]
      have hLh : (Lh : ℝ) ≥ 10 ^ 30 * Real.log v := hL
      nlinarith
    have hsub : ((A * 10 ^ 30 - 2000 * Lh : ℕ) : ℝ) = (A : ℝ) * 10 ^ 30 - 2000 * Lh := by
      rw [Nat.cast_sub hc.le]; push_cast; ring
    have hpos : 0 < (A * 10 ^ 30 - 2000 * Lh) * v * v := by
      have : 0 < A * 10 ^ 30 - 2000 * Lh := by omega
      positivity
    have hcd := cdiv_ge (990 * 10 ^ 30 * 10 ^ 15) ((A * 10 ^ 30 - 2000 * Lh) * v * v) hpos
    have e : ((990 * 10 ^ 30 * 10 ^ 15 : ℕ) : ℝ) / (((A * 10 ^ 30 - 2000 * Lh) * v * v : ℕ) : ℝ) =
        10 ^ 15 * (990 * 10 ^ 30 / ((A : ℝ) * 10 ^ 30 - 2000 * Lh) / ((v * v : ℕ) : ℝ)) := by
      have hd : (((A * 10 ^ 30 - 2000 * Lh) * v * v : ℕ) : ℝ) =
          ((A : ℝ) * 10 ^ 30 - 2000 * Lh) * ((v * v : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, hsub]; push_cast; ring
      rw [hd]
      push_cast
      field_simp
      norm_num
    rw [e] at hcd
    calc 10 ^ 15 * (betaf ((A : ℝ) / 1000) v / (v * v : ℕ))
        ≤ 10 ^ 15 * (990 * 10 ^ 30 / ((A : ℝ) * 10 ^ 30 - 2000 * Lh) / ((v * v : ℕ) : ℝ)) := by
          gcongr
      _ ≤ _ := hcd
  · exact h5

theorem tm_spec {A Lh v : ℕ} (hv : 1 ≤ v) (hL : 10 ^ 30 * Real.log v ≤ Lh) :
    10 ^ 15 * (|(μ v : ℝ)| / (v * v : ℕ) * betaf ((A : ℝ) / 1000) v) ≤ tm A Lh v := by
  unfold tm
  cases hs : sqf v
  · rw [moebius_zero_of_sqf hs]; simp
  · simp only [if_true]
    have hμ : |(μ v : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hb0 := betaf_nonneg' ((A : ℝ) / 1000) v
    have hvv : (0 : ℝ) ≤ ((v * v : ℕ) : ℝ) := Nat.cast_nonneg _
    have h := bup_spec (A := A) hv hL
    calc 10 ^ 15 * (|(μ v : ℝ)| / (v * v : ℕ) * betaf ((A : ℝ) / 1000) v)
        ≤ 10 ^ 15 * (1 / (v * v : ℕ) * betaf ((A : ℝ) / 1000) v) := by gcongr
      _ = 10 ^ 15 * (betaf ((A : ℝ) / 1000) v / (v * v : ℕ)) := by ring
      _ ≤ _ := h

/-! ### The walk -/

/-- The grid points `A` (`a = A/1000`). -/
def GA : List ℕ := [2800, 2868, 2973, 3124, 3320, 3546, 3780, 3999, 4290, 4691, 5328, 6252, 7824, 10766, 16787, 28807, 51009]

structure CS where
  Lh : ℕ
  acc : List ℕ
deriving DecidableEq

def cstep (u : ℕ) (s : CS) : CS :=
  let Lh := s.Lh + incrHi u
  { Lh := Lh, acc := List.zipWith (fun A x => x + tm A Lh (u + 1)) GA s.acc }

def walkC : ℕ → ℕ → CS → Option CS
  | _, 0, s => some s
  | u, len + 1, s =>
    if s.Lh + s.acc.sum < 10 ^ 200 then walkC (u + 1) len (cstep u s) else none

noncomputable def Gsum (a : ℝ) (u : ℕ) : ℝ := ∑ v ∈ Icc 1 u, |(μ v : ℝ)| / (v * v : ℕ) * betaf a v

def Inv (u : ℕ) (s : CS) : Prop :=
  10 ^ 30 * Real.log u ≤ s.Lh ∧
    List.Forall₂ (fun (A x : ℕ) => 10 ^ 15 * Gsum ((A : ℝ) / 1000) u ≤ (x : ℝ)) GA s.acc

theorem forall₂_zipWith {R R' : ℕ → ℕ → Prop} {f : ℕ → ℕ} (hf : ∀ a x, R a x → R' a (x + f a)) :
    ∀ {l1 l2 : List ℕ}, List.Forall₂ R l1 l2 →
      List.Forall₂ R' l1 (List.zipWith (fun a x => x + f a) l1 l2)
  | _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, List.Forall₂.cons h t => List.Forall₂.cons (hf _ _ h) (forall₂_zipWith hf t)

theorem Inv_step {u : ℕ} (hu : 1 ≤ u) {s : CS} (h : Inv u s) : Inv (u + 1) (cstep u s) := by
  obtain ⟨hL, hacc⟩ := h
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have i2 := (incr_bounds hu).2
  have hlog : Real.log ((u + 1 : ℕ) : ℝ) = Real.log u + Real.log (1 + (u : ℝ)⁻¹) := by
    rw [← Real.log_mul hu0.ne' (by positivity)]; congr 1; push_cast; field_simp
  have hL' : 10 ^ 30 * Real.log ((u + 1 : ℕ) : ℝ) ≤ ((s.Lh + incrHi u : ℕ) : ℝ) := by
    rw [hlog]; push_cast; linarith
  refine ⟨hL', forall₂_zipWith (fun A x hx => ?_) hacc⟩
  have hG : Gsum ((A : ℝ) / 1000) (u + 1) = Gsum ((A : ℝ) / 1000) u +
      |(μ (u + 1) : ℝ)| / ((u + 1) * (u + 1) : ℕ) * betaf ((A : ℝ) / 1000) (u + 1) := by
    rw [Gsum, Gsum, sum_Icc_succ_top (by omega)]
  have ht := tm_spec (A := A) (v := u + 1) (by omega) hL'
  rw [hG, mul_add, Nat.cast_add]
  linarith

theorem walkC_spec : ∀ (len u : ℕ) (s s' : CS), 1 ≤ u → u + len ≤ 3000 → Inv u s →
    walkC u len s = some s' → Inv (u + len) s' := by
  intro len
  induction len with
  | zero => intro u s s' _ _ h hw; simp only [walkC, Option.some.injEq] at hw; subst hw; simpa using h
  | succ len ih =>
    intro u s s' hu hl h hw
    rw [walkC] at hw
    split_ifs at hw
    rw [show u + (len + 1) = u + 1 + len by ring]
    exact ih (u + 1) _ _ (by omega) (by omega) (Inv_step hu h) hw

theorem forall₂_map_self {R : ℕ → ℕ → Prop} {f : ℕ → ℕ} (hf : ∀ a, R a (f a)) :
    ∀ l : List ℕ, List.Forall₂ R l (l.map f)
  | [] => List.Forall₂.nil
  | a :: l => List.Forall₂.cons (hf a) (forall₂_map_self hf l)

theorem Inv_one (l : List ℕ) (hl : GA.map (fun A => tm A 0 1) = l) : Inv 1 ⟨0, l⟩ := by
  subst hl
  refine ⟨by simp, ?_⟩
  show List.Forall₂ _ GA (GA.map (fun A => tm A 0 1))
  refine forall₂_map_self (fun A => ?_) GA
  have := tm_spec (A := A) (Lh := 0) (v := 1) le_rfl (by simp)
  simpa [Gsum] using this

theorem wk_1 : walkC 1 499 ⟨0, [353571428571429, 345188284518829, 332996972754794, 316901408450705, 298192771084338, 279187817258884, 261904761904762, 247561890472619, 230769230769231, 211042421658495, 185810810810811, 158349328214972, 126533742331289, 91956158276055, 58974206231013, 34366646995522, 19408339704758]⟩ = some ⟨6214608098422228116792615491426, [973622971677253, 938705367020778, 893264693702695, 840512245106538, 786647415914275, 737832772298544, 697289651212628, 649927197276612, 593990325585903, 522571483178692, 444886933101853, 354867167204647, 257116272781197, 163950898539572, 95853027995732, 54028200291055, 30020180664762]⟩ := by decide +kernel
theorem wk_2 : walkC 500 500 ⟨6214608098422228116792615491426, [973622971677253, 938705367020778, 893264693702695, 840512245106538, 786647415914275, 737832772298544, 697289651212628, 649927197276612, 593990325585903, 522571483178692, 444886933101853, 354867167204647, 257116272781197, 163950898539572, 95853027995732, 54028200291055, 30020180664762]⟩ = some ⟨6907755278982173426209847618105, [974628859967481, 939711255311006, 894270581992923, 841518133396766, 787653304204503, 738838660588772, 698295539502856, 650933085566840, 594996213876131, 523577371468920, 445892821392081, 355873055494875, 258122161071425, 164956786829800, 96014519953281, 54066129414733, 30035920510146]⟩ := by decide +kernel
theorem wk_3 : walkC 1000 500 ⟨6907755278982173426209847618105, [974628859967481, 939711255311006, 894270581992923, 841518133396766, 787653304204503, 738838660588772, 698295539502856, 650933085566840, 594996213876131, 523577371468920, 445892821392081, 355873055494875, 258122161071425, 164956786829800, 96014519953281, 54066129414733, 30035920510146]⟩ = some ⟨7313220387090337808187860739024, [974969487004004, 940051882347529, 894611209029446, 841858760433289, 787993931241026, 739179287625295, 698636166539379, 651273712603363, 595336840912654, 523917998505443, 446233448428604, 356213682531398, 258462788107948, 165297413866323, 96093232712739, 54079980155250, 30041416837750]⟩ := by decide +kernel
theorem wk_4 : walkC 1500 500 ⟨7313220387090337808187860739024, [974969487004004, 940051882347529, 894611209029446, 841858760433289, 787993931241026, 739179287625295, 698636166539379, 651273712603363, 595336840912654, 523917998505443, 446233448428604, 356213682531398, 258462788107948, 165297413866323, 96093232712739, 54079980155250, 30041416837750]⟩ = some ⟨7600902459542118735627079750529, [975136232720576, 940218628064101, 894777954746018, 842025506149861, 788160676957598, 739346033341867, 698802912255951, 651440458319935, 595503586629226, 524084744222015, 446400194145176, 356380428247970, 258629533824520, 165464159582895, 96146133399760, 54087103064813, 30044159863605]⟩ := by decide +kernel
theorem wk_5 : walkC 2000 500 ⟨7600902459542118735627079750529, [975136232720576, 940218628064101, 894777954746018, 842025506149861, 788160676957598, 739346033341867, 698802912255951, 651440458319935, 595503586629226, 524084744222015, 446400194145176, 356380428247970, 258629533824520, 165464159582895, 96146133399760, 54087103064813, 30044159863605]⟩ = some ⟨7824046010856328491393374846315, [975238743824682, 940321139168207, 894880465850124, 842128017253967, 788263188061704, 739448544445973, 698905423360057, 651542969424041, 595606097733332, 524187255326121, 446502705249282, 356482939352076, 258732044928626, 165566670687001, 96191021015240, 54091651410008, 30045870762462]⟩ := by decide +kernel
theorem wk_6 : walkC 2500 500 ⟨7824046010856328491393374846315, [975238743824682, 940321139168207, 894880465850124, 842128017253967, 788263188061704, 739448544445973, 698905423360057, 651542969424041, 595606097733332, 524187255326121, 446502705249282, 356482939352076, 258732044928626, 165566670687001, 96191021015240, 54091651410008, 30045870762462]⟩ = some ⟨8006367567650283117605092876962, [975305543789721, 940387939133246, 894947265815163, 842194817219006, 788329988026743, 739515344411012, 698972223325096, 651609769389080, 595672897698371, 524254055291160, 446569505214321, 356549739317115, 258798844893665, 165633470652040, 96232828213588, 54094708374189, 30046998573778]⟩ := by decide +kernel

theorem inv_1 : Inv 1 ⟨0, [353571428571429, 345188284518829, 332996972754794, 316901408450705, 298192771084338, 279187817258884, 261904761904762, 247561890472619, 230769230769231, 211042421658495, 185810810810811, 158349328214972, 126533742331289, 91956158276055, 58974206231013, 34366646995522, 19408339704758]⟩ := Inv_one _ (by decide +kernel)
theorem inv_500 : Inv 500 ⟨6214608098422228116792615491426, [973622971677253, 938705367020778, 893264693702695, 840512245106538, 786647415914275, 737832772298544, 697289651212628, 649927197276612, 593990325585903, 522571483178692, 444886933101853, 354867167204647, 257116272781197, 163950898539572, 95853027995732, 54028200291055, 30020180664762]⟩ := walkC_spec 499 1 _ _ (by norm_num) (by norm_num) inv_1 wk_1
theorem inv_1000 : Inv 1000 ⟨6907755278982173426209847618105, [974628859967481, 939711255311006, 894270581992923, 841518133396766, 787653304204503, 738838660588772, 698295539502856, 650933085566840, 594996213876131, 523577371468920, 445892821392081, 355873055494875, 258122161071425, 164956786829800, 96014519953281, 54066129414733, 30035920510146]⟩ := walkC_spec 500 500 _ _ (by norm_num) (by norm_num) inv_500 wk_2
theorem inv_1500 : Inv 1500 ⟨7313220387090337808187860739024, [974969487004004, 940051882347529, 894611209029446, 841858760433289, 787993931241026, 739179287625295, 698636166539379, 651273712603363, 595336840912654, 523917998505443, 446233448428604, 356213682531398, 258462788107948, 165297413866323, 96093232712739, 54079980155250, 30041416837750]⟩ := walkC_spec 500 1000 _ _ (by norm_num) (by norm_num) inv_1000 wk_3
theorem inv_2000 : Inv 2000 ⟨7600902459542118735627079750529, [975136232720576, 940218628064101, 894777954746018, 842025506149861, 788160676957598, 739346033341867, 698802912255951, 651440458319935, 595503586629226, 524084744222015, 446400194145176, 356380428247970, 258629533824520, 165464159582895, 96146133399760, 54087103064813, 30044159863605]⟩ := walkC_spec 500 1500 _ _ (by norm_num) (by norm_num) inv_1500 wk_4
theorem inv_2500 : Inv 2500 ⟨7824046010856328491393374846315, [975238743824682, 940321139168207, 894880465850124, 842128017253967, 788263188061704, 739448544445973, 698905423360057, 651542969424041, 595606097733332, 524187255326121, 446502705249282, 356482939352076, 258732044928626, 165566670687001, 96191021015240, 54091651410008, 30045870762462]⟩ := walkC_spec 500 2000 _ _ (by norm_num) (by norm_num) inv_2000 wk_5
theorem inv_3000 : Inv 3000 ⟨8006367567650283117605092876962, [975305543789721, 940387939133246, 894947265815163, 842194817219006, 788329988026743, 739515344411012, 698972223325096, 651609769389080, 595672897698371, 524254055291160, 446569505214321, 356549739317115, 258798844893665, 165633470652040, 96232828213588, 54094708374189, 30046998573778]⟩ := walkC_spec 500 2500 _ _ (by norm_num) (by norm_num) inv_2500 wk_6

/-! ### The grid -/

/-- `(A, B, acc)`: the interval `[A/1000, B/1000]` and the accumulated bound at `A`. -/
def GT : List (ℕ × ℕ × ℕ) := [(2800, 2868, 975305543789721), (2868, 2973, 940387939133246), (2973, 3124, 894947265815163), (3124, 3320, 842194817219006), (3320, 3546, 788329988026743), (3546, 3780, 739515344411012), (3780, 3999, 698972223325096), (3999, 4290, 651609769389080), (4290, 4691, 595672897698371), (4691, 5328, 524254055291160), (5328, 6252, 446569505214321), (6252, 7824, 356549739317115), (7824, 10766, 258798844893665), (10766, 16787, 165633470652040), (16787, 28807, 96232828213588), (28807, 51009, 54094708374189), (51009, 80000, 30046998573778)]

theorem GT_ok : GT.all (fun t => t.2.1 * (18003 * t.2.2 + 10 * 10 ^ 15) ≤ 2800 * 18003 * 10 ^ 15) =
    true := by decide +kernel

theorem forall₂_map_map {R : ℕ → ℕ → Prop} {f g : ℕ × ℕ × ℕ → ℕ} :
    ∀ {l : List (ℕ × ℕ × ℕ)}, List.Forall₂ R (l.map f) (l.map g) → ∀ t ∈ l, R (f t) (g t)
  | [], _, t, ht => by simp at ht
  | a :: l, h, t, ht => by
    simp only [List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.forall₂_cons.1 h
    rcases List.mem_cons.1 ht with rfl | ht'
    · exact h1
    · exact forall₂_map_map h2 t ht'

theorem acc_bound {t : ℕ × ℕ × ℕ} (ht : t ∈ GT) :
    10 ^ 15 * Gsum ((t.1 : ℝ) / 1000) 3000 ≤ (t.2.2 : ℝ) := by
  have h : List.Forall₂ (fun (A x : ℕ) => 10 ^ 15 * Gsum ((A : ℝ) / 1000) 3000 ≤ (x : ℝ)) GA
      [975305543789721, 940387939133246, 894947265815163, 842194817219006, 788329988026743, 739515344411012, 698972223325096, 651609769389080, 595672897698371, 524254055291160, 446569505214321, 356549739317115, 258798844893665, 165633470652040, 96232828213588, 54094708374189, 30046998573778] := inv_3000.2
  have e1 : GA = GT.map (fun t => t.1) := by decide +kernel
  have e2 : ([975305543789721, 940387939133246, 894947265815163, 842194817219006, 788329988026743, 739515344411012, 698972223325096, 651609769389080, 595672897698371, 524254055291160, 446569505214321, 356549739317115, 258798844893665, 165633470652040, 96232828213588, 54094708374189, 30046998573778] : List ℕ) = GT.map (fun t => t.2.2) := by decide +kernel
  rw [e1, e2] at h
  exact forall₂_map_map h t ht

/-- **`b G(a) ≤ 2.8`** on every grid interval. -/
theorem grid_ok {t : ℕ × ℕ × ℕ} (ht : t ∈ GT) :
    ((t.2.1 : ℝ) / 1000) * Gs ((t.1 : ℝ) / 1000) ≤ 2.8 := by
  have h1 := acc_bound ht
  have h2 : t.2.1 * (18003 * t.2.2 + 10 * 10 ^ 15) ≤ 2800 * 18003 * 10 ^ 15 := by
    have := List.all_eq_true.1 GT_ok t ht
    simpa using this
  have h2' : (t.2.1 : ℝ) * (18003 * t.2.2 + 10 * 10 ^ 15) ≤ 2800 * 18003 * 10 ^ 15 := by
    exact_mod_cast h2
  have hb : (0 : ℝ) ≤ t.2.1 := Nat.cast_nonneg _
  have hG : Gs ((t.1 : ℝ) / 1000) = Gsum ((t.1 : ℝ) / 1000) 3000 + 5 / 3 / (3000 + 1 / 2) := rfl
  rw [hG]
  have : Gsum ((t.1 : ℝ) / 1000) 3000 ≤ (t.2.2 : ℝ) / 10 ^ 15 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  calc (t.2.1 : ℝ) / 1000 * (Gsum ((t.1 : ℝ) / 1000) 3000 + 5 / 3 / (3000 + 1 / 2))
      ≤ (t.2.1 : ℝ) / 1000 * ((t.2.2 : ℝ) / 10 ^ 15 + 5 / 3 / (3000 + 1 / 2)) := by gcongr
    _ = (t.2.1 : ℝ) * (18003 * t.2.2 + 10 * 10 ^ 15) / (1000 * 18003 * 10 ^ 15) := by
        field_simp; ring
    _ ≤ 2800 * 18003 * 10 ^ 15 / (1000 * 18003 * 10 ^ 15) := by gcongr
    _ = 2.8 := by norm_num

/-- The grid intervals cover `[2.8, 80)`. -/
theorem C_cover {y : ℝ} (h1 : 2.8 ≤ y) (h2 : y < 80) :
    ∃ t ∈ GT, (t.1 : ℝ) / 1000 ≤ y ∧ y ≤ (t.2.1 : ℝ) / 1000 := by
  rcases lt_or_ge y (2868 / 1000) with h0 | h0
  · exact ⟨(2800, 2868, 975305543789721), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
  ·
    rcases lt_or_ge y (2973 / 1000) with h1 | h1
    · exact ⟨(2868, 2973, 940387939133246), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
    ·
      rcases lt_or_ge y (3124 / 1000) with h2 | h2
      · exact ⟨(2973, 3124, 894947265815163), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
      ·
        rcases lt_or_ge y (3320 / 1000) with h3 | h3
        · exact ⟨(3124, 3320, 842194817219006), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
        ·
          rcases lt_or_ge y (3546 / 1000) with h4 | h4
          · exact ⟨(3320, 3546, 788329988026743), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
          ·
            rcases lt_or_ge y (3780 / 1000) with h5 | h5
            · exact ⟨(3546, 3780, 739515344411012), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
            ·
              rcases lt_or_ge y (3999 / 1000) with h6 | h6
              · exact ⟨(3780, 3999, 698972223325096), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
              ·
                rcases lt_or_ge y (4290 / 1000) with h7 | h7
                · exact ⟨(3999, 4290, 651609769389080), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                ·
                  rcases lt_or_ge y (4691 / 1000) with h8 | h8
                  · exact ⟨(4290, 4691, 595672897698371), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                  ·
                    rcases lt_or_ge y (5328 / 1000) with h9 | h9
                    · exact ⟨(4691, 5328, 524254055291160), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                    ·
                      rcases lt_or_ge y (6252 / 1000) with h10 | h10
                      · exact ⟨(5328, 6252, 446569505214321), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                      ·
                        rcases lt_or_ge y (7824 / 1000) with h11 | h11
                        · exact ⟨(6252, 7824, 356549739317115), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                        ·
                          rcases lt_or_ge y (10766 / 1000) with h12 | h12
                          · exact ⟨(7824, 10766, 258798844893665), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                          ·
                            rcases lt_or_ge y (16787 / 1000) with h13 | h13
                            · exact ⟨(10766, 16787, 165633470652040), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                            ·
                              rcases lt_or_ge y (28807 / 1000) with h14 | h14
                              · exact ⟨(16787, 28807, 96232828213588), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                              ·
                                rcases lt_or_ge y (51009 / 1000) with h15 | h15
                                · exact ⟨(28807, 51009, 54094708374189), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩
                                ·
                                  exact ⟨(51009, 80000, 30046998573778), by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩

end CGrid

end TernaryGoldbach.Prelim
