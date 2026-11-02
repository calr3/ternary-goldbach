import Mathlib

/-!
# `∑_{q ≤ 150000, q odd} μ²(q)/φ(q) ∈ [6.798779, 6.79878]`, checked by the kernel

For odd `q`, trial division (`phiTD`, proved correct) decides whether `q` is squarefree and computes
`φ(q)`. The kernel walks `q = 1, …, 150000` accumulating `L(K) = ∑_{q ≤ K odd squarefree} ⌊10¹⁸/φ(q)⌋`,
with the state certified every 1000 steps; then `L ≤ 10¹⁸ S ≤ L + 150000`.
-/

open Finset

namespace TernaryGoldbach.Prelim.SmallMuPhi

/-- Trial division by odd `d`, for `m` without prime factors below `d`: `some none` if `m` is not
squarefree, `some (some φ(m))` if it is, `none` when out of fuel. -/
def phiTD : ℕ → ℕ → ℕ → Option (Option ℕ)
  | 0, _, _ => none
  | f + 1, m, d =>
    if m < 2 then some (some 1)
    else if m < d * d then some (some (m - 1))
    else if m % d = 0 then
      (if (m / d) % d = 0 then some none
        else (phiTD f (m / d) (d + 2)).map (Option.map (· * (d - 1))))
    else phiTD f m (d + 2)

theorem next_le {d p : ℕ} (h3 : 3 ≤ d) (hd : d % 2 = 1) (hp : p.Prime) (hdp : d ≤ p) (hne : p ≠ d) :
    d + 2 ≤ p := by
  by_contra hlt
  have hp1 : p = d + 1 := by omega
  have hev : 2 ∣ p := by omega
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hev
  omega

theorem phiTD_spec : ∀ (f m d : ℕ) (r : Option ℕ), 3 ≤ d → d % 2 = 1 → 1 ≤ m →
    (∀ p, p.Prime → p ∣ m → d ≤ p) → phiTD f m d = some r →
    (r = none → ¬ Squarefree m) ∧ (∀ t, r = some t → Squarefree m ∧ m.totient = t) := by
  intro f
  induction f with
  | zero => intro m d r _ _ _ _ h; simp [phiTD] at h
  | succ f ih =>
    intro m d r hd hodd hm1 hinv h
    rw [phiTD] at h
    split_ifs at h with h1 h2 h3 h4
    · cases h
      have : m = 1 := by omega
      subst this
      exact ⟨fun h => by simp at h, fun t ht => by
        simp only [Option.some.injEq] at ht; subst ht; exact ⟨squarefree_one, Nat.totient_one⟩⟩
    · cases h
      have hp : m.Prime := by
        by_contra hnp
        have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
        have hle := hinv _ hmf (Nat.minFac_dvd m)
        have hsq := Nat.minFac_sq_le_self (by omega) hnp
        have : d * d ≤ m.minFac ^ 2 := by rw [sq]; exact Nat.mul_le_mul hle hle
        omega
      exact ⟨fun h => by simp at h, fun t ht => by
        simp only [Option.some.injEq] at ht; subst ht; exact ⟨hp.squarefree, Nat.totient_prime hp⟩⟩
    · cases h
      refine ⟨fun _ hsq => ?_, fun t ht => by simp at ht⟩
      have hdm : d ∣ m := Nat.dvd_of_mod_eq_zero h3
      have hdd : d ∣ m / d := Nat.dvd_of_mod_eq_zero h4
      have : d * d ∣ m := by
        rw [← Nat.mul_div_cancel' hdm]; exact Nat.mul_dvd_mul_left d hdd
      have := Nat.isUnit_iff.1 (hsq d this)
      omega
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
      have hdm : d ∣ m := Nat.dvd_of_mod_eq_zero h3
      have hnd : ¬ d ∣ m / d := fun hc => h4 (Nat.mod_eq_zero_of_dvd hc)
      have hdp : d.Prime := by
        rw [Nat.prime_def_minFac]
        refine ⟨by omega, ?_⟩
        have hmf := Nat.minFac_prime (show d ≠ 1 by omega)
        have h1' := hinv _ hmf ((Nat.minFac_dvd d).trans hdm)
        have h2' := Nat.minFac_le (show 0 < d by omega)
        omega
      have hq : 1 ≤ m / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdm) (by omega)
      have hcop : Nat.Coprime d (m / d) := (Nat.Prime.coprime_iff_not_dvd hdp).2 hnd
      have ih' := ih (m / d) (d + 2) r' (by omega) (by omega) hq (fun p hp hpd => by
        have h1' := hinv p hp (hpd.trans (Nat.div_dvd_of_dvd hdm))
        have hne : p ≠ d := fun e => hnd (e ▸ hpd)
        exact next_le hd hodd hp h1' hne) hr'
      have hm : m = d * (m / d) := (Nat.mul_div_cancel' hdm).symm
      refine ⟨fun hr hsq => ?_, fun t ht => ?_⟩
      · cases r' with
        | none => exact ih'.1 rfl (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm))
        | some _ => simp at hr
      · cases r' with
        | none => simp at ht
        | some t' =>
          simp only [Option.map_some, Option.some.injEq] at ht
          obtain ⟨hs', ht'⟩ := ih'.2 t' rfl
          rw [hm, Nat.squarefree_mul hcop, Nat.totient_mul hcop, Nat.totient_prime hdp, ht', ← ht]
          exact ⟨⟨hdp.squarefree, hs'⟩, by ring⟩
    · refine ih m (d + 2) r (by omega) (by omega) hm1 (fun p hp hpm => ?_) h
      have h1' := hinv p hp hpm
      have hne : p ≠ d := fun e => h3 (Nat.mod_eq_zero_of_dvd (e ▸ hpm))
      exact next_le hd hodd hp h1' hne

/-- `L(K) = ∑_{q ≤ K, q odd squarefree} ⌊10¹⁸/φ(q)⌋`. -/
noncomputable def Lt (K : ℕ) : ℕ :=
  ∑ q ∈ Icc 1 K, if q % 2 = 1 ∧ Squarefree q then 1000000000000000000 / q.totient else 0

theorem Lt_succ (K : ℕ) : Lt (K + 1) = Lt K +
    if (K + 1) % 2 = 1 ∧ Squarefree (K + 1) then 1000000000000000000 / (K + 1).totient else 0 := by
  rw [Lt, Lt, sum_Icc_succ_top (by omega)]

/-- Processes `q + 1, …, q + len` from the state `L` at `q`. -/
def walkS : ℕ → ℕ → ℕ → Option ℕ
  | _, L, 0 => some L
  | q, L, len + 1 =>
    if L ≤ 10 ^ 20 then
      if (q + 1) % 2 = 0 then walkS (q + 1) L len
      else match phiTD (q + 3) (q + 1) 3 with
        | none => none
        | some none => walkS (q + 1) L len
        | some (some t) => walkS (q + 1) (L + 1000000000000000000 / t) len
    else none

theorem odd_factor {q p : ℕ} (hq : (q + 1) % 2 = 1) (hp : p.Prime) (hpq : p ∣ q + 1) : 3 ≤ p := by
  have h2 := hp.two_le
  by_contra hlt
  have : p = 2 := by omega
  subst this
  omega

theorem walkS_spec : ∀ (len q r : ℕ), walkS q (Lt q) len = some r → r = Lt (q + len) := by
  intro len
  induction len with
  | zero => intro q r h; simp only [walkS, Option.some.injEq] at h; exact h.symm
  | succ len ih =>
    intro q r h
    rw [walkS] at h
    split_ifs at h with hL hev
    · have e : Lt (q + 1) = Lt q := by rw [Lt_succ, if_neg (by omega), add_zero]
      rw [← e] at h
      rw [ih (q + 1) r h]; congr 1; omega
    · have hodd : (q + 1) % 2 = 1 := by omega
      rcases hpt : phiTD (q + 3) (q + 1) 3 with _ | _ | t
      · rw [hpt] at h; simp at h
      · rw [hpt] at h
        have hs := (phiTD_spec _ _ _ _ le_rfl rfl (by omega)
          (fun p hp hpq => odd_factor hodd hp hpq) hpt).1 rfl
        have e : Lt (q + 1) = Lt q := by
          rw [Lt_succ, if_neg (fun hc => hs hc.2), add_zero]
        simp only at h
        rw [← e] at h
        rw [ih (q + 1) r h]; congr 1; omega
      · rw [hpt] at h
        obtain ⟨hs, ht⟩ := (phiTD_spec _ _ _ _ le_rfl rfl (by omega)
          (fun p hp hpq => odd_factor hodd hp hpq) hpt).2 t rfl
        have e : Lt (q + 1) = Lt q + 1000000000000000000 / t := by
          rw [Lt_succ, if_pos ⟨hodd, hs⟩, ht]
        simp only at h
        rw [← e] at h
        rw [ih (q + 1) r h]; congr 1; omega

/-- `S(K) = ∑_{q ≤ K odd} μ²(q)/φ(q)`, with `μ²` as an indicator. -/
noncomputable def S (K : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 K).filter Odd, (if Squarefree q then (1 : ℝ) else 0) / q.totient

theorem S_approx (K : ℕ) : (Lt K : ℝ) ≤ 1000000000000000000 * S K ∧
    1000000000000000000 * S K ≤ Lt K + K := by
  induction K with
  | zero => simp [Lt, S]
  | succ K ih =>
    have hS : S (K + 1) = S K + if Odd (K + 1) then
        (if Squarefree (K + 1) then (1 : ℝ) else 0) / (K + 1).totient else 0 := by
      rw [S, S, sum_filter, sum_filter, sum_Icc_succ_top (by omega)]
    rw [hS, Lt_succ]
    by_cases ho : (K + 1) % 2 = 1
    · have hO : Odd (K + 1) := Nat.odd_iff.2 ho
      rw [if_pos hO]
      by_cases hsq : Squarefree (K + 1)
      · rw [if_pos hsq, if_pos ⟨ho, hsq⟩]
        have ht : 0 < (K + 1).totient := Nat.totient_pos.2 (by omega)
        have ht' : (0 : ℝ) < (K + 1).totient := by exact_mod_cast ht
        set t := (K + 1).totient
        have hf1 : (((1000000000000000000 / t : ℕ) : ℝ)) ≤ 1000000000000000000 / (t : ℝ) := by
          have := Nat.cast_div_le (α := ℝ) (m := 1000000000000000000) (n := t)
          push_cast at this; exact this
        have hf2 : 1000000000000000000 / (t : ℝ) < (((1000000000000000000 / t : ℕ) : ℝ)) + 1 := by
          rw [div_lt_iff₀ ht']
          have h2 := Nat.lt_mul_div_succ 1000000000000000000 ht
          have := (Nat.cast_lt (α := ℝ)).2 h2
          push_cast at this
          linarith
        have e : (1000000000000000000 : ℝ) * (S K + 1 / (t : ℝ)) =
            1000000000000000000 * S K + 1000000000000000000 / (t : ℝ) := by ring
        rw [e]; push_cast
        constructor <;> linarith [ih.1, ih.2]
      · rw [if_neg hsq, if_neg (fun hc => hsq hc.2), zero_div]
        push_cast
        constructor <;> linarith [ih.1, ih.2]
    · have hO : ¬ Odd (K + 1) := fun h => ho (Nat.odd_iff.1 h)
      rw [if_neg hO, if_neg (fun hc => ho hc.1)]
      push_cast
      constructor <;> linarith [ih.1, ih.2]

theorem w_0 : walkS 0 0 1000 = some 4290506541316088690 := by decide +kernel
theorem w_1 : walkS 1000 4290506541316088690 1000 = some 4639608775027046773 := by decide +kernel
theorem w_2 : walkS 2000 4639608775027046773 1000 = some 4841401367758095653 := by decide +kernel
theorem w_3 : walkS 3000 4841401367758095653 1000 = some 4987016589152311447 := by decide +kernel
theorem w_4 : walkS 4000 4987016589152311447 1000 = some 5098301051803967027 := by decide +kernel
theorem w_5 : walkS 5000 5098301051803967027 1000 = some 5189281828313639202 := by decide +kernel
theorem w_6 : walkS 6000 5189281828313639202 1000 = some 5265744141781868910 := by decide +kernel
theorem w_7 : walkS 7000 5265744141781868910 1000 = some 5333265472548250985 := by decide +kernel
theorem w_8 : walkS 8000 5333265472548250985 1000 = some 5392238033382364349 := by decide +kernel
theorem w_9 : walkS 9000 5392238033382364349 1000 = some 5445041050478589276 := by decide +kernel
theorem w_10 : walkS 10000 5445041050478589276 1000 = some 5492539020344018444 := by decide +kernel
theorem w_11 : walkS 11000 5492539020344018444 1000 = some 5535683387219304391 := by decide +kernel
theorem w_12 : walkS 12000 5535683387219304391 1000 = some 5575622090668539691 := by decide +kernel
theorem w_13 : walkS 13000 5575622090668539691 1000 = some 5612948604051624264 := by decide +kernel
theorem w_14 : walkS 14000 5612948604051624264 1000 = some 5647438175875884944 := by decide +kernel
theorem w_15 : walkS 15000 5647438175875884944 1000 = some 5679672119114485244 := by decide +kernel
theorem w_16 : walkS 16000 5679672119114485244 1000 = some 5710216096653661175 := by decide +kernel
theorem w_17 : walkS 17000 5710216096653661175 1000 = some 5738592982690245403 := by decide +kernel
theorem w_18 : walkS 18000 5738592982690245403 1000 = some 5765571756087070825 := by decide +kernel
theorem w_19 : walkS 19000 5765571756087070825 1000 = some 5791155102095729101 := by decide +kernel
theorem w_20 : walkS 20000 5791155102095729101 1000 = some 5815638732749345379 := by decide +kernel
theorem w_21 : walkS 21000 5815638732749345379 1000 = some 5839102124491832347 := by decide +kernel
theorem w_22 : walkS 22000 5839102124491832347 1000 = some 5861236985644610922 := by decide +kernel
theorem w_23 : walkS 23000 5861236985644610922 1000 = some 5882656775069292781 := by decide +kernel
theorem w_24 : walkS 24000 5882656775069292781 1000 = some 5903016526692635321 := by decide +kernel
theorem w_25 : walkS 25000 5903016526692635321 1000 = some 5922836062194439568 := by decide +kernel
theorem w_26 : walkS 26000 5922836062194439568 1000 = some 5941456254532505240 := by decide +kernel
theorem w_27 : walkS 27000 5941456254532505240 1000 = some 5959558567650452718 := by decide +kernel
theorem w_28 : walkS 28000 5959558567650452718 1000 = some 5977145970120794001 := by decide +kernel
theorem w_29 : walkS 29000 5977145970120794001 1000 = some 5994232938706865460 := by decide +kernel
theorem w_30 : walkS 30000 5994232938706865460 1000 = some 6010579634112590458 := by decide +kernel
theorem w_31 : walkS 31000 6010579634112590458 1000 = some 6026239888406583395 := by decide +kernel
theorem w_32 : walkS 32000 6026239888406583395 1000 = some 6041532789035198747 := by decide +kernel
theorem w_33 : walkS 33000 6041532789035198747 1000 = some 6056626555382961449 := by decide +kernel
theorem w_34 : walkS 34000 6056626555382961449 1000 = some 6071089891007726376 := by decide +kernel
theorem w_35 : walkS 35000 6071089891007726376 1000 = some 6085112080338549379 := by decide +kernel
theorem w_36 : walkS 36000 6085112080338549379 1000 = some 6098752067671157773 := by decide +kernel
theorem w_37 : walkS 37000 6098752067671157773 1000 = some 6112024217455047803 := by decide +kernel
theorem w_38 : walkS 38000 6112024217455047803 1000 = some 6125020528886857110 := by decide +kernel
theorem w_39 : walkS 39000 6125020528886857110 1000 = some 6137687800269161755 := by decide +kernel
theorem w_40 : walkS 40000 6137687800269161755 1000 = some 6150084269582216558 := by decide +kernel
theorem w_41 : walkS 41000 6150084269582216558 1000 = some 6162185786677230815 := by decide +kernel
theorem w_42 : walkS 42000 6162185786677230815 1000 = some 6174050768885621072 := by decide +kernel
theorem w_43 : walkS 43000 6174050768885621072 1000 = some 6185574718704977747 := by decide +kernel
theorem w_44 : walkS 44000 6185574718704977747 1000 = some 6196852969737838131 := by decide +kernel
theorem w_45 : walkS 45000 6196852969737838131 1000 = some 6207885150237268578 := by decide +kernel
theorem w_46 : walkS 46000 6207885150237268578 1000 = some 6218640094764858792 := by decide +kernel
theorem w_47 : walkS 47000 6218640094764858792 1000 = some 6229183066675562833 := by decide +kernel
theorem w_48 : walkS 48000 6229183066675562833 1000 = some 6239478978853675699 := by decide +kernel
theorem w_49 : walkS 49000 6239478978853675699 1000 = some 6249512832373330015 := by decide +kernel
theorem w_50 : walkS 50000 6249512832373330015 1000 = some 6259478677510107524 := by decide +kernel
theorem w_51 : walkS 51000 6259478677510107524 1000 = some 6269156441836850239 := by decide +kernel
theorem w_52 : walkS 52000 6269156441836850239 1000 = some 6278672018359388781 := by decide +kernel
theorem w_53 : walkS 53000 6278672018359388781 1000 = some 6288012920199803430 := by decide +kernel
theorem w_54 : walkS 54000 6288012920199803430 1000 = some 6297168401211892141 := by decide +kernel
theorem w_55 : walkS 55000 6297168401211892141 1000 = some 6306143018676849473 := by decide +kernel
theorem w_56 : walkS 56000 6306143018676849473 1000 = some 6314932087822780987 := by decide +kernel
theorem w_57 : walkS 57000 6314932087822780987 1000 = some 6323709056464560750 := by decide +kernel
theorem w_58 : walkS 58000 6323709056464560750 1000 = some 6332037750828486859 := by decide +kernel
theorem w_59 : walkS 59000 6332037750828486859 1000 = some 6340485974806064888 := by decide +kernel
theorem w_60 : walkS 60000 6340485974806064888 1000 = some 6348829067407334979 := by decide +kernel
theorem w_61 : walkS 61000 6348829067407334979 1000 = some 6357005936277029289 := by decide +kernel
theorem w_62 : walkS 62000 6357005936277029289 1000 = some 6365057853254757333 := by decide +kernel
theorem w_63 : walkS 63000 6365057853254757333 1000 = some 6372977338632451915 := by decide +kernel
theorem w_64 : walkS 64000 6372977338632451915 1000 = some 6380735462685738051 := by decide +kernel
theorem w_65 : walkS 65000 6380735462685738051 1000 = some 6388393663559164492 := by decide +kernel
theorem w_66 : walkS 66000 6388393663559164492 1000 = some 6395831780632133491 := by decide +kernel
theorem w_67 : walkS 67000 6395831780632133491 1000 = some 6403235545904530578 := by decide +kernel
theorem w_68 : walkS 68000 6403235545904530578 1000 = some 6410525838016258636 := by decide +kernel
theorem w_69 : walkS 69000 6410525838016258636 1000 = some 6417742063988916291 := by decide +kernel
theorem w_70 : walkS 70000 6417742063988916291 1000 = some 6424879186666546602 := by decide +kernel
theorem w_71 : walkS 71000 6424879186666546602 1000 = some 6431867814092512085 := by decide +kernel
theorem w_72 : walkS 72000 6431867814092512085 1000 = some 6438749327307107183 := by decide +kernel
theorem w_73 : walkS 73000 6438749327307107183 1000 = some 6445466504056148119 := by decide +kernel
theorem w_74 : walkS 74000 6445466504056148119 1000 = some 6452224576218461304 := by decide +kernel
theorem w_75 : walkS 75000 6452224576218461304 1000 = some 6458824552463683005 := by decide +kernel
theorem w_76 : walkS 76000 6458824552463683005 1000 = some 6465300609816709405 := by decide +kernel
theorem w_77 : walkS 77000 6465300609816709405 1000 = some 6471841139871762510 := by decide +kernel
theorem w_78 : walkS 78000 6471841139871762510 1000 = some 6478156356896934691 := by decide +kernel
theorem w_79 : walkS 79000 6478156356896934691 1000 = some 6484417592571512157 := by decide +kernel
theorem w_80 : walkS 80000 6484417592571512157 1000 = some 6490603861401649041 := by decide +kernel
theorem w_81 : walkS 81000 6490603861401649041 1000 = some 6496712110764215543 := by decide +kernel
theorem w_82 : walkS 82000 6496712110764215543 1000 = some 6502824663412353262 := by decide +kernel
theorem w_83 : walkS 83000 6502824663412353262 1000 = some 6508819310397126214 := by decide +kernel
theorem w_84 : walkS 84000 6508819310397126214 1000 = some 6514767353155126609 := by decide +kernel
theorem w_85 : walkS 85000 6514767353155126609 1000 = some 6520532005328876337 := by decide +kernel
theorem w_86 : walkS 86000 6520532005328876337 1000 = some 6526337122000886657 := by decide +kernel
theorem w_87 : walkS 87000 6526337122000886657 1000 = some 6532056021152032188 := by decide +kernel
theorem w_88 : walkS 88000 6532056021152032188 1000 = some 6537753991917232659 := by decide +kernel
theorem w_89 : walkS 89000 6537753991917232659 1000 = some 6543300288098367874 := by decide +kernel
theorem w_90 : walkS 90000 6543300288098367874 1000 = some 6548840125776438597 := by decide +kernel
theorem w_91 : walkS 91000 6548840125776438597 1000 = some 6554342880406220611 := by decide +kernel
theorem w_92 : walkS 92000 6554342880406220611 1000 = some 6559769985549341371 := by decide +kernel
theorem w_93 : walkS 93000 6559769985549341371 1000 = some 6565107079631088609 := by decide +kernel
theorem w_94 : walkS 94000 6565107079631088609 1000 = some 6570360604802795689 := by decide +kernel
theorem w_95 : walkS 95000 6570360604802795689 1000 = some 6575578320490708140 := by decide +kernel
theorem w_96 : walkS 96000 6575578320490708140 1000 = some 6580773909469147188 := by decide +kernel
theorem w_97 : walkS 97000 6580773909469147188 1000 = some 6585879451323040724 := by decide +kernel
theorem w_98 : walkS 98000 6585879451323040724 1000 = some 6590935110322018480 := by decide +kernel
theorem w_99 : walkS 99000 6590935110322018480 1000 = some 6596000883407292217 := by decide +kernel
theorem w_100 : walkS 100000 6596000883407292217 1000 = some 6600981890988093287 := by decide +kernel
theorem w_101 : walkS 101000 6600981890988093287 1000 = some 6605989527056240475 := by decide +kernel
theorem w_102 : walkS 102000 6605989527056240475 1000 = some 6610837732568966564 := by decide +kernel
theorem w_103 : walkS 103000 6610837732568966564 1000 = some 6615601895072018913 := by decide +kernel
theorem w_104 : walkS 104000 6615601895072018913 1000 = some 6620441721485812363 := by decide +kernel
theorem w_105 : walkS 105000 6620441721485812363 1000 = some 6625179854929626329 := by decide +kernel
theorem w_106 : walkS 106000 6625179854929626329 1000 = some 6629897803982890150 := by decide +kernel
theorem w_107 : walkS 107000 6629897803982890150 1000 = some 6634567152388323521 := by decide +kernel
theorem w_108 : walkS 108000 6634567152388323521 1000 = some 6639192575806384998 := by decide +kernel
theorem w_109 : walkS 109000 6639192575806384998 1000 = some 6643745631151585649 := by decide +kernel
theorem w_110 : walkS 110000 6643745631151585649 1000 = some 6648232954118903762 := by decide +kernel
theorem w_111 : walkS 111000 6648232954118903762 1000 = some 6652738693332884054 := by decide +kernel
theorem w_112 : walkS 112000 6652738693332884054 1000 = some 6657145696182332173 := by decide +kernel
theorem w_113 : walkS 113000 6657145696182332173 1000 = some 6661586584718710094 := by decide +kernel
theorem w_114 : walkS 114000 6661586584718710094 1000 = some 6665970046730170624 := by decide +kernel
theorem w_115 : walkS 115000 6665970046730170624 1000 = some 6670248047441342741 := by decide +kernel
theorem w_116 : walkS 116000 6670248047441342741 1000 = some 6674541235583940925 := by decide +kernel
theorem w_117 : walkS 117000 6674541235583940925 1000 = some 6678820064222002188 := by decide +kernel
theorem w_118 : walkS 118000 6678820064222002188 1000 = some 6683018893906618267 := by decide +kernel
theorem w_119 : walkS 119000 6683018893906618267 1000 = some 6687206554484702760 := by decide +kernel
theorem w_120 : walkS 120000 6687206554484702760 1000 = some 6691341463704370266 := by decide +kernel
theorem w_121 : walkS 121000 6691341463704370266 1000 = some 6695414452891015997 := by decide +kernel
theorem w_122 : walkS 122000 6695414452891015997 1000 = some 6699486504654875044 := by decide +kernel
theorem w_123 : walkS 123000 6699486504654875044 1000 = some 6703566135293605854 := by decide +kernel
theorem w_124 : walkS 124000 6703566135293605854 1000 = some 6707609846256649616 := by decide +kernel
theorem w_125 : walkS 125000 6707609846256649616 1000 = some 6711552151962069658 := by decide +kernel
theorem w_126 : walkS 126000 6711552151962069658 1000 = some 6715539164519801917 := by decide +kernel
theorem w_127 : walkS 127000 6715539164519801917 1000 = some 6719482415920170262 := by decide +kernel
theorem w_128 : walkS 128000 6719482415920170262 1000 = some 6723372341205862139 := by decide +kernel
theorem w_129 : walkS 129000 6723372341205862139 1000 = some 6727269073361332994 := by decide +kernel
theorem w_130 : walkS 130000 6727269073361332994 1000 = some 6731072587089282558 := by decide +kernel
theorem w_131 : walkS 131000 6731072587089282558 1000 = some 6734875660393277758 := by decide +kernel
theorem w_132 : walkS 132000 6734875660393277758 1000 = some 6738638775247437262 := by decide +kernel
theorem w_133 : walkS 133000 6738638775247437262 1000 = some 6742390657824783779 := by decide +kernel
theorem w_134 : walkS 134000 6742390657824783779 1000 = some 6746060703792373515 := by decide +kernel
theorem w_135 : walkS 135000 6746060703792373515 1000 = some 6749757422632792613 := by decide +kernel
theorem w_136 : walkS 136000 6749757422632792613 1000 = some 6753453381091269697 := by decide +kernel
theorem w_137 : walkS 137000 6753453381091269697 1000 = some 6757093904261128892 := by decide +kernel
theorem w_138 : walkS 138000 6757093904261128892 1000 = some 6760747087559032429 := by decide +kernel
theorem w_139 : walkS 139000 6760747087559032429 1000 = some 6764289375758062501 := by decide +kernel
theorem w_140 : walkS 140000 6764289375758062501 1000 = some 6767876150983055743 := by decide +kernel
theorem w_141 : walkS 141000 6767876150983055743 1000 = some 6771405179907296656 := by decide +kernel
theorem w_142 : walkS 142000 6771405179907296656 1000 = some 6774933504372483218 := by decide +kernel
theorem w_143 : walkS 143000 6774933504372483218 1000 = some 6778382565504218659 := by decide +kernel
theorem w_144 : walkS 144000 6778382565504218659 1000 = some 6781827103346562807 := by decide +kernel
theorem w_145 : walkS 145000 6781827103346562807 1000 = some 6785282442498161141 := by decide +kernel
theorem w_146 : walkS 146000 6785282442498161141 1000 = some 6788694386611773813 := by decide +kernel
theorem w_147 : walkS 147000 6788694386611773813 1000 = some 6792127848307623369 := by decide +kernel
theorem w_148 : walkS 148000 6792127848307623369 1000 = some 6795472087827430446 := by decide +kernel
theorem w_149 : walkS 149000 6795472087827430446 1000 = some 6798779173123473292 := by decide +kernel

theorem c_0 : Lt 0 = 0 := by simp [Lt]

theorem c_1 : Lt 1000 = 4290506541316088690 := (walkS_spec 1000 0 4290506541316088690 (by rw [c_0]; exact w_0)).symm
theorem c_2 : Lt 2000 = 4639608775027046773 := (walkS_spec 1000 1000 4639608775027046773 (by rw [c_1]; exact w_1)).symm
theorem c_3 : Lt 3000 = 4841401367758095653 := (walkS_spec 1000 2000 4841401367758095653 (by rw [c_2]; exact w_2)).symm
theorem c_4 : Lt 4000 = 4987016589152311447 := (walkS_spec 1000 3000 4987016589152311447 (by rw [c_3]; exact w_3)).symm
theorem c_5 : Lt 5000 = 5098301051803967027 := (walkS_spec 1000 4000 5098301051803967027 (by rw [c_4]; exact w_4)).symm
theorem c_6 : Lt 6000 = 5189281828313639202 := (walkS_spec 1000 5000 5189281828313639202 (by rw [c_5]; exact w_5)).symm
theorem c_7 : Lt 7000 = 5265744141781868910 := (walkS_spec 1000 6000 5265744141781868910 (by rw [c_6]; exact w_6)).symm
theorem c_8 : Lt 8000 = 5333265472548250985 := (walkS_spec 1000 7000 5333265472548250985 (by rw [c_7]; exact w_7)).symm
theorem c_9 : Lt 9000 = 5392238033382364349 := (walkS_spec 1000 8000 5392238033382364349 (by rw [c_8]; exact w_8)).symm
theorem c_10 : Lt 10000 = 5445041050478589276 := (walkS_spec 1000 9000 5445041050478589276 (by rw [c_9]; exact w_9)).symm
theorem c_11 : Lt 11000 = 5492539020344018444 := (walkS_spec 1000 10000 5492539020344018444 (by rw [c_10]; exact w_10)).symm
theorem c_12 : Lt 12000 = 5535683387219304391 := (walkS_spec 1000 11000 5535683387219304391 (by rw [c_11]; exact w_11)).symm
theorem c_13 : Lt 13000 = 5575622090668539691 := (walkS_spec 1000 12000 5575622090668539691 (by rw [c_12]; exact w_12)).symm
theorem c_14 : Lt 14000 = 5612948604051624264 := (walkS_spec 1000 13000 5612948604051624264 (by rw [c_13]; exact w_13)).symm
theorem c_15 : Lt 15000 = 5647438175875884944 := (walkS_spec 1000 14000 5647438175875884944 (by rw [c_14]; exact w_14)).symm
theorem c_16 : Lt 16000 = 5679672119114485244 := (walkS_spec 1000 15000 5679672119114485244 (by rw [c_15]; exact w_15)).symm
theorem c_17 : Lt 17000 = 5710216096653661175 := (walkS_spec 1000 16000 5710216096653661175 (by rw [c_16]; exact w_16)).symm
theorem c_18 : Lt 18000 = 5738592982690245403 := (walkS_spec 1000 17000 5738592982690245403 (by rw [c_17]; exact w_17)).symm
theorem c_19 : Lt 19000 = 5765571756087070825 := (walkS_spec 1000 18000 5765571756087070825 (by rw [c_18]; exact w_18)).symm
theorem c_20 : Lt 20000 = 5791155102095729101 := (walkS_spec 1000 19000 5791155102095729101 (by rw [c_19]; exact w_19)).symm
theorem c_21 : Lt 21000 = 5815638732749345379 := (walkS_spec 1000 20000 5815638732749345379 (by rw [c_20]; exact w_20)).symm
theorem c_22 : Lt 22000 = 5839102124491832347 := (walkS_spec 1000 21000 5839102124491832347 (by rw [c_21]; exact w_21)).symm
theorem c_23 : Lt 23000 = 5861236985644610922 := (walkS_spec 1000 22000 5861236985644610922 (by rw [c_22]; exact w_22)).symm
theorem c_24 : Lt 24000 = 5882656775069292781 := (walkS_spec 1000 23000 5882656775069292781 (by rw [c_23]; exact w_23)).symm
theorem c_25 : Lt 25000 = 5903016526692635321 := (walkS_spec 1000 24000 5903016526692635321 (by rw [c_24]; exact w_24)).symm
theorem c_26 : Lt 26000 = 5922836062194439568 := (walkS_spec 1000 25000 5922836062194439568 (by rw [c_25]; exact w_25)).symm
theorem c_27 : Lt 27000 = 5941456254532505240 := (walkS_spec 1000 26000 5941456254532505240 (by rw [c_26]; exact w_26)).symm
theorem c_28 : Lt 28000 = 5959558567650452718 := (walkS_spec 1000 27000 5959558567650452718 (by rw [c_27]; exact w_27)).symm
theorem c_29 : Lt 29000 = 5977145970120794001 := (walkS_spec 1000 28000 5977145970120794001 (by rw [c_28]; exact w_28)).symm
theorem c_30 : Lt 30000 = 5994232938706865460 := (walkS_spec 1000 29000 5994232938706865460 (by rw [c_29]; exact w_29)).symm
theorem c_31 : Lt 31000 = 6010579634112590458 := (walkS_spec 1000 30000 6010579634112590458 (by rw [c_30]; exact w_30)).symm
theorem c_32 : Lt 32000 = 6026239888406583395 := (walkS_spec 1000 31000 6026239888406583395 (by rw [c_31]; exact w_31)).symm
theorem c_33 : Lt 33000 = 6041532789035198747 := (walkS_spec 1000 32000 6041532789035198747 (by rw [c_32]; exact w_32)).symm
theorem c_34 : Lt 34000 = 6056626555382961449 := (walkS_spec 1000 33000 6056626555382961449 (by rw [c_33]; exact w_33)).symm
theorem c_35 : Lt 35000 = 6071089891007726376 := (walkS_spec 1000 34000 6071089891007726376 (by rw [c_34]; exact w_34)).symm
theorem c_36 : Lt 36000 = 6085112080338549379 := (walkS_spec 1000 35000 6085112080338549379 (by rw [c_35]; exact w_35)).symm
theorem c_37 : Lt 37000 = 6098752067671157773 := (walkS_spec 1000 36000 6098752067671157773 (by rw [c_36]; exact w_36)).symm
theorem c_38 : Lt 38000 = 6112024217455047803 := (walkS_spec 1000 37000 6112024217455047803 (by rw [c_37]; exact w_37)).symm
theorem c_39 : Lt 39000 = 6125020528886857110 := (walkS_spec 1000 38000 6125020528886857110 (by rw [c_38]; exact w_38)).symm
theorem c_40 : Lt 40000 = 6137687800269161755 := (walkS_spec 1000 39000 6137687800269161755 (by rw [c_39]; exact w_39)).symm
theorem c_41 : Lt 41000 = 6150084269582216558 := (walkS_spec 1000 40000 6150084269582216558 (by rw [c_40]; exact w_40)).symm
theorem c_42 : Lt 42000 = 6162185786677230815 := (walkS_spec 1000 41000 6162185786677230815 (by rw [c_41]; exact w_41)).symm
theorem c_43 : Lt 43000 = 6174050768885621072 := (walkS_spec 1000 42000 6174050768885621072 (by rw [c_42]; exact w_42)).symm
theorem c_44 : Lt 44000 = 6185574718704977747 := (walkS_spec 1000 43000 6185574718704977747 (by rw [c_43]; exact w_43)).symm
theorem c_45 : Lt 45000 = 6196852969737838131 := (walkS_spec 1000 44000 6196852969737838131 (by rw [c_44]; exact w_44)).symm
theorem c_46 : Lt 46000 = 6207885150237268578 := (walkS_spec 1000 45000 6207885150237268578 (by rw [c_45]; exact w_45)).symm
theorem c_47 : Lt 47000 = 6218640094764858792 := (walkS_spec 1000 46000 6218640094764858792 (by rw [c_46]; exact w_46)).symm
theorem c_48 : Lt 48000 = 6229183066675562833 := (walkS_spec 1000 47000 6229183066675562833 (by rw [c_47]; exact w_47)).symm
theorem c_49 : Lt 49000 = 6239478978853675699 := (walkS_spec 1000 48000 6239478978853675699 (by rw [c_48]; exact w_48)).symm
theorem c_50 : Lt 50000 = 6249512832373330015 := (walkS_spec 1000 49000 6249512832373330015 (by rw [c_49]; exact w_49)).symm
theorem c_51 : Lt 51000 = 6259478677510107524 := (walkS_spec 1000 50000 6259478677510107524 (by rw [c_50]; exact w_50)).symm
theorem c_52 : Lt 52000 = 6269156441836850239 := (walkS_spec 1000 51000 6269156441836850239 (by rw [c_51]; exact w_51)).symm
theorem c_53 : Lt 53000 = 6278672018359388781 := (walkS_spec 1000 52000 6278672018359388781 (by rw [c_52]; exact w_52)).symm
theorem c_54 : Lt 54000 = 6288012920199803430 := (walkS_spec 1000 53000 6288012920199803430 (by rw [c_53]; exact w_53)).symm
theorem c_55 : Lt 55000 = 6297168401211892141 := (walkS_spec 1000 54000 6297168401211892141 (by rw [c_54]; exact w_54)).symm
theorem c_56 : Lt 56000 = 6306143018676849473 := (walkS_spec 1000 55000 6306143018676849473 (by rw [c_55]; exact w_55)).symm
theorem c_57 : Lt 57000 = 6314932087822780987 := (walkS_spec 1000 56000 6314932087822780987 (by rw [c_56]; exact w_56)).symm
theorem c_58 : Lt 58000 = 6323709056464560750 := (walkS_spec 1000 57000 6323709056464560750 (by rw [c_57]; exact w_57)).symm
theorem c_59 : Lt 59000 = 6332037750828486859 := (walkS_spec 1000 58000 6332037750828486859 (by rw [c_58]; exact w_58)).symm
theorem c_60 : Lt 60000 = 6340485974806064888 := (walkS_spec 1000 59000 6340485974806064888 (by rw [c_59]; exact w_59)).symm
theorem c_61 : Lt 61000 = 6348829067407334979 := (walkS_spec 1000 60000 6348829067407334979 (by rw [c_60]; exact w_60)).symm
theorem c_62 : Lt 62000 = 6357005936277029289 := (walkS_spec 1000 61000 6357005936277029289 (by rw [c_61]; exact w_61)).symm
theorem c_63 : Lt 63000 = 6365057853254757333 := (walkS_spec 1000 62000 6365057853254757333 (by rw [c_62]; exact w_62)).symm
theorem c_64 : Lt 64000 = 6372977338632451915 := (walkS_spec 1000 63000 6372977338632451915 (by rw [c_63]; exact w_63)).symm
theorem c_65 : Lt 65000 = 6380735462685738051 := (walkS_spec 1000 64000 6380735462685738051 (by rw [c_64]; exact w_64)).symm
theorem c_66 : Lt 66000 = 6388393663559164492 := (walkS_spec 1000 65000 6388393663559164492 (by rw [c_65]; exact w_65)).symm
theorem c_67 : Lt 67000 = 6395831780632133491 := (walkS_spec 1000 66000 6395831780632133491 (by rw [c_66]; exact w_66)).symm
theorem c_68 : Lt 68000 = 6403235545904530578 := (walkS_spec 1000 67000 6403235545904530578 (by rw [c_67]; exact w_67)).symm
theorem c_69 : Lt 69000 = 6410525838016258636 := (walkS_spec 1000 68000 6410525838016258636 (by rw [c_68]; exact w_68)).symm
theorem c_70 : Lt 70000 = 6417742063988916291 := (walkS_spec 1000 69000 6417742063988916291 (by rw [c_69]; exact w_69)).symm
theorem c_71 : Lt 71000 = 6424879186666546602 := (walkS_spec 1000 70000 6424879186666546602 (by rw [c_70]; exact w_70)).symm
theorem c_72 : Lt 72000 = 6431867814092512085 := (walkS_spec 1000 71000 6431867814092512085 (by rw [c_71]; exact w_71)).symm
theorem c_73 : Lt 73000 = 6438749327307107183 := (walkS_spec 1000 72000 6438749327307107183 (by rw [c_72]; exact w_72)).symm
theorem c_74 : Lt 74000 = 6445466504056148119 := (walkS_spec 1000 73000 6445466504056148119 (by rw [c_73]; exact w_73)).symm
theorem c_75 : Lt 75000 = 6452224576218461304 := (walkS_spec 1000 74000 6452224576218461304 (by rw [c_74]; exact w_74)).symm
theorem c_76 : Lt 76000 = 6458824552463683005 := (walkS_spec 1000 75000 6458824552463683005 (by rw [c_75]; exact w_75)).symm
theorem c_77 : Lt 77000 = 6465300609816709405 := (walkS_spec 1000 76000 6465300609816709405 (by rw [c_76]; exact w_76)).symm
theorem c_78 : Lt 78000 = 6471841139871762510 := (walkS_spec 1000 77000 6471841139871762510 (by rw [c_77]; exact w_77)).symm
theorem c_79 : Lt 79000 = 6478156356896934691 := (walkS_spec 1000 78000 6478156356896934691 (by rw [c_78]; exact w_78)).symm
theorem c_80 : Lt 80000 = 6484417592571512157 := (walkS_spec 1000 79000 6484417592571512157 (by rw [c_79]; exact w_79)).symm
theorem c_81 : Lt 81000 = 6490603861401649041 := (walkS_spec 1000 80000 6490603861401649041 (by rw [c_80]; exact w_80)).symm
theorem c_82 : Lt 82000 = 6496712110764215543 := (walkS_spec 1000 81000 6496712110764215543 (by rw [c_81]; exact w_81)).symm
theorem c_83 : Lt 83000 = 6502824663412353262 := (walkS_spec 1000 82000 6502824663412353262 (by rw [c_82]; exact w_82)).symm
theorem c_84 : Lt 84000 = 6508819310397126214 := (walkS_spec 1000 83000 6508819310397126214 (by rw [c_83]; exact w_83)).symm
theorem c_85 : Lt 85000 = 6514767353155126609 := (walkS_spec 1000 84000 6514767353155126609 (by rw [c_84]; exact w_84)).symm
theorem c_86 : Lt 86000 = 6520532005328876337 := (walkS_spec 1000 85000 6520532005328876337 (by rw [c_85]; exact w_85)).symm
theorem c_87 : Lt 87000 = 6526337122000886657 := (walkS_spec 1000 86000 6526337122000886657 (by rw [c_86]; exact w_86)).symm
theorem c_88 : Lt 88000 = 6532056021152032188 := (walkS_spec 1000 87000 6532056021152032188 (by rw [c_87]; exact w_87)).symm
theorem c_89 : Lt 89000 = 6537753991917232659 := (walkS_spec 1000 88000 6537753991917232659 (by rw [c_88]; exact w_88)).symm
theorem c_90 : Lt 90000 = 6543300288098367874 := (walkS_spec 1000 89000 6543300288098367874 (by rw [c_89]; exact w_89)).symm
theorem c_91 : Lt 91000 = 6548840125776438597 := (walkS_spec 1000 90000 6548840125776438597 (by rw [c_90]; exact w_90)).symm
theorem c_92 : Lt 92000 = 6554342880406220611 := (walkS_spec 1000 91000 6554342880406220611 (by rw [c_91]; exact w_91)).symm
theorem c_93 : Lt 93000 = 6559769985549341371 := (walkS_spec 1000 92000 6559769985549341371 (by rw [c_92]; exact w_92)).symm
theorem c_94 : Lt 94000 = 6565107079631088609 := (walkS_spec 1000 93000 6565107079631088609 (by rw [c_93]; exact w_93)).symm
theorem c_95 : Lt 95000 = 6570360604802795689 := (walkS_spec 1000 94000 6570360604802795689 (by rw [c_94]; exact w_94)).symm
theorem c_96 : Lt 96000 = 6575578320490708140 := (walkS_spec 1000 95000 6575578320490708140 (by rw [c_95]; exact w_95)).symm
theorem c_97 : Lt 97000 = 6580773909469147188 := (walkS_spec 1000 96000 6580773909469147188 (by rw [c_96]; exact w_96)).symm
theorem c_98 : Lt 98000 = 6585879451323040724 := (walkS_spec 1000 97000 6585879451323040724 (by rw [c_97]; exact w_97)).symm
theorem c_99 : Lt 99000 = 6590935110322018480 := (walkS_spec 1000 98000 6590935110322018480 (by rw [c_98]; exact w_98)).symm
theorem c_100 : Lt 100000 = 6596000883407292217 := (walkS_spec 1000 99000 6596000883407292217 (by rw [c_99]; exact w_99)).symm
theorem c_101 : Lt 101000 = 6600981890988093287 := (walkS_spec 1000 100000 6600981890988093287 (by rw [c_100]; exact w_100)).symm
theorem c_102 : Lt 102000 = 6605989527056240475 := (walkS_spec 1000 101000 6605989527056240475 (by rw [c_101]; exact w_101)).symm
theorem c_103 : Lt 103000 = 6610837732568966564 := (walkS_spec 1000 102000 6610837732568966564 (by rw [c_102]; exact w_102)).symm
theorem c_104 : Lt 104000 = 6615601895072018913 := (walkS_spec 1000 103000 6615601895072018913 (by rw [c_103]; exact w_103)).symm
theorem c_105 : Lt 105000 = 6620441721485812363 := (walkS_spec 1000 104000 6620441721485812363 (by rw [c_104]; exact w_104)).symm
theorem c_106 : Lt 106000 = 6625179854929626329 := (walkS_spec 1000 105000 6625179854929626329 (by rw [c_105]; exact w_105)).symm
theorem c_107 : Lt 107000 = 6629897803982890150 := (walkS_spec 1000 106000 6629897803982890150 (by rw [c_106]; exact w_106)).symm
theorem c_108 : Lt 108000 = 6634567152388323521 := (walkS_spec 1000 107000 6634567152388323521 (by rw [c_107]; exact w_107)).symm
theorem c_109 : Lt 109000 = 6639192575806384998 := (walkS_spec 1000 108000 6639192575806384998 (by rw [c_108]; exact w_108)).symm
theorem c_110 : Lt 110000 = 6643745631151585649 := (walkS_spec 1000 109000 6643745631151585649 (by rw [c_109]; exact w_109)).symm
theorem c_111 : Lt 111000 = 6648232954118903762 := (walkS_spec 1000 110000 6648232954118903762 (by rw [c_110]; exact w_110)).symm
theorem c_112 : Lt 112000 = 6652738693332884054 := (walkS_spec 1000 111000 6652738693332884054 (by rw [c_111]; exact w_111)).symm
theorem c_113 : Lt 113000 = 6657145696182332173 := (walkS_spec 1000 112000 6657145696182332173 (by rw [c_112]; exact w_112)).symm
theorem c_114 : Lt 114000 = 6661586584718710094 := (walkS_spec 1000 113000 6661586584718710094 (by rw [c_113]; exact w_113)).symm
theorem c_115 : Lt 115000 = 6665970046730170624 := (walkS_spec 1000 114000 6665970046730170624 (by rw [c_114]; exact w_114)).symm
theorem c_116 : Lt 116000 = 6670248047441342741 := (walkS_spec 1000 115000 6670248047441342741 (by rw [c_115]; exact w_115)).symm
theorem c_117 : Lt 117000 = 6674541235583940925 := (walkS_spec 1000 116000 6674541235583940925 (by rw [c_116]; exact w_116)).symm
theorem c_118 : Lt 118000 = 6678820064222002188 := (walkS_spec 1000 117000 6678820064222002188 (by rw [c_117]; exact w_117)).symm
theorem c_119 : Lt 119000 = 6683018893906618267 := (walkS_spec 1000 118000 6683018893906618267 (by rw [c_118]; exact w_118)).symm
theorem c_120 : Lt 120000 = 6687206554484702760 := (walkS_spec 1000 119000 6687206554484702760 (by rw [c_119]; exact w_119)).symm
theorem c_121 : Lt 121000 = 6691341463704370266 := (walkS_spec 1000 120000 6691341463704370266 (by rw [c_120]; exact w_120)).symm
theorem c_122 : Lt 122000 = 6695414452891015997 := (walkS_spec 1000 121000 6695414452891015997 (by rw [c_121]; exact w_121)).symm
theorem c_123 : Lt 123000 = 6699486504654875044 := (walkS_spec 1000 122000 6699486504654875044 (by rw [c_122]; exact w_122)).symm
theorem c_124 : Lt 124000 = 6703566135293605854 := (walkS_spec 1000 123000 6703566135293605854 (by rw [c_123]; exact w_123)).symm
theorem c_125 : Lt 125000 = 6707609846256649616 := (walkS_spec 1000 124000 6707609846256649616 (by rw [c_124]; exact w_124)).symm
theorem c_126 : Lt 126000 = 6711552151962069658 := (walkS_spec 1000 125000 6711552151962069658 (by rw [c_125]; exact w_125)).symm
theorem c_127 : Lt 127000 = 6715539164519801917 := (walkS_spec 1000 126000 6715539164519801917 (by rw [c_126]; exact w_126)).symm
theorem c_128 : Lt 128000 = 6719482415920170262 := (walkS_spec 1000 127000 6719482415920170262 (by rw [c_127]; exact w_127)).symm
theorem c_129 : Lt 129000 = 6723372341205862139 := (walkS_spec 1000 128000 6723372341205862139 (by rw [c_128]; exact w_128)).symm
theorem c_130 : Lt 130000 = 6727269073361332994 := (walkS_spec 1000 129000 6727269073361332994 (by rw [c_129]; exact w_129)).symm
theorem c_131 : Lt 131000 = 6731072587089282558 := (walkS_spec 1000 130000 6731072587089282558 (by rw [c_130]; exact w_130)).symm
theorem c_132 : Lt 132000 = 6734875660393277758 := (walkS_spec 1000 131000 6734875660393277758 (by rw [c_131]; exact w_131)).symm
theorem c_133 : Lt 133000 = 6738638775247437262 := (walkS_spec 1000 132000 6738638775247437262 (by rw [c_132]; exact w_132)).symm
theorem c_134 : Lt 134000 = 6742390657824783779 := (walkS_spec 1000 133000 6742390657824783779 (by rw [c_133]; exact w_133)).symm
theorem c_135 : Lt 135000 = 6746060703792373515 := (walkS_spec 1000 134000 6746060703792373515 (by rw [c_134]; exact w_134)).symm
theorem c_136 : Lt 136000 = 6749757422632792613 := (walkS_spec 1000 135000 6749757422632792613 (by rw [c_135]; exact w_135)).symm
theorem c_137 : Lt 137000 = 6753453381091269697 := (walkS_spec 1000 136000 6753453381091269697 (by rw [c_136]; exact w_136)).symm
theorem c_138 : Lt 138000 = 6757093904261128892 := (walkS_spec 1000 137000 6757093904261128892 (by rw [c_137]; exact w_137)).symm
theorem c_139 : Lt 139000 = 6760747087559032429 := (walkS_spec 1000 138000 6760747087559032429 (by rw [c_138]; exact w_138)).symm
theorem c_140 : Lt 140000 = 6764289375758062501 := (walkS_spec 1000 139000 6764289375758062501 (by rw [c_139]; exact w_139)).symm
theorem c_141 : Lt 141000 = 6767876150983055743 := (walkS_spec 1000 140000 6767876150983055743 (by rw [c_140]; exact w_140)).symm
theorem c_142 : Lt 142000 = 6771405179907296656 := (walkS_spec 1000 141000 6771405179907296656 (by rw [c_141]; exact w_141)).symm
theorem c_143 : Lt 143000 = 6774933504372483218 := (walkS_spec 1000 142000 6774933504372483218 (by rw [c_142]; exact w_142)).symm
theorem c_144 : Lt 144000 = 6778382565504218659 := (walkS_spec 1000 143000 6778382565504218659 (by rw [c_143]; exact w_143)).symm
theorem c_145 : Lt 145000 = 6781827103346562807 := (walkS_spec 1000 144000 6781827103346562807 (by rw [c_144]; exact w_144)).symm
theorem c_146 : Lt 146000 = 6785282442498161141 := (walkS_spec 1000 145000 6785282442498161141 (by rw [c_145]; exact w_145)).symm
theorem c_147 : Lt 147000 = 6788694386611773813 := (walkS_spec 1000 146000 6788694386611773813 (by rw [c_146]; exact w_146)).symm
theorem c_148 : Lt 148000 = 6792127848307623369 := (walkS_spec 1000 147000 6792127848307623369 (by rw [c_147]; exact w_147)).symm
theorem c_149 : Lt 149000 = 6795472087827430446 := (walkS_spec 1000 148000 6795472087827430446 (by rw [c_148]; exact w_148)).symm
theorem c_150 : Lt 150000 = 6798779173123473292 := (walkS_spec 1000 149000 6798779173123473292 (by rw [c_149]; exact w_149)).symm

/-- **`6.798779 ≤ ∑_{q ≤ 150000, q odd} μ²(q)/φ(q) ≤ 6.79878`** (kernel-checked). -/
theorem sum_bounds : 6.798779 ≤ S 150000 ∧ S 150000 ≤ 6.79878 := by
  have h := S_approx 150000
  rw [c_150] at h
  push_cast at h
  constructor <;> linarith [h.1, h.2]

end TernaryGoldbach.Prelim.SmallMuPhi
