import TernaryGoldbach.Prelim.SmallPsiData1
import TernaryGoldbach.Prelim.SmallPsiData2
import TernaryGoldbach.Prelim.SmallPsiData3
import TernaryGoldbach.Prelim.SmallPsiData4
import TernaryGoldbach.Prelim.SmallPsiData5
import TernaryGoldbach.Prelim.SmallPsiData6

/-!
# `θ` and `ψ` on `[12, 10⁶]`, kernel-checked (route D, step P9a)

`|ψ(t) − t| ≤ √t` and `t − 2.3662 √t ≤ θ(t) ≤ t` for real `12 ≤ t < 10⁶` (`small_table`), chaining
`outer_spec` through the chunks `chunk0`, …, `chunk117` (stage lemmas `stage_k`).
-/

open Finset

namespace TernaryGoldbach.Prelim.SmallTab

theorem Inv_one : Inv 1 0 0 0 0 := by
  have h1 : thS 1 = 0 := by unfold thS; simp [Finset.filter_singleton, Nat.not_prime_one]
  have h2 : ppS 1 = 0 := by unfold ppS; simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h1, h2]

theorem stage0 : Inv 12 7745002791 7745002816 2484906642 2484906657 ∧ ((2484906647 : ℕ) : ℝ) / S ≤ Real.log ((12 : ℕ) : ℝ) ∧ Real.log ((12 : ℕ) : ℝ) ≤ ((2484906652 : ℕ) : ℝ) / S := by
  obtain ⟨-, I, L, H⟩ := outer_spec (cN := 1000000) (cD := 1) (tN := 1000000) (tD := 1) (by norm_num) (by norm_num)
    gs0 1 0 0 0 0 0 0 12 7745002791 7745002816 2484906642 2484906657 2484906647 2484906652 (by norm_num) sum0 Inv_one (by simp) (by simp)
    (resEq_spec chunk0)
  exact ⟨I, L, H⟩

theorem stage1 : (∀ t : ℝ, 12 ≤ t → t < 262 → Rt 1 1 23662 10000 t) ∧ Inv 262 237668036021 237668036296 19374109982 19374110062 ∧ ((5568344501 : ℕ) : ℝ) / S ≤ Real.log ((262 : ℕ) : ℝ) ∧ Real.log ((262 : ℕ) : ℝ) ≤ ((5568344506 : ℕ) : ℝ) / S := by
  obtain ⟨I0, L0, H0⟩ := stage0
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs1 12 7745002791 7745002816 2484906642 2484906657 2484906647 2484906652 262 237668036021 237668036296 19374109982 19374110062 5568344501 5568344506 (by norm_num) sum1 I0 L0 H0 (resEq_spec chunk1)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  exact R t (by exact_mod_cast h1) (by exact_mod_cast h2)

theorem stage2 : (∀ t : ℝ, 12 ≤ t → t < 300 → Rt 1 1 23662 10000 t) ∧ Inv 300 277025011919 277025012229 22207323324 22207323409 ∧ ((5703782472 : ℕ) : ℝ) / S ≤ Real.log ((300 : ℕ) : ℝ) ∧ Real.log ((300 : ℕ) : ℝ) ≤ ((5703782477 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage1
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs2 262 237668036021 237668036296 19374109982 19374110062 5568344501 5568344506 300 277025011919 277025012229 22207323324 22207323409 5703782472 5703782477 (by norm_num) sum2 I0 L0 H0 (resEq_spec chunk2)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 262 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage3 : (∀ t : ℝ, 12 ≤ t → t < 550 → Rt 1 1 23662 10000 t) ∧ Inv 550 512120681676 512120682181 30926313839 30926313944 ∧ ((6309918276 : ℕ) : ℝ) / S ≤ Real.log ((550 : ℕ) : ℝ) ∧ Real.log ((550 : ℕ) : ℝ) ≤ ((6309918281 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage2
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs3 300 277025011919 277025012229 22207323324 22207323409 5703782472 5703782477 550 512120681676 512120682181 30926313839 30926313944 6309918276 6309918281 (by norm_num) sum3 I0 L0 H0 (resEq_spec chunk3)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 300 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage4 : (∀ t : ℝ, 12 ≤ t → t < 800 → Rt 1 1 23662 10000 t) ∧ Inv 800 759094660383 759094661078 33634364035 33634364150 ∧ ((6684611725 : ℕ) : ℝ) / S ≤ Real.log ((800 : ℕ) : ℝ) ∧ Real.log ((800 : ℕ) : ℝ) ≤ ((6684611730 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage3
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs4 550 512120681676 512120682181 30926313839 30926313944 6309918276 6309918281 800 759094660383 759094661078 33634364035 33634364150 6684611725 6684611730 (by norm_num) sum4 I0 L0 H0 (resEq_spec chunk4)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 550 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage5 : (∀ t : ℝ, 12 ≤ t → t < 1000 → Rt 1 1 23662 10000 t) ∧ Inv 1000 956245264699 956245265539 40435647064 40435647189 ∧ ((6907755276 : ℕ) : ℝ) / S ≤ Real.log ((1000 : ℕ) : ℝ) ∧ Real.log ((1000 : ℕ) : ℝ) ≤ ((6907755281 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage4
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs5 800 759094660383 759094661078 33634364035 33634364150 6684611725 6684611730 1000 956245264699 956245265539 40435647064 40435647189 6907755276 6907755281 (by norm_num) sum5 I0 L0 H0 (resEq_spec chunk5)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 800 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage6 : (∀ t : ℝ, 12 ≤ t → t < 2374 → Rt 1 1 23662 10000 t) ∧ Inv 2374 2308585330272 2309211661195 62819236017 62819236187 ∧ ((7772331573 : ℕ) : ℝ) / S ≤ Real.log ((2374 : ℕ) : ℝ) ∧ Real.log ((2374 : ℕ) : ℝ) ≤ ((7772331578 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage5
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs6 1000 956245264699 956245265539 40435647064 40435647189 6907755276 6907755281 2374 2308585330272 2309211661195 62819236017 62819236187 7772331573 7772331578 (by norm_num) sum6 I0 L0 H0 (resEq_spec chunk6)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 1000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage7 : (∀ t : ℝ, 12 ≤ t → t < 2500 → Rt 1 1 23662 10000 t) ∧ Inv 2500 2433247711734 2433920267152 64765146164 64765146339 ∧ ((7824046008 : ℕ) : ℝ) / S ≤ Real.log ((2500 : ℕ) : ℝ) ∧ Real.log ((2500 : ℕ) : ℝ) ≤ ((7824046013 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage6
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs7 2374 2308585330272 2309211661195 62819236017 62819236187 7772331573 7772331578 2500 2433247711734 2433920267152 64765146164 64765146339 7824046008 7824046013 (by norm_num) sum7 I0 L0 H0 (resEq_spec chunk7)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 2374 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage8 : (∀ t : ℝ, 12 ≤ t → t < 4568 → Rt 1 1 23662 10000 t) ∧ Inv 4568 4487280779193 4488557708024 83431127083 83431127288 ∧ ((8426830749 : ℕ) : ℝ) / S ≤ Real.log ((4568 : ℕ) : ℝ) ∧ Real.log ((4568 : ℕ) : ℝ) ≤ ((8426830754 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage7
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs8 2500 2433247711734 2433920267152 64765146164 64765146339 7824046008 7824046013 4568 4487280779193 4488557708024 83431127083 83431127288 8426830749 8426830754 (by norm_num) sum8 I0 L0 H0 (resEq_spec chunk8)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 2500 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage9 : (∀ t : ℝ, 12 ≤ t → t < 5000 → Rt 1 1 23662 10000 t) ∧ Inv 5000 4910968834720 4912348532268 86264340425 86264340635 ∧ ((8517193189 : ℕ) : ℝ) / S ≤ Real.log ((5000 : ℕ) : ℝ) ∧ Real.log ((5000 : ℕ) : ℝ) ≤ ((8517193194 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage8
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs9 4568 4487280779193 4488557708024 83431127083 83431127288 8426830749 8426830754 5000 4910968834720 4912348532268 86264340425 86264340635 8517193189 8517193194 (by norm_num) sum9 I0 L0 H0 (resEq_spec chunk9)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 4568 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage10 : (∀ t : ℝ, 12 ≤ t → t < 7857 → Rt 1 1 23662 10000 t) ∧ Inv 7857 7739447645111 7741410564892 107648819457 107648819697 ∧ ((8969160131 : ℕ) : ℝ) / S ≤ Real.log ((7857 : ℕ) : ℝ) ∧ Real.log ((7857 : ℕ) : ℝ) ≤ ((8969160136 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage9
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs10 5000 4910968834720 4912348532268 86264340425 86264340635 8517193189 8517193194 7857 7739447645111 7741410564892 107648819457 107648819697 8969160131 8969160136 (by norm_num) sum10 I0 L0 H0 (resEq_spec chunk10)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 5000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage11 : (∀ t : ℝ, 12 ≤ t → t < 10000 → Rt 1 1 23662 10000 t) ∧ Inv 10000 9894752164677 9897077033149 117405313978 117405314233 ∧ ((9210340369 : ℕ) : ℝ) / S ≤ Real.log ((10000 : ℕ) : ℝ) ∧ Real.log ((10000 : ℕ) : ℝ) ≤ ((9210340374 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage10
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs11 7857 7739447645111 7741410564892 107648819457 107648819697 8969160131 8969160136 10000 9894752164677 9897077033149 117405313978 117405314233 9210340369 9210340374 (by norm_num) sum11 I0 L0 H0 (resEq_spec chunk11)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 7857 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage12 : (∀ t : ℝ, 12 ≤ t → t < 13974 → Rt 1 1 23662 10000 t) ∧ Inv 13974 13846688513429 13849575532394 143882222219 143882222504 ∧ ((9544953737 : ℕ) : ℝ) / S ≤ Real.log ((13974 : ℕ) : ℝ) ∧ Real.log ((13974 : ℕ) : ℝ) ≤ ((9544953742 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage11
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs12 10000 9894752164677 9897077033149 117405313978 117405314233 9210340369 9210340374 13974 13846688513429 13849575532394 143882222219 143882222504 9544953737 9544953742 (by norm_num) sum12 I0 L0 H0 (resEq_spec chunk12)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 10000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage13 : (∀ t : ℝ, 12 ≤ t → t < 18623 → Rt 1 1 23662 10000 t) ∧ Inv 18623 18490739090706 18494175871893 160247997129 160247997444 ∧ ((9832152652 : ℕ) : ℝ) / S ≤ Real.log ((18623 : ℕ) : ℝ) ∧ Real.log ((18623 : ℕ) : ℝ) ≤ ((9832152657 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage12
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs13 13974 13846688513429 13849575532394 143882222219 143882222504 9544953737 9544953742 18623 18490739090706 18494175871893 160247997129 160247997444 9832152652 9832152657 (by norm_num) sum13 I0 L0 H0 (resEq_spec chunk13)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 13974 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage14 : (∀ t : ℝ, 12 ≤ t → t < 20000 → Rt 1 1 23662 10000 t) ∧ Inv 20000 19803430873910 19807006776244 171201064269 171201064599 ∧ ((9903487550 : ℕ) : ℝ) / S ≤ Real.log ((20000 : ℕ) : ℝ) ∧ Real.log ((20000 : ℕ) : ℝ) ≤ ((9903487555 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage13
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs14 18623 18490739090706 18494175871893 160247997129 160247997444 9832152652 9832152657 20000 19803430873910 19807006776244 171201064269 171201064599 9903487550 9903487555 (by norm_num) sum14 I0 L0 H0 (resEq_spec chunk14)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 18623 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage15 : (∀ t : ℝ, 12 ≤ t → t < 25515 → Rt 1 1 23662 10000 t) ∧ Inv 25515 25298616452783 25302794013961 189645832036 189645832386 ∧ ((10146903458 : ℕ) : ℝ) / S ≤ Real.log ((25515 : ℕ) : ℝ) ∧ Real.log ((25515 : ℕ) : ℝ) ≤ ((10147140194 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage14
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs15 20000 19803430873910 19807006776244 171201064269 171201064599 9903487550 9903487555 25515 25298616452783 25302794013961 189645832036 189645832386 10146903458 10147140194 (by norm_num) sum15 I0 L0 H0 (resEq_spec chunk15)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 20000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage16 : (∀ t : ℝ, 12 ≤ t → t < 30000 → Rt 1 1 23662 10000 t) ∧ Inv 30000 29747930135060 29752523969636 211009804193 211009804568 ∧ ((10308881506 : ℕ) : ℝ) / S ≤ Real.log ((30000 : ℕ) : ℝ) ∧ Real.log ((30000 : ℕ) : ℝ) ≤ ((10309023854 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage15
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs16 25515 25298616452783 25302794013961 189645832036 189645832386 10146903458 10147140194 30000 29747930135060 29752523969636 211009804193 211009804568 10308881506 10309023854 (by norm_num) sum16 I0 L0 H0 (resEq_spec chunk16)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 25515 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage17 : (∀ t : ℝ, 12 ≤ t → t < 36722 → Rt 1 1 23662 10000 t) ∧ Inv 36722 36505689150272 36510862883907 227341107629 227341108024 ∧ ((10511049714 : ℕ) : ℝ) / S ≤ Real.log ((36722 : ℕ) : ℝ) ∧ Real.log ((36722 : ℕ) : ℝ) ≤ ((10511212946 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage16
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs17 30000 29747930135060 29752523969636 211009804193 211009804568 10308881506 10309023854 36722 36505689150272 36510862883907 227341107629 227341108024 10511049714 10511212946 (by norm_num) sum17 I0 L0 H0 (resEq_spec chunk17)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 30000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage18 : (∀ t : ℝ, 12 ≤ t → t < 40000 → Rt 1 1 23662 10000 t) ∧ Inv 40000 39766891192290 39772306761954 243180306363 243180306773 ∧ ((10596602890 : ℕ) : ℝ) / S ≤ Real.log ((40000 : ℕ) : ℝ) ∧ Real.log ((40000 : ℕ) : ℝ) ≤ ((10596666591 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage17
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs18 36722 36505689150272 36510862883907 227341107629 227341108024 10511049714 10511212946 40000 39766891192290 39772306761954 243180306363 243180306773 10596602890 10596666591 (by norm_num) sum18 I0 L0 H0 (resEq_spec chunk18)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 36722 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage19 : (∀ t : ℝ, 12 ≤ t → t < 47728 → Rt 1 1 23662 10000 t) ∧ Inv 47728 47429150187344 47435118276747 248532164494 248532164909 ∧ ((10773211229 : ℕ) : ℝ) / S ≤ Real.log ((47728 : ℕ) : ℝ) ∧ Real.log ((47728 : ℕ) : ℝ) ≤ ((10773335826 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage18
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs19 40000 39766891192290 39772306761954 243180306363 243180306773 10596602890 10596666591 47728 47429150187344 47435118276747 248532164494 248532164909 10773211229 10773335826 (by norm_num) sum19 I0 L0 H0 (resEq_spec chunk19)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 40000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage20 : (∀ t : ℝ, 12 ≤ t → t < 50000 → Rt 1 1 23662 10000 t) ∧ Inv 50000 49728862457905 49734975638883 253939336263 253939336683 ∧ ((10819762966 : ℕ) : ℝ) / S ≤ Real.log ((50000 : ℕ) : ℝ) ∧ Real.log ((50000 : ℕ) : ℝ) ≤ ((10819793608 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage19
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs20 47728 47429150187344 47435118276747 248532164494 248532164909 10773211229 10773335826 50000 49728862457905 49734975638883 253939336263 253939336683 10819762966 10819793608 (by norm_num) sum20 I0 L0 H0 (resEq_spec chunk20)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 47728 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage21 : (∀ t : ℝ, 12 ≤ t → t < 58603 → Rt 1 1 23662 10000 t) ∧ Inv 58603 58428358518170 58435020148807 284821225120 284821225570 ∧ ((10978490834 : ℕ) : ℝ) / S ≤ Real.log ((58603 : ℕ) : ℝ) ∧ Real.log ((58603 : ℕ) : ℝ) ≤ ((10978591527 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage20
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs21 50000 49728862457905 49734975638883 253939336263 253939336683 10819762966 10819793608 58603 58428358518170 58435020148807 284821225120 284821225570 10978490834 10978591527 (by norm_num) sum21 I0 L0 H0 (resEq_spec chunk21)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 50000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage22 : (∀ t : ℝ, 12 ≤ t → t < 60000 → Rt 1 1 23662 10000 t) ∧ Inv 60000 59813091299149 59819830154921 285919837406 285919837861 ∧ ((11002092887 : ℕ) : ℝ) / S ≤ Real.log ((60000 : ℕ) : ℝ) ∧ Real.log ((60000 : ℕ) : ℝ) ≤ ((11002106799 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage21
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs22 58603 58428358518170 58435020148807 284821225120 284821225570 10978490834 10978591527 60000 59813091299149 59819830154921 285919837406 285919837861 11002092887 11002106799 (by norm_num) sum22 I0 L0 H0 (resEq_spec chunk22)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 58603 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage23 : (∀ t : ℝ, 12 ≤ t → t < 69408 → Rt 1 1 23662 10000 t) ∧ Inv 69408 69039824116987 69047084486356 306973239697 306973240177 ∧ ((11147715020 : ℕ) : ℝ) / S ≤ Real.log ((69408 : ℕ) : ℝ) ∧ Real.log ((69408 : ℕ) : ℝ) ≤ ((11147799818 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage22
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs23 60000 59813091299149 59819830154921 285919837406 285919837861 11002092887 11002106799 69408 69039824116987 69047084486356 306973239697 306973240177 11147715020 11147799818 (by norm_num) sum23 I0 L0 H0 (resEq_spec chunk23)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 60000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage24 : (∀ t : ℝ, 12 ≤ t → t < 70000 → Rt 1 1 23662 10000 t) ∧ Inv 70000 69541652331916 69548937643344 306973239697 306973240177 ∧ ((11156248317 : ℕ) : ℝ) / S ≤ Real.log ((70000 : ℕ) : ℝ) ∧ Real.log ((70000 : ℕ) : ℝ) ≤ ((11156252728 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage23
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs24 69408 69039824116987 69047084486356 306973239697 306973240177 11147715020 11147799818 70000 69541652331916 69548937643344 306973239697 306973240177 11156248317 11156252728 (by norm_num) sum24 I0 L0 H0 (resEq_spec chunk24)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 69408 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage25 : (∀ t : ℝ, 12 ≤ t → t < 80000 → Rt 1 1 23662 10000 t) ∧ Inv 80000 79665177214958 79672983301336 334803080086 334803080596 ∧ ((11289745816 : ℕ) : ℝ) / S ≤ Real.log ((80000 : ℕ) : ℝ) ∧ Real.log ((80000 : ℕ) : ℝ) ≤ ((11289818022 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage24
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs25 70000 69541652331916 69548937643344 306973239697 306973240177 11156248317 11156252728 80000 79665177214958 79672983301336 334803080086 334803080596 11289745816 11289818022 (by norm_num) sum25 I0 L0 H0 (resEq_spec chunk25)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 70000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage26 : (∀ t : ℝ, 12 ≤ t → t < 90000 → Rt 1 1 23662 10000 t) ∧ Inv 90000 89607130692855 89615408431028 348961912930 348961913455 ∧ ((11407535050 : ℕ) : ℝ) / S ≤ Real.log ((90000 : ℕ) : ℝ) ∧ Real.log ((90000 : ℕ) : ℝ) ≤ ((11407594858 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage25
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs26 80000 79665177214958 79672983301336 334803080086 334803080596 11289745816 11289818022 90000 89607130692855 89615408431028 348961912930 348961913455 11407535050 11407594858 (by norm_num) sum26 I0 L0 H0 (resEq_spec chunk26)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 80000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage27 : (∀ t : ℝ, 12 ≤ t → t < 100000 → Rt 1 1 23662 10000 t) ∧ Inv 100000 99680902378766 99689626404964 366174756773 366174757313 ∧ ((11512900100 : ℕ) : ℝ) / S ≤ Real.log ((100000 : ℕ) : ℝ) ∧ Real.log ((100000 : ℕ) : ℝ) ≤ ((11512950835 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage26
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs27 90000 89607130692855 89615408431028 348961912930 348961913455 11407535050 11407594858 100000 99680902378766 99689626404964 366174756773 366174757313 11512900100 11512950835 (by norm_num) sum27 I0 L0 H0 (resEq_spec chunk27)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 90000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage28 : (∀ t : ℝ, 12 ≤ t → t < 110000 → Rt 1 1 23662 10000 t) ∧ Inv 110000 109635131750198 109644269365069 381585924516 381585925071 ∧ ((11608213818 : ℕ) : ℝ) / S ≤ Real.log ((110000 : ℕ) : ℝ) ∧ Real.log ((110000 : ℕ) : ℝ) ≤ ((11608257484 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage27
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs28 100000 99680902378766 99689626404964 366174756773 366174757313 11512900100 11512950835 110000 109635131750198 109644269365069 381585924516 381585925071 11608213818 11608257484 (by norm_num) sum28 I0 L0 H0 (resEq_spec chunk28)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 100000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage29 : (∀ t : ℝ, 12 ≤ t → t < 120000 → Rt 1 1 23662 10000 t) ∧ Inv 120000 119516369361260 119525894212237 389351917591 389351918156 ∧ ((11695227987 : ℕ) : ℝ) / S ≤ Real.log ((120000 : ℕ) : ℝ) ∧ Real.log ((120000 : ℕ) : ℝ) ≤ ((11695266060 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage28
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs29 110000 109635131750198 109644269365069 381585924516 381585925071 11608213818 11608257484 120000 119516369361260 119525894212237 389351917591 389351918156 11695227987 11695266060 (by norm_num) sum29 I0 L0 H0 (resEq_spec chunk29)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 110000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage30 : (∀ t : ℝ, 12 ≤ t → t < 130000 → Rt 1 1 23662 10000 t) ∧ Inv 130000 129585296658237 129595196864111 412806104728 412806105313 ∧ ((11775272912 : ℕ) : ℝ) / S ≤ Real.log ((130000 : ℕ) : ℝ) ∧ Real.log ((130000 : ℕ) : ℝ) ≤ ((11775306543 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage29
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs30 120000 119516369361260 119525894212237 389351917591 389351918156 11695227987 11695266060 130000 129585296658237 129595196864111 412806104728 412806105313 11775272912 11775306543 (by norm_num) sum30 I0 L0 H0 (resEq_spec chunk30)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 120000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage31 : (∀ t : ℝ, 12 ≤ t → t < 140000 → Rt 1 1 23662 10000 t) ∧ Inv 140000 139637889274506 139648146511016 428270631146 428270631751 ∧ ((11849382703 : ℕ) : ℝ) / S ≤ Real.log ((140000 : ℕ) : ℝ) ∧ Real.log ((140000 : ℕ) : ℝ) ≤ ((11849412693 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage30
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs31 130000 129585296658237 129595196864111 412806104728 412806105313 11775272912 11775306543 140000 139637889274506 139648146511016 428270631146 428270631751 11849382703 11849412693 (by norm_num) sum31 I0 L0 H0 (resEq_spec chunk31)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 130000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage32 : (∀ t : ℝ, 12 ≤ t → t < 150000 → Rt 1 1 23662 10000 t) ∧ Inv 150000 149596926831452 149607522391066 444126494247 444126494867 ∧ ((11918377105 : ℕ) : ℝ) / S ≤ Real.log ((150000 : ℕ) : ℝ) ∧ Real.log ((150000 : ℕ) : ℝ) ≤ ((11918404037 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage31
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs32 140000 139637889274506 139648146511016 428270631146 428270631751 11849382703 11849412693 150000 149596926831452 149607522391066 444126494247 444126494867 11918377105 11918404037 (by norm_num) sum32 I0 L0 H0 (resEq_spec chunk32)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 140000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage33 : (∀ t : ℝ, 12 ≤ t → t < 160000 → Rt 1 1 23662 10000 t) ∧ Inv 160000 159575522492210 159586443613342 456074009866 456074010496 ∧ ((11982916900 : ℕ) : ℝ) / S ≤ Real.log ((160000 : ℕ) : ℝ) ∧ Real.log ((160000 : ℕ) : ℝ) ≤ ((11982941290 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage32
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs33 150000 149596926831452 149607522391066 444126494247 444126494867 11918377105 11918404037 160000 159575522492210 159586443613342 456074009866 456074010496 11982916900 11982941290 (by norm_num) sum33 I0 L0 H0 (resEq_spec chunk33)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 150000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage34 : (∀ t : ℝ, 12 ≤ t → t < 170000 → Rt 1 1 23662 10000 t) ∧ Inv 170000 169354251915362 169365480141680 470479581715 470479582360 ∧ ((12043542613 : ℕ) : ℝ) / S ≤ Real.log ((170000 : ℕ) : ℝ) ∧ Real.log ((170000 : ℕ) : ℝ) ≤ ((12043564834 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage33
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs34 160000 159575522492210 159586443613342 456074009866 456074010496 11982916900 11982941290 170000 169354251915362 169365480141680 470479581715 470479582360 12043542613 12043564834 (by norm_num) sum34 I0 L0 H0 (resEq_spec chunk34)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 160000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage35 : (∀ t : ℝ, 12 ≤ t → t < 180000 → Rt 1 1 23662 10000 t) ∧ Inv 180000 179555531330625 179567068461418 483658697749 483658698409 ∧ ((12100701956 : ℕ) : ℝ) / S ≤ Real.log ((180000 : ℕ) : ℝ) ∧ Real.log ((180000 : ℕ) : ℝ) ≤ ((12100722307 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage34
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs35 170000 169354251915362 169365480141680 470479581715 470479582360 12043542613 12043564834 180000 179555531330625 179567068461418 483658697749 483658698409 12100701956 12100722307 (by norm_num) sum35 I0 L0 H0 (resEq_spec chunk35)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 170000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage36 : (∀ t : ℝ, 12 ≤ t → t < 190000 → Rt 1 1 23662 10000 t) ∧ Inv 190000 189597745497963 189609576586038 495795543563 495795544233 ∧ ((12154769991 : ℕ) : ℝ) / S ≤ Real.log ((190000 : ℕ) : ℝ) ∧ Real.log ((190000 : ℕ) : ℝ) ≤ ((12154788718 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage35
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs36 180000 179555531330625 179567068461418 483658697749 483658698409 12100701956 12100722307 190000 189597745497963 189609576586038 495795543563 495795544233 12154769991 12154788718 (by norm_num) sum36 I0 L0 H0 (resEq_spec chunk36)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 180000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage37 : (∀ t : ℝ, 12 ≤ t → t < 200000 → Rt 1 1 23662 10000 t) ∧ Inv 200000 199512767756885 199524879942370 507973612742 507973613422 ∧ ((12206063995 : ℕ) : ℝ) / S ≤ Real.log ((200000 : ℕ) : ℝ) ∧ Real.log ((200000 : ℕ) : ℝ) ≤ ((12206081296 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage36
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs37 190000 189597745497963 189609576586038 495795543563 495795544233 12154769991 12154788718 200000 199512767756885 199524879942370 507973612742 507973613422 12206063995 12206081296 (by norm_num) sum37 I0 L0 H0 (resEq_spec chunk37)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 190000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage38 : (∀ t : ℝ, 12 ≤ t → t < 210000 → Rt 1 1 23662 10000 t) ∧ Inv 210000 209578835331633 209591224617625 524282856456 524282857151 ∧ ((12254854771 : ℕ) : ℝ) / S ≤ Real.log ((210000 : ℕ) : ℝ) ∧ Real.log ((210000 : ℕ) : ℝ) ≤ ((12254870846 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage37
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs38 200000 199512767756885 199524879942370 507973612742 507973613422 12206063995 12206081296 210000 209578835331633 209591224617625 524282856456 524282857151 12254854771 12254870846 (by norm_num) sum38 I0 L0 H0 (resEq_spec chunk38)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 200000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage39 : (∀ t : ℝ, 12 ≤ t → t < 220000 → Rt 1 1 23662 10000 t) ∧ Inv 220000 219536596509658 219549252079880 542700310803 542700311513 ∧ ((12301375342 : ℕ) : ℝ) / S ≤ Real.log ((220000 : ℕ) : ℝ) ∧ Real.log ((220000 : ℕ) : ℝ) ≤ ((12301390314 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage38
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs39 210000 209578835331633 209591224617625 524282856456 524282857151 12254854771 12254870846 220000 219536596509658 219549252079880 542700310803 542700311513 12301375342 12301390314 (by norm_num) sum39 I0 L0 H0 (resEq_spec chunk39)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 210000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage40 : (∀ t : ℝ, 12 ≤ t → t < 230000 → Rt 1 1 23662 10000 t) ∧ Inv 230000 229629936112469 229642854085503 552982885260 552982885980 ∧ ((12345827608 : ℕ) : ℝ) / S ≤ Real.log ((230000 : ℕ) : ℝ) ∧ Real.log ((230000 : ℕ) : ℝ) ≤ ((12345841581 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage39
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs40 220000 219536596509658 219549252079880 542700310803 542700311513 12301375342 12301390314 230000 229629936112469 229642854085503 552982885260 552982885980 12345827608 12345841581 (by norm_num) sum40 I0 L0 H0 (resEq_spec chunk40)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 220000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage41 : (∀ t : ℝ, 12 ≤ t → t < 240000 → Rt 1 1 23662 10000 t) ∧ Inv 240000 239325753119381 239338917020322 559171149381 559171150106 ∧ ((12388387646 : ℕ) : ℝ) / S ≤ Real.log ((240000 : ℕ) : ℝ) ∧ Real.log ((240000 : ℕ) : ℝ) ≤ ((12388400762 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage40
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs41 230000 229629936112469 229642854085503 552982885260 552982885980 12345827608 12345841581 240000 239325753119381 239338917020322 559171149381 559171150106 12388387646 12388400762 (by norm_num) sum41 I0 L0 H0 (resEq_spec chunk41)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 230000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage42 : (∀ t : ℝ, 12 ≤ t → t < 250000 → Rt 1 1 23662 10000 t) ∧ Inv 250000 249538230575125 249551646747035 571580199599 571580200334 ∧ ((12429210047 : ℕ) : ℝ) / S ≤ Real.log ((250000 : ℕ) : ℝ) ∧ Real.log ((250000 : ℕ) : ℝ) ≤ ((12429222353 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage41
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs42 240000 239325753119381 239338917020322 559171149381 559171150106 12388387646 12388400762 250000 249538230575125 249551646747035 571580199599 571580200334 12429210047 12429222353 (by norm_num) sum42 I0 L0 H0 (resEq_spec chunk42)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 240000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage43 : (∀ t : ℝ, 12 ≤ t → t < 260000 → Rt 1 1 23662 10000 t) ∧ Inv 260000 259410189582654 259423844352558 584033237781 584033238526 ∧ ((12468431099 : ℕ) : ℝ) / S ≤ Real.log ((260000 : ℕ) : ℝ) ∧ Real.log ((260000 : ℕ) : ℝ) ≤ ((12468442719 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage42
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs43 250000 249538230575125 249551646747035 571580199599 571580200334 12429210047 12429222353 260000 259410189582654 259423844352558 584033237781 584033238526 12468431099 12468442719 (by norm_num) sum43 I0 L0 H0 (resEq_spec chunk43)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 250000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage44 : (∀ t : ℝ, 12 ≤ t → t < 270000 → Rt 1 1 23662 10000 t) ∧ Inv 270000 269462663529153 269476555333012 584726384959 584726385709 ∧ ((12506171762 : ℕ) : ℝ) / S ≤ Real.log ((270000 : ℕ) : ℝ) ∧ Real.log ((270000 : ℕ) : ℝ) ≤ ((12506182707 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage43
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs44 260000 259410189582654 259423844352558 584033237781 584033238526 12468431099 12468442719 270000 269462663529153 269476555333012 584726384959 584726385709 12506171762 12506182707 (by norm_num) sum44 I0 L0 H0 (resEq_spec chunk44)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 260000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage45 : (∀ t : ℝ, 12 ≤ t → t < 280000 → Rt 1 1 23662 10000 t) ∧ Inv 280000 279356720666540 279370841087691 600377210673 600377211438 ∧ ((12542539696 : ℕ) : ℝ) / S ≤ Real.log ((280000 : ℕ) : ℝ) ∧ Real.log ((280000 : ℕ) : ℝ) ≤ ((12542550081 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage44
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs45 270000 269462663529153 269476555333012 584726384959 584726385709 12506171762 12506182707 280000 279356720666540 279370841087691 600377210673 600377211438 12542539696 12542550081 (by norm_num) sum45 I0 L0 H0 (resEq_spec chunk45)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 270000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage46 : (∀ t : ℝ, 12 ≤ t → t < 290000 → Rt 1 1 23662 10000 t) ∧ Inv 290000 289304071090888 289318416023718 600377210673 600377211438 ∧ ((12577631288 : ℕ) : ℝ) / S ≤ Real.log ((290000 : ℕ) : ℝ) ∧ Real.log ((290000 : ℕ) : ℝ) ≤ ((12577641119 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage45
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs46 280000 279356720666540 279370841087691 600377210673 600377211438 12542539696 12542550081 290000 289304071090888 289318416023718 600377210673 600377211438 12577631288 12577641119 (by norm_num) sum46 I0 L0 H0 (resEq_spec chunk46)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 280000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage47 : (∀ t : ℝ, 12 ≤ t → t < 300000 → Rt 1 1 23662 10000 t) ∧ Inv 300000 299039525744364 299054085923416 612975078749 612975079524 ∧ ((12611533081 : ℕ) : ℝ) / S ≤ Real.log ((300000 : ℕ) : ℝ) ∧ Real.log ((300000 : ℕ) : ℝ) ≤ ((12611542418 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage46
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs47 290000 289304071090888 289318416023718 600377210673 600377211438 12577631288 12577641119 300000 299039525744364 299054085923416 612975078749 612975079524 12611533081 12611542418 (by norm_num) sum47 I0 L0 H0 (resEq_spec chunk47)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 290000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage48 : (∀ t : ℝ, 12 ≤ t → t < 310000 → Rt 1 1 23662 10000 t) ∧ Inv 310000 309179556465782 309194336784032 617179771366 617179772146 ∧ ((12644323131 : ℕ) : ℝ) / S ≤ Real.log ((310000 : ℕ) : ℝ) ∧ Real.log ((310000 : ℕ) : ℝ) ≤ ((12644332022 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage47
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs48 300000 299039525744364 299054085923416 612975078749 612975079524 12611533081 12611542418 310000 309179556465782 309194336784032 617179771366 617179772146 12644323131 12644332022 (by norm_num) sum48 I0 L0 H0 (resEq_spec chunk48)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 300000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage49 : (∀ t : ℝ, 12 ≤ t → t < 320000 → Rt 1 1 23662 10000 t) ∧ Inv 320000 319409170375061 319424168261300 629835616229 629835617019 ∧ ((12676072040 : ℕ) : ℝ) / S ≤ Real.log ((320000 : ℕ) : ℝ) ∧ Real.log ((320000 : ℕ) : ℝ) ≤ ((12676080505 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage48
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs49 310000 309179556465782 309194336784032 617179771366 617179772146 12644323131 12644332022 320000 319409170375061 319424168261300 629835616229 629835617019 12676072040 12676080505 (by norm_num) sum49 I0 L0 H0 (resEq_spec chunk49)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 310000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage50 : (∀ t : ℝ, 12 ≤ t → t < 330000 → Rt 1 1 23662 10000 t) ∧ Inv 330000 329511520285348 329526728998582 642526885868 642526886668 ∧ ((12706843887 : ℕ) : ℝ) / S ≤ Real.log ((330000 : ℕ) : ℝ) ∧ Real.log ((330000 : ℕ) : ℝ) ≤ ((12706851975 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage49
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs50 320000 319409170375061 319424168261300 629835616229 629835617019 12676072040 12676080505 330000 329511520285348 329526728998582 642526885868 642526886668 12706843887 12706851975 (by norm_num) sum50 I0 L0 H0 (resEq_spec chunk50)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 320000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage51 : (∀ t : ℝ, 12 ≤ t → t < 340000 → Rt 1 1 23662 10000 t) ∧ Inv 340000 339408867100241 339424279260017 648884728132 648884728937 ∧ ((12736697030 : ℕ) : ℝ) / S ≤ Real.log ((340000 : ℕ) : ℝ) ∧ Real.log ((340000 : ℕ) : ℝ) ≤ ((12736704767 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage50
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs51 330000 329511520285348 329526728998582 642526885868 642526886668 12706843887 12706851975 340000 339408867100241 339424279260017 648884728132 648884728937 12736697030 12736704767 (by norm_num) sum51 I0 L0 H0 (resEq_spec chunk51)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 330000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage52 : (∀ t : ℝ, 12 ≤ t → t < 350000 → Rt 1 1 23662 10000 t) ∧ Inv 350000 349546023744774 349561640679421 655259752949 655259753759 ∧ ((12765684734 : ℕ) : ℝ) / S ≤ Real.log ((350000 : ℕ) : ℝ) ∧ Real.log ((350000 : ℕ) : ℝ) ≤ ((12765692136 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage51
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs52 340000 339408867100241 339424279260017 648884728132 648884728937 12736697030 12736704767 350000 349546023744774 349561640679421 655259752949 655259753759 12765684734 12765692136 (by norm_num) sum52 I0 L0 H0 (resEq_spec chunk52)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 340000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage53 : (∀ t : ℝ, 12 ≤ t → t < 360000 → Rt 1 1 23662 10000 t) ∧ Inv 360000 359514118732143 359529933357726 672302888816 672302889641 ∧ ((12793855768 : ℕ) : ℝ) / S ≤ Real.log ((360000 : ℕ) : ℝ) ∧ Real.log ((360000 : ℕ) : ℝ) ≤ ((12793862854 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage52
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs53 350000 349546023744774 349561640679421 655259752949 655259753759 12765684734 12765692136 360000 359514118732143 359529933357726 672302888816 672302889641 12793855768 12793862854 (by norm_num) sum53 I0 L0 H0 (resEq_spec chunk53)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 350000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage54 : (∀ t : ℝ, 12 ≤ t → t < 370000 → Rt 1 1 23662 10000 t) ∧ Inv 370000 369311798736193 369327804784771 685110012537 685110013372 ∧ ((12821254878 : ℕ) : ℝ) / S ≤ Real.log ((370000 : ℕ) : ℝ) ∧ Real.log ((370000 : ℕ) : ℝ) ≤ ((12821261694 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage53
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs54 360000 359514118732143 359529933357726 672302888816 672302889641 12793855768 12793862854 370000 369311798736193 369327804784771 685110012537 685110013372 12821254878 12821261694 (by norm_num) sum54 I0 L0 H0 (resEq_spec chunk54)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 360000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage55 : (∀ t : ℝ, 12 ≤ t → t < 380000 → Rt 1 1 23662 10000 t) ∧ Inv 380000 379297184572796 379313382097334 694093326825 694093327670 ∧ ((12847923265 : ℕ) : ℝ) / S ≤ Real.log ((380000 : ℕ) : ℝ) ∧ Real.log ((380000 : ℕ) : ℝ) ≤ ((12847929803 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage54
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs55 370000 369311798736193 369327804784771 685110012537 685110013372 12821254878 12821261694 380000 379297184572796 379313382097334 694093326825 694093327670 12847923265 12847929803 (by norm_num) sum55 I0 L0 H0 (resEq_spec chunk55)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 370000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage56 : (∀ t : ℝ, 12 ≤ t → t < 390000 → Rt 1 1 23662 10000 t) ∧ Inv 390000 389161533411786 389177917529124 711236760555 711236761415 ∧ ((12873898867 : ℕ) : ℝ) / S ≤ Real.log ((390000 : ℕ) : ℝ) ∧ Real.log ((390000 : ℕ) : ℝ) ≤ ((12873905164 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage55
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs56 380000 379297184572796 379313382097334 694093326825 694093327670 12847923265 12847929803 390000 389161533411786 389177917529124 711236760555 711236761415 12873898867 12873905164 (by norm_num) sum56 I0 L0 H0 (resEq_spec chunk56)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 380000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage57 : (∀ t : ℝ, 12 ≤ t → t < 400000 → Rt 1 1 23662 10000 t) ∧ Inv 400000 399380411061785 399396985318397 719293504325 719293505195 ∧ ((12899216802 : ℕ) : ℝ) / S ≤ Real.log ((400000 : ℕ) : ℝ) ∧ Real.log ((400000 : ℕ) : ℝ) ≤ ((12899222852 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage56
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs57 390000 389161533411786 389177917529124 711236760555 711236761415 12873898867 12873905164 400000 399380411061785 399396985318397 719293504325 719293505195 12899216802 12899222852 (by norm_num) sum57 I0 L0 H0 (resEq_spec chunk57)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 390000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage58 : (∀ t : ℝ, 12 ≤ t → t < 410000 → Rt 1 1 23662 10000 t) ∧ Inv 410000 409115901519291 409132654143161 719293504325 719293505195 ∧ ((12923909527 : ℕ) : ℝ) / S ≤ Real.log ((410000 : ℕ) : ℝ) ∧ Real.log ((410000 : ℕ) : ℝ) ≤ ((12923915357 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage57
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs58 400000 399380411061785 399396985318397 719293504325 719293505195 12899216802 12899222852 410000 409115901519291 409132654143161 719293504325 719293505195 12923909527 12923915357 (by norm_num) sum58 I0 L0 H0 (resEq_spec chunk58)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 400000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage59 : (∀ t : ℝ, 12 ≤ t → t < 420000 → Rt 1 1 23662 10000 t) ∧ Inv 420000 419154220549211 419171155187965 738695024793 738695025678 ∧ ((12948007173 : ℕ) : ℝ) / S ≤ Real.log ((420000 : ℕ) : ℝ) ∧ Real.log ((420000 : ℕ) : ℝ) ≤ ((12948012810 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage58
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs59 410000 409115901519291 409132654143161 719293504325 719293505195 12923909527 12923915357 420000 419154220549211 419171155187965 738695024793 738695025678 12948007173 12948012810 (by norm_num) sum59 I0 L0 H0 (resEq_spec chunk59)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 410000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage60 : (∀ t : ℝ, 12 ≤ t → t < 430000 → Rt 1 1 23662 10000 t) ∧ Inv 430000 429159190451658 429176303560733 745176601920 745176602810 ∧ ((12971537773 : ℕ) : ℝ) / S ≤ Real.log ((430000 : ℕ) : ℝ) ∧ Real.log ((430000 : ℕ) : ℝ) ≤ ((12971543206 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage59
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs60 420000 419154220549211 419171155187965 738695024793 738695025678 12948007173 12948012810 430000 429159190451658 429176303560733 745176601920 745176602810 12971537773 12971543206 (by norm_num) sum60 I0 L0 H0 (resEq_spec chunk60)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 420000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage61 : (∀ t : ℝ, 12 ≤ t → t < 440000 → Rt 1 1 23662 10000 t) ∧ Inv 440000 439272791526059 439290082383411 758161079289 758161080189 ∧ ((12994527387 : ℕ) : ℝ) / S ≤ Real.log ((440000 : ℕ) : ℝ) ∧ Real.log ((440000 : ℕ) : ℝ) ≤ ((12994532631 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage60
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs61 430000 429159190451658 429176303560733 745176601920 745176602810 12971537773 12971543206 440000 439272791526059 439290082383411 758161079289 758161080189 12994527387 12994532631 (by norm_num) sum61 I0 L0 H0 (resEq_spec chunk61)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 430000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage62 : (∀ t : ℝ, 12 ≤ t → t < 450000 → Rt 1 1 23662 10000 t) ∧ Inv 450000 449221981413056 449239444715789 758161079289 758161080189 ∧ ((13017000329 : ℕ) : ℝ) / S ≤ Real.log ((450000 : ℕ) : ℝ) ∧ Real.log ((450000 : ℕ) : ℝ) ≤ ((13017005399 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage61
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs62 440000 439272791526059 439290082383411 758161079289 758161080189 12994527387 12994532631 450000 449221981413056 449239444715789 758161079289 758161080189 13017000329 13017005399 (by norm_num) sum62 I0 L0 H0 (resEq_spec chunk62)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 440000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage63 : (∀ t : ℝ, 12 ≤ t → t < 460000 → Rt 1 1 23662 10000 t) ∧ Inv 460000 459018824812337 459036456329932 771190495886 771190496796 ∧ ((13038979315 : ℕ) : ℝ) / S ≤ Real.log ((460000 : ℕ) : ℝ) ∧ Real.log ((460000 : ℕ) : ℝ) ≤ ((13038984222 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage62
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs63 450000 449221981413056 449239444715789 758161079289 758161080189 13017000329 13017005399 460000 459018824812337 459036456329932 771190495886 771190496796 13038979315 13038984222 (by norm_num) sum63 I0 L0 H0 (resEq_spec chunk63)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 450000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage64 : (∀ t : ℝ, 12 ≤ t → t < 470000 → Rt 1 1 23662 10000 t) ∧ Inv 470000 469001903548132 469019704023146 777716990743 777716991658 ∧ ((13060485596 : ℕ) : ℝ) / S ≤ Real.log ((470000 : ℕ) : ℝ) ∧ Real.log ((470000 : ℕ) : ℝ) ≤ ((13060490348 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage63
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs64 460000 459018824812337 459036456329932 771190495886 771190496796 13038979315 13038984222 470000 469001903548132 469019704023146 777716990743 777716991658 13060485596 13060490348 (by norm_num) sum64 I0 L0 H0 (resEq_spec chunk64)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 460000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage65 : (∀ t : ℝ, 12 ≤ t → t < 480000 → Rt 1 1 23662 10000 t) ∧ Inv 480000 479223273891535 479241245493343 784255130564 784255131484 ∧ ((13081539085 : ℕ) : ℝ) / S ≤ Real.log ((480000 : ℕ) : ℝ) ∧ Real.log ((480000 : ℕ) : ℝ) ≤ ((13081543689 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage64
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs65 470000 469001903548132 469019704023146 777716990743 777716991658 13060485596 13060490348 480000 479223273891535 479241245493343 784255130564 784255131484 13081539085 13081543689 (by norm_num) sum65 I0 L0 H0 (resEq_spec chunk65)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 470000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage66 : (∀ t : ℝ, 12 ≤ t → t < 490000 → Rt 1 1 23662 10000 t) ∧ Inv 490000 489186143530030 489204279761515 784255130564 784255131484 ∧ ((13102158435 : ℕ) : ℝ) / S ≤ Real.log ((490000 : ℕ) : ℝ) ∧ Real.log ((490000 : ℕ) : ℝ) ≤ ((13102162901 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage65
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs66 480000 479223273891535 479241245493343 784255130564 784255131484 13081539085 13081543689 490000 489186143530030 489204279761515 784255130564 784255131484 13102158435 13102162901 (by norm_num) sum66 I0 L0 H0 (resEq_spec chunk66)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 480000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage67 : (∀ t : ℝ, 12 ≤ t → t < 500000 → Rt 1 1 23662 10000 t) ∧ Inv 500000 499308790687869 499327092460411 795177086299 795177087229 ∧ ((13122361213 : ℕ) : ℝ) / S ≤ Real.log ((500000 : ℕ) : ℝ) ∧ Real.log ((500000 : ℕ) : ℝ) ≤ ((13122365547 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage66
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs67 490000 489186143530030 489204279761515 784255130564 784255131484 13102158435 13102162901 500000 499308790687869 499327092460411 795177086299 795177087229 13122361213 13122365547 (by norm_num) sum67 I0 L0 H0 (resEq_spec chunk67)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 490000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage68 : (∀ t : ℝ, 12 ≤ t → t < 510000 → Rt 1 1 23662 10000 t) ∧ Inv 510000 509197343389829 509215804826712 801740941823 801740942758 ∧ ((13142163899 : ℕ) : ℝ) / S ≤ Real.log ((510000 : ℕ) : ℝ) ∧ Real.log ((510000 : ℕ) : ℝ) ≤ ((13142168106 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage67
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs68 500000 499308790687869 499327092460411 795177086299 795177087229 13122361213 13122365547 510000 509197343389829 509215804826712 801740941823 801740942758 13142163899 13142168106 (by norm_num) sum68 I0 L0 H0 (resEq_spec chunk68)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 500000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage69 : (∀ t : ℝ, 12 ≤ t → t < 520000 → Rt 1 1 23662 10000 t) ∧ Inv 520000 519324309550335 519342932371293 808318803178 808318804118 ∧ ((13161582045 : ℕ) : ℝ) / S ≤ Real.log ((520000 : ℕ) : ℝ) ∧ Real.log ((520000 : ℕ) : ℝ) ≤ ((13161586130 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage68
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs69 510000 509197343389829 509215804826712 801740941823 801740942758 13142163899 13142168106 520000 519324309550335 519342932371293 808318803178 808318804118 13161582045 13161586130 (by norm_num) sum69 I0 L0 H0 (resEq_spec chunk69)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 510000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage70 : (∀ t : ℝ, 12 ≤ t → t < 530000 → Rt 1 1 23662 10000 t) ∧ Inv 530000 529386959390423 529405740358551 815600876831 815600877781 ∧ ((13180630296 : ℕ) : ℝ) / S ≤ Real.log ((530000 : ℕ) : ℝ) ∧ Real.log ((530000 : ℕ) : ℝ) ≤ ((13180634266 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage69
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs70 520000 519324309550335 519342932371293 808318803178 808318804118 13161582045 13161586130 530000 529386959390423 529405740358551 815600876831 815600877781 13180630296 13180634266 (by norm_num) sum70 I0 L0 H0 (resEq_spec chunk70)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 520000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage71 : (∀ t : ℝ, 12 ≤ t → t < 540000 → Rt 1 1 23662 10000 t) ∧ Inv 540000 539239777363550 539258712095865 823296634816 823296635776 ∧ ((13199322488 : ℕ) : ℝ) / S ≤ Real.log ((540000 : ℕ) : ℝ) ∧ Real.log ((540000 : ℕ) : ℝ) ≤ ((13199326347 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage70
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs71 530000 529386959390423 529405740358551 815600876831 815600877781 13180630296 13180634266 540000 539239777363550 539258712095865 823296634816 823296635776 13199322488 13199326347 (by norm_num) sum71 I0 L0 H0 (resEq_spec chunk71)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 530000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage72 : (∀ t : ℝ, 12 ≤ t → t < 550000 → Rt 1 1 23662 10000 t) ∧ Inv 550000 549146103775554 549165191339169 829901932734 829901933699 ∧ ((13217671677 : ℕ) : ℝ) / S ≤ Real.log ((550000 : ℕ) : ℝ) ∧ Real.log ((550000 : ℕ) : ℝ) ≤ ((13217675434 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage71
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs72 540000 539239777363550 539258712095865 823296634816 823296635776 13199322488 13199326347 550000 549146103775554 549165191339169 829901932734 829901933699 13217671677 13217675434 (by norm_num) sum72 I0 L0 H0 (resEq_spec chunk72)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 540000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage73 : (∀ t : ℝ, 12 ≤ t → t < 560000 → Rt 1 1 23662 10000 t) ∧ Inv 560000 559066036895201 559085276022060 836512628776 836512629746 ∧ ((13235690231 : ℕ) : ℝ) / S ≤ Real.log ((560000 : ℕ) : ℝ) ∧ Real.log ((560000 : ℕ) : ℝ) ≤ ((13235693893 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage72
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs73 550000 549146103775554 549165191339169 829901932734 829901933699 13217671677 13217675434 560000 559066036895201 559085276022060 836512628776 836512629746 13235690231 13235693893 (by norm_num) sum73 I0 L0 H0 (resEq_spec chunk73)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 550000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage74 : (∀ t : ℝ, 12 ≤ t → t < 570000 → Rt 1 1 23662 10000 t) ∧ Inv 570000 568959631136627 568979020012881 843134034425 843134035400 ∧ ((13253389859 : ℕ) : ℝ) / S ≤ Real.log ((570000 : ℕ) : ℝ) ∧ Real.log ((570000 : ℕ) : ℝ) ≤ ((13253393426 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage73
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs74 560000 559066036895201 559085276022060 836512628776 836512629746 13235690231 13235693893 570000 568959631136627 568979020012881 843134034425 843134035400 13253389859 13253393426 (by norm_num) sum74 I0 L0 H0 (resEq_spec chunk74)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 560000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage75 : (∀ t : ℝ, 12 ≤ t → t < 580000 → Rt 1 1 23662 10000 t) ∧ Inv 580000 579158072447011 579177613709065 860816871636 860816872626 ∧ ((13270781644 : ℕ) : ℝ) / S ≤ Real.log ((580000 : ℕ) : ℝ) ∧ Real.log ((580000 : ℕ) : ℝ) ≤ ((13270785115 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage74
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs75 570000 568959631136627 568979020012881 843134034425 843134035400 13253389859 13253393426 580000 579158072447011 579177613709065 860816871636 860816872626 13270781644 13270785115 (by norm_num) sum75 I0 L0 H0 (resEq_spec chunk75)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 570000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage76 : (∀ t : ℝ, 12 ≤ t → t < 590000 → Rt 1 1 23662 10000 t) ∧ Inv 590000 589290154149163 589309845485450 860816871636 860816872626 ∧ ((13287876124 : ℕ) : ℝ) / S ≤ Real.log ((590000 : ℕ) : ℝ) ∧ Real.log ((590000 : ℕ) : ℝ) ≤ ((13287879506 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage75
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs76 580000 579158072447011 579177613709065 860816871636 860816872626 13270781644 13270785115 590000 589290154149163 589309845485450 860816871636 860816872626 13287876124 13287879506 (by norm_num) sum76 I0 L0 H0 (resEq_spec chunk76)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 580000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage77 : (∀ t : ℝ, 12 ≤ t → t < 600000 → Rt 1 1 23662 10000 t) ∧ Inv 600000 599222438384008 599242275287015 874112241649 874112242649 ∧ ((13304683285 : ℕ) : ℝ) / S ≤ Real.log ((600000 : ℕ) : ℝ) ∧ Real.log ((600000 : ℕ) : ℝ) ≤ ((13304686587 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage76
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs77 590000 589290154149163 589309845485450 860816871636 860816872626 13287876124 13287879506 600000 599222438384008 599242275287015 874112241649 874112242649 13304683285 13304686587 (by norm_num) sum77 I0 L0 H0 (resEq_spec chunk77)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 590000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage78 : (∀ t : ℝ, 12 ≤ t → t < 610000 → Rt 1 1 23662 10000 t) ∧ Inv 610000 609380200181435 609400184471389 874112241649 874112242649 ∧ ((13321212625 : ℕ) : ℝ) / S ≤ Real.log ((610000 : ℕ) : ℝ) ∧ Real.log ((610000 : ℕ) : ℝ) ≤ ((13321215850 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage77
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs78 600000 599222438384008 599242275287015 874112241649 874112242649 13304683285 13304686587 610000 609380200181435 609400184471389 874112241649 874112242649 13321212625 13321215850 (by norm_num) sum78 I0 L0 H0 (resEq_spec chunk78)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 600000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage79 : (∀ t : ℝ, 12 ≤ t → t < 620000 → Rt 1 1 23662 10000 t) ∧ Inv 620000 619390507699096 619410635594397 880780469895 880780470900 ∧ ((13337473190 : ℕ) : ℝ) / S ≤ Real.log ((620000 : ℕ) : ℝ) ∧ Real.log ((620000 : ℕ) : ℝ) ≤ ((13337476332 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage78
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs79 610000 609380200181435 609400184471389 874112241649 874112242649 13321212625 13321215850 620000 619390507699096 619410635594397 880780469895 880780470900 13337473190 13337476332 (by norm_num) sum79 I0 L0 H0 (resEq_spec chunk79)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 610000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage80 : (∀ t : ℝ, 12 ≤ t → t < 630000 → Rt 1 1 23662 10000 t) ∧ Inv 630000 629119267121640 629139533410617 880780469895 880780470900 ∧ ((13353473563 : ℕ) : ℝ) / S ≤ Real.log ((630000 : ℕ) : ℝ) ∧ Real.log ((630000 : ℕ) : ℝ) ≤ ((13353476630 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage79
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs80 620000 619390507699096 619410635594397 880780469895 880780470900 13337473190 13337476332 630000 629119267121640 629139533410617 880780469895 880780470900 13353473563 13353476630 (by norm_num) sum80 I0 L0 H0 (resEq_spec chunk80)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 620000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage81 : (∀ t : ℝ, 12 ≤ t → t < 640000 → Rt 1 1 23662 10000 t) ∧ Inv 640000 638912994305343 638933398888365 887461324571 887461325581 ∧ ((13369221952 : ℕ) : ℝ) / S ≤ Real.log ((640000 : ℕ) : ℝ) ∧ Real.log ((640000 : ℕ) : ℝ) ≤ ((13369224956 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage80
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs81 630000 629119267121640 629139533410617 880780469895 880780470900 13353473563 13353476630 640000 638912994305343 638933398888365 887461324571 887461325581 13369221952 13369224956 (by norm_num) sum81 I0 L0 H0 (resEq_spec chunk81)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 630000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage82 : (∀ t : ℝ, 12 ≤ t → t < 650000 → Rt 1 1 23662 10000 t) ∧ Inv 650000 649039417347740 649059963523998 887461324571 887461325581 ∧ ((13384726182 : ℕ) : ℝ) / S ≤ Real.log ((650000 : ℕ) : ℝ) ∧ Real.log ((650000 : ℕ) : ℝ) ≤ ((13384729112 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage81
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs82 640000 638912994305343 638933398888365 887461324571 887461325581 13369221952 13369224956 650000 649039417347740 649059963523998 887461324571 887461325581 13384726182 13384729112 (by norm_num) sum82 I0 L0 H0 (resEq_spec chunk82)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 640000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage83 : (∀ t : ℝ, 12 ≤ t → t < 660000 → Rt 1 1 23662 10000 t) ∧ Inv 660000 658856024673746 658876706861051 900855391538 900855392558 ∧ ((13399993680 : ℕ) : ℝ) / S ≤ Real.log ((660000 : ℕ) : ℝ) ∧ Real.log ((660000 : ℕ) : ℝ) ≤ ((13399996544 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage82
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs83 650000 649039417347740 649059963523998 887461324571 887461325581 13384726182 13384729112 660000 658856024673746 658876706861051 900855391538 900855392558 13399993680 13399996544 (by norm_num) sum83 I0 L0 H0 (resEq_spec chunk83)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 650000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage84 : (∀ t : ℝ, 12 ≤ t → t < 670000 → Rt 1 1 23662 10000 t) ∧ Inv 670000 668844481503879 668865301236634 900855391538 900855392558 ∧ ((13415031588 : ℕ) : ℝ) / S ≤ Real.log ((670000 : ℕ) : ℝ) ∧ Real.log ((670000 : ℕ) : ℝ) ≤ ((13415034395 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage83
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs84 660000 658856024673746 658876706861051 900855391538 900855392558 13399993680 13399996544 670000 668844481503879 668865301236634 900855391538 900855392558 13415031588 13415034395 (by norm_num) sum84 I0 L0 H0 (resEq_spec chunk84)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 660000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage85 : (∀ t : ℝ, 12 ≤ t → t < 680000 → Rt 1 1 23662 10000 t) ∧ Inv 680000 678964980784373 678985937996697 914278870843 914278871873 ∧ ((13429846708 : ℕ) : ℝ) / S ≤ Real.log ((680000 : ℕ) : ℝ) ∧ Real.log ((680000 : ℕ) : ℝ) ≤ ((13429849447 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage84
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs85 670000 668844481503879 668865301236634 900855391538 900855392558 13415031588 13415034395 680000 678964980784373 678985937996697 914278870843 914278871873 13429846708 13429849447 (by norm_num) sum85 I0 L0 H0 (resEq_spec chunk85)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 670000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage86 : (∀ t : ℝ, 12 ≤ t → t < 690000 → Rt 1 1 23662 10000 t) ∧ Inv 690000 689069709034632 689090802774719 927716895689 927716896729 ∧ ((13444445534 : ℕ) : ℝ) / S ≤ Real.log ((690000 : ℕ) : ℝ) ∧ Real.log ((690000 : ℕ) : ℝ) ≤ ((13444448219 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage85
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs86 680000 678964980784373 678985937996697 914278870843 914278871873 13429846708 13429849447 690000 689069709034632 689090802774719 927716895689 927716896729 13444445534 13444448219 (by norm_num) sum86 I0 L0 H0 (resEq_spec chunk86)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 680000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage87 : (∀ t : ℝ, 12 ≤ t → t < 700000 → Rt 1 1 23662 10000 t) ∧ Inv 700000 698862445372480 698883670411265 927716895689 927716896729 ∧ ((13458834305 : ℕ) : ℝ) / S ≤ Real.log ((700000 : ℕ) : ℝ) ∧ Real.log ((700000 : ℕ) : ℝ) ≤ ((13458836930 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage86
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs87 690000 689069709034632 689090802774719 927716895689 927716896729 13444445534 13444448219 700000 698862445372480 698883670411265 927716895689 927716896729 13458834305 13458836930 (by norm_num) sum87 I0 L0 H0 (resEq_spec chunk87)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 690000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage88 : (∀ t : ℝ, 12 ≤ t → t < 710000 → Rt 1 1 23662 10000 t) ∧ Inv 710000 709136919652764 709158281046126 942305038587 942305039642 ∧ ((13473018965 : ℕ) : ℝ) / S ≤ Real.log ((710000 : ℕ) : ℝ) ∧ Real.log ((710000 : ℕ) : ℝ) ≤ ((13473021535 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage87
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs88 700000 698862445372480 698883670411265 927716895689 927716896729 13458834305 13458836930 710000 709136919652764 709158281046126 942305038587 942305039642 13473018965 13473021535 (by norm_num) sum88 I0 L0 H0 (resEq_spec chunk88)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 700000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage89 : (∀ t : ℝ, 12 ≤ t → t < 720000 → Rt 1 1 23662 10000 t) ∧ Inv 720000 718882846055000 718904335776996 942305038587 942305039642 ∧ ((13487005229 : ℕ) : ℝ) / S ≤ Real.log ((720000 : ℕ) : ℝ) ∧ Real.log ((720000 : ℕ) : ℝ) ≤ ((13487007748 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage88
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs89 710000 709136919652764 709158281046126 942305038587 942305039642 13473018965 13473021535 720000 718882846055000 718904335776996 942305038587 942305039642 13487005229 13487007748 (by norm_num) sum89 I0 L0 H0 (resEq_spec chunk89)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 710000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage90 : (∀ t : ℝ, 12 ≤ t → t < 730000 → Rt 1 1 23662 10000 t) ∧ Inv 730000 729138117870555 729159741407208 949053798132 949053799192 ∧ ((13500798583 : ℕ) : ℝ) / S ≤ Real.log ((730000 : ℕ) : ℝ) ∧ Real.log ((730000 : ℕ) : ℝ) ≤ ((13500801048 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage89
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs90 720000 718882846055000 718904335776996 942305038587 942305039642 13487005229 13487007748 730000 729138117870555 729159741407208 949053798132 949053799192 13500798583 13500801048 (by norm_num) sum90 I0 L0 H0 (resEq_spec chunk90)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 720000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage91 : (∀ t : ℝ, 12 ≤ t → t < 740000 → Rt 1 1 23662 10000 t) ∧ Inv 740000 739160766411705 739182520109709 962563004967 962563006037 ∧ ((13514404254 : ℕ) : ℝ) / S ≤ Real.log ((740000 : ℕ) : ℝ) ∧ Real.log ((740000 : ℕ) : ℝ) ≤ ((13514406673 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage90
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs91 730000 729138117870555 729159741407208 949053798132 949053799192 13500798583 13500801048 740000 739160766411705 739182520109709 962563004967 962563006037 13514404254 13514406673 (by norm_num) sum91 I0 L0 H0 (resEq_spec chunk91)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 730000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage92 : (∀ t : ℝ, 12 ≤ t → t < 750000 → Rt 1 1 23662 10000 t) ∧ Inv 750000 748720198731459 748742075365838 969323419656 969323420731 ∧ ((13527827305 : ℕ) : ℝ) / S ≤ Real.log ((750000 : ℕ) : ℝ) ∧ Real.log ((750000 : ℕ) : ℝ) ≤ ((13527829673 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage91
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs92 740000 739160766411705 739182520109709 962563004967 962563006037 13514404254 13514406673 750000 748720198731459 748742075365838 969323419656 969323420731 13527827305 13527829673 (by norm_num) sum92 I0 L0 H0 (resEq_spec chunk92)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 740000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage93 : (∀ t : ℝ, 12 ≤ t → t < 760000 → Rt 1 1 23662 10000 t) ∧ Inv 760000 758735628006145 758757632802281 969323419656 969323420731 ∧ ((13541072548 : ℕ) : ℝ) / S ≤ Real.log ((760000 : ℕ) : ℝ) ∧ Real.log ((760000 : ℕ) : ℝ) ≤ ((13541074878 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage92
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs93 750000 748720198731459 748742075365838 969323419656 969323420731 13527827305 13527829673 760000 758735628006145 758757632802281 969323419656 969323420731 13541072548 13541074878 (by norm_num) sum93 I0 L0 H0 (resEq_spec chunk93)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 750000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage94 : (∀ t : ℝ, 12 ≤ t → t < 770000 → Rt 1 1 23662 10000 t) ∧ Inv 770000 768963989167771 768986123250138 976099926646 976099927726 ∧ ((13554144658 : ℕ) : ℝ) / S ≤ Real.log ((770000 : ℕ) : ℝ) ∧ Real.log ((770000 : ℕ) : ℝ) ≤ ((13554146936 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage93
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs94 760000 758735628006145 758757632802281 969323419656 969323420731 13541072548 13541074878 770000 768963989167771 768986123250138 976099926646 976099927726 13554144658 13554146936 (by norm_num) sum94 I0 L0 H0 (resEq_spec chunk94)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 760000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage95 : (∀ t : ℝ, 12 ≤ t → t < 780000 → Rt 1 1 23662 10000 t) ∧ Inv 780000 778930969020513 778953228695428 989664309467 989664310557 ∧ ((13567048079 : ℕ) : ℝ) / S ≤ Real.log ((780000 : ℕ) : ℝ) ∧ Real.log ((780000 : ℕ) : ℝ) ≤ ((13567050320 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage94
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs95 770000 768963989167771 768986123250138 976099926646 976099927726 13554144658 13554146936 780000 778930969020513 778953228695428 989664309467 989664310557 13567048079 13567050320 (by norm_num) sum95 I0 L0 H0 (resEq_spec chunk95)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 770000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage96 : (∀ t : ℝ, 12 ≤ t → t < 790000 → Rt 1 1 23662 10000 t) ∧ Inv 790000 788948078303475 788970462776110 996452154447 996452155542 ∧ ((13579787129 : ℕ) : ℝ) / S ≤ Real.log ((790000 : ℕ) : ℝ) ∧ Real.log ((790000 : ℕ) : ℝ) ≤ ((13579789322 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage95
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs96 780000 778930969020513 778953228695428 989664309467 989664310557 13567048079 13567050320 790000 788948078303475 788970462776110 996452154447 996452155542 13579787129 13579789322 (by norm_num) sum96 I0 L0 H0 (resEq_spec chunk96)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 780000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage97 : (∀ t : ℝ, 12 ≤ t → t < 800000 → Rt 1 1 23662 10000 t) ∧ Inv 800000 799069596978632 799092106602724 996452154447 996452155542 ∧ ((13592365929 : ℕ) : ℝ) / S ≤ Real.log ((800000 : ℕ) : ℝ) ∧ Real.log ((800000 : ℕ) : ℝ) ≤ ((13592368086 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage96
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs97 790000 788948078303475 788970462776110 996452154447 996452155542 13579787129 13579789322 800000 799069596978632 799092106602724 996452154447 996452155542 13592365929 13592368086 (by norm_num) sum97 I0 L0 H0 (resEq_spec chunk97)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 790000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage98 : (∀ t : ℝ, 12 ≤ t → t < 810000 → Rt 1 1 23662 10000 t) ∧ Inv 810000 809023667727647 809046299675304 996452154447 996452155542 ∧ ((13604788467 : ℕ) : ℝ) / S ≤ Real.log ((810000 : ℕ) : ℝ) ∧ Real.log ((810000 : ℕ) : ℝ) ≤ ((13604790579 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage97
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs98 800000 799069596978632 799092106602724 996452154447 996452155542 13592365929 13592368086 810000 809023667727647 809046299675304 996452154447 996452155542 13604788467 13604790579 (by norm_num) sum98 I0 L0 H0 (resEq_spec chunk98)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 800000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage99 : (∀ t : ℝ, 12 ≤ t → t < 820000 → Rt 1 1 23662 10000 t) ∧ Inv 820000 819000419028304 819023173009242 996452154447 996452155542 ∧ ((13617058579 : ℕ) : ℝ) / S ≤ Real.log ((820000 : ℕ) : ℝ) ∧ Real.log ((820000 : ℕ) : ℝ) ≤ ((13617060660 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage98
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs99 810000 809023667727647 809046299675304 996452154447 996452155542 13604788467 13604790579 820000 819000419028304 819023173009242 996452154447 996452155542 13617058579 13617060660 (by norm_num) sum99 I0 L0 H0 (resEq_spec chunk99)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 810000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage100 : (∀ t : ℝ, 12 ≤ t → t < 830000 → Rt 1 1 23662 10000 t) ∧ Inv 830000 829149509194242 829172386273000 1012022749937 1012022751047 ∧ ((13629179954 : ℕ) : ℝ) / S ≤ Real.log ((830000 : ℕ) : ℝ) ∧ Real.log ((830000 : ℕ) : ℝ) ≤ ((13629181994 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage99
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs100 820000 819000419028304 819023173009242 996452154447 996452155542 13617058579 13617060660 830000 829149509194242 829172386273000 1012022749937 1012022751047 13629179954 13629181994 (by norm_num) sum100 I0 L0 H0 (resEq_spec chunk100)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 820000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage101 : (∀ t : ℝ, 12 ≤ t → t < 840000 → Rt 1 1 23662 10000 t) ∧ Inv 840000 839089437882242 839112434667585 1012022749937 1012022751047 ∧ ((13641156169 : ℕ) : ℝ) / S ≤ Real.log ((840000 : ℕ) : ℝ) ∧ Real.log ((840000 : ℕ) : ℝ) ≤ ((13641158174 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage100
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs101 830000 829149509194242 829172386273000 1012022749937 1012022751047 13629179954 13629181994 840000 839089437882242 839112434667585 1012022749937 1012022751047 13641156169 13641158174 (by norm_num) sum101 I0 L0 H0 (resEq_spec chunk101)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 830000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage102 : (∀ t : ℝ, 12 ≤ t → t < 850000 → Rt 1 1 23662 10000 t) ∧ Inv 850000 849010802090629 849033917513776 1018846036057 1018846037172 ∧ ((13652990644 : ℕ) : ℝ) / S ≤ Real.log ((850000 : ℕ) : ℝ) ∧ Real.log ((850000 : ℕ) : ℝ) ≤ ((13652992613 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage101
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs102 840000 839089437882242 839112434667585 1012022749937 1012022751047 13641156169 13641158174 850000 849010802090629 849033917513776 1018846036057 1018846037172 13652990644 13652992613 (by norm_num) sum102 I0 L0 H0 (resEq_spec chunk102)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 840000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage103 : (∀ t : ℝ, 12 ≤ t → t < 860000 → Rt 1 1 23662 10000 t) ∧ Inv 860000 858913409515164 858936642475523 1018846036057 1018846037172 ∧ ((13664686703 : ℕ) : ℝ) / S ≤ Real.log ((860000 : ℕ) : ℝ) ∧ Real.log ((860000 : ℕ) : ℝ) ≤ ((13664688636 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage102
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs103 850000 849010802090629 849033917513776 1018846036057 1018846037172 13652990644 13652992613 860000 858913409515164 858936642475523 1018846036057 1018846037172 13664686703 13664688636 (by norm_num) sum103 I0 L0 H0 (resEq_spec chunk103)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 850000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage104 : (∀ t : ℝ, 12 ≤ t → t < 870000 → Rt 1 1 23662 10000 t) ∧ Inv 870000 869207217894383 869230572491491 1025680144793 1025680145913 ∧ ((13676247544 : ℕ) : ℝ) / S ≤ Real.log ((870000 : ℕ) : ℝ) ∧ Real.log ((870000 : ℕ) : ℝ) ≤ ((13676249450 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage103
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs104 860000 858913409515164 858936642475523 1018846036057 1018846037172 13664686703 13664688636 870000 869207217894383 869230572491491 1025680144793 1025680145913 13676247544 13676249450 (by norm_num) sum104 I0 L0 H0 (resEq_spec chunk104)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 860000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage105 : (∀ t : ℝ, 12 ≤ t → t < 880000 → Rt 1 1 23662 10000 t) ∧ Inv 880000 879167682589989 879191153850857 1032522828073 1032522829198 ∧ ((13687676251 : ℕ) : ℝ) / S ≤ Real.log ((880000 : ℕ) : ℝ) ∧ Real.log ((880000 : ℕ) : ℝ) ≤ ((13687678122 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage104
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs105 870000 869207217894383 869230572491491 1025680144793 1025680145913 13676247544 13676249450 880000 879167682589989 879191153850857 1032522828073 1032522829198 13687676251 13687678122 (by norm_num) sum105 I0 L0 H0 (resEq_spec chunk105)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 870000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage106 : (∀ t : ℝ, 12 ≤ t → t < 890000 → Rt 1 1 23662 10000 t) ∧ Inv 890000 889191121671767 889214709792069 1039369771210 1039369772340 ∧ ((13698975818 : ℕ) : ℝ) / S ≤ Real.log ((890000 : ℕ) : ℝ) ∧ Real.log ((890000 : ℕ) : ℝ) ≤ ((13698977663 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage105
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs106 880000 879167682589989 879191153850857 1032522828073 1032522829198 13687676251 13687678122 890000 889191121671767 889214709792069 1039369771210 1039369772340 13698975818 13698977663 (by norm_num) sum106 I0 L0 H0 (resEq_spec chunk106)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 880000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage107 : (∀ t : ℝ, 12 ≤ t → t < 900000 → Rt 1 1 23662 10000 t) ∧ Inv 900000 899044600223899 899068302355544 1046223070301 1046223071436 ∧ ((13710149137 : ℕ) : ℝ) / S ≤ Real.log ((900000 : ℕ) : ℝ) ∧ Real.log ((900000 : ℕ) : ℝ) ≤ ((13710150946 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage106
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs107 890000 889191121671767 889214709792069 1039369771210 1039369772340 13698975818 13698977663 900000 899044600223899 899068302355544 1046223070301 1046223071436 13710149137 13710150946 (by norm_num) sum107 I0 L0 H0 (resEq_spec chunk107)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 890000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage108 : (∀ t : ℝ, 12 ≤ t → t < 910000 → Rt 1 1 23662 10000 t) ∧ Inv 910000 909358850426667 909382671024430 1053082685202 1053082686342 ∧ ((13721198990 : ℕ) : ℝ) / S ≤ Real.log ((910000 : ℕ) : ℝ) ∧ Real.log ((910000 : ℕ) : ℝ) ≤ ((13721200770 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage107
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs108 900000 899044600223899 899068302355544 1046223070301 1046223071436 13710149137 13710150946 910000 909358850426667 909382671024430 1053082685202 1053082686342 13721198990 13721200770 (by norm_num) sum108 I0 L0 H0 (resEq_spec chunk108)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 900000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage109 : (∀ t : ℝ, 12 ≤ t → t < 920000 → Rt 1 1 23662 10000 t) ∧ Inv 920000 919077348474374 919101280221294 1057657396178 1057657397323 ∧ ((13732128071 : ℕ) : ℝ) / S ≤ Real.log ((920000 : ℕ) : ℝ) ∧ Real.log ((920000 : ℕ) : ℝ) ≤ ((13732129827 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage108
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs109 910000 909358850426667 909382671024430 1053082685202 1053082686342 13721198990 13721200770 920000 919077348474374 919101280221294 1057657396178 1057657397323 13732128071 13732129827 (by norm_num) sum109 I0 L0 H0 (resEq_spec chunk109)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 910000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage110 : (∀ t : ℝ, 12 ≤ t → t < 930000 → Rt 1 1 23662 10000 t) ∧ Inv 930000 929243060263688 929267107353046 1061091383380 1061091384530 ∧ ((13742939002 : ℕ) : ℝ) / S ≤ Real.log ((930000 : ℕ) : ℝ) ∧ Real.log ((930000 : ℕ) : ℝ) ≤ ((13742940727 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage109
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs110 920000 919077348474374 919101280221294 1057657396178 1057657397323 13732128071 13732129827 930000 929243060263688 929267107353046 1061091383380 1061091384530 13742939002 13742940727 (by norm_num) sum110 I0 L0 H0 (resEq_spec chunk110)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 920000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage111 : (∀ t : ℝ, 12 ≤ t → t < 940000 → Rt 1 1 23662 10000 t) ∧ Inv 940000 939045537483162 939069695163117 1067965581873 1067965583028 ∧ ((13753634301 : ℕ) : ℝ) / S ≤ Real.log ((940000 : ℕ) : ℝ) ∧ Real.log ((940000 : ℕ) : ℝ) ≤ ((13753636001 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage110
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs111 930000 929243060263688 929267107353046 1061091383380 1061091384530 13742939002 13742940727 940000 939045537483162 939069695163117 1067965581873 1067965583028 13753634301 13753636001 (by norm_num) sum111 I0 L0 H0 (resEq_spec chunk111)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 930000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage112 : (∀ t : ℝ, 12 ≤ t → t < 950000 → Rt 1 1 23662 10000 t) ∧ Inv 950000 948951855822348 948976124441292 1074843908339 1074843909499 ∧ ((13764216426 : ℕ) : ℝ) / S ≤ Real.log ((950000 : ℕ) : ℝ) ∧ Real.log ((950000 : ℕ) : ℝ) ≤ ((13764218098 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage111
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs112 940000 939045537483162 939069695163117 1067965581873 1067965583028 13753634301 13753636001 950000 948951855822348 948976124441292 1074843908339 1074843909499 13764216426 13764218098 (by norm_num) sum112 I0 L0 H0 (resEq_spec chunk112)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 940000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage113 : (∀ t : ℝ, 12 ≤ t → t < 960000 → Rt 1 1 23662 10000 t) ∧ Inv 960000 958741851658025 958766229255803 1081728394989 1081728396154 ∧ ((13774687740 : ℕ) : ℝ) / S ≤ Real.log ((960000 : ℕ) : ℝ) ∧ Real.log ((960000 : ℕ) : ℝ) ≤ ((13774689384 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage112
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs113 950000 948951855822348 948976124441292 1074843908339 1074843909499 13764216426 13764218098 960000 958741851658025 958766229255803 1081728394989 1081728396154 13774687740 13774689384 (by norm_num) sum113 I0 L0 H0 (resEq_spec chunk113)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 950000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage114 : (∀ t : ℝ, 12 ≤ t → t < 970000 → Rt 1 1 23662 10000 t) ∧ Inv 970000 968828629243099 968853118918236 1088619004107 1088619005277 ∧ ((13785050536 : ℕ) : ℝ) / S ≤ Real.log ((970000 : ℕ) : ℝ) ∧ Real.log ((970000 : ℕ) : ℝ) ≤ ((13785052164 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage113
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs114 960000 958741851658025 958766229255803 1081728394989 1081728396154 13774687740 13774689384 970000 968828629243099 968853118918236 1088619004107 1088619005277 13785050536 13785052164 (by norm_num) sum114 I0 L0 H0 (resEq_spec chunk114)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 960000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage115 : (∀ t : ℝ, 12 ≤ t → t < 980000 → Rt 1 1 23662 10000 t) ∧ Inv 980000 978716043523562 978740642097793 1088619004107 1088619005277 ∧ ((13795307051 : ℕ) : ℝ) / S ≤ Real.log ((980000 : ℕ) : ℝ) ∧ Real.log ((980000 : ℕ) : ℝ) ≤ ((13795308648 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage114
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs115 970000 968828629243099 968853118918236 1088619004107 1088619005277 13785050536 13785052164 980000 978716043523562 978740642097793 1088619004107 1088619005277 13795307051 13795308648 (by norm_num) sum115 I0 L0 H0 (resEq_spec chunk115)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 970000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage116 : (∀ t : ℝ, 12 ≤ t → t < 990000 → Rt 1 1 23662 10000 t) ∧ Inv 990000 988514272897214 988538978330558 1095517718639 1095517719814 ∧ ((13805459436 : ℕ) : ℝ) / S ≤ Real.log ((990000 : ℕ) : ℝ) ∧ Real.log ((990000 : ℕ) : ℝ) ≤ ((13805461008 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage115
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs116 980000 978716043523562 978740642097793 1088619004107 1088619005277 13795307051 13795308648 990000 988514272897214 988538978330558 1095517718639 1095517719814 13805459436 13805461008 (by norm_num) sum116 I0 L0 H0 (resEq_spec chunk116)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 980000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

theorem stage117 : (∀ t : ℝ, 12 ≤ t → t < 1000000 → Rt 1 1 23662 10000 t) ∧ Inv 1000000 998471582592719 998496396556575 1102422469406 1102422470586 ∧ ((13815509781 : ℕ) : ℝ) / S ≤ Real.log ((1000000 : ℕ) : ℝ) ∧ Real.log ((1000000 : ℕ) : ℝ) ≤ ((13815511333 : ℕ) : ℝ) / S := by
  obtain ⟨Rp, I0, L0, H0⟩ := stage116
  obtain ⟨R, I, L, H⟩ := outer_spec (cN := 1) (cD := 1) (tN := 23662) (tD := 10000) (by norm_num) (by norm_num)
    gs117 990000 988514272897214 988538978330558 1095517718639 1095517719814 13805459436 13805461008 1000000 998471582592719 998496396556575 1102422469406 1102422470586 13815509781 13815511333 (by norm_num) sum117 I0 L0 H0 (resEq_spec chunk117)
  refine ⟨fun t h1 h2 => ?_, I, L, H⟩
  rcases lt_or_ge t 990000 with h | h
  · exact Rp t h1 h
  · exact R t (by exact_mod_cast h) (by exact_mod_cast h2)

/-- **`θ` and `ψ` on `[12, 10⁶)`**: `|ψ(t) − t| ≤ √t` and `t − 2.3662√t ≤ θ(t) ≤ t`. -/
theorem small_table {t : ℝ} (h1 : 12 ≤ t) (h2 : t < 1000000) : Rt 1 1 23662 10000 t :=
  stage117.1 t h1 h2

end TernaryGoldbach.Prelim.SmallTab
