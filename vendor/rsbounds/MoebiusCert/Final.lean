/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.MoebiusInputs
import MoebiusCert.Agg.Small
import MoebiusCert.Agg.Ms
import MoebiusCert.Agg.AL00
import MoebiusCert.Agg.AL01
import MoebiusCert.Agg.AL02
import MoebiusCert.Agg.AL03
import MoebiusCert.Agg.AL04
import MoebiusCert.Agg.AL05
import MoebiusCert.Agg.AL06
import MoebiusCert.Agg.AL07
import MoebiusCert.Agg.AL08
import MoebiusCert.Agg.AL09
import MoebiusCert.Agg.AL10
import MoebiusCert.Agg.AL11
import MoebiusCert.Agg.AL12
import MoebiusCert.Agg.AL13
import MoebiusCert.Agg.AL14
import MoebiusCert.Agg.AL15
import MoebiusCert.Agg.AL16
import MoebiusCert.Agg.AL17
import MoebiusCert.Agg.AL18
import MoebiusCert.Agg.AL19
import MoebiusCert.Agg.AL20
import MoebiusCert.Agg.AL21
import MoebiusCert.Agg.AL22
import MoebiusCert.Agg.AL23
import MoebiusCert.Agg.AL24
import MoebiusCert.Agg.AL25
import MoebiusCert.Agg.AL26
import MoebiusCert.Agg.AL27
import MoebiusCert.Agg.AL28
import MoebiusCert.Agg.AL29
import MoebiusCert.Agg.AL30
import MoebiusCert.Agg.AL31
import MoebiusCert.Agg.AL32
import MoebiusCert.Agg.AL33
import MoebiusCert.Agg.AL34
import MoebiusCert.Agg.AL35
import MoebiusCert.Agg.AL36
import MoebiusCert.Agg.AL37
import MoebiusCert.Agg.AL38
import MoebiusCert.Agg.AL39

/-!
# The two Möbius computations

`mertensSqrt` and `smallMoebiusSum`, the hypotheses (M) and (m) of `mobius003.tex`, from the
kernel-checked segment computations.
-/

namespace MoebiusCert

/-- The whole range `[1, 1000013823]` for `(M)`. -/
theorem mertens_all : SegGood 1 1000013823 0 (-146) := by
  have h0 := MoebiusCert.Agg.small
  have h1 := SegGood.trans_eq (T := 25427967) h0 (MoebiusCert.Agg.large_00) (by norm_num) (by norm_num)
  have h2 := SegGood.trans_eq (T := 50593791) h1 (MoebiusCert.Agg.large_01) (by norm_num) (by norm_num)
  have h3 := SegGood.trans_eq (T := 75759615) h2 (MoebiusCert.Agg.large_02) (by norm_num) (by norm_num)
  have h4 := SegGood.trans_eq (T := 100925439) h3 (MoebiusCert.Agg.large_03) (by norm_num) (by norm_num)
  have h5 := SegGood.trans_eq (T := 126091263) h4 (MoebiusCert.Agg.large_04) (by norm_num) (by norm_num)
  have h6 := SegGood.trans_eq (T := 151257087) h5 (MoebiusCert.Agg.large_05) (by norm_num) (by norm_num)
  have h7 := SegGood.trans_eq (T := 176422911) h6 (MoebiusCert.Agg.large_06) (by norm_num) (by norm_num)
  have h8 := SegGood.trans_eq (T := 201588735) h7 (MoebiusCert.Agg.large_07) (by norm_num) (by norm_num)
  have h9 := SegGood.trans_eq (T := 226754559) h8 (MoebiusCert.Agg.large_08) (by norm_num) (by norm_num)
  have h10 := SegGood.trans_eq (T := 251920383) h9 (MoebiusCert.Agg.large_09) (by norm_num) (by norm_num)
  have h11 := SegGood.trans_eq (T := 277086207) h10 (MoebiusCert.Agg.large_10) (by norm_num) (by norm_num)
  have h12 := SegGood.trans_eq (T := 302252031) h11 (MoebiusCert.Agg.large_11) (by norm_num) (by norm_num)
  have h13 := SegGood.trans_eq (T := 327417855) h12 (MoebiusCert.Agg.large_12) (by norm_num) (by norm_num)
  have h14 := SegGood.trans_eq (T := 352583679) h13 (MoebiusCert.Agg.large_13) (by norm_num) (by norm_num)
  have h15 := SegGood.trans_eq (T := 377749503) h14 (MoebiusCert.Agg.large_14) (by norm_num) (by norm_num)
  have h16 := SegGood.trans_eq (T := 402915327) h15 (MoebiusCert.Agg.large_15) (by norm_num) (by norm_num)
  have h17 := SegGood.trans_eq (T := 428081151) h16 (MoebiusCert.Agg.large_16) (by norm_num) (by norm_num)
  have h18 := SegGood.trans_eq (T := 453246975) h17 (MoebiusCert.Agg.large_17) (by norm_num) (by norm_num)
  have h19 := SegGood.trans_eq (T := 478412799) h18 (MoebiusCert.Agg.large_18) (by norm_num) (by norm_num)
  have h20 := SegGood.trans_eq (T := 503578623) h19 (MoebiusCert.Agg.large_19) (by norm_num) (by norm_num)
  have h21 := SegGood.trans_eq (T := 528744447) h20 (MoebiusCert.Agg.large_20) (by norm_num) (by norm_num)
  have h22 := SegGood.trans_eq (T := 553910271) h21 (MoebiusCert.Agg.large_21) (by norm_num) (by norm_num)
  have h23 := SegGood.trans_eq (T := 579076095) h22 (MoebiusCert.Agg.large_22) (by norm_num) (by norm_num)
  have h24 := SegGood.trans_eq (T := 604241919) h23 (MoebiusCert.Agg.large_23) (by norm_num) (by norm_num)
  have h25 := SegGood.trans_eq (T := 629407743) h24 (MoebiusCert.Agg.large_24) (by norm_num) (by norm_num)
  have h26 := SegGood.trans_eq (T := 654573567) h25 (MoebiusCert.Agg.large_25) (by norm_num) (by norm_num)
  have h27 := SegGood.trans_eq (T := 679739391) h26 (MoebiusCert.Agg.large_26) (by norm_num) (by norm_num)
  have h28 := SegGood.trans_eq (T := 704905215) h27 (MoebiusCert.Agg.large_27) (by norm_num) (by norm_num)
  have h29 := SegGood.trans_eq (T := 730071039) h28 (MoebiusCert.Agg.large_28) (by norm_num) (by norm_num)
  have h30 := SegGood.trans_eq (T := 755236863) h29 (MoebiusCert.Agg.large_29) (by norm_num) (by norm_num)
  have h31 := SegGood.trans_eq (T := 780402687) h30 (MoebiusCert.Agg.large_30) (by norm_num) (by norm_num)
  have h32 := SegGood.trans_eq (T := 805568511) h31 (MoebiusCert.Agg.large_31) (by norm_num) (by norm_num)
  have h33 := SegGood.trans_eq (T := 830734335) h32 (MoebiusCert.Agg.large_32) (by norm_num) (by norm_num)
  have h34 := SegGood.trans_eq (T := 855900159) h33 (MoebiusCert.Agg.large_33) (by norm_num) (by norm_num)
  have h35 := SegGood.trans_eq (T := 881065983) h34 (MoebiusCert.Agg.large_34) (by norm_num) (by norm_num)
  have h36 := SegGood.trans_eq (T := 906231807) h35 (MoebiusCert.Agg.large_35) (by norm_num) (by norm_num)
  have h37 := SegGood.trans_eq (T := 931397631) h36 (MoebiusCert.Agg.large_36) (by norm_num) (by norm_num)
  have h38 := SegGood.trans_eq (T := 956563455) h37 (MoebiusCert.Agg.large_37) (by norm_num) (by norm_num)
  have h39 := SegGood.trans_eq (T := 981729279) h38 (MoebiusCert.Agg.large_38) (by norm_num) (by norm_num)
  have h40 := SegGood.trans_eq (T := 1000013823) h39 (MoebiusCert.Agg.large_39) (by norm_num) (by norm_num)
  exact h40

end MoebiusCert

namespace TernaryGoldbach.RSBounds.MoebiusInputs

open MoebiusCert

theorem mertensSqrt : MertensSqrt := by
  intro n hn1 hn2
  obtain ⟨hb, -⟩ := mertens_all (by simp [mert_zero])
  exact hb n (by omega) (by omega) hn1

theorem smallMoebiusSum : SmallMoebiusSum := by
  intro n hn1 hn2
  obtain ⟨hb, -⟩ := MoebiusCert.Agg.msAll (by simp [MsInv, msum])
  exact hb n (by omega) (by omega) hn1

end TernaryGoldbach.RSBounds.MoebiusInputs
