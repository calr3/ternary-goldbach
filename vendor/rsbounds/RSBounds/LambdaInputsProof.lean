/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/

import RSBounds.LambdaCert.Sound
import RSBounds.LambdaCert.Segs.Seg00
import RSBounds.LambdaCert.Segs.Seg01
import RSBounds.LambdaCert.Segs.Seg02
import RSBounds.LambdaCert.Segs.Seg03
import RSBounds.LambdaCert.Segs.Seg04
import RSBounds.LambdaCert.Segs.Seg05
import RSBounds.LambdaCert.Segs.Seg06
import RSBounds.LambdaCert.Segs.Seg07
import RSBounds.LambdaCert.Segs.Seg08
import RSBounds.LambdaCert.Segs.Seg09
import RSBounds.LambdaCert.Segs.Seg10
import RSBounds.LambdaCert.Segs.Seg11
import RSBounds.LambdaCert.Segs.Seg12
import RSBounds.LambdaCert.Segs.Seg13
import RSBounds.LambdaCert.Segs.Seg14
import RSBounds.LambdaCert.Segs.Seg15

/-!
# The von Mangoldt computations (L): proofs

`weightSumBound` and `ghBounds`, the two statements of `RSBounds.LambdaInputs`.

The invariant `Cert.Inv` holds for `Cert.init` and is carried along the chain of states
`st0, st1, …` by the kernel checks `seg1, seg2, …` (via `Cert.inv_checkSeg`).  The last state has
`n = 2^20`; the states at the checkpoints of `ghTable` give the enclosures of `G` and `H`.
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs

namespace Cert

theorem inv0 : Inv st0 := inv_init


theorem inv1 : Inv st1 := inv_checkSeg seg1 inv0
theorem inv2 : Inv st2 := inv_checkSeg seg2 inv1
theorem inv3 : Inv st3 := inv_checkSeg seg3 inv2
theorem inv4 : Inv st4 := inv_checkSeg seg4 inv3
theorem inv5 : Inv st5 := inv_checkSeg seg5 inv4
theorem inv6 : Inv st6 := inv_checkSeg seg6 inv5
theorem inv7 : Inv st7 := inv_checkSeg seg7 inv6
theorem inv8 : Inv st8 := inv_checkSeg seg8 inv7
theorem inv9 : Inv st9 := inv_checkSeg seg9 inv8
theorem inv10 : Inv st10 := inv_checkSeg seg10 inv9
theorem inv11 : Inv st11 := inv_checkSeg seg11 inv10
theorem inv12 : Inv st12 := inv_checkSeg seg12 inv11
theorem inv13 : Inv st13 := inv_checkSeg seg13 inv12
theorem inv14 : Inv st14 := inv_checkSeg seg14 inv13
theorem inv15 : Inv st15 := inv_checkSeg seg15 inv14
theorem inv16 : Inv st16 := inv_checkSeg seg16 inv15
theorem inv17 : Inv st17 := inv_checkSeg seg17 inv16
theorem inv18 : Inv st18 := inv_checkSeg seg18 inv17
theorem inv19 : Inv st19 := inv_checkSeg seg19 inv18
theorem inv20 : Inv st20 := inv_checkSeg seg20 inv19
theorem inv21 : Inv st21 := inv_checkSeg seg21 inv20
theorem inv22 : Inv st22 := inv_checkSeg seg22 inv21
theorem inv23 : Inv st23 := inv_checkSeg seg23 inv22
theorem inv24 : Inv st24 := inv_checkSeg seg24 inv23
theorem inv25 : Inv st25 := inv_checkSeg seg25 inv24
theorem inv26 : Inv st26 := inv_checkSeg seg26 inv25
theorem inv27 : Inv st27 := inv_checkSeg seg27 inv26
theorem inv28 : Inv st28 := inv_checkSeg seg28 inv27
theorem inv29 : Inv st29 := inv_checkSeg seg29 inv28
theorem inv30 : Inv st30 := inv_checkSeg seg30 inv29
theorem inv31 : Inv st31 := inv_checkSeg seg31 inv30
theorem inv32 : Inv st32 := inv_checkSeg seg32 inv31
theorem inv33 : Inv st33 := inv_checkSeg seg33 inv32
theorem inv34 : Inv st34 := inv_checkSeg seg34 inv33
theorem inv35 : Inv st35 := inv_checkSeg seg35 inv34
theorem inv36 : Inv st36 := inv_checkSeg seg36 inv35
theorem inv37 : Inv st37 := inv_checkSeg seg37 inv36
theorem inv38 : Inv st38 := inv_checkSeg seg38 inv37
theorem inv39 : Inv st39 := inv_checkSeg seg39 inv38
theorem inv40 : Inv st40 := inv_checkSeg seg40 inv39
theorem inv41 : Inv st41 := inv_checkSeg seg41 inv40
theorem inv42 : Inv st42 := inv_checkSeg seg42 inv41
theorem inv43 : Inv st43 := inv_checkSeg seg43 inv42
theorem inv44 : Inv st44 := inv_checkSeg seg44 inv43
theorem inv45 : Inv st45 := inv_checkSeg seg45 inv44
theorem inv46 : Inv st46 := inv_checkSeg seg46 inv45
theorem inv47 : Inv st47 := inv_checkSeg seg47 inv46
theorem inv48 : Inv st48 := inv_checkSeg seg48 inv47
theorem inv49 : Inv st49 := inv_checkSeg seg49 inv48
theorem inv50 : Inv st50 := inv_checkSeg seg50 inv49
theorem inv51 : Inv st51 := inv_checkSeg seg51 inv50
theorem inv52 : Inv st52 := inv_checkSeg seg52 inv51
theorem inv53 : Inv st53 := inv_checkSeg seg53 inv52
theorem inv54 : Inv st54 := inv_checkSeg seg54 inv53
theorem inv55 : Inv st55 := inv_checkSeg seg55 inv54
theorem inv56 : Inv st56 := inv_checkSeg seg56 inv55
theorem inv57 : Inv st57 := inv_checkSeg seg57 inv56
theorem inv58 : Inv st58 := inv_checkSeg seg58 inv57
theorem inv59 : Inv st59 := inv_checkSeg seg59 inv58
theorem inv60 : Inv st60 := inv_checkSeg seg60 inv59
theorem inv61 : Inv st61 := inv_checkSeg seg61 inv60
theorem inv62 : Inv st62 := inv_checkSeg seg62 inv61
theorem inv63 : Inv st63 := inv_checkSeg seg63 inv62
theorem inv64 : Inv st64 := inv_checkSeg seg64 inv63
theorem inv65 : Inv st65 := inv_checkSeg seg65 inv64
theorem inv66 : Inv st66 := inv_checkSeg seg66 inv65
theorem inv67 : Inv st67 := inv_checkSeg seg67 inv66
theorem inv68 : Inv st68 := inv_checkSeg seg68 inv67
theorem inv69 : Inv st69 := inv_checkSeg seg69 inv68
theorem inv70 : Inv st70 := inv_checkSeg seg70 inv69
theorem inv71 : Inv st71 := inv_checkSeg seg71 inv70
theorem inv72 : Inv st72 := inv_checkSeg seg72 inv71
theorem inv73 : Inv st73 := inv_checkSeg seg73 inv72
theorem inv74 : Inv st74 := inv_checkSeg seg74 inv73
theorem inv75 : Inv st75 := inv_checkSeg seg75 inv74
theorem inv76 : Inv st76 := inv_checkSeg seg76 inv75
theorem inv77 : Inv st77 := inv_checkSeg seg77 inv76
theorem inv78 : Inv st78 := inv_checkSeg seg78 inv77
theorem inv79 : Inv st79 := inv_checkSeg seg79 inv78
theorem inv80 : Inv st80 := inv_checkSeg seg80 inv79
theorem inv81 : Inv st81 := inv_checkSeg seg81 inv80
theorem inv82 : Inv st82 := inv_checkSeg seg82 inv81
theorem inv83 : Inv st83 := inv_checkSeg seg83 inv82
theorem inv84 : Inv st84 := inv_checkSeg seg84 inv83
theorem inv85 : Inv st85 := inv_checkSeg seg85 inv84
theorem inv86 : Inv st86 := inv_checkSeg seg86 inv85
theorem inv87 : Inv st87 := inv_checkSeg seg87 inv86
theorem inv88 : Inv st88 := inv_checkSeg seg88 inv87
theorem inv89 : Inv st89 := inv_checkSeg seg89 inv88
theorem inv90 : Inv st90 := inv_checkSeg seg90 inv89
theorem inv91 : Inv st91 := inv_checkSeg seg91 inv90
theorem inv92 : Inv st92 := inv_checkSeg seg92 inv91
theorem inv93 : Inv st93 := inv_checkSeg seg93 inv92
theorem inv94 : Inv st94 := inv_checkSeg seg94 inv93
theorem inv95 : Inv st95 := inv_checkSeg seg95 inv94
theorem inv96 : Inv st96 := inv_checkSeg seg96 inv95
theorem inv97 : Inv st97 := inv_checkSeg seg97 inv96
theorem inv98 : Inv st98 := inv_checkSeg seg98 inv97
theorem inv99 : Inv st99 := inv_checkSeg seg99 inv98
theorem inv100 : Inv st100 := inv_checkSeg seg100 inv99
theorem inv101 : Inv st101 := inv_checkSeg seg101 inv100
theorem inv102 : Inv st102 := inv_checkSeg seg102 inv101
theorem inv103 : Inv st103 := inv_checkSeg seg103 inv102
theorem inv104 : Inv st104 := inv_checkSeg seg104 inv103
theorem inv105 : Inv st105 := inv_checkSeg seg105 inv104
theorem inv106 : Inv st106 := inv_checkSeg seg106 inv105
theorem inv107 : Inv st107 := inv_checkSeg seg107 inv106
theorem inv108 : Inv st108 := inv_checkSeg seg108 inv107
theorem inv109 : Inv st109 := inv_checkSeg seg109 inv108
theorem inv110 : Inv st110 := inv_checkSeg seg110 inv109
theorem inv111 : Inv st111 := inv_checkSeg seg111 inv110
theorem inv112 : Inv st112 := inv_checkSeg seg112 inv111
theorem inv113 : Inv st113 := inv_checkSeg seg113 inv112
theorem inv114 : Inv st114 := inv_checkSeg seg114 inv113
theorem inv115 : Inv st115 := inv_checkSeg seg115 inv114
theorem inv116 : Inv st116 := inv_checkSeg seg116 inv115
theorem inv117 : Inv st117 := inv_checkSeg seg117 inv116
theorem inv118 : Inv st118 := inv_checkSeg seg118 inv117
theorem inv119 : Inv st119 := inv_checkSeg seg119 inv118
theorem inv120 : Inv st120 := inv_checkSeg seg120 inv119
theorem inv121 : Inv st121 := inv_checkSeg seg121 inv120
theorem inv122 : Inv st122 := inv_checkSeg seg122 inv121
theorem inv123 : Inv st123 := inv_checkSeg seg123 inv122
theorem inv124 : Inv st124 := inv_checkSeg seg124 inv123
theorem inv125 : Inv st125 := inv_checkSeg seg125 inv124
theorem inv126 : Inv st126 := inv_checkSeg seg126 inv125
theorem inv127 : Inv st127 := inv_checkSeg seg127 inv126
theorem inv128 : Inv st128 := inv_checkSeg seg128 inv127
theorem inv129 : Inv st129 := inv_checkSeg seg129 inv128
theorem inv130 : Inv st130 := inv_checkSeg seg130 inv129
theorem inv131 : Inv st131 := inv_checkSeg seg131 inv130
theorem inv132 : Inv st132 := inv_checkSeg seg132 inv131
theorem inv133 : Inv st133 := inv_checkSeg seg133 inv132
theorem inv134 : Inv st134 := inv_checkSeg seg134 inv133
theorem inv135 : Inv st135 := inv_checkSeg seg135 inv134
theorem inv136 : Inv st136 := inv_checkSeg seg136 inv135
theorem inv137 : Inv st137 := inv_checkSeg seg137 inv136
theorem inv138 : Inv st138 := inv_checkSeg seg138 inv137
theorem inv139 : Inv st139 := inv_checkSeg seg139 inv138
theorem inv140 : Inv st140 := inv_checkSeg seg140 inv139
theorem inv141 : Inv st141 := inv_checkSeg seg141 inv140
theorem inv142 : Inv st142 := inv_checkSeg seg142 inv141
theorem inv143 : Inv st143 := inv_checkSeg seg143 inv142
theorem inv144 : Inv st144 := inv_checkSeg seg144 inv143
theorem inv145 : Inv st145 := inv_checkSeg seg145 inv144
theorem inv146 : Inv st146 := inv_checkSeg seg146 inv145
theorem inv147 : Inv st147 := inv_checkSeg seg147 inv146
theorem inv148 : Inv st148 := inv_checkSeg seg148 inv147
theorem inv149 : Inv st149 := inv_checkSeg seg149 inv148
theorem inv150 : Inv st150 := inv_checkSeg seg150 inv149
theorem inv151 : Inv st151 := inv_checkSeg seg151 inv150
theorem inv152 : Inv st152 := inv_checkSeg seg152 inv151
theorem inv153 : Inv st153 := inv_checkSeg seg153 inv152
theorem inv154 : Inv st154 := inv_checkSeg seg154 inv153
theorem inv155 : Inv st155 := inv_checkSeg seg155 inv154
theorem inv156 : Inv st156 := inv_checkSeg seg156 inv155
theorem inv157 : Inv st157 := inv_checkSeg seg157 inv156
theorem inv158 : Inv st158 := inv_checkSeg seg158 inv157
theorem inv159 : Inv st159 := inv_checkSeg seg159 inv158
theorem inv160 : Inv st160 := inv_checkSeg seg160 inv159
theorem inv161 : Inv st161 := inv_checkSeg seg161 inv160
theorem inv162 : Inv st162 := inv_checkSeg seg162 inv161
theorem inv163 : Inv st163 := inv_checkSeg seg163 inv162
theorem inv164 : Inv st164 := inv_checkSeg seg164 inv163
theorem inv165 : Inv st165 := inv_checkSeg seg165 inv164
theorem inv166 : Inv st166 := inv_checkSeg seg166 inv165
theorem inv167 : Inv st167 := inv_checkSeg seg167 inv166
theorem inv168 : Inv st168 := inv_checkSeg seg168 inv167
theorem inv169 : Inv st169 := inv_checkSeg seg169 inv168
theorem inv170 : Inv st170 := inv_checkSeg seg170 inv169
theorem inv171 : Inv st171 := inv_checkSeg seg171 inv170
theorem inv172 : Inv st172 := inv_checkSeg seg172 inv171
theorem inv173 : Inv st173 := inv_checkSeg seg173 inv172
theorem inv174 : Inv st174 := inv_checkSeg seg174 inv173
theorem inv175 : Inv st175 := inv_checkSeg seg175 inv174
theorem inv176 : Inv st176 := inv_checkSeg seg176 inv175
theorem inv177 : Inv st177 := inv_checkSeg seg177 inv176
theorem inv178 : Inv st178 := inv_checkSeg seg178 inv177
theorem inv179 : Inv st179 := inv_checkSeg seg179 inv178
theorem inv180 : Inv st180 := inv_checkSeg seg180 inv179
theorem inv181 : Inv st181 := inv_checkSeg seg181 inv180
theorem inv182 : Inv st182 := inv_checkSeg seg182 inv181
theorem inv183 : Inv st183 := inv_checkSeg seg183 inv182
theorem inv184 : Inv st184 := inv_checkSeg seg184 inv183
theorem inv185 : Inv st185 := inv_checkSeg seg185 inv184
theorem inv186 : Inv st186 := inv_checkSeg seg186 inv185
theorem inv187 : Inv st187 := inv_checkSeg seg187 inv186
theorem inv188 : Inv st188 := inv_checkSeg seg188 inv187
theorem inv189 : Inv st189 := inv_checkSeg seg189 inv188
theorem inv190 : Inv st190 := inv_checkSeg seg190 inv189
theorem inv191 : Inv st191 := inv_checkSeg seg191 inv190
theorem inv192 : Inv st192 := inv_checkSeg seg192 inv191
theorem inv193 : Inv st193 := inv_checkSeg seg193 inv192
theorem inv194 : Inv st194 := inv_checkSeg seg194 inv193
theorem inv195 : Inv st195 := inv_checkSeg seg195 inv194
theorem inv196 : Inv st196 := inv_checkSeg seg196 inv195
theorem inv197 : Inv st197 := inv_checkSeg seg197 inv196
theorem inv198 : Inv st198 := inv_checkSeg seg198 inv197
theorem inv199 : Inv st199 := inv_checkSeg seg199 inv198
theorem inv200 : Inv st200 := inv_checkSeg seg200 inv199
theorem inv201 : Inv st201 := inv_checkSeg seg201 inv200
theorem inv202 : Inv st202 := inv_checkSeg seg202 inv201
theorem inv203 : Inv st203 := inv_checkSeg seg203 inv202
theorem inv204 : Inv st204 := inv_checkSeg seg204 inv203
theorem inv205 : Inv st205 := inv_checkSeg seg205 inv204
theorem inv206 : Inv st206 := inv_checkSeg seg206 inv205
theorem inv207 : Inv st207 := inv_checkSeg seg207 inv206
theorem inv208 : Inv st208 := inv_checkSeg seg208 inv207
theorem inv209 : Inv st209 := inv_checkSeg seg209 inv208
theorem inv210 : Inv st210 := inv_checkSeg seg210 inv209
theorem inv211 : Inv st211 := inv_checkSeg seg211 inv210
theorem inv212 : Inv st212 := inv_checkSeg seg212 inv211
theorem inv213 : Inv st213 := inv_checkSeg seg213 inv212
theorem inv214 : Inv st214 := inv_checkSeg seg214 inv213
theorem inv215 : Inv st215 := inv_checkSeg seg215 inv214
theorem inv216 : Inv st216 := inv_checkSeg seg216 inv215
theorem inv217 : Inv st217 := inv_checkSeg seg217 inv216
theorem inv218 : Inv st218 := inv_checkSeg seg218 inv217
theorem inv219 : Inv st219 := inv_checkSeg seg219 inv218
theorem inv220 : Inv st220 := inv_checkSeg seg220 inv219
theorem inv221 : Inv st221 := inv_checkSeg seg221 inv220
theorem inv222 : Inv st222 := inv_checkSeg seg222 inv221
theorem inv223 : Inv st223 := inv_checkSeg seg223 inv222
theorem inv224 : Inv st224 := inv_checkSeg seg224 inv223
theorem inv225 : Inv st225 := inv_checkSeg seg225 inv224
theorem inv226 : Inv st226 := inv_checkSeg seg226 inv225
theorem inv227 : Inv st227 := inv_checkSeg seg227 inv226
theorem inv228 : Inv st228 := inv_checkSeg seg228 inv227
theorem inv229 : Inv st229 := inv_checkSeg seg229 inv228
theorem inv230 : Inv st230 := inv_checkSeg seg230 inv229
theorem inv231 : Inv st231 := inv_checkSeg seg231 inv230
theorem inv232 : Inv st232 := inv_checkSeg seg232 inv231
theorem inv233 : Inv st233 := inv_checkSeg seg233 inv232
theorem inv234 : Inv st234 := inv_checkSeg seg234 inv233
theorem inv235 : Inv st235 := inv_checkSeg seg235 inv234
theorem inv236 : Inv st236 := inv_checkSeg seg236 inv235
theorem inv237 : Inv st237 := inv_checkSeg seg237 inv236
theorem inv238 : Inv st238 := inv_checkSeg seg238 inv237
theorem inv239 : Inv st239 := inv_checkSeg seg239 inv238
theorem inv240 : Inv st240 := inv_checkSeg seg240 inv239
theorem inv241 : Inv st241 := inv_checkSeg seg241 inv240
theorem inv242 : Inv st242 := inv_checkSeg seg242 inv241
theorem inv243 : Inv st243 := inv_checkSeg seg243 inv242
theorem inv244 : Inv st244 := inv_checkSeg seg244 inv243
theorem inv245 : Inv st245 := inv_checkSeg seg245 inv244
theorem inv246 : Inv st246 := inv_checkSeg seg246 inv245
theorem inv247 : Inv st247 := inv_checkSeg seg247 inv246
theorem inv248 : Inv st248 := inv_checkSeg seg248 inv247
theorem inv249 : Inv st249 := inv_checkSeg seg249 inv248
theorem inv250 : Inv st250 := inv_checkSeg seg250 inv249
theorem inv251 : Inv st251 := inv_checkSeg seg251 inv250
theorem inv252 : Inv st252 := inv_checkSeg seg252 inv251
theorem inv253 : Inv st253 := inv_checkSeg seg253 inv252
theorem inv254 : Inv st254 := inv_checkSeg seg254 inv253
theorem inv255 : Inv st255 := inv_checkSeg seg255 inv254
theorem inv256 : Inv st256 := inv_checkSeg seg256 inv255
theorem inv257 : Inv st257 := inv_checkSeg seg257 inv256
theorem inv258 : Inv st258 := inv_checkSeg seg258 inv257
theorem inv259 : Inv st259 := inv_checkSeg seg259 inv258
theorem inv260 : Inv st260 := inv_checkSeg seg260 inv259
theorem inv261 : Inv st261 := inv_checkSeg seg261 inv260
theorem inv262 : Inv st262 := inv_checkSeg seg262 inv261
theorem inv263 : Inv st263 := inv_checkSeg seg263 inv262
theorem inv264 : Inv st264 := inv_checkSeg seg264 inv263
theorem inv265 : Inv st265 := inv_checkSeg seg265 inv264
theorem inv266 : Inv st266 := inv_checkSeg seg266 inv265
theorem inv267 : Inv st267 := inv_checkSeg seg267 inv266
theorem inv268 : Inv st268 := inv_checkSeg seg268 inv267
theorem inv269 : Inv st269 := inv_checkSeg seg269 inv268
theorem inv270 : Inv st270 := inv_checkSeg seg270 inv269
theorem inv271 : Inv st271 := inv_checkSeg seg271 inv270
theorem inv272 : Inv st272 := inv_checkSeg seg272 inv271
theorem inv273 : Inv st273 := inv_checkSeg seg273 inv272
theorem inv274 : Inv st274 := inv_checkSeg seg274 inv273
theorem inv275 : Inv st275 := inv_checkSeg seg275 inv274
theorem inv276 : Inv st276 := inv_checkSeg seg276 inv275
theorem inv277 : Inv st277 := inv_checkSeg seg277 inv276
theorem inv278 : Inv st278 := inv_checkSeg seg278 inv277
theorem inv279 : Inv st279 := inv_checkSeg seg279 inv278
theorem inv280 : Inv st280 := inv_checkSeg seg280 inv279
theorem inv281 : Inv st281 := inv_checkSeg seg281 inv280
theorem inv282 : Inv st282 := inv_checkSeg seg282 inv281
theorem inv283 : Inv st283 := inv_checkSeg seg283 inv282
theorem inv284 : Inv st284 := inv_checkSeg seg284 inv283
theorem inv285 : Inv st285 := inv_checkSeg seg285 inv284
theorem inv286 : Inv st286 := inv_checkSeg seg286 inv285
theorem inv287 : Inv st287 := inv_checkSeg seg287 inv286
theorem inv288 : Inv st288 := inv_checkSeg seg288 inv287
theorem inv289 : Inv st289 := inv_checkSeg seg289 inv288
theorem inv290 : Inv st290 := inv_checkSeg seg290 inv289
theorem inv291 : Inv st291 := inv_checkSeg seg291 inv290
theorem inv292 : Inv st292 := inv_checkSeg seg292 inv291

theorem row_of_inv {s : State} (hs : Inv s) (r : GHRow) (hN : s.n = r.N)
    (h : r.gLo * 10 ^ 18 ≤ s.glo ∧ s.ghi ≤ r.gHi * 10 ^ 18 ∧ r.hLo * 10 ^ 18 ≤ s.hlo ∧
      s.hhi ≤ r.hHi * 10 ^ 18) :
    (r.gLo : ℝ) / 10 ^ 6 ≤ G r.N ∧ G r.N ≤ (r.gHi : ℝ) / 10 ^ 6 ∧
      (r.hLo : ℝ) / 10 ^ 6 ≤ H r.N ∧ H r.N ≤ (r.hHi : ℝ) / 10 ^ 6 := by
  rw [← hN]
  have hS : ((S : ℕ) : ℝ) = 10 ^ 24 := by norm_num [S]
  obtain ⟨h1, h2, h3, h4⟩ := h
  have c1 : ((r.gLo * 10 ^ 18 : ℕ) : ℝ) ≤ s.glo := by exact_mod_cast h1
  have c2 : (s.ghi : ℝ) ≤ ((r.gHi * 10 ^ 18 : ℕ) : ℝ) := by exact_mod_cast h2
  have c3 : ((r.hLo * 10 ^ 18 : ℕ) : ℝ) ≤ s.hlo := by exact_mod_cast h3
  have c4 : (s.hhi : ℝ) ≤ ((r.hHi * 10 ^ 18 : ℕ) : ℝ) := by exact_mod_cast h4
  have i1 := hs.glo
  have i2 := hs.ghi
  have i3 := hs.hlo
  have i4 := hs.hhi
  rw [hS] at i1 i2 i3 i4
  push_cast at c1 c2 c3 c4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by norm_num)]; linarith
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [div_le_iff₀ (by norm_num)]; linarith
  · rw [le_div_iff₀ (by norm_num)]; linarith

end Cert

open Cert

/-- `A(n) ≤ 2(n − 1)` for `1 ≤ n ≤ 2²⁰`. -/
theorem weightSumBound : WeightSumBound := by
  intro n hn1 hn
  have hlast : st292.n = 2 ^ 20 := rfl
  exact inv292.hist n hn1 (by rw [hlast]; exact hn)

/-- The enclosures of `ghTable`. -/
theorem ghBounds : GHBounds := by
  intro r hr
  simp only [ghTable, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl


  · exact row_of_inv inv1 _ rfl (by decide +kernel)
  · exact row_of_inv inv2 _ rfl (by decide +kernel)
  · exact row_of_inv inv3 _ rfl (by decide +kernel)
  · exact row_of_inv inv4 _ rfl (by decide +kernel)
  · exact row_of_inv inv5 _ rfl (by decide +kernel)
  · exact row_of_inv inv6 _ rfl (by decide +kernel)
  · exact row_of_inv inv7 _ rfl (by decide +kernel)
  · exact row_of_inv inv8 _ rfl (by decide +kernel)
  · exact row_of_inv inv9 _ rfl (by decide +kernel)
  · exact row_of_inv inv10 _ rfl (by decide +kernel)
  · exact row_of_inv inv11 _ rfl (by decide +kernel)
  · exact row_of_inv inv12 _ rfl (by decide +kernel)
  · exact row_of_inv inv13 _ rfl (by decide +kernel)
  · exact row_of_inv inv14 _ rfl (by decide +kernel)
  · exact row_of_inv inv15 _ rfl (by decide +kernel)
  · exact row_of_inv inv16 _ rfl (by decide +kernel)
  · exact row_of_inv inv17 _ rfl (by decide +kernel)
  · exact row_of_inv inv18 _ rfl (by decide +kernel)
  · exact row_of_inv inv19 _ rfl (by decide +kernel)
  · exact row_of_inv inv20 _ rfl (by decide +kernel)
  · exact row_of_inv inv21 _ rfl (by decide +kernel)
  · exact row_of_inv inv22 _ rfl (by decide +kernel)
  · exact row_of_inv inv24 _ rfl (by decide +kernel)
  · exact row_of_inv inv25 _ rfl (by decide +kernel)
  · exact row_of_inv inv26 _ rfl (by decide +kernel)
  · exact row_of_inv inv28 _ rfl (by decide +kernel)
  · exact row_of_inv inv31 _ rfl (by decide +kernel)
  · exact row_of_inv inv32 _ rfl (by decide +kernel)
  · exact row_of_inv inv35 _ rfl (by decide +kernel)
  · exact row_of_inv inv39 _ rfl (by decide +kernel)
  · exact row_of_inv inv42 _ rfl (by decide +kernel)
  · exact row_of_inv inv45 _ rfl (by decide +kernel)
  · exact row_of_inv inv52 _ rfl (by decide +kernel)
  · exact row_of_inv inv60 _ rfl (by decide +kernel)
  · exact row_of_inv inv61 _ rfl (by decide +kernel)
  · exact row_of_inv inv73 _ rfl (by decide +kernel)
  · exact row_of_inv inv88 _ rfl (by decide +kernel)
  · exact row_of_inv inv95 _ rfl (by decide +kernel)
  · exact row_of_inv inv109 _ rfl (by decide +kernel)
  · exact row_of_inv inv135 _ rfl (by decide +kernel)
  · exact row_of_inv inv161 _ rfl (by decide +kernel)
  · exact row_of_inv inv171 _ rfl (by decide +kernel)
  · exact row_of_inv inv218 _ rfl (by decide +kernel)
  · exact row_of_inv inv280 _ rfl (by decide +kernel)
  · exact row_of_inv inv292 _ rfl (by decide +kernel)

end TernaryGoldbach.RSBounds.LambdaInputs
