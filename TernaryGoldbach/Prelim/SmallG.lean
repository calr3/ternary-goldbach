import TernaryGoldbach.Prelim.MVLemma8
import TernaryGoldbach.Prelim.SmallPsi

/-!
# `G(r) ≥ log r + 1.07` for `6 ≤ r < 21400`, checked by the kernel

`G(a) = ∑_{s ≤ a} μ²(s)/φ(s) ≥ ∑_{T ⊆ P, ∏T ≤ a} ∏_{p ∈ T} 1/(p−1)` for any set `P` of primes
(`Phi_le_GS`). `dfs` computes a lower bound for `10¹⁵` times the right side (depth-first
over the list `PL` of primes `≤ 21400`, rounding down; `dfs_le`). For 32 blocks `[a, b)` the kernel
checks `dfs a ≥ 10¹⁵ (U_b + 1.07)` and `log b < U_b` (`chkStep`), so `G(r) ≥ G(a) > log b + 1.07` on
the block. Only the primality of the entries of `PL` is used (trial division).
-/

open Finset

namespace TernaryGoldbach.Prelim.SmallG

open TernaryGoldbach.Prelim.MV (gS GS)
def PL0 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987]
def PL1 : List ℕ := [1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409]
def PL2 : List ℕ := [4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997]
def PL3 : List ℕ := [7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733]
def PL4 : List ℕ := [9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111, 10133, 10139, 10141, 10151, 10159, 10163, 10169, 10177, 10181, 10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271, 10273, 10289, 10301, 10303, 10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433, 10453, 10457, 10459, 10463, 10477, 10487, 10499, 10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601, 10607, 10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667, 10687, 10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939, 10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071, 11083, 11087, 11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213, 11239, 11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399, 11411, 11423, 11437, 11443, 11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699, 11701, 11717, 11719, 11731, 11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833, 11839, 11863, 11867, 11887, 11897, 11903, 11909, 11923, 11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987, 12007, 12011, 12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149, 12157, 12161, 12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289, 12301, 12323, 12329, 12343, 12347, 12373, 12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433, 12437, 12451, 12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553]
def PL5 : List ℕ := [12569, 12577, 12583, 12589, 12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739, 12743, 12757, 12763, 12781, 12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899, 12907, 12911, 12917, 12919, 12923, 12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001, 13003, 13007, 13009, 13033, 13037, 13043, 13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163, 13171, 13177, 13183, 13187, 13217, 13219, 13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327, 13331, 13337, 13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463, 13469, 13477, 13487, 13499, 13513, 13523, 13537, 13553, 13567, 13577, 13591, 13597, 13613, 13619, 13627, 13633, 13649, 13669, 13679, 13681, 13687, 13691, 13693, 13697, 13709, 13711, 13721, 13723, 13729, 13751, 13757, 13759, 13763, 13781, 13789, 13799, 13807, 13829, 13831, 13841, 13859, 13873, 13877, 13879, 13883, 13901, 13903, 13907, 13913, 13921, 13931, 13933, 13963, 13967, 13997, 13999, 14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087, 14107, 14143, 14149, 14153, 14159, 14173, 14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323, 14327, 14341, 14347, 14369, 14387, 14389, 14401, 14407, 14411, 14419, 14423, 14431, 14437, 14447, 14449, 14461, 14479, 14489, 14503, 14519, 14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563, 14591, 14593, 14621, 14627, 14629, 14633, 14639, 14653, 14657, 14669, 14683, 14699, 14713, 14717, 14723, 14731, 14737, 14741, 14747, 14753, 14759, 14767, 14771, 14779, 14783, 14797, 14813, 14821, 14827, 14831, 14843, 14851, 14867, 14869, 14879, 14887, 14891, 14897, 14923, 14929, 14939, 14947, 14951, 14957, 14969, 14983, 15013, 15017, 15031, 15053, 15061, 15073, 15077, 15083, 15091, 15101, 15107, 15121, 15131, 15137, 15139, 15149, 15161, 15173, 15187, 15193, 15199, 15217, 15227, 15233, 15241, 15259, 15263, 15269, 15271, 15277, 15287, 15289, 15299, 15307, 15313, 15319, 15329, 15331, 15349, 15359, 15361, 15373, 15377, 15383, 15391, 15401]
def PL6 : List ℕ := [15413, 15427, 15439, 15443, 15451, 15461, 15467, 15473, 15493, 15497, 15511, 15527, 15541, 15551, 15559, 15569, 15581, 15583, 15601, 15607, 15619, 15629, 15641, 15643, 15647, 15649, 15661, 15667, 15671, 15679, 15683, 15727, 15731, 15733, 15737, 15739, 15749, 15761, 15767, 15773, 15787, 15791, 15797, 15803, 15809, 15817, 15823, 15859, 15877, 15881, 15887, 15889, 15901, 15907, 15913, 15919, 15923, 15937, 15959, 15971, 15973, 15991, 16001, 16007, 16033, 16057, 16061, 16063, 16067, 16069, 16073, 16087, 16091, 16097, 16103, 16111, 16127, 16139, 16141, 16183, 16187, 16189, 16193, 16217, 16223, 16229, 16231, 16249, 16253, 16267, 16273, 16301, 16319, 16333, 16339, 16349, 16361, 16363, 16369, 16381, 16411, 16417, 16421, 16427, 16433, 16447, 16451, 16453, 16477, 16481, 16487, 16493, 16519, 16529, 16547, 16553, 16561, 16567, 16573, 16603, 16607, 16619, 16631, 16633, 16649, 16651, 16657, 16661, 16673, 16691, 16693, 16699, 16703, 16729, 16741, 16747, 16759, 16763, 16787, 16811, 16823, 16829, 16831, 16843, 16871, 16879, 16883, 16889, 16901, 16903, 16921, 16927, 16931, 16937, 16943, 16963, 16979, 16981, 16987, 16993, 17011, 17021, 17027, 17029, 17033, 17041, 17047, 17053, 17077, 17093, 17099, 17107, 17117, 17123, 17137, 17159, 17167, 17183, 17189, 17191, 17203, 17207, 17209, 17231, 17239, 17257, 17291, 17293, 17299, 17317, 17321, 17327, 17333, 17341, 17351, 17359, 17377, 17383, 17387, 17389, 17393, 17401, 17417, 17419, 17431, 17443, 17449, 17467, 17471, 17477, 17483, 17489, 17491, 17497, 17509, 17519, 17539, 17551, 17569, 17573, 17579, 17581, 17597, 17599, 17609, 17623, 17627, 17657, 17659, 17669, 17681, 17683, 17707, 17713, 17729, 17737, 17747, 17749, 17761, 17783, 17789, 17791, 17807, 17827, 17837, 17839, 17851, 17863, 17881, 17891, 17903, 17909, 17911, 17921, 17923, 17929, 17939, 17957, 17959, 17971, 17977, 17981, 17987, 17989, 18013, 18041, 18043, 18047, 18049, 18059, 18061, 18077, 18089, 18097, 18119, 18121, 18127, 18131, 18133, 18143, 18149, 18169, 18181, 18191, 18199, 18211, 18217, 18223, 18229, 18233, 18251, 18253, 18257, 18269, 18287, 18289, 18301, 18307, 18311, 18313]
def PL7 : List ℕ := [18329, 18341, 18353, 18367, 18371, 18379, 18397, 18401, 18413, 18427, 18433, 18439, 18443, 18451, 18457, 18461, 18481, 18493, 18503, 18517, 18521, 18523, 18539, 18541, 18553, 18583, 18587, 18593, 18617, 18637, 18661, 18671, 18679, 18691, 18701, 18713, 18719, 18731, 18743, 18749, 18757, 18773, 18787, 18793, 18797, 18803, 18839, 18859, 18869, 18899, 18911, 18913, 18917, 18919, 18947, 18959, 18973, 18979, 19001, 19009, 19013, 19031, 19037, 19051, 19069, 19073, 19079, 19081, 19087, 19121, 19139, 19141, 19157, 19163, 19181, 19183, 19207, 19211, 19213, 19219, 19231, 19237, 19249, 19259, 19267, 19273, 19289, 19301, 19309, 19319, 19333, 19373, 19379, 19381, 19387, 19391, 19403, 19417, 19421, 19423, 19427, 19429, 19433, 19441, 19447, 19457, 19463, 19469, 19471, 19477, 19483, 19489, 19501, 19507, 19531, 19541, 19543, 19553, 19559, 19571, 19577, 19583, 19597, 19603, 19609, 19661, 19681, 19687, 19697, 19699, 19709, 19717, 19727, 19739, 19751, 19753, 19759, 19763, 19777, 19793, 19801, 19813, 19819, 19841, 19843, 19853, 19861, 19867, 19889, 19891, 19913, 19919, 19927, 19937, 19949, 19961, 19963, 19973, 19979, 19991, 19993, 19997, 20011, 20021, 20023, 20029, 20047, 20051, 20063, 20071, 20089, 20101, 20107, 20113, 20117, 20123, 20129, 20143, 20147, 20149, 20161, 20173, 20177, 20183, 20201, 20219, 20231, 20233, 20249, 20261, 20269, 20287, 20297, 20323, 20327, 20333, 20341, 20347, 20353, 20357, 20359, 20369, 20389, 20393, 20399, 20407, 20411, 20431, 20441, 20443, 20477, 20479, 20483, 20507, 20509, 20521, 20533, 20543, 20549, 20551, 20563, 20593, 20599, 20611, 20627, 20639, 20641, 20663, 20681, 20693, 20707, 20717, 20719, 20731, 20743, 20747, 20749, 20753, 20759, 20771, 20773, 20789, 20807, 20809, 20849, 20857, 20873, 20879, 20887, 20897, 20899, 20903, 20921, 20929, 20939, 20947, 20959, 20963, 20981, 20983, 21001, 21011, 21013, 21017, 21019, 21023, 21031, 21059, 21061, 21067, 21089, 21101, 21107, 21121, 21139, 21143, 21149, 21157, 21163, 21169, 21179, 21187, 21191, 21193, 21211, 21221, 21227, 21247, 21269, 21277, 21283, 21313, 21317, 21319, 21323, 21341, 21347, 21377, 21379, 21383]
def PL8 : List ℕ := [21391, 21397]
def PL : List ℕ := PL0 ++ PL1 ++ PL2 ++ PL3 ++ PL4 ++ PL5 ++ PL6 ++ PL7 ++ PL8

/-- Trial division by `2 ≤ d ≤ 147` with `d² ≤ p` (enough for `p < 147²`). -/
def primeCheck2 (p : ℕ) : Bool :=
  2 ≤ p && p < 21609 && (List.range' 2 146).all (fun d => p < d * d || p % d != 0)

theorem prime_of_primeCheck2 {p : ℕ} (h : primeCheck2 p = true) : p.Prime := by
  unfold primeCheck2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h.1.1, fun m hm2 hms hdvd => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
  have hm : m ≤ 147 := by nlinarith [h.1.2]
  rcases h.2 m ⟨hm2, by omega⟩ with h1 | h1
  · omega
  · exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
theorem PL0_ok : PL0.all primeCheck2 = true := by decide +kernel
theorem PL1_ok : PL1.all primeCheck2 = true := by decide +kernel
theorem PL2_ok : PL2.all primeCheck2 = true := by decide +kernel
theorem PL3_ok : PL3.all primeCheck2 = true := by decide +kernel
theorem PL4_ok : PL4.all primeCheck2 = true := by decide +kernel
theorem PL5_ok : PL5.all primeCheck2 = true := by decide +kernel
theorem PL6_ok : PL6.all primeCheck2 = true := by decide +kernel
theorem PL7_ok : PL7.all primeCheck2 = true := by decide +kernel
theorem PL8_ok : PL8.all primeCheck2 = true := by decide +kernel
theorem PL_ok : PL.all primeCheck2 = true := by
  simp only [PL, List.all_append, PL0_ok, PL1_ok, PL2_ok, PL3_ok, PL4_ok, PL5_ok, PL6_ok, PL7_ok, PL8_ok, Bool.and_self]

theorem PL_chain : PL.IsChain (· < ·) := by decide +kernel

theorem PL_nodup : PL.Nodup := (List.isChain_iff_pairwise.1 PL_chain).nodup

theorem PL_prime : ∀ p ∈ PL, p.Prime := fun p hp =>
  prime_of_primeCheck2 (List.all_eq_true.1 PL_ok p hp)

/-- Depth-first lower bound for `w ∑_{T ⊆ l, m ∏T ≤ r} ∏_{p ∈ T} 1/(p−1)` (rounding down; it stops
at the first `p` with `mp > r`, which only drops terms). -/
def dfs (r : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, w => w
  | p :: l, m, w => if m * p ≤ r then dfs r l m w + dfs r l (m * p) (w / (p - 1)) else w

/-- `Φ = ∑_{T ⊆ s} [m ∏T ≤ r] ∏_{q ∈ T} 1/(q−1)`. -/
noncomputable def Phi (r m : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ T ∈ s.powerset, if m * ∏ q ∈ T, q ≤ r then ∏ q ∈ T, (1 / ((q : ℝ) - 1)) else 0

theorem Phi_term_nonneg {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) (r m : ℕ) (T : Finset ℕ)
    (hT : T ∈ s.powerset) :
    0 ≤ (if m * ∏ q ∈ T, q ≤ r then ∏ q ∈ T, (1 / ((q : ℝ) - 1)) else 0) := by
  split_ifs
  · refine prod_nonneg fun q hq => ?_
    have : (2 : ℝ) ≤ q := by exact_mod_cast (hs q (mem_powerset.1 hT hq)).two_le
    exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

theorem one_le_Phi {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) {r m : ℕ} (hm : m ≤ r) :
    1 ≤ Phi r m s := by
  unfold Phi
  have h := single_le_sum (f := fun T => if m * ∏ q ∈ T, q ≤ r then
      ∏ q ∈ T, (1 / ((q : ℝ) - 1)) else 0) (fun T hT => Phi_term_nonneg hs r m T hT)
    (empty_mem_powerset s)
  simpa [hm] using h

theorem Phi_insert {s : Finset ℕ} {p : ℕ} (hp : p ∉ s) (r m : ℕ) :
    Phi r m (insert p s) = Phi r m s + 1 / ((p : ℝ) - 1) * Phi r (m * p) s := by
  unfold Phi
  rw [sum_powerset_insert hp, mul_sum]
  congr 1
  refine sum_congr rfl fun T hT => ?_
  have hpT : p ∉ T := fun h => hp (mem_powerset.1 hT h)
  rw [prod_insert hpT, prod_insert hpT, ← mul_assoc, mul_comm m p]
  split_ifs <;> ring

theorem dfs_le (r : ℕ) : ∀ (l : List ℕ), l.Nodup → (∀ p ∈ l, p.Prime) → ∀ m w : ℕ, m ≤ r →
    (dfs r l m w : ℝ) ≤ w * Phi r m l.toFinset := by
  intro l
  induction l with
  | nil =>
    intro _ _ m w hm
    simp [dfs, Phi, hm]
  | cons p l ih =>
    intro hnd hpr m w hm
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    have hl : l.Nodup := (List.nodup_cons.1 hnd).2
    have hlp : ∀ q ∈ l, q.Prime := fun q hq => hpr q (List.mem_cons_of_mem p hq)
    have hpp : p.Prime := hpr p List.mem_cons_self
    have hs : ∀ q ∈ l.toFinset, q.Prime := fun q hq => hlp q (List.mem_toFinset.1 hq)
    rw [List.toFinset_cons, Phi_insert (by simpa using hpl)]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    unfold dfs
    split_ifs with h
    · push_cast
      have h1 := ih hl hlp m w hm
      have h2 := ih hl hlp (m * p) (w / (p - 1)) h
      have h3 : ((w / (p - 1) : ℕ) : ℝ) ≤ (w : ℝ) / ((p : ℝ) - 1) := by
        have := Nat.cast_div_le (α := ℝ) (m := w) (n := p - 1)
        rwa [Nat.cast_sub hpp.one_le, Nat.cast_one] at this
      have hP2 : 0 ≤ Phi r (m * p) l.toFinset := le_trans (by norm_num) (one_le_Phi hs h)
      have h4 : ((w / (p - 1) : ℕ) : ℝ) * Phi r (m * p) l.toFinset ≤
          (w : ℝ) / ((p : ℝ) - 1) * Phi r (m * p) l.toFinset :=
        mul_le_mul_of_nonneg_right h3 hP2
      have e : (w : ℝ) * (Phi r m l.toFinset + 1 / ((p : ℝ) - 1) * Phi r (m * p) l.toFinset) =
          w * Phi r m l.toFinset + (w : ℝ) / ((p : ℝ) - 1) * Phi r (m * p) l.toFinset := by ring
      rw [e]; linarith
    · have h1 := one_le_Phi hs hm
      have h2 : 0 ≤ 1 / ((p : ℝ) - 1) * Phi r (m * p) l.toFinset := by
        apply mul_nonneg (div_nonneg (by norm_num) (by linarith))
        unfold Phi; exact sum_nonneg fun T hT => Phi_term_nonneg hs _ _ T hT
      nlinarith

/-- `φ(∏T) = ∏_{p ∈ T} (p − 1)` for a set of primes. -/
theorem totient_prod_primes (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    Nat.totient (∏ p ∈ T, p) = ∏ p ∈ T, (p - 1) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hap : a.Prime := hT a (mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hT p (mem_insert_of_mem hp)
    rw [prod_insert ha, prod_insert ha, Nat.totient_mul, Nat.totient_prime hap, ih hs]
    refine Nat.Coprime.prod_right fun q hq => ?_
    exact (Nat.coprime_primes hap (hs q hq)).2 (fun h => ha (h ▸ hq))

theorem gS_prod_primes (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    gS (∏ p ∈ T, p) = ∏ p ∈ T, (1 / ((p : ℝ) - 1)) := by
  have hsq : Squarefree (∏ p ∈ T, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
      fun p hp => (hT p hp).squarefree
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hT a ha) (hT b hb)).mpr hab
  unfold gS
  rw [if_pos hsq, totient_prod_primes T hT, Nat.cast_prod, one_div, ← prod_inv_distrib]
  refine prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (hT p hp).one_le, Nat.cast_one, one_div]

/-- `∑_{T ⊆ P, ∏T ≤ r} ∏_{p ∈ T} 1/(p−1) ≤ G(r)` for a set `P` of primes. -/
theorem Phi_le_GS (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ) : Phi r 1 P ≤ GS r := by
  unfold Phi GS
  simp only [one_mul]
  rw [← sum_filter]
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ q ∈ T, q)
      ((P.powerset.filter fun T => ∏ q ∈ T, q ≤ r : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro T1 h1 T2 h2 he
    simp only [coe_filter, Set.mem_setOf_eq, mem_powerset] at h1 h2
    have e1 := Nat.primeFactors_prod (fun p hp => hP p (h1.1 hp))
    have e2 := Nat.primeFactors_prod (fun p hp => hP p (h2.1 hp))
    simp only at he
    rw [← e1, ← e2, he]
  have hval : ∀ T ∈ P.powerset.filter (fun T => ∏ q ∈ T, q ≤ r),
      ∏ q ∈ T, (1 / ((q : ℝ) - 1)) = gS (∏ q ∈ T, q) := fun T hT =>
    (gS_prod_primes T fun p hp => hP p ((mem_powerset.1 (mem_filter.1 hT).1) hp)).symm
  rw [sum_congr rfl hval, ← sum_image (f := gS) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
  · intro n hn
    obtain ⟨T, hT, rfl⟩ := mem_image.1 hn
    have hT' := mem_filter.1 hT
    refine mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun p hp =>
      (hP p ((mem_powerset.1 hT'.1) hp)).ne_zero), hT'.2⟩
  · unfold gS; split_ifs <;> positivity

theorem GS_mono {a r : ℕ} (h : a ≤ r) : GS a ≤ GS r := by
  unfold GS
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun n _ _ => by
    unfold gS; split_ifs <;> positivity

/-- One block: `(100 U + 107·10⁸)·10¹⁵ ≤ 10¹⁰ dfs(a)` and `log b < U/10⁸` give `G ≥ log + 1.07` on `[a, b)`. -/
theorem block_ok {a b cN : ℕ} (ha : 1 ≤ a)
    (hdfs : (100 * cN + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs a PL 1 (10 ^ 15) * 10 ^ 8 * 100)
    (hlog : TernaryGoldbach.Prelim.Small.chkStep cN (10 ^ 8) 1 b = true) {r : ℕ} (har : a ≤ r)
    (hrb : r < b) : Real.log r + 1.07 ≤ GS r := by
  have hb0 : 0 < b := by omega
  have hl := TernaryGoldbach.Prelim.Small.log_lt_of_chk (by norm_num) hb0 hlog
  push_cast at hl
  set X := dfs a PL 1 (10 ^ 15) with hX
  have hd : (X : ℝ) ≤ (10 : ℝ) ^ 15 * Phi a 1 PL.toFinset := by
    have := dfs_le a PL PL_nodup PL_prime 1 (10 ^ 15) ha
    rw [← hX] at this; push_cast at this; norm_num; exact this
  have hP := Phi_le_GS PL.toFinset (fun p hp => PL_prime p (List.mem_toFinset.1 hp)) a
  have hdr : ((100 * cN + 107 * 10 ^ 8) * 10 ^ 15 : ℝ) ≤ (X : ℝ) * 10 ^ 8 * 100 := by
    exact_mod_cast hdfs
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlr : Real.log r ≤ Real.log b := Real.log_le_log hr0 (by exact_mod_cast hrb.le)
  have hG := GS_mono har
  linarith
theorem dfs_0 : (100 * 207944157 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 6 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_0 : TernaryGoldbach.Prelim.Small.chkStep 207944157 (10 ^ 8) 1 8 = true := by decide +kernel
theorem dfs_1 : (100 * 230258512 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 8 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_1 : TernaryGoldbach.Prelim.Small.chkStep 230258512 (10 ^ 8) 1 10 = true := by decide +kernel
theorem dfs_2 : (100 * 256494938 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 10 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_2 : TernaryGoldbach.Prelim.Small.chkStep 256494938 (10 ^ 8) 1 13 = true := by decide +kernel
theorem dfs_3 : (100 * 277258875 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 13 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_3 : TernaryGoldbach.Prelim.Small.chkStep 277258875 (10 ^ 8) 1 16 = true := by decide +kernel
theorem dfs_4 : (100 * 304452246 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 16 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_4 : TernaryGoldbach.Prelim.Small.chkStep 304452246 (10 ^ 8) 1 21 = true := by decide +kernel
theorem dfs_5 : (100 * 325809656 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 21 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_5 : TernaryGoldbach.Prelim.Small.chkStep 325809656 (10 ^ 8) 1 26 = true := by decide +kernel
theorem dfs_6 : (100 * 349650759 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 26 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_6 : TernaryGoldbach.Prelim.Small.chkStep 349650759 (10 ^ 8) 1 33 = true := by decide +kernel
theorem dfs_7 : (100 * 373766964 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 33 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_7 : TernaryGoldbach.Prelim.Small.chkStep 373766964 (10 ^ 8) 1 42 = true := by decide +kernel
theorem dfs_8 : (100 * 407753747 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 42 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_8 : TernaryGoldbach.Prelim.Small.chkStep 407753747 (10 ^ 8) 1 59 = true := by decide +kernel
theorem dfs_9 : (100 * 431748814 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 59 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_9 : TernaryGoldbach.Prelim.Small.chkStep 431748814 (10 ^ 8) 1 75 = true := by decide +kernel
theorem dfs_10 : (100 * 458496750 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 75 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_10 : TernaryGoldbach.Prelim.Small.chkStep 458496750 (10 ^ 8) 1 98 = true := by decide +kernel
theorem dfs_11 : (100 * 483628193 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 98 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_11 : TernaryGoldbach.Prelim.Small.chkStep 483628193 (10 ^ 8) 1 126 = true := by decide +kernel
theorem dfs_12 : (100 * 509375023 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 126 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_12 : TernaryGoldbach.Prelim.Small.chkStep 509375023 (10 ^ 8) 1 163 = true := by decide +kernel
theorem dfs_13 : (100 * 533753810 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 163 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_13 : TernaryGoldbach.Prelim.Small.chkStep 533753810 (10 ^ 8) 1 208 = true := by decide +kernel
theorem dfs_14 : (100 * 558724868 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 208 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_14 : TernaryGoldbach.Prelim.Small.chkStep 558724868 (10 ^ 8) 1 267 = true := by decide +kernel
theorem dfs_15 : (100 * 585793318 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 267 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_15 : TernaryGoldbach.Prelim.Small.chkStep 585793318 (10 ^ 8) 1 350 = true := by decide +kernel
theorem dfs_16 : (100 * 611146736 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 350 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_16 : TernaryGoldbach.Prelim.Small.chkStep 611146736 (10 ^ 8) 1 451 = true := by decide +kernel
theorem dfs_17 : (100 * 637331981 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 451 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_17 : TernaryGoldbach.Prelim.Small.chkStep 637331981 (10 ^ 8) 1 586 = true := by decide +kernel
theorem dfs_18 : (100 * 663725806 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 586 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_18 : TernaryGoldbach.Prelim.Small.chkStep 663725806 (10 ^ 8) 1 763 = true := by decide +kernel
theorem dfs_19 : (100 * 689972313 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 763 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_19 : TernaryGoldbach.Prelim.Small.chkStep 689972313 (10 ^ 8) 1 992 = true := by decide +kernel
theorem dfs_20 : (100 * 716162203 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 992 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_20 : TernaryGoldbach.Prelim.Small.chkStep 716162203 (10 ^ 8) 1 1289 = true := by decide +kernel
theorem dfs_21 : (100 * 742057893 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 1289 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_21 : TernaryGoldbach.Prelim.Small.chkStep 742057893 (10 ^ 8) 1 1670 = true := by decide +kernel
theorem dfs_22 : (100 * 768708018 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 1670 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_22 : TernaryGoldbach.Prelim.Small.chkStep 768708018 (10 ^ 8) 1 2180 = true := by decide +kernel
theorem dfs_23 : (100 * 794590962 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 2180 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_23 : TernaryGoldbach.Prelim.Small.chkStep 794590962 (10 ^ 8) 1 2824 = true := by decide +kernel
theorem dfs_24 : (100 * 820903629 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 2824 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_24 : TernaryGoldbach.Prelim.Small.chkStep 820903629 (10 ^ 8) 1 3674 = true := by decide +kernel
theorem dfs_25 : (100 * 847219585 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 3674 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_25 : TernaryGoldbach.Prelim.Small.chkStep 847219585 (10 ^ 8) 1 4780 = true := by decide +kernel
theorem dfs_26 : (100 * 873488192 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 4780 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_26 : TernaryGoldbach.Prelim.Small.chkStep 873488192 (10 ^ 8) 1 6216 = true := by decide +kernel
theorem dfs_27 : (100 * 899714718 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 6216 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_27 : TernaryGoldbach.Prelim.Small.chkStep 899714718 (10 ^ 8) 1 8080 = true := by decide +kernel
theorem dfs_28 : (100 * 926036789 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 8080 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_28 : TernaryGoldbach.Prelim.Small.chkStep 926036789 (10 ^ 8) 1 10513 = true := by decide +kernel
theorem dfs_29 : (100 * 952325152 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 10513 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_29 : TernaryGoldbach.Prelim.Small.chkStep 952325152 (10 ^ 8) 1 13674 = true := by decide +kernel
theorem dfs_30 : (100 * 978543576 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 13674 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_30 : TernaryGoldbach.Prelim.Small.chkStep 978543576 (10 ^ 8) 1 17773 = true := by decide +kernel
theorem dfs_31 : (100 * 997114623 + 107 * 10 ^ 8) * 10 ^ 15 ≤ dfs 17773 PL 1 (10 ^ 15) * 10 ^ 8 * 100 := by decide +kernel
theorem log_31 : TernaryGoldbach.Prelim.Small.chkStep 997114623 (10 ^ 8) 1 21400 = true := by decide +kernel

/-- **`G(r) ≥ log r + 1.07` for `6 ≤ r < 21400`** (kernel-checked). -/
theorem lemma7_small (r : ℕ) (h6 : 6 ≤ r) (hr : r < 21400) : Real.log r + 1.07 ≤ GS r := by
  by_cases h0 : r < 8
  · exact block_ok (by norm_num) dfs_0 log_0 (by omega) h0
  by_cases h1 : r < 10
  · exact block_ok (by norm_num) dfs_1 log_1 (by omega) h1
  by_cases h2 : r < 13
  · exact block_ok (by norm_num) dfs_2 log_2 (by omega) h2
  by_cases h3 : r < 16
  · exact block_ok (by norm_num) dfs_3 log_3 (by omega) h3
  by_cases h4 : r < 21
  · exact block_ok (by norm_num) dfs_4 log_4 (by omega) h4
  by_cases h5 : r < 26
  · exact block_ok (by norm_num) dfs_5 log_5 (by omega) h5
  by_cases h6 : r < 33
  · exact block_ok (by norm_num) dfs_6 log_6 (by omega) h6
  by_cases h7 : r < 42
  · exact block_ok (by norm_num) dfs_7 log_7 (by omega) h7
  by_cases h8 : r < 59
  · exact block_ok (by norm_num) dfs_8 log_8 (by omega) h8
  by_cases h9 : r < 75
  · exact block_ok (by norm_num) dfs_9 log_9 (by omega) h9
  by_cases h10 : r < 98
  · exact block_ok (by norm_num) dfs_10 log_10 (by omega) h10
  by_cases h11 : r < 126
  · exact block_ok (by norm_num) dfs_11 log_11 (by omega) h11
  by_cases h12 : r < 163
  · exact block_ok (by norm_num) dfs_12 log_12 (by omega) h12
  by_cases h13 : r < 208
  · exact block_ok (by norm_num) dfs_13 log_13 (by omega) h13
  by_cases h14 : r < 267
  · exact block_ok (by norm_num) dfs_14 log_14 (by omega) h14
  by_cases h15 : r < 350
  · exact block_ok (by norm_num) dfs_15 log_15 (by omega) h15
  by_cases h16 : r < 451
  · exact block_ok (by norm_num) dfs_16 log_16 (by omega) h16
  by_cases h17 : r < 586
  · exact block_ok (by norm_num) dfs_17 log_17 (by omega) h17
  by_cases h18 : r < 763
  · exact block_ok (by norm_num) dfs_18 log_18 (by omega) h18
  by_cases h19 : r < 992
  · exact block_ok (by norm_num) dfs_19 log_19 (by omega) h19
  by_cases h20 : r < 1289
  · exact block_ok (by norm_num) dfs_20 log_20 (by omega) h20
  by_cases h21 : r < 1670
  · exact block_ok (by norm_num) dfs_21 log_21 (by omega) h21
  by_cases h22 : r < 2180
  · exact block_ok (by norm_num) dfs_22 log_22 (by omega) h22
  by_cases h23 : r < 2824
  · exact block_ok (by norm_num) dfs_23 log_23 (by omega) h23
  by_cases h24 : r < 3674
  · exact block_ok (by norm_num) dfs_24 log_24 (by omega) h24
  by_cases h25 : r < 4780
  · exact block_ok (by norm_num) dfs_25 log_25 (by omega) h25
  by_cases h26 : r < 6216
  · exact block_ok (by norm_num) dfs_26 log_26 (by omega) h26
  by_cases h27 : r < 8080
  · exact block_ok (by norm_num) dfs_27 log_27 (by omega) h27
  by_cases h28 : r < 10513
  · exact block_ok (by norm_num) dfs_28 log_28 (by omega) h28
  by_cases h29 : r < 13674
  · exact block_ok (by norm_num) dfs_29 log_29 (by omega) h29
  by_cases h30 : r < 17773
  · exact block_ok (by norm_num) dfs_30 log_30 (by omega) h30
  exact block_ok (by norm_num) dfs_31 log_31 (by omega) (by omega)

end TernaryGoldbach.Prelim.SmallG
