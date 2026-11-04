"""Coloured chain: lists of 4-cycles that put every balanced arrangement of one inner orbit on its home faces.

Run `uv run python scripts/chain_col.py` to rebuild scripts/chain_col.json from the lists stored below (a few minutes,
because of the template search), and `uv run python scripts/check_chain_col.py` to verify it independently.
`--search N m1 m2 seconds seed` reruns the annealing that found the lists, and `--descend N file seconds repair seed mode`
shrinks a solution file (mode 0: product, mode 1: larger list).

Abstract stage. Omega has N points, the first four are the slots F of the colour being placed. A state is the 4-subset
A of positions holding that colour. T1 is a list of 4-cycles and FF a family of 4-subsets with at most two points outside
F, such that every A has t in T1 with t(A) in FF. T2 has one 4-cycle per member S of FF with t2(S) = F, so T2 T1 covers.

Statement proved by the data (see the `statement` field of the JSON and PLAN.md):
  for every stage j and every 4-subset A of Omega_j there are t1 in list1, t2 in list2 with t2 t1 (A) = F_j,
  supp t in Omega_j, and every list element comes with a 4-cycle D on one whole face disjoint from it and a row word
  P with P^-1 K^d P = t, P^-1 L^d P = D (d = +1 for list1, -1 for list2).
"""
import itertools, json, math, os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rot import act, MUL, INV, RX, RY, RZ

# Solutions on abstract points 0..N-1, F = {0,1,2,3}: (N, T1 cycles, FF as bitmasks)
SOLUTIONS = {
    'best': [
        (24, [(3, 1, 19, 2), (6, 1, 16, 11), (1, 2, 6, 9), (2, 15, 1, 4), (18, 1, 22, 2), (1, 16, 2, 21), (3, 1, 6, 0), (9, 1, 3, 0), (12, 1, 3, 0), (3, 1, 15, 0), (3, 0, 18, 1), (21, 0, 3, 1), (9, 1, 6, 0), (6, 1, 12, 0), (6, 1, 15, 0), (6, 1, 18, 0), (6, 0, 21, 1), (12, 0, 9, 1), (9, 0, 15, 1), (9, 1, 18, 0), (9, 1, 21, 0), (15, 1, 12, 0), (12, 1, 18, 0), (21, 1, 12, 0), (18, 1, 15, 0), (15, 0, 21, 1), (18, 1, 21, 0), (4, 0, 10, 15), (7, 0, 2, 15), (3, 10, 0, 2), (13, 0, 2, 9), (16, 0, 6, 20), (19, 0, 4, 3), (20, 22, 0, 21), (7, 1, 4, 0), (4, 1, 10, 0), (13, 1, 4, 0), (4, 0, 16, 1), (19, 0, 4, 1), (4, 0, 22, 1), (10, 0, 7, 1), (13, 0, 7, 1), (7, 0, 16, 1), (19, 0, 7, 1), (22, 1, 7, 0), (13, 0, 10, 1), (16, 1, 10, 0), (19, 0, 10, 1), (22, 1, 10, 0), (16, 1, 13, 0), (13, 1, 19, 0), (13, 0, 22, 1), (19, 0, 16, 1), (16, 1, 22, 0), (22, 1, 19, 0), (2, 0, 5, 1), (2, 1, 8, 0), (11, 1, 2, 0), (2, 0, 14, 1), (2, 1, 17, 0), (2, 0, 20, 1), (2, 1, 23, 0), (8, 0, 5, 1), (5, 1, 11, 0), (5, 0, 14, 1), (17, 1, 5, 0), (20, 0, 5, 1), (23, 1, 5, 0), (8, 0, 11, 1), (14, 1, 8, 0), (17, 1, 8, 0), (8, 1, 20, 0), (23, 1, 8, 0), (14, 0, 11, 1), (11, 1, 17, 0), (20, 0, 11, 1), (11, 1, 23, 0), (14, 1, 17, 0), (14, 0, 20, 1), (23, 1, 14, 0), (17, 0, 20, 1), (17, 1, 23, 0), (20, 0, 23, 1)],
         [4131, 15, 39, 34819, 135, 2228227, 4259843, 131587, 262155, 4227075, 8199, 8388615, 294915, 1049091, 132099, 262151, 6149, 8389635, 2097159, 16899, 8454147, 9437187, 43, 525317, 163843, 8451, 18435, 323, 131139, 524295, 8203, 5123, 524309, 8912899, 2097187, 4202499, 262275, 5242883, 131079, 524803, 51, 99, 131091, 275, 1059, 2055, 2097171, 4115, 4357, 16403, 135171, 524323, 643, 2162691, 131203, 1048595, 2105347, 525315, 8388627, 65543, 131331, 131107, 2097163, 291, 20483, 69635, 8519683, 65603, 2067, 65571, 2115, 4103, 4194311, 73731, 32803, 4194339, 270339, 3145731, 27, 262179, 8388675, 1052675, 33027, 135173, 32835, 10243, 81923, 23, 4194435, 8707, 2097219, 4194371, 8388619, 32779, 1050627, 1045, 12582915, 8388643, 786435, 16515, 32775, 2099203, 139, 2097411, 2563, 266243, 2097283, 83, 4163, 1081347, 2113539, 33283, 32787, 163, 133123, 1031, 33795, 2101251, 65795, 524547, 1179651, 2621443, 16395, 327683, 263171, 524299, 4611, 771, 195, 2097667, 66051, 524355, 65547, 4227, 267, 262659, 523, 8389123, 1539, 1049603, 71, 98307, 3075, 531, 40963, 1035, 1056771, 2098179, 278531, 1048583, 2083, 4194819, 17411, 10485763, 4355, 1048643, 264195, 526339, 8323, 1048587, 16643, 8404995, 547, 12291, 36867, 387, 8392707, 8388867, 528387, 2307, 1091, 4198403, 8396803, 6147, 16391, 4133, 1114115, 262211, 16419, 655363, 4456451, 20485, 4194563, 49155, 196611, 4198405, 262163, 540675, 139267, 4196355, 519, 131083, 8227, 8390659, 2179, 557059, 579, 2129923, 8388739, 8421379, 262403, 1310723, 8392709, 75, 393219, 8259, 263, 2059, 1283, 1048835, 4210691, 4325379, 32899, 147459, 1064963, 2359299, 4107, 8650755, 1572867, 16451, 1048707, 65667, 24579, 1052677, 1048611, 6291459, 67587, 4194315]),
        (20, [(1, 9, 3, 0), (6, 0, 1, 15), (13, 9, 1, 3), (15, 1, 6, 10), (8, 9, 18, 1), (6, 1, 3, 0), (3, 1, 9, 0), (12, 0, 3, 1), (3, 0, 15, 1), (3, 0, 18, 1), (9, 1, 6, 0), (12, 0, 6, 1), (15, 0, 6, 1), (18, 0, 6, 1), (12, 1, 10, 15), (9, 0, 12, 1), (18, 0, 9, 1), (12, 0, 15, 1), (12, 0, 18, 1), (18, 1, 15, 0), (2, 4, 0, 9), (2, 7, 0, 9), (0, 9, 2, 10), (13, 0, 9, 2), (16, 0, 9, 2), (0, 9, 2, 19), (4, 1, 7, 0), (10, 1, 4, 0), (1, 4, 0, 13), (1, 4, 0, 16), (19, 1, 4, 0), (10, 1, 7, 0), (13, 1, 7, 0), (7, 1, 16, 0), (19, 0, 7, 1), (0, 13, 1, 10), (0, 16, 1, 10), (10, 1, 19, 0), (13, 1, 16, 0), (13, 1, 19, 0), (16, 0, 19, 1), (5, 1, 2, 0), (2, 0, 8, 1), (11, 1, 2, 0), (14, 1, 2, 0), (2, 0, 17, 1), (0, 8, 1, 5), (0, 5, 1, 11), (5, 1, 14, 0), (5, 1, 17, 0), (11, 0, 8, 1), (8, 0, 14, 1), (1, 8, 0, 17), (11, 0, 14, 1), (17, 0, 11, 1), (17, 0, 14, 1)],
         [99, 9219, 540675, 327683, 4227, 1155, 526339, 323, 69635, 33795, 262403, 786435, 65795, 34821, 49155, 195, 3075, 133123, 262151, 589827, 2083, 1539, 163, 65667, 83, 12291, 4131, 147, 524323, 15, 524299, 16643, 65555, 131091, 33029, 524419, 8259, 387, 98307, 34819, 18435, 66563, 525315, 524547, 139267, 8211, 66051, 278531, 131139, 291, 643, 519, 531, 1043, 163843, 267, 8451, 270339, 16899, 771, 547, 557059, 65543, 139, 16391, 524355, 8323, 33027, 32787, 16515, 131107, 532483, 71, 51, 2115, 262218, 196611, 2055, 131331, 40963, 65547, 2563, 8227, 23, 24579, 32775, 43, 32899, 6147, 4355, 8199, 2067, 17411, 10243, 16419, 262163, 4170, 393219, 81923, 1035, 131203, 135, 275, 1059, 135171, 147459, 20483, 8707, 65603, 39, 1091, 16451, 264195, 4115, 524803, 263, 163845, 1031, 65571, 131587, 4103, 528387, 49157, 524295, 73731, 16403, 8203, 2307, 67587, 2179, 1283, 27, 33286, 5123, 266243, 263171, 524307, 2059, 262275, 33283, 655363, 32803, 16395, 557062, 131079, 132099, 32805, 262179, 131083]),
        (16, [(12, 10, 6, 1), (1, 14, 4, 9), (12, 1, 3, 6), (10, 15, 1, 9), (9, 1, 3, 0), (3, 1, 12, 0), (15, 0, 3, 1), (9, 0, 6, 1), (12, 1, 6, 0), (15, 1, 6, 0), (12, 0, 9, 1), (9, 1, 15, 0), (12, 0, 15, 1), (6, 13, 4, 0), (7, 0, 3, 6), (0, 4, 7, 10), (6, 7, 13, 0), (4, 1, 7, 0), (10, 0, 4, 1), (4, 0, 13, 1), (7, 0, 10, 1), (1, 13, 0, 7), (13, 1, 10, 0), (2, 0, 5, 1), (2, 0, 8, 1), (11, 1, 2, 0), (0, 14, 1, 2), (5, 0, 8, 1), (11, 0, 5, 1), (14, 0, 5, 1), (11, 0, 8, 1), (1, 14, 0, 8), (1, 11, 0, 14)],
         [15, 16515, 8227, 8323, 643, 6147, 1035, 1031, 771, 32775, 2055, 329, 32803, 2563, 18435, 75, 105, 267, 1155, 2059, 33795, 2067, 16391, 16395, 2083, 39, 83, 4131, 275, 531, 23, 135, 4115, 8203, 163, 49155, 1091, 5123, 579, 547, 1059, 12291, 1043, 291, 4103, 2307, 3075, 323, 43, 519, 27, 16457, 16451, 195, 99, 147, 16419, 2179, 8211, 139, 8451, 32899, 1283, 77, 2115, 4355, 387, 16643, 33027, 2121, 263, 8259, 8707, 16403, 32787, 71, 1539, 40963, 16899, 8199, 36874, 10243, 51, 34819, 9219, 20483, 24579, 17411, 4227]),
        (12, [(9, 2, 4, 1), (2, 8, 1, 4), (2, 3, 1, 0), (9, 1, 11, 2), (11, 9, 5, 1), (2, 9, 1, 8), (9, 1, 3, 5), (5, 4, 1, 2), (7, 2, 6, 1), (1, 11, 2, 8), (8, 2, 5, 11), (2, 10, 1, 6), (1, 5, 2, 11), (8, 2, 3, 1), (10, 1, 7, 2), (11, 1, 4, 5), (1, 9, 3, 8), (2, 8, 3, 9)],
         [1094, 2070, 2118, 99, 106, 86, 2062, 39, 23, 142, 30, 71, 78, 2055, 1059, 54, 582, 263, 294, 170, 2182, 102, 390, 1031, 1158, 46, 135, 1062, 519, 15, 198, 150, 3078, 526, 1038, 163, 550, 1046, 1066, 166]),
        (8, [(0, 6, 7, 2), (6, 0, 1, 5), (6, 4, 3, 5), (2, 6, 3, 4), (2, 1, 0, 4), (7, 5, 2, 3), (7, 6, 0, 4)],
         [202, 197, 58, 153, 169, 172, 86, 53, 83, 102]),
    ],
    'balanced': [
        (24, [(1, 20, 3, 4), (2, 13, 0, 5), (21, 3, 23, 1), (19, 1, 2, 20), (3, 20, 1, 2), (2, 23, 0, 21), (4, 2, 14, 0), (8, 2, 5, 0), (1, 12, 3, 23), (11, 1, 17, 3), (20, 12, 19, 2), (3, 5, 0, 20), (3, 15, 2, 21), (2, 17, 0, 23), (14, 1, 0, 3), (4, 0, 23, 2), (2, 14, 8, 4), (0, 8, 20, 12), (23, 0, 12, 2), (1, 5, 3, 20), (2, 23, 9, 1), (3, 11, 0, 15), (1, 23, 3, 0), (17, 2, 1, 23), (23, 0, 3, 2), (0, 22, 2, 15), (6, 10, 2, 8), (0, 4, 2, 15), (2, 14, 0, 5), (17, 3, 19, 1), (20, 2, 23, 0), (20, 1, 14, 3), (1, 8, 3, 12), (2, 3, 0, 1), (21, 0, 13, 2), (3, 13, 1, 20), (20, 0, 11, 2), (19, 0, 23, 2), (0, 14, 2, 12), (19, 0, 10, 2), (20, 1, 18, 3), (2, 12, 0, 21), (6, 0, 23, 2), (23, 2, 5, 0), (6, 3, 18, 1), (5, 2, 21, 0), (18, 1, 7, 3), (3, 20, 1, 15), (3, 20, 1, 17), (7, 3, 17, 0), (1, 12, 3, 4), (4, 14, 5, 2), (23, 0, 18, 2), (0, 4, 3, 10), (2, 12, 17, 7), (23, 0, 22, 2), (2, 1, 0, 23), (4, 2, 21, 0), (0, 23, 1, 14), (2, 13, 3, 21), (0, 1, 20, 3), (13, 0, 23, 2), (13, 0, 14, 2), (2, 20, 1, 6), (5, 2, 12, 0), (22, 1, 23, 2), (21, 2, 14, 0), (1, 2, 9, 0), (21, 1, 0, 3), (3, 7, 1, 15), (16, 1, 20, 3), (9, 3, 20, 1), (23, 0, 16, 2), (8, 3, 2, 1), (1, 16, 3, 6), (11, 1, 18, 3), (1, 23, 3, 14), (4, 2, 22, 0), (1, 8, 3, 23), (3, 7, 1, 4), (1, 21, 3, 2), (1, 20, 0, 13), (18, 0, 16, 2), (1, 10, 3, 15), (1, 15, 3, 22), (2, 23, 18, 3), (22, 3, 6, 1), (9, 2, 11, 0), (3, 16, 1, 9), (1, 20, 3, 21), (1, 18, 3, 17), (13, 1, 21, 3), (3, 16, 1, 7), (1, 5, 3, 8), (2, 10, 0, 23), (0, 15, 1, 22), (20, 3, 23, 1), (16, 22, 2, 3), (13, 0, 8, 2), (20, 0, 18, 2), (1, 6, 3, 9), (2, 8, 0, 21), (0, 19, 2, 13), (3, 11, 1, 16), (7, 0, 21, 1), (2, 20, 0, 9), (3, 17, 1, 16), (0, 4, 2, 5), (12, 0, 4, 2), (0, 3, 8, 1), (1, 6, 0, 11), (22, 3, 15, 0), (10, 1, 22, 3), (3, 18, 1, 16), (2, 3, 0, 9), (23, 0, 4, 1), (1, 14, 3, 5), (20, 1, 11, 3), (1, 2, 3, 12), (7, 1, 11, 3), (7, 0, 23, 2), (12, 1, 0, 3), (17, 3, 9, 1), (1, 12, 3, 5), (21, 0, 23, 3), (8, 2, 14, 0), (0, 10, 1, 19), (22, 3, 19, 1), (9, 1, 18, 3), (9, 1, 7, 3), (23, 2, 15, 0), (20, 1, 7, 3), (8, 0, 1, 20), (3, 4, 1, 17), (12, 1, 14, 3), (12, 3, 21, 1), (17, 0, 7, 2), (2, 1, 23, 12), (2, 17, 18, 1), (13, 0, 10, 2), (2, 11, 3, 20), (20, 0, 1, 2), (20, 3, 6, 1), (3, 23, 8, 2), (0, 8, 16, 3), (1, 7, 3, 6), (3, 13, 1, 23), (3, 13, 2, 10), (14, 2, 5, 8), (4, 0, 19, 3), (3, 18, 20, 9), (13, 0, 21, 1), (16, 1, 10, 17), (19, 3, 15, 1), (23, 2, 8, 0), (2, 13, 0, 6), (3, 20, 1, 8), (19, 3, 10, 1), (3, 14, 1, 2), (14, 0, 23, 2), (1, 20, 3, 22), (3, 6, 1, 11), (3, 6, 1, 17), (1, 14, 3, 8), (0, 8, 2, 4), (2, 3, 0, 11), (2, 20, 0, 3), (11, 2, 1, 0), (2, 8, 0, 12), (3, 11, 1, 9), (17, 3, 7, 1), (23, 3, 2, 1), (12, 0, 13, 2)],
         [2098186, 132101, 528394, 1290, 1048583, 2565, 17418, 524330, 131114, 4227077, 4618, 1048590, 66053, 40970, 154, 524362, 327690, 524805, 32906, 270341, 131210, 2097418, 645, 65578, 4202506, 4103, 655370, 4194821, 581, 16906, 533, 2097290, 65605, 4194570, 2228234, 4718602, 1157, 524554, 4456458, 4194346, 9226, 2314, 132106, 524357, 8266, 1052677, 85, 66565, 32842, 4210698, 16650, 2181, 262186, 2097674, 33285, 524309, 262165, 1098, 1066, 8203, 4194437, 4325381, 32789, 4259850, 131098, 32810, 2097194, 4194325, 196613, 266250, 163850, 3077, 526341, 170, 67589, 32794, 2162698, 525317, 73733, 12298, 2099210, 16522, 131205, 18442, 262213, 1048589, 330, 81930, 532490, 4259845, 10245, 1093, 589829, 1050, 147466, 1162, 8388650, 8458, 131146, 36874, 394, 262277, 2117, 58, 8234, 264197, 34821, 4234, 32837, 106, 16410, 8330, 139274, 65669, 294917, 262661, 4109, 540682, 4456453, 202, 65802, 135178, 525322, 1541, 8388619, 43, 2621450, 8709, 5130, 282, 131589, 278538, 557066, 4194378, 98309, 133125, 90, 524314, 2113546, 2097226, 65557, 554, 2069, 262410, 131338, 33034, 263173, 33802, 524426, 2359306, 786437, 49162, 778, 393221, 8218, 6154, 2090, 24586, 2129930, 8206, 69642, 46, 4195338, 6291466, 2097178, 9437189, 524421, 4198410, 8229, 1045, 4170, 4196357, 163845, 16458]),
        (20, [(3, 5, 15, 12), (19, 2, 13, 1), (13, 1, 17, 2), (6, 2, 16, 1), (1, 17, 2, 11), (12, 0, 16, 3), (0, 5, 3, 11), (10, 1, 16, 2), (14, 3, 5, 1), (16, 1, 11, 2), (0, 12, 3, 5), (0, 15, 3, 9), (3, 14, 0, 5), (1, 8, 2, 11), (3, 16, 0, 17), (7, 1, 19, 2), (0, 11, 1, 16), (1, 18, 0, 12), (6, 3, 13, 0), (9, 2, 5, 1), (18, 2, 5, 1), (2, 19, 5, 18), (16, 1, 18, 2), (8, 3, 17, 0), (0, 8, 3, 12), (14, 7, 8, 0), (4, 0, 12, 3), (17, 3, 8, 1), (1, 19, 2, 4), (16, 3, 4, 1), (17, 1, 12, 2), (1, 5, 2, 19), (2, 19, 16, 13), (19, 14, 1, 3), (11, 3, 16, 2), (1, 18, 2, 4), (8, 3, 16, 0), (19, 2, 9, 1), (2, 14, 1, 8), (19, 15, 9, 2), (7, 2, 9, 15), (16, 2, 0, 1), (1, 7, 2, 12), (2, 5, 1, 15), (1, 3, 16, 6), (10, 8, 3, 12), (8, 0, 5, 3), (3, 1, 16, 2), (10, 1, 5, 2), (1, 5, 2, 7), (1, 4, 2, 8), (1, 18, 2, 11), (15, 1, 7, 9), (2, 19, 1, 8), (3, 7, 0, 15), (0, 4, 3, 5), (2, 15, 1, 7), (7, 9, 18, 3), (3, 16, 0, 4), (1, 18, 2, 14), (2, 12, 1, 10), (19, 0, 2, 11), (11, 1, 14, 2), (2, 15, 1, 19), (2, 0, 17, 3), (9, 1, 12, 2), (16, 2, 15, 1), (16, 10, 2, 19), (1, 2, 19, 6), (2, 17, 1, 8), (3, 10, 0, 6), (15, 2, 16, 17), (12, 13, 7, 1), (0, 12, 3, 18), (7, 0, 9, 3), (1, 17, 0, 16), (19, 1, 18, 2), (2, 14, 1, 19), (0, 1, 19, 11), (1, 14, 0, 18), (9, 13, 1, 11), (17, 0, 19, 3), (14, 0, 12, 3), (0, 17, 3, 1), (19, 2, 5, 0), (1, 18, 2, 17), (2, 4, 1, 17), (1, 10, 5, 9), (2, 6, 1, 19), (2, 11, 1, 4), (3, 5, 0, 17), (5, 1, 16, 2), (15, 1, 17, 2), (19, 1, 0, 2), (10, 2, 1, 12), (2, 4, 0, 14), (0, 18, 3, 8), (17, 2, 14, 1), (4, 5, 3, 1), (19, 2, 12, 1), (10, 2, 11, 1), (2, 16, 1, 19), (2, 16, 8, 1), (15, 3, 12, 0), (4, 2, 12, 0), (2, 13, 1, 16), (19, 2, 10, 1), (4, 3, 5, 2), (10, 0, 13, 3), (2, 11, 1, 12), (18, 3, 17, 0), (0, 16, 3, 14), (19, 3, 12, 2), (14, 0, 4, 3)],
         [20486, 646, 294921, 89, 1094, 262665, 1542, 1161, 524550, 262182, 201, 270345, 32902, 33033, 262217, 131086, 582, 153, 198, 4358, 1289, 262409, 16905, 8326, 9225, 65550, 132105, 81926, 266246, 2118, 32793, 65558, 34825, 294, 1158, 4134, 4138, 16646, 262281, 2121, 40969, 131593, 65543, 69638, 3078, 540678, 131145, 524326, 537, 262406, 135174, 2569, 33289, 2062, 46, 131079, 786438, 8217, 524302, 8713, 2566, 2185, 4103, 131209, 4118, 33801, 2055, 10249, 278534, 393, 8265, 8329, 329, 33286, 1545, 8457, 196614, 524310, 16457, 54, 16406, 262166, 65798, 1049, 649, 9222, 777, 16422, 32838, 49161, 39, 278, 34822, 589830, 10246, 32841, 16521, 40966, 65574, 585, 8710, 327686, 263177, 16409, 33798, 133126, 528390, 17417, 655366, 131110, 4110, 2182, 8262, 24585, 1097]),
        (16, [(3, 11, 5, 15), (0, 6, 3, 15), (1, 3, 12, 0), (7, 0, 11, 3), (0, 4, 3, 13), (12, 13, 0, 6), (13, 12, 6, 3), (3, 4, 0, 11), (2, 0, 15, 3), (6, 0, 13, 3), (5, 0, 14, 3), (2, 10, 9, 7), (0, 4, 1, 6), (3, 6, 0, 12), (0, 15, 3, 4), (6, 3, 11, 0), (7, 2, 9, 0), (9, 2, 7, 3), (1, 0, 14, 3), (0, 2, 3, 13), (0, 10, 3, 4), (11, 0, 2, 3), (10, 7, 0, 9), (13, 3, 8, 2), (8, 3, 14, 12), (12, 3, 15, 0), (0, 13, 3, 9), (4, 11, 0, 15), (0, 2, 3, 10), (1, 0, 6, 3), (7, 3, 13, 0), (8, 0, 1, 9), (5, 3, 12, 0), (0, 9, 3, 11), (1, 3, 5, 0), (2, 3, 4, 0), (0, 6, 3, 8), (3, 9, 0, 7), (13, 0, 8, 3), (8, 2, 11, 3), (5, 3, 6, 0), (14, 3, 12, 0), (8, 0, 7, 3), (9, 3, 2, 5), (5, 3, 15, 0), (11, 0, 8, 3), (0, 15, 3, 13), (3, 14, 0, 15), (13, 0, 11, 3), (0, 4, 14, 15), (11, 0, 15, 3), (3, 15, 0, 1), (8, 3, 9, 0), (6, 0, 4, 3), (3, 6, 0, 14)],
         [33801, 1289, 2089, 553, 5129, 16397, 1035, 141, 16521, 2121, 17417, 43, 12297, 649, 16425, 57, 1093, 27, 537, 4109, 15, 40969, 4233, 4617, 4137, 777, 3081, 169, 32841, 16649, 297, 525, 269, 1545, 4121, 523, 18441, 20489, 9225, 45, 29, 4361, 267, 393, 1065, 8203, 16905, 1161, 281, 10249, 4107, 139, 153, 33036, 16395, 16409]),
        (12, [(3, 10, 2, 1), (2, 0, 7, 3), (6, 1, 7, 0), (0, 2, 1, 9), (6, 1, 2, 0), (1, 7, 0, 11), (1, 7, 0, 2), (6, 1, 3, 0), (0, 3, 1, 8), (9, 1, 6, 0), (1, 4, 0, 10), (5, 1, 4, 0), (2, 0, 11, 1), (9, 0, 7, 1), (7, 1, 2, 11), (5, 0, 10, 1), (9, 11, 7, 8), (9, 0, 3, 1), (0, 2, 1, 3), (9, 7, 0, 3), (5, 11, 1, 2), (1, 8, 0, 9), (2, 8, 3, 0), (9, 10, 11, 0), (0, 8, 1, 6), (7, 2, 3, 1), (0, 7, 1, 3)],
         [2059, 1031, 3075, 1091, 27, 2563, 523, 163, 2083, 1283, 1043, 83, 1059, 2067, 531, 263, 2115, 547, 51, 1539, 291, 99, 387, 579, 75, 275, 2307]),
        (8, [(7, 6, 4, 2), (3, 7, 0, 5), (4, 0, 1, 6), (5, 7, 6, 3), (1, 3, 4, 2), (1, 5, 6, 2), (0, 4, 3, 1), (6, 5, 2, 0), (0, 3, 1, 2)],
         [102, 198, 57, 153, 201, 166, 89, 54]),
    ],
}

FACE_ORDER = [(0, 3, 10, 19), (4, 13, 7, 18), (8, 16, 21, 11), (1, 5, 14, 9), (2, 6, 15, 22), (12, 20, 17, 23)]  # kc = 0..5

N0, U0, V0 = 100, 37, 59
AX = {'x': 0, 'y': 1, 'z': 2}
def clamp(t): return N0 - 1 if t == N0 else (-(N0 - 1) if t == -N0 else t)
def sl(ax, layer, d=1, base=(-U0, V0, N0)):
    rot = {'x': RX, 'y': RY, 'z': RZ}[ax]
    if d == -1: rot = INV[rot]
    return tuple(MUL[rot][k] if clamp(act(k, base)[AX[ax]]) == layer else k for k in range(24))
def comp(a, b): return tuple(a[b[i]] for i in range(24))
def invp(a):
    r = [0] * 24
    for i, x in enumerate(a): r[x] = i
    return tuple(r)
FACE = {'U': ('z', 1), 'D': ('z', -1), 'F': ('y', 1), 'B': ('y', -1), 'r': ('x', 1), 'l': ('x', -1)}
def facep(f, d=1):
    ax, s = FACE[f]
    return sl(ax, s * (N0 - 1), d)
K, L = sl('x', V0), sl('x', -V0)
def cyc4(p):
    i = next(i for i in range(24) if p[i] != i)
    return (i, p[i], p[p[i]], p[p[p[i]]])
def norm(c):
    i = c.index(min(c))
    return tuple(c[i:]) + tuple(c[:i])
KC, LC = cyc4(K), cyc4(L)

class Templates:
    """Row words: pieces f r f^-1, r a slice of the row's index. Phase 1 moves K onto c, phase 2 moves L onto a cycle on
    a face disjoint from c, using pieces and short commutators that fix c pointwise."""
    def __init__(s):
        faces = list(FACE)
        words = [()] + [((f, d),) for f in faces for d in (1, -1)] + [((f, 1), (f, 1)) for f in faces]
        words += [((f, d), (g, e)) for f, g in itertools.combinations(faces, 2) for d in (1, -1) for e in (1, -1)]
        res = {}
        for ax in 'xyz':
            for sg in (1, -1):
                for di in (1, -1):
                    r = sl(ax, sg * U0, di)
                    for w in words:
                        P = tuple(range(24))
                        for (f, d) in w: P = comp(facep(f, d), P)
                        perm = comp(invp(P), comp(r, P))
                        cost = 2 * len(w) + 1
                        if perm not in res or res[perm][0] > cost:
                            res[perm] = (cost, w, ax, sg, di)
        s.plist = list(res.items())
        s.pidx = {p: i for i, (p, _) in enumerate(s.plist)}
        s.pinv = [s.pidx[invp(p)] for p, _ in s.plist]
        s.par1 = {norm(KC): None}
        frontier = [norm(KC)]
        while frontier:
            nx = []
            for st in frontier:
                for i, (p, _) in enumerate(s.plist):
                    t = norm(tuple(p[x] for x in st))
                    if t not in s.par1:
                        s.par1[t] = (st, i)
                        nx.append(t)
            frontier = nx
        extra = {}
        for i, (p, vi) in enumerate(s.plist):
            pi = invp(p)
            for j, (q, vj) in enumerate(s.plist):
                if all(p[x] == x or q[x] == x for x in range(24)):
                    continue            # disjoint: trivial commutator
                qi = invp(q)
                e = tuple(p[q[pi[qi[x]]]] for x in range(24))
                sup = sum(e[x] != x for x in range(24))
                if 0 < sup <= 3:
                    c = vi[0] + vj[0]
                    if e not in extra or extra[e][0] > c:
                        extra[e] = (c, i, j)
        s.extra = list(extra.items())
    def template(s, c, Ds, d):
        tgt = tuple(c) if d == 1 else tuple(reversed(c))
        cur = norm(tgt); seq1 = []
        while s.par1[cur] is not None:
            prev, i = s.par1[cur]
            seq1.append(i); cur = prev
        seq1.reverse()
        Lc = LC
        for i in seq1:
            p = s.plist[i][0]
            Lc = tuple(p[x] for x in Lc)
        Dt = {norm(x if d == 1 else tuple(reversed(x))) for x in Ds}
        cs = set(tgt)
        gens = [(p, [i]) for i, (p, _) in enumerate(s.plist) if all(p[x] == x for x in cs)]
        gens += [(t, [s.pinv[j], s.pinv[i], j, i]) for t, (cc, i, j) in s.extra if all(t[x] == x for x in cs)]
        start = norm(Lc)
        par = {start: None}; fr = [start]; hit = start if start in Dt else None
        while hit is None and fr:
            nx = []
            for st in fr:
                for p, se in gens:
                    t = norm(tuple(p[x] for x in st))
                    if t not in par:
                        par[t] = (st, se)
                        if t in Dt:
                            hit = t; break
                        nx.append(t)
                if hit: break
            fr = nx
        if hit is None:
            raise RuntimeError(f"no template for {c} {d}")
        seq2 = []; q = hit
        while par[q] is not None:
            a, b = par[q]; seq2 = b + seq2; q = a
        seq = seq1 + seq2
        D = hit if d == 1 else norm(tuple(reversed(hit)))
        word = []
        for i in reversed(seq):
            cost, w, ax, sg, di = s.plist[i][1]
            word.append(([[FACE[f][0], FACE[f][1], fd] for (f, fd) in w], ax, sg, -di))
        return word, D

def apply_c(c, S):
    m = {c[i]: c[(i + 1) % 4] for i in range(4)}
    return tuple(sorted(m.get(x, x) for x in S))
def find_t2(N, S):
    wrong = [x for x in S if x >= 4]; free = [x for x in range(4) if x not in S]
    if len(wrong) == 2: return (wrong[0], free[0], wrong[1], free[1])
    if len(wrong) == 1:
        rest = [x for x in range(4, N) if x != wrong[0]]
        return (wrong[0], free[0], rest[0], rest[1])
    if not wrong: return (4, 5, 6, 7)
    raise ValueError(S)

def build_scheme(name, sols, TT):
    stages = []
    for j, (N, T1, masks) in enumerate(sols):
        FF = [tuple(x for x in range(N) if m >> x & 1) for m in masks]
        T2 = [find_t2(N, S) for S in FF]
        idx = {S: i for i, S in enumerate(FF)}
        omega = [x for c in range(j, 6) for x in FACE_ORDER[c]]
        wit = []
        for A in itertools.combinations(range(N), 4):
            got = next(((i, idx[apply_c(t, A)]) for i, t in enumerate(T1) if apply_c(t, A) in idx), None)
            assert got is not None, (name, j, A)
            wit.append([sorted(omega[x] for x in A), got[0], got[1]])
        def el(t, d):
            c = [omega[x] for x in t]
            faces = [y for y in range(6) if not set(FACE_ORDER[y]) & set(c)]
            Ds = set()
            for y in faces:
                f = FACE_ORDER[y]
                for q in itertools.permutations(f[1:]): Ds.add(norm((f[0],) + q))
            word, D = TT.template(c, Ds, d)
            y = next(y for y in range(6) if set(FACE_ORDER[y]) == set(D))
            return {"c": c, "y": y, "D": list(D), "word": word}
        stages.append({"colour": j, "N": N, "omega": sorted(omega), "list1": [el(t, 1) for t in T1],
                       "list2": [el(t, -1) for t in T2], "witness": wit})
        print(name, "stage", j, len(T1), len(T2), flush=True)
    B = sum(math.log2(len(s["list1"])) + math.log2(len(s["list2"])) for s in stages)
    return {"stages": stages, "B_sum_logs": B, "B_same_block": sum(2 * math.log2(max(len(s["list1"]), len(s["list2"]))) for s in stages)}

STATEMENT = """Coordinates: k in Fin 24 = act k (-u, v, n); mirror frame k = act k (-u, -v, n); kc k = face of k (same in both frames).
Y = {sigma : kc o sigma = kc}. F_c = kc^-1(c). Omega_j = union of F_c for c >= j. For stages j = 0..4, d(list1)=+1, d(list2)=-1:
(1) forall A subset Omega_j with |A|=4, exists t1 in list1_j, t2 in list2_j, t2(t1(A)) = F_j [checked via the witness table].
(2) forall t in list_j, supp t subset Omega_j.
(3) forall element (t, D, P): P^-1 K^d P = t, P^-1 L^d P = D, D is a 4-cycle on a whole face (hence D in Y), and P is a word of
pieces f r f^-1 with r a slice of the row index and f a face word.
Consequence on the cube: processing row blocks one after another, each block running the two passes of each stage, every
inner orbit (u,v) with u, v in different blocks ends in Y, every other sticker returns exactly to where it was, so the
final colouring equals faceOf: the position is solved with phi = id."""

SA_CPP = r"""// SA for pair lists: fixed sizes m1 (T1 4-cycles), m2 (family FF, sets with <=2 wrong).
// Minimise uncovered 4-subsets A of [N]; t acts x->t(x); require t(A) in FF.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned int u32;
static int N;
static vector<int> rk; // mask->rank (N<=24): use hash map via vector of size 1<<N
static vector<u32> subs;
struct Cyc{int a,b,c,d;};
static inline int rankmask(u32 m){return rk[m];}
static inline u32 preimg(const Cyc&t,u32 S){
  // A=t^{-1}(S): x in A iff t(x) in S. t: a->b->c->d->a
  u32 A=S; 
  // clear support bits
  u32 sup=(1u<<t.a)|(1u<<t.b)|(1u<<t.c)|(1u<<t.d);
  A&=~sup;
  if(S>>t.b&1) A|=1u<<t.a;
  if(S>>t.c&1) A|=1u<<t.b;
  if(S>>t.d&1) A|=1u<<t.c;
  if(S>>t.a&1) A|=1u<<t.d;
  return A;
}
static mt19937_64 rng;
static inline int ri(int n){return (int)(rng()%n);}
Cyc randcyc(){int p[4];for(int i=0;i<4;i++){bool ok;do{ok=true;p[i]=ri(N);for(int j=0;j<i;j++)if(p[j]==p[i])ok=false;}while(!ok);}return {p[0],p[1],p[2],p[3]};}
int main(int argc,char**argv){
  N=atoi(argv[1]);int m1=atoi(argv[2]),m2=atoi(argv[3]);double tl=atof(argv[4]);long seed=atol(argv[5]);
  double T0=argc>6?atof(argv[6]):1.0, T1=argc>7?atof(argv[7]):0.1;
  rng.seed(seed);
  rk.assign(1u<<N,-1);
  for(u32 m=0;m<(1u<<N);m++) if(__builtin_popcount(m)==4){rk[m]=subs.size();subs.push_back(m);}
  int nA=subs.size();
  u32 Fm=0xF;
  vector<u32> cand; for(u32 s:subs) if(__builtin_popcount(s&~Fm)<=2) cand.push_back(s);
  vector<Cyc> T(m1); vector<u32> FF(m2);
  vector<int> cov(nA,0);
  for(auto&t:T)t=randcyc();
  { // init family distinct
    vector<u32> c=cand; shuffle(c.begin(),c.end(),rng); for(int i=0;i<m2;i++)FF[i]=c[i%c.size()]; }
  long unc=0;
  for(auto&t:T)for(u32 S:FF)cov[rk[preimg(t,S)]]++;
  for(int i=0;i<nA;i++)if(!cov[i])unc++;
  long best=unc; vector<Cyc> bT=T; vector<u32> bF=FF;
  auto t0=chrono::steady_clock::now(); long it=0; double temp=T0;
  while(true){
    if((it&0x3ff)==0){double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count(); if(el>tl||best==0)break; double f=el/tl; temp=T0*pow(T1/T0,f);}
    it++;
    long delta=0;
    if(ri(m1+m2)<m1){ // change t
      int i=ri(m1); Cyc old=T[i],nw=old;
      int r=ri(5);
      if(r==4) nw=randcyc();
      else { int v=ri(N); int*p[4]={&nw.a,&nw.b,&nw.c,&nw.d}; bool dup=false; for(int k=0;k<4;k++) if(*p[k]==v) dup=true; if(dup){ // swap positions
            int k1=ri(4),k2=ri(4); swap(*p[k1],*p[k2]); }
          else *p[r]=v; }
      for(u32 S:FF){int a=rk[preimg(old,S)]; if(--cov[a]==0)delta++;}
      for(u32 S:FF){int a=rk[preimg(nw,S)]; if(cov[a]++==0)delta--;}
      if(delta<=0|| (double)(rng()>>11)/(1ull<<53)<exp(-delta/temp)){T[i]=nw;unc+=delta;}
      else { for(u32 S:FF){int a=rk[preimg(nw,S)]; --cov[a];} for(u32 S:FF){int a=rk[preimg(old,S)]; cov[a]++;} }
    } else {
      int i=ri(m2); u32 old=FF[i],nw;
      if(ri(3)==0) nw=cand[ri(cand.size())];
      else { // swap one element
        int tries=0; do{ int out; do{out=ri(N);}while(!(old>>out&1)); int in; do{in=ri(N);}while(old>>in&1); nw=(old&~(1u<<out))|(1u<<in); }while(__builtin_popcount(nw&~Fm)>2&&++tries<20);
        if(__builtin_popcount(nw&~Fm)>2) continue;
      }
      if(nw==old) continue;
      for(auto&t:T){int a=rk[preimg(t,old)]; if(--cov[a]==0)delta++;}
      for(auto&t:T){int a=rk[preimg(t,nw)]; if(cov[a]++==0)delta--;}
      if(delta<=0|| (double)(rng()>>11)/(1ull<<53)<exp(-delta/temp)){FF[i]=nw;unc+=delta;}
      else { for(auto&t:T){int a=rk[preimg(t,nw)]; --cov[a];} for(auto&t:T){int a=rk[preimg(t,old)]; cov[a]++;} }
    }
    if(unc<best){best=unc;bT=T;bF=FF;}
  }
  printf("N=%d m1=%d m2=%d seed=%ld best_unc=%ld iters=%ld\n",N,m1,m2,seed,best,it);
  if(best==0){ printf("SOL %d %d %d\n",N,m1,m2); for(auto&t:bT)printf("%d %d %d %d\n",t.a,t.b,t.c,t.d); for(u32 s:bF)printf("%u\n",s);}
}
"""
DESCEND_CPP = r"""// Warm-start descent: repeatedly remove an element (from list chosen by mode) and repair by SA. 
// usage: descend N infile tl_total tl_repair seed mode outprefix [targetbal]
// mode 0: minimise product; mode 1: minimise max(m1,m2)  (balanced)
#include <bits/stdc++.h>
using namespace std;
typedef unsigned int u32;
static int N; static vector<int> rk; static vector<u32> subs;
struct Cyc{int a,b,c,d;};
static inline u32 preimg(const Cyc&t,u32 S){u32 sup=(1u<<t.a)|(1u<<t.b)|(1u<<t.c)|(1u<<t.d);u32 A=S&~sup;if(S>>t.b&1)A|=1u<<t.a;if(S>>t.c&1)A|=1u<<t.b;if(S>>t.d&1)A|=1u<<t.c;if(S>>t.a&1)A|=1u<<t.d;return A;}
static mt19937_64 rng; static inline int ri(int n){return (int)(rng()%n);}
Cyc randcyc(){int p[4];for(int i=0;i<4;i++){bool ok;do{ok=true;p[i]=ri(N);for(int j=0;j<i;j++)if(p[j]==p[i])ok=false;}while(!ok);}return {p[0],p[1],p[2],p[3]};}
vector<Cyc> T; vector<u32> FF; vector<int> cov; long unc; vector<u32> cand; u32 Fm=0xF;
void rebuild(){int nA=subs.size();cov.assign(nA,0);for(auto&t:T)for(u32 S:FF)cov[rk[preimg(t,S)]]++;unc=0;for(int i=0;i<nA;i++)if(!cov[i])unc++;}
bool repair(double tl,double T0,double T1){
  int m1=T.size(),m2=FF.size();
  auto t0=chrono::steady_clock::now();long it=0;double temp=T0;
  vector<Cyc> bT=T;vector<u32> bF=FF;long best=unc;
  while(true){
    if((it&0xff)==0){double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();if(el>tl)break;temp=T0*pow(T1/T0,el/tl);}
    it++;long delta=0;
    if(unc==0)return true;
    if(ri(m1+m2)<m1){int i=ri(m1);Cyc old=T[i],nw=old;int r=ri(5);
      if(r==4)nw=randcyc();else{int v=ri(N);int*p[4]={&nw.a,&nw.b,&nw.c,&nw.d};bool dup=false;for(int k=0;k<4;k++)if(*p[k]==v)dup=true;if(dup){int k1=ri(4),k2=ri(4);swap(*p[k1],*p[k2]);}else *p[r]=v;}
      for(u32 S:FF){int a=rk[preimg(old,S)];if(--cov[a]==0)delta++;}
      for(u32 S:FF){int a=rk[preimg(nw,S)];if(cov[a]++==0)delta--;}
      if(delta<=0||(double)(rng()>>11)/(1ull<<53)<exp(-delta/temp)){T[i]=nw;unc+=delta;}
      else{for(u32 S:FF){int a=rk[preimg(nw,S)];--cov[a];}for(u32 S:FF){int a=rk[preimg(old,S)];cov[a]++;}}
    }else{int i=ri(m2);u32 old=FF[i],nw;
      if(ri(3)==0)nw=cand[ri(cand.size())];
      else{int tries=0;do{int out;do{out=ri(N);}while(!(old>>out&1));int in;do{in=ri(N);}while(old>>in&1);nw=(old&~(1u<<out))|(1u<<in);}while(__builtin_popcount(nw&~Fm)>2&&++tries<20);if(__builtin_popcount(nw&~Fm)>2)continue;}
      if(nw==old)continue;
      for(auto&t:T){int a=rk[preimg(t,old)];if(--cov[a]==0)delta++;}
      for(auto&t:T){int a=rk[preimg(t,nw)];if(cov[a]++==0)delta--;}
      if(delta<=0||(double)(rng()>>11)/(1ull<<53)<exp(-delta/temp)){FF[i]=nw;unc+=delta;}
      else{for(auto&t:T){int a=rk[preimg(t,nw)];--cov[a];}for(auto&t:T){int a=rk[preimg(t,old)];cov[a]++;}}
    }
    if(unc<best){best=unc;bT=T;bF=FF;}
  }
  if(best==0){T=bT;FF=bF;rebuild();return true;}
  return false;
}
void save(const char*pref){char fn[256];sprintf(fn,"%s_%d_%d_%d.sol",pref,N,(int)T.size(),(int)FF.size());FILE*f=fopen(fn,"w");fprintf(f,"%d %d %d\n",N,(int)T.size(),(int)FF.size());for(auto&t:T)fprintf(f,"%d %d %d %d\n",t.a,t.b,t.c,t.d);for(u32 s:FF)fprintf(f,"%u\n",s);fclose(f);}
int main(int argc,char**argv){
  N=atoi(argv[1]);const char*in=argv[2];double tlT=atof(argv[3]),tlR=atof(argv[4]);rng.seed(atol(argv[5]));int mode=atoi(argv[6]);const char*pref=argv[7];
  rk.assign(1u<<N,-1);for(u32 m=0;m<(1u<<N);m++)if(__builtin_popcount(m)==4){rk[m]=subs.size();subs.push_back(m);}
  for(u32 s:subs)if(__builtin_popcount(s&~Fm)<=2)cand.push_back(s);
  FILE*f=fopen(in,"r");int n0,m1,m2;fscanf(f,"%d %d %d",&n0,&m1,&m2);T.resize(m1);FF.resize(m2);for(auto&t:T)fscanf(f,"%d %d %d %d",&t.a,&t.b,&t.c,&t.d);for(auto&s:FF)fscanf(f,"%u",&s);fclose(f);
  rebuild();printf("start %d %d unc %ld\n",m1,m2,unc);
  auto t0=chrono::steady_clock::now();double bestval=1e18;
  auto valf=[&](int a,int b){return mode==0?log2((double)a)+log2((double)b):max(a,b)+1e-3*min(a,b);};
  if(unc==0){bestval=valf(m1,m2);save(pref);}
  while(chrono::duration<double>(chrono::steady_clock::now()-t0).count()<tlT){
    vector<Cyc> sT=T;vector<u32> sF=FF;
    int a=T.size(),b=FF.size();
    bool remT;
    if(mode==1){remT=a>=b; if(a==b)remT=ri(2);}
    else {remT=ri(a+b)<(int)(a+b)*(1.0/2);}
    // choose element whose removal uncovers least; sample
    int bi=-1;long bl=1e18;
    if(remT){for(int i=0;i<(int)T.size();i++){long l=0;for(u32 S:FF){int x=rk[preimg(T[i],S)];if(cov[x]==1)l++;}l=l*4+ri(4);if(l<bl){bl=l;bi=i;}} T.erase(T.begin()+bi);}
    else{for(int i=0;i<(int)FF.size();i++){long l=0;for(auto&t:T){int x=rk[preimg(t,FF[i])];if(cov[x]==1)l++;}l=l*4+ri(4);if(l<bl){bl=l;bi=i;}} FF.erase(FF.begin()+bi);}
    rebuild();
    bool ok=repair(tlR,0.35,0.05);
    if(ok&&valf(T.size(),FF.size())<bestval-1e-9){bestval=valf(T.size(),FF.size());save(pref);printf("OK %d %d prod %ld bits %.3f\n",(int)T.size(),(int)FF.size(),(long)T.size()*(long)FF.size(),log2((double)T.size()*FF.size()));fflush(stdout);}
    if(!ok){ // revert, maybe add to the other list
      T=sT;FF=sF;rebuild();
      printf("fail at %d %d remT=%d\n",(int)T.size(),(int)FF.size(),remT);fflush(stdout);
      if(mode==1&&((int)T.size()!=(int)FF.size())){ } 
    }
  }
  printf("END best %.3f\n",bestval);
}
"""

def run_cpp(src, args):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "a.cpp"); e = os.path.join(d, "a")
        open(p, "w").write(src)
        subprocess.check_call(["g++", "-O2", "-w", "-o", e, p])
        subprocess.check_call([e] + args)

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--search":
        return run_cpp(SA_CPP, sys.argv[2:])
    if len(sys.argv) > 1 and sys.argv[1] == "--descend":
        return run_cpp(DESCEND_CPP, sys.argv[2:])
    TT = Templates()
    print("pieces", len(TT.plist), "extra", len(TT.extra), flush=True)
    schemes = {name: build_scheme(name, sols, TT) for name, sols in SOLUTIONS.items()}
    out = {"faces": [sorted(f) for f in FACE_ORDER], "K": list(KC), "L": list(LC), "pair_phases": 5,
           "log2_Z": math.log2(math.factorial(24) / 24 ** 6), "statement": STATEMENT, "schemes": schemes}
    json.dump(out, open(os.path.join(HERE, "chain_col.json"), "w"), separators=(",", ":"))
    for name, s in schemes.items():
        print(name, "B_sum_logs", s["B_sum_logs"], "limit", s["B_sum_logs"] / 4, "B_same_block", s["B_same_block"], "limit", s["B_same_block"] / 4)

if __name__ == "__main__":
    main()
