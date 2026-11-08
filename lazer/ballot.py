from math import sqrt
vname = "lvm_ballot"
# The voter's proof of a well-formed ballot (src/ballot_proof.c), for LaZer's
# lin-codegen.sage, stated over LaZer's own ring R_64 = Z_q[Y]/(Y^64 + 1), q the
# BGV modulus (the prime 2^88 - 25 2^16 + 1). R_q of degree 4096 is
# R_64[X]/(X^64 - Y), an element a being sum_k X^k a_k(Y); a vote for candidate
# j is X^(64 j) = Y^j, in piece 0 alone. With p = 2 and witness
# w = (r_0..r_63, e1_0..e1_63, e2_0..e2_63, m, m', u'):
#
#   u_k = (a r)_k + 2 e1_k                   for k < 64
#   v_k = (b r)_k + 2 e2_k + [k = 0] m       for k < 64
#   0   = m - u'
#   0   = Y^(64 - NCAND) m - m'
#
# with (r, e1, e2) short, m and m' binary and ||u'|| <= 1, so that m is Y^j or
# 0, a vote for one candidate or none. The last row bounds j: R_64 is
# negacyclic, so Y^(64 - NCAND) Y^j is Y^(64 - NCAND + j), binary, when
# j < NCAND, and -Y^(j - NCAND), not binary, when j >= NCAND. NCAND is a
# coefficient of A, set at run time; the parameters here do not depend on it.
deg   = 64
mod   = 309485009821345068723142657
dim   = (130, 195)
wpart = [list(range(192)), [192, 193], [194]]
# ZO_dist: each coefficient of r, e1, e2 is +-1 with probability 1/2, so
# ||(r, e1, e2)||^2 is about 6144, far below 1.2^2 * 6144.
wl2   = [1.2*sqrt(3*4096*0.5), 0, 1]
wbin  = [0, 1, 0]
wlinf = 1
# LaZer's default target, a root Hermite factor of 1.0044, is about 102 bits
# core-SVP (lattice-estimator); 1.0036 gives 128 or more.
DELTA_TARGET = 1.0036
