from math import sqrt
vname = "lvm_ballot"
# The voter's proof of a well-formed ballot (src/ballot.c), for LaZer's
# lin-codegen.sage. The statement over R_q, q the BGV modulus (two 44-bit
# primes) and degree 4096, with p = 2:
#
#   u = a r + 2 e1
#   v = b r + 2 e2 + m
#   0 = m - u'
#
# with witness w = (r, e1, e2, m, u'): (r, e1, e2) short, m binary and
# ||u'|| <= 1, so that m is X^j or 0, a vote for one candidate or none.
deg   = 4096
mod   = 309483570976529976228052993
dim   = (3, 5)
wpart = [[0, 1, 2], [3], [4]]
# ZO_dist: each coefficient of r, e1, e2 is +-1 with probability 1/2, so
# ||(r, e1, e2)||^2 is about 6144, far below 1.2^2 * 6144.
wl2   = [1.2*sqrt(3*4096*0.5), 0, 1]
wbin  = [0, 1, 0]
wlinf = 1
# LaZer's default target, a root Hermite factor of 1.0044, is about 102 bits
# core-SVP (lattice-estimator); 1.0036 gives 128 or more.
DELTA_TARGET = 1.0036
