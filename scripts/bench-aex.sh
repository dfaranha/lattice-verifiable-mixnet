#!/bin/bash
# Benchmark the amortized exact proof (Pi_AEx) across a range of tau and compare
# with Table 4 of the paper, which reports (99.6 + 19.7) tau ms on a 4 GHz
# Skylake with tau = 1000.
#
#   scripts/bench-aex.sh [tau ...]
#
# tau must be a power of two (the interpolation nodes are the tau-th roots of
# unity). Defaults to 128 256 512 1024. Override the clock with GHZ=... and the
# repetition count with BENCH=... (fewer repetitions at large tau).
#
# This wants a lot of memory: roughly 11 GB at tau = 1024. Each size is skipped
# if the estimate exceeds what is available, so it is safe to pass a long list.

set -u
cd "$(dirname "$0")/.."

TAUS=${*:-"128 256 512 1024"}
GHZ=${GHZ:-4.0}
BENCH=${BENCH:-3}

# paper Table 4, per vote, in ms
PAPER_P=99.6
PAPER_V=19.7

# geometry, must match src/pismall.cpp and include/common.h
V=7          # WIDTH + 3
R=3          # HEIGHT + 2
N=4096       # DEGREE
ETA=325

avail_kb() { awk '/MemAvailable/{print $2}' /proc/meminfo; }

est_gb() { # tau -> estimated peak resident GB
  python3 -c "
tau=$1; V=$V; R=$R; N=$N
H   = tau*3*V*262144          # codewords, 4N symbols x 2 limbs
v   = 3*tau*V*N*(16+40)       # mpz_t structs plus one-limb allocations
s   = tau*V*65536             # witness polynomials
t   = tau*R*65536
res = 2*N*tau*8               # residue gather
print('%.2f' % ((H+v+s+t+res)/1e9))"
}

LOG=${LOG:-/tmp/bench-aex.log}
: > "$LOG"

if [ ! -f deps/libnfllib_static.a ]; then
  echo "error: deps/libnfllib_static.a is missing -- NFLlib has not been built here."
  echo "       mkdir -p deps && cd deps &&"
  echo "       cmake ../NFLlib -DCMAKE_BUILD_TYPE=Release -DNFL_OPTIMIZED=ON && make"
  exit 1
fi

echo "toolchain: $(${CXX:-g++} --version | head -1)"
echo "flint:     $(pkg-config --modversion flint 2>/dev/null || grep -m1 'define FLINT_VERSION' /usr/include/flint/flint.h 2>/dev/null || echo unknown)"
echo "build log: $LOG"
echo

printf '%-6s %-9s %-16s %-16s %-11s %-11s %-9s %s\n' \
  tau mem_GB prover_cycles verifier_cycles prover_ms/vote ver_ms/vote vs_paper_p vs_paper_v
printf '%.0s-' {1..104}; echo

for TAU in $TAUS; do
  if [ $(( TAU & (TAU - 1) )) -ne 0 ]; then
    printf '%-6s SKIP  not a power of two\n' "$TAU"; continue
  fi
  NEED=$(est_gb "$TAU")
  HAVE=$(python3 -c "print('%.2f' % ($(avail_kb)/1e6))")
  if python3 -c "import sys; sys.exit(0 if $NEED > $HAVE else 1)"; then
    printf '%-6s %-9s SKIP  needs more than the %s GB available\n' "$TAU" "$NEED" "$HAVE"
    continue
  fi

  make clean >>"$LOG" 2>&1
  echo "=== build tau=$TAU ===" >>"$LOG"
  if ! make CONFIG="-DTAU=$TAU -DBENCH=$BENCH" pismall >>"$LOG" 2>&1; then
    printf '%-6s %-9s BUILD FAILED -- first errors:\n' "$TAU" "$NEED"
    grep -iE 'error|undefined reference|No such file' "$LOG" | tail -8 | sed 's/^/        /'
    echo "        (full log: $LOG)"
    continue
  fi

  OUT=$(./pismall 2>/dev/null)
  if ! grep -q 'AEX proof is consistent\.*.*PASS' <<<"$(sed 's/\x1b\[[0-9;]*m//g' <<<"$OUT")"; then
    printf '%-6s %-9s TESTS FAILED -- timings not reported\n' "$TAU" "$NEED"; continue
  fi
  P=$(sed 's/\x1b\[[0-9;]*m//g' <<<"$OUT" | awk '/pismall_prover/{print $(NF-1)}')
  W=$(sed 's/\x1b\[[0-9;]*m//g' <<<"$OUT" | awk '/pismall_verifier/{print $(NF-1)}')
  [ -z "${P:-}" ] && { printf '%-6s %-9s NO TIMING\n' "$TAU" "$NEED"; continue; }

  python3 -c "
tau=$TAU; p=$P; w=$W; ghz=$GHZ
pm = p/(ghz*1e6)/tau      # ms per vote
wm = w/(ghz*1e6)/tau
print('%-6d %-9s %-16d %-16d %-11.2f %-11.2f %-9.2f %.2f' %
      (tau, '$NEED', p, w, pm, wm, pm/$PAPER_P, wm/$PAPER_V))"
done

echo
echo "paper Table 4 (tau = 1000, 4 GHz): prover ${PAPER_P} ms/vote, verifier ${PAPER_V} ms/vote"
echo "vs_paper columns are ratios; > 1 means slower than the paper reports."
echo
echo "Note: the paper's figure was measured on an implementation without the"
echo "Merkle commitment, without the two encoding identities, and with v_{i,j}"
echo "that do not satisfy step 3, so this compares a complete proof against an"
echo "incomplete one."
