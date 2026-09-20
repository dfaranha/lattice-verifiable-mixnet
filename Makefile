CPP      = g++

# NFLlib predates C++20 and uses std::allocator<void>::const_pointer, which was
# removed in that standard, so the language level has to be pinned. The GNU
# dialect is required for the `Q` suffix on __float128 literals in param.h.
STD      = -std=gnu++17

# A params::poly_q is 64 KiB, so it is very easy to write a function whose
# locals silently overflow the stack. Fail loudly instead: 4 MiB is half the
# usual default limit, and every function here is well under it.
WARN     = -Wall -Wframe-larger-than=4194304
OPT      = -O3 -march=native -mtune=native -flto
INCLUDE  = -I NFLlib/include/ -I NFLlib/include/nfl -I NFLlib/include/nfl/prng -I include
DEFINE   = -DNFL_OPTIMIZED=ON -DNTT_AVX2
# Extra defines for a build, e.g. make CONFIG="-DTAU=10 -DNTI=8" to shrink the
# proofs enough to run them on a machine without tens of gigabytes of RAM.
CONFIG   =
CFLAGS   = $(STD) $(OPT) $(WARN) -ggdb $(INCLUDE) $(DEFINE) $(CONFIG) -MMD -MP

LIBS     = deps/libnfllib_static.a -lgmp -lmpfr -lquadmath
# Only pismall uses FLINT, for GR(q,2) scalar arithmetic and for the dense
# polynomials over Z_q that are not in the NTT domain. Everything else works
# through NFLlib, so linking it everywhere only obscured which binary actually
# depends on it.
FLINT    = -L deps/ -lflint

OBJ      = obj
BIN      = bdlop bgv shuffle pismall pibnd

BLAKE3_SRC = src/blake3/blake3.c src/blake3/blake3_dispatch.c \
             src/blake3/blake3_portable.c \
             src/blake3/blake3_sse2_x86-64_unix.S \
             src/blake3/blake3_sse41_x86-64_unix.S \
             src/blake3/blake3_avx2_x86-64_unix.S \
             src/blake3/blake3_avx512_x86-64_unix.S
BLAKE3   = $(OBJ)/blake3.o
COMMON   = $(OBJ)/test.o $(OBJ)/bench.o $(OBJ)/cpucycles.o

.PHONY: all clean
.SECONDARY:

all: $(BIN)

$(OBJ):
	mkdir -p $(OBJ)

# Support code, compiled once and shared by every binary.
$(OBJ)/%.o: src/%.c | $(OBJ)
	$(CPP) $(CFLAGS) -c $< -o $@

$(OBJ)/%.o: src/%.cpp | $(OBJ)
	$(CPP) $(CFLAGS) -c $< -o $@

# BLAKE3 is bundled as a mix of C and assembly; keep it in a single object.
$(BLAKE3): $(BLAKE3_SRC) | $(OBJ)
	$(CPP) $(CFLAGS) -r -nostdlib $(BLAKE3_SRC) -o $@

# pismall commits to SIZE=3 messages, every other binary to the default SIZE.
# The two configurations must not share an object file, or whichever target is
# built last silently links the wrong one.
$(OBJ)/bdlop-size3.o: src/bdlop.cpp | $(OBJ)
	$(CPP) $(CFLAGS) -DSIZE=3 -c $< -o $@

bdlop: src/bdlop.cpp $(OBJ)/bgv.o $(COMMON)
	$(CPP) $(CFLAGS) -DMAIN src/bdlop.cpp $(OBJ)/bgv.o $(COMMON) -o $@ $(LIBS)

bgv: src/bgv.cpp $(COMMON)
	$(CPP) $(CFLAGS) -DMAIN src/bgv.cpp $(COMMON) -o $@ $(LIBS)

shuffle: src/shuffle.cpp $(OBJ)/bdlop.o $(OBJ)/sample_z_small.o $(COMMON) $(BLAKE3)
	$(CPP) $(CFLAGS) -DMAIN src/shuffle.cpp $(OBJ)/bdlop.o \
		$(OBJ)/sample_z_small.o $(COMMON) $(BLAKE3) -o $@ $(LIBS)

pismall: src/pismall.cpp $(OBJ)/bdlop-size3.o $(COMMON) $(BLAKE3)
	$(CPP) $(CFLAGS) -DSIZE=3 -DMAIN src/pismall.cpp \
		$(OBJ)/bdlop-size3.o $(COMMON) $(BLAKE3) -o $@ $(LIBS) $(FLINT)

pibnd: src/pibnd.cpp $(OBJ)/sample_z_small.o $(OBJ)/sample_z_large.o $(COMMON) $(BLAKE3)
	$(CPP) $(CFLAGS) -DMAIN src/pibnd.cpp $(OBJ)/sample_z_small.o \
		$(OBJ)/sample_z_large.o $(COMMON) $(BLAKE3) -o $@ $(LIBS)

clean:
	rm -rf $(OBJ) $(BIN)

-include $(wildcard $(OBJ)/*.d)
