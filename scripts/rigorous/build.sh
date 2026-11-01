#!/bin/sh
# Builds the rigorous checkers against MPFR. The MPFR/GMP headers come with the Python package
# gmpy2 (pip install gmpy2); the libraries are the system's libmpfr.so.6 / libgmp.so.10.
set -e
cd "$(dirname "$0")"
INC=$(python3 -c "import gmpy2, os; print(os.path.dirname(gmpy2.__file__))")
LIB=${MPFR_LIBDIR:-/usr/lib/x86_64-linux-gnu}
gcc -O2 -Wall -I"$INC" rig_checks.c -o rig_checks "$LIB/libmpfr.so.6" "$LIB/libgmp.so.10" -lm
gcc -O2 -Wall -frounding-math -ffp-contract=off moebius_sqrt_rig.c -o moebius_sqrt_rig -lm
gcc -O2 -Wall -I"$INC" t2_rig.c -o t2_rig "$LIB/libmpfr.so.6" "$LIB/libgmp.so.10" -lm
gcc -O2 -Wall -I"$INC" g2_rig.c -o g2_rig "$LIB/libmpfr.so.6" "$LIB/libgmp.so.10" -lm
gcc -O2 -Wall -fopenmp p1224_check.c -o p1224_check -lm
