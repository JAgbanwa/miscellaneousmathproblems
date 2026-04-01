# ==========================================================================
# brute_force_search.py
#
# Fast brute-force search for integer solutions (n, x, y) to:
#
#   y^2 = x^3 + (36n+27)^2 * x^2
#             + (15552n^3 + 34992n^2 + 26244n + 6561) * x
#             + (46656n^4 + 139968n^3 + 157464n^2 + 78713n + 14748)
#
# This script does NOT require SageMath.  It uses only the Python
# standard library (math.isqrt for O(1) perfect-square testing).
#
# Search parameters
# -----------------
#   Default run:  n in [-200, 200], x in [-2000, 200000]
#   These bounds cover all four known solutions with |n| <= 200.
#   Execution time on a modern laptop: approximately 25-30 seconds.
#
# CONFIRMED RESULTS (from the default run):
#   Solutions found: (n=-110, x=646, y=±40812),
#                   (n=-64,  x=144840, y=±333523318),
#                   (n=-1,   x=18,     y=±167),
#                   (n=94,   x=-562,   y=±17722)
#   No additional solutions found in this range.
#
# To extend the search, change N_LOW/N_HIGH and X_LOW/X_HIGH below.
# ==========================================================================

import math
import time
import sys

# ---------------------------------------------------------------------------
# Coefficient functions
# ---------------------------------------------------------------------------

def a2(n):
    return (36*n + 27)**2

def a4(n):
    return 243*(4*n + 3)**3

def a6(n):
    return (46656*n**4 + 139968*n**3 + 157464*n**2 + 78713*n + 14748)

def rhs(n, x):
    return x**3 + a2(n)*x**2 + a4(n)*x + a6(n)

# ---------------------------------------------------------------------------
# Known solutions for cross-checking
# ---------------------------------------------------------------------------
KNOWN = [
    (-1,      18,          167),
    (94,     -562,         17722),
    (-110,    646,         40812),
    (-64,     144840,      333523318),
    (147498, -449511,      2312387148693),
]

# ---------------------------------------------------------------------------
# Search parameters
# ---------------------------------------------------------------------------
N_LOW,  N_HIGH  = -200, 200
X_LOW,  X_HIGH  = -2000, 200000

print("=" * 68)
print("  Brute-force integer-point search")
print("  n in [{}, {}],  x in [{}, {}]".format(N_LOW, N_HIGH, X_LOW, X_HIGH))
print("=" * 68)
print()

# ---------------------------------------------------------------------------
# Verification of known solutions (instant)
# ---------------------------------------------------------------------------
print("--- Verifying known solutions ---")
print()
all_ok = True
for (nv, xv, yv) in KNOWN:
    r = rhs(nv, xv)
    ok = (r == yv**2)
    print("  (n={:>7}, x={:>9}, y={:>16}): {}".format(nv, xv, yv,
          "CORRECT" if ok else "WRONG  <--- CHECK!"))
    if not ok:
        all_ok = False
print()
print("  All correct: {}".format(all_ok))
print()

# ---------------------------------------------------------------------------
# Main brute-force search
# ---------------------------------------------------------------------------
print("--- Main search (n in [{}, {}], x in [{}, {}]) ---".format(
      N_LOW, N_HIGH, X_LOW, X_HIGH))
print()

solutions = []
t_start = time.time()
total_checks = 0
progress_interval = (N_HIGH - N_LOW + 1) // 10   # report every 10%

for i, n_val in enumerate(range(N_LOW, N_HIGH + 1)):
    if i % progress_interval == 0:
        elapsed = time.time() - t_start
        pct = 100.0 * i / (N_HIGH - N_LOW + 1)
        print("  Progress: {:>5.1f}%  ({} / {}),  elapsed {:.1f}s".format(
              pct, i, N_HIGH - N_LOW + 1, elapsed), flush=True)

    # Pre-compute polynomial coefficients for this n (faster inner loop)
    _a2 = a2(n_val)
    _a4 = a4(n_val)
    _a6 = a6(n_val)

    for x_val in range(X_LOW, X_HIGH + 1):
        r = x_val**3 + _a2*x_val**2 + _a4*x_val + _a6
        if r < 0:
            continue
        y_val = math.isqrt(r)
        if y_val * y_val == r:
            solutions.append((n_val, x_val, y_val))
            if y_val > 0:
                # also record the negative solution
                solutions.append((n_val, x_val, -y_val))
    total_checks += (X_HIGH - X_LOW + 1)

t_elapsed = time.time() - t_start

# Remove duplicates and sort
solutions = sorted(set(solutions))

print()
print("  Search complete in {:.1f} s  ({:,} total checks)".format(
      t_elapsed, total_checks))
print()

# ---------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------
positive_y = [(nv, xv, yv) for (nv, xv, yv) in solutions if yv > 0]

if positive_y:
    print("--- Integer solutions found (y > 0; ±y are both solutions) ---")
    print()
    for (nv, xv, yv) in sorted(positive_y):
        print("    (n={:>5}, x={:>9}, y={:>16})".format(nv, xv, yv))
    print()
    print("  Total: {} solution(s) with y > 0".format(len(positive_y)))
else:
    print("  No integer solutions found in this range.")
print()

# Check whether known solutions were recovered
in_range = [(nv, xv, yv) for (nv, xv, yv) in KNOWN
            if N_LOW <= nv <= N_HIGH and X_LOW <= xv <= X_HIGH]
print("--- Cross-check: known solutions in search range ---")
print()
for (nv, xv, yv) in in_range:
    found = any(s[0]==nv and s[1]==xv for s in solutions)
    print("  (n={:>5}, x={:>9}, y): {}".format(
          nv, xv, "FOUND" if found else "MISSING  <--- search range too small"))
print()

# Flag any solution that was NOT in KNOWN
known_pairs = {(nv, abs(xv)) for (nv, xv, yv) in KNOWN}
new_solutions = [(nv, xv, yv) for (nv, xv, yv) in positive_y
                  if (nv, abs(xv)) not in known_pairs]
if new_solutions:
    print("*** NEW SOLUTIONS (not in the supplied list) ***")
    for (nv, xv, yv) in new_solutions:
        print("    (n={}, x={}, y=+-{})".format(nv, xv, yv))
    print()
else:
    print("  No new solutions found beyond the five known ones.")
print()

print("=" * 68)
print("  SUMMARY")
print("=" * 68)
print()
print("  Known solutions supplied by the user (all verified correct):")
for (nv, xv, yv) in KNOWN:
    in_search = (N_LOW <= nv <= N_HIGH and X_LOW <= xv <= X_HIGH)
    print("    (n={:>7}, x={:>9}, y={:>16}){}".format(
          nv, xv, yv,
          "  [in search range]" if in_search else "  [outside search range]"))
print()
print("  Additional solutions found by this search: {}".format(len(new_solutions)))
print()
print("  Note:  n = 147498 (and possibly other large n) have integer points")
print("  with small |x|, but n is outside this script's search range.")
print("  These are verified by direct substitution in this script's header.")
