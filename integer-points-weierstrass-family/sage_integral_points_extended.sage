# ==========================================================================
# sage_integral_points_extended.sage
#
# For each n in a given range, construct the elliptic curve E_n:
#
#   y^2 = x^3 + (36n+27)^2 * x^2
#             + 243*(4n+3)^3 * x
#             + (46656n^4 + 139968n^3 + 157464n^2 + 78713n + 14748)
#
# and call E_n.integral_points(both_signs=True, proof=False) to find
# ALL integer points.  Any point with |x| <= 10^8 is reported.
#
# Run with:
#   sage sage_integral_points_extended.sage
#
# Running time: roughly 1-60 seconds per curve; expect a few hours for
# the full n in [-1000, 1000] range, considerably less for [-200, 200].
#
# To run a specific sub-range (e.g., for parallelism), set N_LOW / N_HIGH
# via environment variables:
#   N_LOW=-500 N_HIGH=0 sage sage_integral_points_extended.sage
# ==========================================================================

import os, sys, time, signal

# -------------------------------------------------------------------------
# Range (override with env variables N_LOW / N_HIGH)
# -------------------------------------------------------------------------
N_LOW  = int(os.environ.get("N_LOW",  "-1000"))
N_HIGH = int(os.environ.get("N_HIGH",  "1000"))
X_LIMIT = int(os.environ.get("X_LIMIT", "100000000"))   # 10^8
TIMEOUT = int(os.environ.get("TIMEOUT", "120"))         # seconds per curve

print("=" * 68)
print("  SageMath integral_points() search")
print("  n in [{}, {}],  |x| <= {}".format(N_LOW, N_HIGH, X_LIMIT))
print("  Per-curve timeout: {}s".format(TIMEOUT))
print("=" * 68)
sys.stdout.flush()

# -------------------------------------------------------------------------
# Timeout handler
# -------------------------------------------------------------------------
class SageTimeout(Exception):
    pass

def _timeout_handler(signum, frame):
    raise SageTimeout("integral_points() exceeded {}s".format(TIMEOUT))

# -------------------------------------------------------------------------
# Coefficient helpers
# -------------------------------------------------------------------------
def a6_coeff(n):
    return 46656*n^4 + 139968*n^3 + 157464*n^2 + 78713*n + 14748

# -------------------------------------------------------------------------
# Known solutions for cross-check
# -------------------------------------------------------------------------
KNOWN = {
    (-1,      18,          167),
    (-1,      18,         -167),
    (94,     -562,        17722),
    (94,     -562,       -17722),
    (-110,    646,         40812),
    (-110,    646,        -40812),
    (-64,     144840,      333523318),
    (-64,     144840,     -333523318),
    (147498, -449511,  2312387148693),
    (147498, -449511, -2312387148693),
}

all_solutions = []
timeout_count = 0
error_count = 0

t_total = time.time()

for n_val in range(N_LOW, N_HIGH + 1):
    a2_c = (36*n_val + 27)^2
    a4_c = 243*(4*n_val + 3)^3
    a6_c = a6_coeff(n_val)

    try:
        E = EllipticCurve([0, a2_c, 0, a4_c, a6_c])
        t0 = time.time()

        # Enforce per-curve timeout via SIGALRM
        signal.signal(signal.SIGALRM, _timeout_handler)
        signal.alarm(TIMEOUT)
        try:
            pts = E.integral_points(both_signs=True)
        finally:
            signal.alarm(0)

        elapsed = time.time() - t0

        found_here = []
        for P in pts:
            xv = Integer(P[0])
            yv = Integer(P[1])
            if abs(xv) <= X_LIMIT:
                found_here.append((int(n_val), int(xv), int(yv)))

        # Only print lines where a solution was found, or every 50 curves
        if found_here:
            for sol in found_here:
                all_solutions.append(sol)
                marker = " <-- KNOWN" if (sol[0], sol[1], sol[2]) in KNOWN or \
                                          (sol[0], sol[1], -sol[2]) in KNOWN else " <-- NEW!"
                print("  SOLUTION: (n={:>8}, x={:>12}, y={:>22})  [t={:.2f}s]{}".format(
                      sol[0], sol[1], sol[2], elapsed, marker))
                sys.stdout.flush()
        elif n_val % 50 == 0:
            t_run = time.time() - t_total
            print("  n={:>6},  |pts|={},  t_curve={:.2f}s,  t_total={:.0f}s".format(
                  n_val, len(pts), elapsed, t_run))
            sys.stdout.flush()

    except SageTimeout:
        timeout_count += 1
        t_run = time.time() - t_total
        print("  n={:>6},  TIMEOUT (>{}s),  t_total={:.0f}s".format(n_val, TIMEOUT, t_run))
        sys.stdout.flush()
    except KeyboardInterrupt:
        print("\nInterrupted at n={}".format(n_val))
        break
    except Exception as e:
        error_count += 1
        if error_count <= 20:
            print("  ERROR at n={}: {}".format(n_val, e))
            sys.stdout.flush()

# -------------------------------------------------------------------------
# Summary
# -------------------------------------------------------------------------
print()
print("=" * 68)
print("  Search complete.")
print("  Total time: {:.1f}s".format(time.time() - t_total))
print("  Solutions found: {}".format(len(all_solutions)))
print("  Timed-out curves: {}".format(timeout_count))
print("  Errors: {}".format(error_count))
print()
print("  All solutions (|x| <= {}):".format(X_LIMIT))
for sol in sorted(set(all_solutions)):
    n_v, x_v, y_v = sol
    marker = "(known)" if (n_v, x_v, y_v) in KNOWN or (n_v, x_v, -y_v) in KNOWN else "*** NEW ***"
    print("    (n={:>8}, x={:>12}, y={:>22})  {}".format(n_v, x_v, y_v, marker))
print("=" * 68)
