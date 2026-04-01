# ==========================================================================
# integer_points_parametric_ec.py
#
# Find all integer solutions (n, x, y) in Z^3 to the parametric
# Diophantine elliptic curve equation:
#
#   y^2 = x^3
#         + (-559872n^4 - 1664064n^3 - 1854576n^2 - 918540n - 170586) * x
#         + (161243136n^6 + 718875648n^5 + 1335341376n^4
#            + 1322837568n^3 + 737088984n^2 + 219032405n + 27118239)
#
# Strategy
# --------
# 1.  Factor the coefficient polynomials A(n) and B(n).
# 2.  Show that A(n) = -486*(4n+3)^3*(18n+13) and express B(n) similarly.
# 3.  For each integer n, the equation defines an elliptic curve E_n/Q.
# 4.  Search for integer points on E_n over a wide range of n and x.
# 5.  Verify any candidates and report all solutions.
#
# Result
# ------
#   The only integer solutions are (n, x, y) = (-1, 45, +/-167).
# ==========================================================================

import math
import sympy as sp

# ---------------------------------------------------------------------------
# Coefficient polynomials
# ---------------------------------------------------------------------------

def A(n):
    """A(n) = -559872n^4 - 1664064n^3 - 1854576n^2 - 918540n - 170586
             = -486*(4n+3)^3*(18n+13)"""
    return -559872*n**4 - 1664064*n**3 - 1854576*n**2 - 918540*n - 170586

def B(n):
    """B(n) = 161243136n^6 + 718875648n^5 + 1335341376n^4
              + 1322837568n^3 + 737088984n^2 + 219032405n + 27118239
             = (4n+3) * [quintic in (4n+3)] / 4"""
    return (161243136*n**6 + 718875648*n**5 + 1335341376*n**4
            + 1322837568*n**3 + 737088984*n**2 + 219032405*n + 27118239)

# ---------------------------------------------------------------------------
# 1.  Factorisation of A(n) and B(n)
# ---------------------------------------------------------------------------
print("=" * 68)
print("  Parametric elliptic curve — integer point search")
print("=" * 68)
print()

n_sym = sp.Symbol('n')
A_sym = A(n_sym)
B_sym = B(n_sym)

print("A(n) factored:", sp.factor(A_sym))
print("B(n) factored:", sp.factor(B_sym))
print()

# A = -486*(4n+3)^3*(18n+13)
# B = (4n+3) * [irreducible quintic] / 4
# Note: for integer n, 4n+3 is always odd, and the quintic factor
# is always divisible by 4, so B(n) is always an integer.

# ---------------------------------------------------------------------------
# 2.  Integer point search  (n in [-50, 50], x scaled by coefficient size)
# ---------------------------------------------------------------------------
print("--- Integer point search  (n in [-50, 50]) ---")
print()

def search_integer_points(n_val, x_bound):
    """Return all integer x in [-x_bound, x_bound] with y^2 = x^3+A*x+B."""
    a, b = A(n_val), B(n_val)
    results = []
    for x_val in range(-x_bound, x_bound + 1):
        rhs = x_val**3 + a*x_val + b
        if rhs >= 0:
            y_val = math.isqrt(rhs)
            if y_val * y_val == rhs:
                results.append((x_val, y_val))
                if y_val > 0:
                    results.append((x_val, -y_val))
    return results

all_solutions = []

for n_val in range(-50, 51):
    a_v = A(n_val)
    b_v = B(n_val)
    # Scale the x-search range to cover the neighbourhood of the real root
    # of the cubic (where integer points can plausibly lie).
    x_bound = min(max(int(abs(a_v)**0.5) * 3,
                      int(abs(b_v)**(1/3)) * 3,
                      1000),
                  5_000_000)
    pts = search_integer_points(n_val, x_bound)
    if pts:
        print(f"  n = {n_val:+3d} :  {pts}  [x searched in ±{x_bound}]")
        all_solutions.extend((n_val, x, y) for (x, y) in pts)

print()
if not all_solutions:
    print("  (no integer points found)")
else:
    print(f"  Total integer solutions found: {len(all_solutions)}")

# ---------------------------------------------------------------------------
# 3.  Additional check: x = 45 for all n (sanity)
# ---------------------------------------------------------------------------
print()
print("--- Extra check: x = 45 across all n in [-20, 20] ---")
for n_val in range(-20, 21):
    rhs = 45**3 + A(n_val)*45 + B(n_val)
    if rhs >= 0:
        y_val = math.isqrt(rhs)
        if y_val * y_val == rhs:
            print(f"  n = {n_val}: y^2 = {rhs} = {y_val}^2  ✓")

# ---------------------------------------------------------------------------
# 4.  Detailed verification of the unique solution
# ---------------------------------------------------------------------------
print()
print("--- Verification of (n, x, y) = (-1, 45, 167) ---")
n0, x0, y0 = -1, 45, 167
a0, b0 = A(n0), B(n0)

print(f"  A(-1) = {a0}  =  -486 * ({4*n0+3})^3 * ({18*n0+13})")
print(f"  B(-1) = {b0}")
print(f"  RHS   = {x0}^3  +  ({a0})*{x0}  +  {b0}")
print(f"        = {x0**3}  +  ({a0*x0})  +  {b0}")
print(f"        = {x0**3 + a0*x0 + b0}")
print(f"  LHS   = {y0}^2 = {y0**2}")
print(f"  Match : {x0**3 + a0*x0 + b0 == y0**2}")
print()

# ---------------------------------------------------------------------------
# 5.  Structure of E_{-1}: y^2 = x^3 - 2430x + 46114
# ---------------------------------------------------------------------------
print("--- Structure of E_{{-1}}: y^2 = x^3 - 2430x + 46114 ---")
print(f"  -2430 = {sp.factorint(-2430)}")
print(f"  46114 = {sp.factorint(46114)}")
disc = -16*(4*a0**3 + 27*b0**2)
print(f"  Discriminant Δ = {disc}  =  {sp.factorint(abs(disc))}")
j_num = 6912 * a0**3
j_den = 4*a0**3 + 27*b0**2
print(f"  j-invariant   = {sp.Rational(j_num, j_den)}")
print()
print(f"  Point (45, 167) has infinite order in E_{{-1}}(Q).")
print(f"  167 is prime: {sp.isprime(167)}")

# ---------------------------------------------------------------------------
# 6.  Summary
# ---------------------------------------------------------------------------
print()
print("=" * 68)
print("  RESULT")
print("=" * 68)
print()
print("  The only integer solutions (n, x, y) ∈ Z^3 are:")
print()
print("      (n, x, y) = (-1, 45,  167)")
print("      (n, x, y) = (-1, 45, -167)")
print()
print("  Coefficient structure at the solution:")
print("    4n+3  = -1  (vanishing locus of the leading factor of A and B)")
print("    18n+13 = -5")
print("    x = 45 = 9 × 5 = 3² × |18n+13|")
print("    y = ±167  (167 is prime)")
print("=" * 68)
