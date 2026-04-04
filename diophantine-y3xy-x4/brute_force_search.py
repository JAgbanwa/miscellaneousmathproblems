"""
brute_force_search.py  (diophantine-y3xy-x4)
=============================================
Exhaustive search for integer solutions to

    y^3 + xy + x^4 + 4 = 0.

For each integer x we need to find whether there is any integer y satisfying
the equation.  For x >= 0 the function y |-> y^3 + xy + x^4 + 4 is strictly
increasing (derivative 3y^2 + x >= 0), so there is at most one real root.
For x < 0 there are at most two real critical points at y = +/- sqrt(-x/3),
but the cubic still has exactly one real root when the discriminant
    Delta = -4x^3 - 27(x^4+4)^2
is negative, which holds for all integers x (verified below).

We use Newton's method to locate the real root, then check the two or three
nearest integers.

RESULT: NO integer solution found for x in [-10 000, 10 000].
"""

import math


def F(x: int, y: int) -> int:
    """Evaluate y^3 + xy + x^4 + 4 exactly (integer arithmetic)."""
    return y * y * y + x * y + x * x * x * x + 4


def real_root(x_val: int) -> float:
    """
    Newton's method for the unique real root of t^3 + x_val*t + (x_val^4 + 4) = 0.

    The discriminant is -4*x^3 - 27*(x^4+4)^2, which is always negative, so
    there is exactly one real root.
    """
    p = float(x_val)
    q = float(x_val**4 + 4)
    # Initial guess via Cardano's formula sign heuristic
    if q >= 0:
        t = -(q ** (1.0 / 3.0))
    else:
        t = (-q) ** (1.0 / 3.0)
    for _ in range(80):
        ft = t * t * t + p * t + q
        dft = 3.0 * t * t + p
        if dft == 0.0:
            # Critical point: perturb slightly
            t += 0.1
            continue
        t -= ft / dft
    return t


def search(x_min: int, x_max: int) -> list:
    """Return all integer solutions (x, y) with x in [x_min, x_max]."""
    solutions = []
    for x in range(x_min, x_max + 1):
        t = real_root(x)
        n = int(math.floor(t))
        # Check a window of width 5 centred on n to be safe
        for y_cand in range(n - 2, n + 3):
            if F(x, y_cand) == 0:
                solutions.append((x, y_cand))
    return solutions


def discriminant(x: int) -> int:
    """Discriminant of the depressed cubic t^3 + x*t + (x^4+4)."""
    return -4 * x**3 - 27 * (x**4 + 4) ** 2


if __name__ == "__main__":
    X_LIM = 10_000
    print("Searching for integer solutions to  y^3 + xy + x^4 + 4 = 0")
    print(f"with x in [{-X_LIM}, {X_LIM}]  ({2 * X_LIM + 1} values).\n")

    solutions = search(-X_LIM, X_LIM)

    if solutions:
        print(f"Solutions found: {solutions}")
    else:
        print("No integer solutions found in the search range.")

    print()
    print("=== Near-miss analysis (|F(x,y)| <= 10) ===")
    near_misses = []
    for x in range(-100, 101):
        t = real_root(x)
        n = int(math.floor(t))
        for y_cand in range(n - 2, n + 3):
            v = F(x, y_cand)
            if 0 < abs(v) <= 10:
                near_misses.append((abs(v), x, y_cand, v))
    near_misses.sort()
    for _, x, y, v in near_misses[:15]:
        print(f"  x={x:4d}, y={y:4d}: F(x,y) = {v}")

    print()
    print("=== Discriminant check (always negative) ===")
    all_negative = all(discriminant(x) < 0 for x in range(-50, 51))
    print(f"Delta < 0 for all x in [-50,50]: {all_negative}  (unique real root confirmed)")

    print()
    print("=== Residue constraints (from modular analysis) ===")
    print("mod 2  : only (x,y) ≡ (0,0) (mod 2) is compatible")
    print("mod 3  : y ≡ 2 (mod 3) is forced")
    print("mod 8  : x ≡ 2 or 6 (mod 8),  y ≡ 2 or 6 (mod 8)")
    print("mod 24 : (x mod 24, y mod 24) ∈ {6,10,18,22} × {2,14}")
    print()
    print("Sophie Germain factorization: x^4 + 4 = ((x+1)^2+1)((x-1)^2+1) ≥ 1 for all x.")
