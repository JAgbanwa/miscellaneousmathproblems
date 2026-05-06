#!/usr/bin/env python3
"""
brute_force_search.py  --  diophantine-z2plusy2zplux3mxm1
==========================================================
Exhaustive integer search for solutions (x, y, z) to:

    z^2 + y^2 * z + x^3 - x - 1 = 0

Key observations used to speed up the search:
  1. y appears only as y^2, so solutions come in pairs (x, y, z) and (x, -y, z).
     We search y >= 0 and note the symmetry.
  2. For fixed (x, y), the equation is a quadratic in z:
       z = (-y^2 ± sqrt(y^4 - 4*(x^3 - x - 1))) / 2
     An integer solution exists iff the discriminant D = y^4 - 4*(x^3-x-1)
     is a non-negative perfect square.
  3. Modular constraints (proved in solution.tex):
       - y must be divisible by 6 (or y = 0).
     This reduces the search over y by a factor of 6.

Usage:
    python3 brute_force_search.py              # default: |x|<=200, |y|<=600
    python3 brute_force_search.py 500 1200     # custom bounds

Output:
    Prints all solutions found, sorted by (x, |y|, z).
"""

import math
import sys


def search(x_bound: int = 200, y_bound: int = 600) -> list[tuple[int, int, int]]:
    """Return all solutions with |x| <= x_bound and 0 <= y <= y_bound."""
    solutions: list[tuple[int, int, int]] = []

    # --- y = 0 branch ---
    for x in range(-x_bound, x_bound + 1):
        val = -x**3 + x + 1   # need z^2 = val
        if val < 0:
            continue
        s = math.isqrt(val)
        if s * s == val:
            solutions.append((x, 0, s))
            if s != 0:
                solutions.append((x, 0, -s))

    # --- y != 0 branch  (y must be divisible by 6) ---
    for y in range(6, y_bound + 1, 6):
        y2 = y * y
        y4 = y2 * y2
        # Upper bound on |x| from disc >= 0:
        # y^4 >= 4(x^3 - x - 1)  approx  x <= (y^4/4)^{1/3} ~ y^{4/3}/1.587
        x_hi = min(x_bound, int(y ** (4 / 3) / 1.587) + 20)
        for x in range(-x_bound, x_hi + 1):
            disc = y4 - 4 * (x**3 - x - 1)
            if disc < 0:
                continue
            s = math.isqrt(disc)
            if s * s != disc:
                continue
            # z = (-y^2 ± s) / 2
            for w in (s, -s):
                num = -y2 + w
                if num % 2 != 0:
                    continue
                z = num // 2
                # Verify (should always pass by construction, but let's be safe)
                if z * z + y2 * z + x**3 - x - 1 == 0:
                    solutions.append((x, y, z))
                    solutions.append((x, -y, z))   # symmetric solution

    # Deduplicate and sort
    solutions = sorted(set(solutions))
    return solutions


def main() -> None:
    args = sys.argv[1:]
    x_bound = int(args[0]) if len(args) >= 1 else 200
    y_bound = int(args[1]) if len(args) >= 2 else 600

    print(f"Searching for solutions with |x| <= {x_bound}, |y| <= {y_bound} ...")
    sols = search(x_bound, y_bound)

    print(f"\nFound {len(sols)} solutions:\n")
    print(f"{'x':>8}  {'y':>8}  {'z':>12}   verification")
    print("-" * 50)
    for x, y, z in sols:
        residual = z * z + y * y * z + x**3 - x - 1
        status = "OK" if residual == 0 else f"FAIL({residual})"
        print(f"{x:>8}  {y:>8}  {z:>12}   {status}")

    # Summarise distinct |y| values with solutions
    nonzero_y = sorted({abs(y) for x, y, z in sols if y != 0})
    print(f"\nDistinct |y| values (nonzero): {nonzero_y}")
    print(f"y=0 solutions: {sum(1 for x,y,z in sols if y==0)}")
    print(f"y!=0 solutions: {sum(1 for x,y,z in sols if y!=0)}")


if __name__ == "__main__":
    main()
