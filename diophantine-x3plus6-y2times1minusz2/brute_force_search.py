"""
brute_force_search.py
=====================
Exhaustive integer search for solutions to

    6 + x^3 = y^2 * (1 - z^2)

over integers (x, y, z).

Strategy
--------
Rewrite as:

    6 + x^3 = y^2 - (yz)^2 = y^2(1 - z^2)

For fixed (x, z) with 1 - z^2 ≠ 0, the right-hand side must equal (6 + x^3),
so we need:
  - (6 + x^3) divisible by (1 - z^2), and
  - the quotient (6 + x^3) / (1 - z^2) to be a non-negative perfect square.

Special cases (handled directly):
  - z = 0:    equation becomes y^2 = x^3 + 6  (Mordell curve, no integer points)
  - z = ±1:   equation becomes 6 + x^3 = 0, i.e. x^3 = -6 (no perfect cube)
  - y = 0:    equation becomes x^3 = -6 (no perfect cube)
  - |z| >= 2: 1 - z^2 <= -3, so 6 + x^3 must be negative; requires x <= -2.
              For x = -2: 6 + x^3 = -2 which exceeds -3, impossible.
              For x <= -3: check all factor pairs.

Search range:  |x| <= 10,000 (primary),  0 <= z <= 10,000.
By sign symmetry y -> -y and z -> -z leave the equation unchanged.
"""

import math
import sys


def is_perfect_square(n: int):
    """Return (True, sqrt) if n is a non-negative perfect square, else (False, 0)."""
    if n < 0:
        return False, 0
    s = math.isqrt(n)
    if s * s == n:
        return True, s
    return False, 0


def search(x_limit: int = 10_000, z_limit: int = 10_000, verbose: bool = True) -> list:
    solutions = []

    if verbose:
        print(f"Searching |x| <= {x_limit}, 0 <= z <= {z_limit}...")

    for x in range(-x_limit, x_limit + 1):
        num = 6 + x ** 3

        for z in range(0, z_limit + 1):
            denom = 1 - z * z
            if denom == 0:
                continue  # z = ±1 gives x^3 = -6, handled separately

            if num % denom != 0:
                continue

            q = num // denom
            ok, y = is_perfect_square(q)
            if not ok:
                continue

            # Sign symmetries: (x, ±y, ±z) are all solutions
            if verbose and (y != 0 or z != 0):
                print(f"  SOLUTION: x={x}, y=±{y}, z=±{z}")
                print(f"    Verify: 6 + {x}^3 = {num},  y^2*(1-z^2) = {y**2}*{denom} = {y**2*denom}")
            solutions.append((x, y, z))

    return solutions


def verify(solutions):
    for (x, y, z) in solutions:
        assert 6 + x ** 3 == y ** 2 * (1 - z ** 2), f"Verification failed: ({x},{y},{z})"
    print(f"All {len(solutions)} solution(s) verified.")


if __name__ == "__main__":
    x_lim = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000
    z_lim = int(sys.argv[2]) if len(sys.argv) > 2 else 10_000

    sols = search(x_lim, z_lim, verbose=True)

    if sols:
        print(f"\n{len(sols)} solution(s) found (counting (x, y, z) with y,z >= 0).")
        verify(sols)
    else:
        print(f"\nNo solutions found for |x| <= {x_lim}, 0 <= z <= {z_lim}.")
        print("This confirms the equation has no integer solutions in this range.")
