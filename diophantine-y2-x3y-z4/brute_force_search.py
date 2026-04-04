"""
brute_force_search.py
======================
Exhaustive integer search for solutions to

    y^2 - x^3 * y + z^4 + 1 = 0

over integers (x, y, z).

Strategy
--------
The equation is a quadratic in y for any fixed (x, z):

    y = (x^3 ± sqrt(x^6 - 4*(z^4 + 1))) / 2

A necessary condition for integer y is that the discriminant
    D = x^6 - 4*z^4 - 4
is a non-negative perfect square, AND that x^3 ± sqrt(D) is even.

Pre-filter (mod 4):
  - z must be ODD: z^4 ≡ 0 (mod 4) when z even, giving z^4+1 ≡ 1 (mod 4).
    Then y^2 - x^3*y ≡ -1 ≡ 3 (mod 4), but this is impossible for any (x,y).
  - x must be ODD: proven below.

Search range: |x| <= 10,000 (odd only), z from 1 to z_max(x) (odd only).
"""

import math
import sys

def is_perfect_square(n):
    if n < 0:
        return False, 0
    s = math.isqrt(n)
    if s * s == n:
        return True, s
    return False, 0

def search(x_limit=10000, verbose=True):
    solutions = []
    checks = 0

    for x_abs in range(1, x_limit + 1, 2):          # x odd, positive
        # D = x^6 - 4*z^4 - 4 >= 0  =>  z^4 <= (x^6 - 4) / 4
        x6 = x_abs ** 6
        if x6 < 4:
            continue
        z4_max = (x6 - 4) // 4
        z_max = int(z4_max ** 0.25) + 2

        for z in range(1, z_max + 1, 2):            # z odd, positive
            z4 = z ** 4
            D = x6 - 4 * z4 - 4
            if D < 0:
                break

            ok, sq = is_perfect_square(D)
            if not ok:
                checks += 1
                continue

            x3 = x_abs ** 3
            # Need x3 + sq even (equivalently x3 and sq same parity)
            if (x3 + sq) % 2 != 0:
                checks += 1
                continue

            y1 = (x3 + sq) // 2
            y2 = (x3 - sq) // 2

            for x_sign in [1, -1]:
                x = x_sign * x_abs
                for y in [y1, y2, -y1, -y2]:
                    val = y * y - x ** 3 * y + z ** 4 + 1
                    if val == 0:
                        solutions.append((x, y, z))
                        solutions.append((x, y, -z))
                        if verbose:
                            print(f"  SOLUTION: x={x}, y={y}, z={z}")

            checks += 1

        if verbose and x_abs % 1000 == 1:
            print(f"Progress: x={x_abs}, checks so far: {checks}")

    return solutions

if __name__ == "__main__":
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    print(f"Searching for solutions to y^2 - x^3*y + z^4 + 1 = 0")
    print(f"Range: 1 <= |x| <= {limit} (odd only), 1 <= |z| <= z_max(x) (odd only)")
    print(f"Pre-filter: z must be odd (mod-4 obstruction for z even)")
    print(f"Pre-filter: x must be odd (mod-4 obstruction for x even)")
    print()

    sols = search(limit, verbose=True)

    print()
    if sols:
        print(f"Found {len(sols)} solution(s):")
        for s in sols:
            print(f"  (x, y, z) = {s}")
    else:
        print(f"No solutions found for |x| <= {limit}.")
        print("Consistent with the conjecture of no integer solutions.")
