#!/usr/bin/env python3
"""
Brute-force search for integer solutions to:
  (36n+29)*y^2 + (12n+10)*z^2 = 1728n^3 + 4320n^2 + 3600n + 998

Equivalent to: (6k-1)*y^2 + 2k*z^2 = 8k^3 - 2, where k = 6n+5.

Searches over |n|, |y|, |z| <= LIMIT.
"""

LIMIT = 200

solutions = []

for n in range(-LIMIT, LIMIT + 1):
    lhs_coeff_y = 36 * n + 29
    lhs_coeff_z = 12 * n + 10
    rhs = 1728 * n**3 + 4320 * n**2 + 3600 * n + 998
    # rhs = (12n+10)^3 - 2
    for y in range(-LIMIT, LIMIT + 1):
        for z in range(-LIMIT, LIMIT + 1):
            if lhs_coeff_y * y**2 + lhs_coeff_z * z**2 == rhs:
                solutions.append((n, y, z))

if solutions:
    print("SOLUTIONS FOUND:")
    for sol in solutions:
        print(f"  n={sol[0]}, y={sol[1]}, z={sol[2]}")
else:
    print(f"No solutions found for |n|, |y|, |z| <= {LIMIT}.")
