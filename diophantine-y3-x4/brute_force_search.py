#!/usr/bin/env python3
"""
brute_force_search.py
=====================
Exhaustive integer-point search for the Diophantine equation

    y^3 - y = x^4 - 2x - 2

Strategy
--------
For each x in [-XBOUND, XBOUND] we compute N = x^4 - 2x - 2, then find the
unique integer y (if any) satisfying y^3 - y = N.  Since f(y) = y^3 - y is
strictly increasing for |y| > 1, Newton's method (one step from a floating-point
cube-root seed) followed by a small neighbourhood check is exact.

Modular pre-filter
------------------
Mod-4 analysis proves x must be *even* (odd x gives RHS ≡ 1 mod 4, which is
impossible for the LHS).  We therefore restrict the loop to even x, halving
the search time.
"""

import math


def integer_cbrt_approx(n: int) -> int:
    """Return an integer near the real cube root of n."""
    if n == 0:
        return 0
    sign = 1 if n > 0 else -1
    approx = round(abs(n) ** (1.0 / 3.0))
    return sign * approx


def has_cube_root_solution(n: int) -> list[int]:
    """
    Return all integers y with y^3 - y == n, checking a small neighbourhood
    around the real cube root.
    """
    y0 = integer_cbrt_approx(n)
    solutions = []
    for y in range(y0 - 3, y0 + 4):
        if y * y * y - y == n:
            solutions.append(y)
    return solutions


def search(xbound: int = 10_000) -> list[tuple[int, int]]:
    """
    Search for integer solutions (x, y) with |x| <= xbound.
    Only even x are tested (odd x is provably impossible mod 4).
    """
    solutions = []
    # Even x: start at -xbound if even, else -xbound+1
    x_start = -xbound if xbound % 2 == 0 else -xbound + 1

    for x in range(x_start, xbound + 1, 2):   # step 2: only even x
        rhs = x * x * x * x - 2 * x - 2
        ys = has_cube_root_solution(rhs)
        for y in ys:
            solutions.append((x, y))
    return solutions


def main():
    XBOUND = 10_000
    print(f"Searching for integer solutions to  y^3 - y = x^4 - 2x - 2")
    print(f"Range: |x| <= {XBOUND}  (only even x tested)\n")

    solutions = search(XBOUND)

    if solutions:
        print(f"{'x':>12}  {'y':>18}  {'Verification':>5}")
        print("-" * 42)
        for x, y in solutions:
            lhs = y**3 - y
            rhs = x**4 - 2*x - 2
            ok = "✓" if lhs == rhs else "✗"
            print(f"{x:>12}  {y:>18}  {ok}")
        print(f"\nTotal: {len(solutions)} solution(s) found.")
    else:
        print(f"No integer solutions found for |x| <= {XBOUND}.")

    # ---------------------------------------------------------------------------
    # Modular pre-filter statistics
    # ---------------------------------------------------------------------------
    print("\n--- Modular necessary conditions ---")
    mods = {
        4:  "x must be even (x ≡ 0 or 2 mod 4)",
        3:  "x ≡ 1 (mod 3)",
        5:  "x ≡ 2 or 4 (mod 5)",
        7:  "x ≢ 0 (mod 7)",
        11: "x ≡ 0, 2, 6, 7, or 10 (mod 11)",
        13: "x ≢ 4, 8, 12 (mod 13)",
    }
    forbidden = {
        4:  {1, 3},
        3:  {0, 2},
        5:  {0, 1, 3},
        7:  {0},
        11: {1, 3, 4, 5, 8, 9},
        13: {4, 8, 12},
    }
    for m, desc in mods.items():
        lhs_res = set((y**3 - y) % m for y in range(m))
        rhs_res = set((x**4 - 2*x - 2) % m for x in range(m))
        allowed = sorted(r for r in range(m) if r not in forbidden[m])
        print(f"  mod {m:2d}: {desc}")
        print(f"          LHS residues: {sorted(lhs_res)}")
        print(f"          RHS residues: {sorted(rhs_res)}")
        print(f"          Allowed x:    {allowed}")

    print()
    print("Combined: x ≡ 4 (mod 6) and x ≡ 4 or 22 (mod 30)")
    lcm = 2 * 3 * 5 * 7 * 11 * 13   # = 30030
    count = sum(
        1 for x in range(lcm)
        if all(x % m not in forb for m, forb in forbidden.items())
    )
    print(f"Density of candidate x: {count}/{lcm} ≈ {count/lcm:.4%}")


if __name__ == "__main__":
    main()
