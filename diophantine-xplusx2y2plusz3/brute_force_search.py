#!/usr/bin/env python3
"""
brute_force_search.py — Integer solutions to x + x^2*y^2 + z^3 = 0

Performs an exhaustive search over |x|, |y|, |z| <= BOUND and records every
integer triple (x, y, z) satisfying the equation.

Additionally verifies the two parametric families:
  Family 1: (0, t, 0)          for t in Z  [from setting x = 0]
  Family 2: (-t^3, 0, t)       for t in Z  [from setting y = 0]
"""

import sys
from typing import Generator

BOUND = 50  # Search |x|, |y|, |z| <= BOUND


# ── Core equation ─────────────────────────────────────────────────────────────

def eq(x: int, y: int, z: int) -> int:
    return x + x**2 * y**2 + z**3


# ── Core search ──────────────────────────────────────────────────────────────

def search_solutions(bound: int) -> list[tuple[int, int, int]]:
    """Return all (x, y, z) with max(|x|,|y|,|z|) <= bound satisfying the eq."""
    solutions: list[tuple[int, int, int]] = []
    for x in range(-bound, bound + 1):
        for y in range(-bound, bound + 1):
            # z^3 = -x - x^2*y^2; check if that is a perfect cube
            rhs = -x - x**2 * y**2
            z = icbrt(rhs)
            if z is not None and abs(z) <= bound:
                solutions.append((x, y, z))
    return sorted(set(solutions))


def icbrt(n: int) -> int | None:
    """Return the integer cube root of n if it exists, else None."""
    if n == 0:
        return 0
    sign = 1 if n > 0 else -1
    a = abs(n)
    r = round(a ** (1 / 3))
    for candidate in range(max(0, r - 2), r + 3):
        if candidate ** 3 == a:
            return sign * candidate
    return None


# ── Parametric family verification ───────────────────────────────────────────

def verify_family1(t_range: range) -> bool:
    """Check (0, t, 0) for all t in t_range."""
    ok = True
    for t in t_range:
        val = eq(0, t, 0)
        if val != 0:
            print(f"  FAIL Family 1 at t={t}: eq = {val}", file=sys.stderr)
            ok = False
    return ok


def verify_family2(t_range: range) -> bool:
    """Check (-t^3, 0, t) for all t in t_range."""
    ok = True
    for t in t_range:
        x, y, z = -(t ** 3), 0, t
        val = eq(x, y, z)
        if val != 0:
            print(f"  FAIL Family 2 at t={t}: eq = {val}", file=sys.stderr)
            ok = False
    return ok


# ── Analysis helpers ──────────────────────────────────────────────────────────

def classify_solution(x: int, y: int, z: int) -> str:
    """Return a human-readable family label for a known solution."""
    if x == 0 and z == 0:
        return f"Family 1 (n={y})"
    if y == 0 and x == -(z ** 3):
        return f"Family 2 (n={z})"
    return "sporadic"


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    print(f"=== Brute-force search: x + x^2*y^2 + z^3 = 0, |x|,|y|,|z| <= {BOUND} ===\n")

    solutions = search_solutions(BOUND)
    print(f"Total solutions found: {len(solutions)}\n")

    family1 = [(x, y, z) for x, y, z in solutions if x == 0 and z == 0]
    family2 = [(x, y, z) for x, y, z in solutions if y == 0 and x == -(z**3) and (x != 0 or z != 0)]
    sporadic = [(x, y, z) for x, y, z in solutions
                if not (x == 0 and z == 0) and not (y == 0 and x == -(z**3))]

    print(f"Family 1 (0, n, 0):    {len(family1)} solutions")
    print(f"Family 2 (-n^3, 0, n): {len(family2)} solutions")
    print(f"Sporadic (x≠0, y≠0):   {len(sporadic)} solutions\n")

    print("Selected sporadic solutions (x != 0, y != 0):")
    for x, y, z in sporadic[:30]:
        print(f"  ({x:6d}, {y:6d}, {z:6d})   verify={eq(x,y,z)}")

    print()
    print("=== Verifying Family 1 for t in [-20, 20] ===")
    ok1 = verify_family1(range(-20, 21))
    print("  Family 1 OK." if ok1 else "  Family 1 FAILED!")

    print()
    print("=== Verifying Family 2 for t in [-20, 20] ===")
    ok2 = verify_family2(range(-20, 21))
    print("  Family 2 OK." if ok2 else "  Family 2 FAILED!")

    print()
    print("=== Checking injectivity of Family 1 map n -> (0, n, 0) ===")
    imgs = [(0, n, 0) for n in range(1, 10)]
    assert len(set(imgs)) == len(imgs), "Family 1 map is NOT injective!"
    print("  Injective (distinct y-components) — confirmed.")

    print()
    print("=== Checking injectivity of Family 2 map n -> (-n^3, 0, n) ===")
    imgs2 = [(-n**3, 0, n) for n in range(1, 10)]
    assert len(set(imgs2)) == len(imgs2), "Family 2 map is NOT injective!"
    print("  Injective (distinct z-components) — confirmed.")

    print()
    print("=== Modular obstruction search, primes p <= 100 ===")
    primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    obstruction_found = False
    for p in primes:
        lhs_vals: set[int] = set()
        for x in range(p):
            for y in range(p):
                for z in range(p):
                    if x == y == z == 0:
                        continue
                    lhs_vals.add((x + x**2 * y**2 + z**3) % p)
        if 0 not in lhs_vals:
            print(f"  OBSTRUCTION mod {p}: no nonzero solution exists!")
            obstruction_found = True
    if not obstruction_found:
        print("  No modular obstruction found for any prime p <= 100.")

    print()
    print("Summary:")
    print("  The equation x + x^2*y^2 + z^3 = 0 has INFINITELY MANY integer solutions.")
    print("  Family 1: (0, n, 0) for all n in Z.")
    print("  Family 2: (-n^3, 0, n) for all n in Z.")
    print("  Both families are infinite and have been verified algebraically and computationally.")


if __name__ == "__main__":
    main()
