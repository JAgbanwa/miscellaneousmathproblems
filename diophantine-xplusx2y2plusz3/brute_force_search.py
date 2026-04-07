#!/usr/bin/env python3
"""
brute_force_search.py — Integer solutions to x + x^2*y^2 + z^3 = 0

Performs an exhaustive search over |x|, |y|, |z| <= BOUND and records every
integer triple (x, y, z) satisfying the equation.

Key optimisation: for a fixed x ≠ 0 we need z^3 = -x - x^2*y^2 with |z| <= BOUND,
so |x^2*y^2| <= BOUND^3 + |x|, giving |y| <= sqrt((BOUND^3 + |x|) / x^2).
For large |x| this y-bound is much smaller than BOUND, keeping the total work
O(BOUND * log BOUND) rather than O(BOUND^2).

Additionally verifies the two parametric families:
  Family 1: (0, t, 0)          for t in Z  [from setting x = 0]
  Family 2: (-t^3, 0, t)       for t in Z  [from setting y = 0]
"""

import math
import sys

BOUND = 10_000  # Search |x|, |y|, |z| <= BOUND


# ── Core equation ─────────────────────────────────────────────────────────────

def eq(x: int, y: int, z: int) -> int:
    return x + x**2 * y**2 + z**3


# ── Integer cube root (exact) ─────────────────────────────────────────────────

def icbrt(n: int) -> int | None:
    """Return the integer cube root of n if it exists, else None."""
    if n == 0:
        return 0
    sign = 1 if n > 0 else -1
    a = abs(n)
    # Use integer Newton's method for large values to avoid float precision loss
    if a < (1 << 53):
        r = round(a ** (1.0 / 3.0))
    else:
        # Integer Newton starting from float estimate
        r = int(a ** (1.0 / 3.0)) + 1
        while True:
            r1 = (2 * r + a // (r * r)) // 3
            if r1 >= r:
                break
            r = r1
    for candidate in range(max(0, r - 2), r + 3):
        if candidate ** 3 == a:
            return sign * candidate
    return None


# ── Optimised core search ─────────────────────────────────────────────────────

def search_solutions(bound: int) -> list[tuple[int, int, int]]:
    """
    Return all (x, y, z) with |x|, |y|, |z| <= bound satisfying the equation.

    For x = 0: equation is 0 + 0 + z^3 = 0 => z = 0; y is free.
    We record only a few witnesses rather than all 2*bound+1 trivial members,
    since Family 1 is infinite and uninteresting beyond being confirmed.

    For x != 0: iterate over the restricted y-range derived from |z| <= bound.
    """
    sporadic: list[tuple[int, int, int]] = []
    family2_found: list[tuple[int, int, int]] = []

    # Cube of the bound, used for y-range trimming
    bound3 = bound ** 3

    for x in range(-bound, bound + 1):
        if x == 0:
            # Family 1: (0, any, 0) — infinite; skip
            continue

        x2 = x * x
        # Maximum |y| such that |z^3| = |x + x^2*y^2| could still be <= bound^3
        # |x^2*y^2| <= bound^3 + |x|  =>  |y| <= sqrt((bound^3 + |x|) / x^2)
        y_lim = math.isqrt((bound3 + abs(x)) // x2)
        # isqrt floors; check y_lim+1 as well (for rounding safety)
        if (y_lim + 1) ** 2 * x2 <= bound3 + abs(x):
            y_lim += 1

        for y in range(-y_lim, y_lim + 1):
            rhs = -x - x2 * y * y
            z = icbrt(rhs)
            if z is None or abs(z) > bound:
                continue
            triple = (x, y, z)
            if y == 0 and x == -(z ** 3):
                family2_found.append(triple)
            else:
                sporadic.append(triple)

    return sorted(set(sporadic)), sorted(set(family2_found))


# ── Parametric family verification ───────────────────────────────────────────

def verify_family1(t_range: range) -> bool:
    """Check (0, t, 0) for all t in t_range."""
    return all(eq(0, t, 0) == 0 for t in t_range)


def verify_family2(t_range: range) -> bool:
    """Check (-t^3, 0, t) for all t in t_range."""
    return all(eq(-(t**3), 0, t) == 0 for t in t_range)


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    print(f"=== Brute-force search: x + x^2*y^2 + z^3 = 0, |x|,|y|,|z| <= {BOUND:,} ===\n")
    print("(Family 1 = (0,n,0) is trivially infinite; only sporadic and Family 2 listed.)\n")

    sporadic, family2 = search_solutions(BOUND)

    print(f"Family 2 (-n^3, 0, n) members found: {len(family2)}")
    print(f"Sporadic (x≠0, y≠0) solutions found: {len(sporadic)}\n")

    print("All sporadic solutions (x != 0, y != 0):")
    for x, y, z in sporadic:
        print(f"  ({x:8d}, {y:8d}, {z:8d})   verify={eq(x,y,z)}")

    print()
    print("=== Verifying Family 1 for t in [-100, 100] ===")
    print("  Family 1 OK." if verify_family1(range(-100, 101)) else "  Family 1 FAILED!")

    print()
    print("=== Verifying Family 2 for t in [-100, 100] ===")
    print("  Family 2 OK." if verify_family2(range(-100, 101)) else "  Family 2 FAILED!")

    print()
    print("=== Checking injectivity of Family 1 map n -> (0, n, 0) ===")
    imgs = [(0, n, 0) for n in range(1, 10)]
    assert len(set(imgs)) == len(imgs)
    print("  Injective (distinct y-components) — confirmed.")

    print()
    print("=== Checking injectivity of Family 2 map n -> (-n^3, 0, n) ===")
    imgs2 = [(-n**3, 0, n) for n in range(1, 10)]
    assert len(set(imgs2)) == len(imgs2)
    print("  Injective (distinct z-components) — confirmed.")

    print()
    print("=== Modular obstruction search, primes p <= 100 ===")
    primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    obstruction_found = False
    for p in primes:
        nonzero_lhs = set()
        for x in range(p):
            for y in range(p):
                for z in range(p):
                    if x == y == z == 0:
                        continue
                    nonzero_lhs.add((x + x**2 * y**2 + z**3) % p)
        if 0 not in nonzero_lhs:
            print(f"  OBSTRUCTION mod {p}: no nonzero solution exists!")
            obstruction_found = True
    if not obstruction_found:
        print("  No modular obstruction found for any prime p <= 100.")

    print()
    print("Summary:")
    print(f"  Search completed for |x|,|y|,|z| <= {BOUND:,}.")
    print(f"  Sporadic solutions (x≠0, y≠0): {len(sporadic)}")
    print("  The equation x + x^2*y^2 + z^3 = 0 has INFINITELY MANY integer solutions.")
    print("  Family 1: (0, n, 0) for all n in Z.")
    print("  Family 2: (-n^3, 0, n) for all n in Z.")


if __name__ == "__main__":
    main()
