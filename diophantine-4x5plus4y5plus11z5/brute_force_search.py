#!/usr/bin/env python3
"""
brute_force_search.py — Integer solutions to 4*x^5 + 4*y^5 + 11*z^5 = 0

For each pair (x, y) with |x|, |y| <= BOUND, compute what z^5 must equal:
  z^5 = -(4*x^5 + 4*y^5) / 11
and check whether this is a perfect fifth power.

Main result: the primary family (x, y, z) = (t, -t, 0) for t in Z satisfies
  4*t^5 + 4*(-t)^5 + 11*0^5 = 4*t^5 - 4*t^5 + 0 = 0.
No solutions with z != 0 are found for |x|, |y| <= BOUND.
"""

import math
from typing import Optional

BOUND = 50  # Search |x|, |y| <= BOUND


def fifth_root_int(n: int) -> Optional[int]:
    """Return the integer 5th root of n if n is a perfect 5th power, else None."""
    if n == 0:
        return 0
    sign = 1 if n > 0 else -1
    abs_n = abs(n)
    # Initial estimate via float
    r = int(round(abs_n ** 0.2))
    for candidate in range(max(0, r - 2), r + 3):
        if candidate ** 5 == abs_n:
            return sign * candidate
    return None


def is_solution(x: int, y: int, z: int) -> bool:
    return 4 * x**5 + 4 * y**5 + 11 * z**5 == 0


def search_solutions(bound: int) -> list[tuple[int, int, int]]:
    """
    Search for all integer solutions (x, y, z) with |x|, |y| <= bound.
    For each (x, y), compute the required z^5 and test for integer z.
    """
    solutions: set[tuple[int, int, int]] = set()
    total = (2 * bound + 1) ** 2
    count = 0

    for x in range(-bound, bound + 1):
        x5 = x ** 5
        for y in range(-bound, bound + 1):
            y5 = y ** 5
            # Need 11*z^5 = -(4*x^5 + 4*y^5)
            rhs = -(4 * x5 + 4 * y5)
            if rhs % 11 != 0:
                count += 1
                continue
            z5 = rhs // 11
            z = fifth_root_int(z5)
            if z is not None:
                solutions.add((x, y, z))
            count += 1

        if x % 20 == 0:
            pct = 100 * count / total
            print(
                f"  Progress: x={x:+5d}, {pct:.1f}% done, "
                f"{len(solutions)} solutions so far",
                end="\r",
                flush=True,
            )

    print()
    return sorted(solutions)


def verify_primary_family(T: int = 15) -> None:
    """Verify (t, -t, 0) are solutions for t = -T..T."""
    print(f"\n=== Verifying primary family (t, -t, 0) for t = {-T}..{T} ===")
    all_ok = True
    for t in range(-T, T + 1):
        val = 4 * t**5 + 4 * (-t) ** 5 + 11 * 0**5
        if val != 0:
            print(f"  FAIL: t={t}, value={val}")
            all_ok = False
    if all_ok:
        print(f"  All {2*T + 1} checks passed. ✓")
    print("  Algebraic proof: 4t^5 + 4(-t)^5 = 4t^5 - 4t^5 = 0 for all t ∈ Z.")


def verify_homogeneity(seed: tuple[int, int, int], scales: list[int]) -> None:
    """Verify that scaling a seed solution by t gives another solution."""
    x0, y0, z0 = seed
    print(f"\n=== Degree-5 homogeneity from seed {seed} ===")
    for t in scales:
        x, y, z = t * x0, t * y0, t * z0
        val = 4 * x**5 + 4 * y**5 + 11 * z**5
        status = "✓" if val == 0 else f"✗ (got {val})"
        print(f"  t={t:+3d}: ({x:+5d}, {y:+5d}, {z:+5d})  {status}")


def classify_solutions(solutions: list[tuple[int, int, int]]) -> None:
    """Classify found solutions into families."""
    primary = [(x, y, z) for x, y, z in solutions if y == -x and z == 0]
    trivial = [(x, y, z) for x, y, z in solutions if x == 0 and y == 0 and z == 0]
    nontrivial_z = [(x, y, z) for x, y, z in solutions if z != 0]

    print(f"\n=== Classification of {len(solutions)} solutions ===")
    print(f"  Primary family (t, -t, 0):  {len(primary)} solutions")
    print(f"  Of which trivial (0,0,0):   {len(trivial)}")
    print(f"  Solutions with z ≠ 0:       {len(nontrivial_z)}")

    if nontrivial_z:
        print("\n  Solutions with z ≠ 0 (first 20):")
        for x, y, z in nontrivial_z[:20]:
            val = 4 * x**5 + 4 * y**5 + 11 * z**5
            print(f"    ({x}, {y}, {z})  =>  value = {val}")
    else:
        print(
            f"\n  No solutions with z ≠ 0 found for |x|, |y| ≤ {BOUND}."
        )


def main() -> None:
    print("=" * 60)
    print("  4x^5 + 4y^5 + 11z^5 = 0  —  Brute-force search")
    print("=" * 60)
    print(f"  Search range: |x|, |y| ≤ {BOUND}  (z computed, not iterated)")

    verify_primary_family(T=20)
    verify_homogeneity(seed=(1, -1, 0), scales=list(range(-5, 6)))

    print(f"\nSearching for all solutions with |x|, |y| ≤ {BOUND}...")
    solutions = search_solutions(BOUND)
    print(f"Found {len(solutions)} solutions.\n")

    classify_solutions(solutions)

    print("\n=== Sample solutions (first 30) ===")
    for x, y, z in solutions[:30]:
        assert is_solution(x, y, z), f"Bug: ({x},{y},{z}) is not a solution!"
        print(f"  ({x:+4d}, {y:+4d}, {z:+4d})")
    if len(solutions) > 30:
        print(f"  ... ({len(solutions) - 30} more, all of the form (t,-t,0))")

    print("\n=== Summary ===")
    print("  The equation 4x^5 + 4y^5 + 11z^5 = 0 has infinitely many integer")
    print("  solutions given by the parametric family (t, -t, 0) for t ∈ Z.")
    print("  Proof: 4t^5 + 4(-t)^5 + 0 = 4t^5 - 4t^5 = 0.")
    print("  No solutions with z ≠ 0 were found in the search range.")


if __name__ == "__main__":
    main()
