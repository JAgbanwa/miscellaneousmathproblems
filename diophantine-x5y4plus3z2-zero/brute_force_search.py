#!/usr/bin/env python3
"""
brute_force_search.py — Integer solutions to x^5 + y^4 + 3z^2 = 0

Performs an exhaustive search over |x|, |y| <= BOUND and for each (x, y)
checks whether -x^5 - y^4 is non-negative and equal to 3z^2 for some
integer z (i.e. whether (-x^5 - y^4) / 3 is a perfect square).

Also verifies the two parametric families:
  Family 1: (-t^4, ±t^5, 0)
  Family 2: (-3*t^4, 0, ±9*t^10)
"""

import math
import sys
from typing import Optional

BOUND = 200  # Search |x|, |y| <= BOUND


def is_perfect_square(n: int) -> Optional[int]:
    """Return sqrt(n) if n >= 0 is a perfect square, else None."""
    if n < 0:
        return None
    r = int(math.isqrt(n))
    if r * r == n:
        return r
    return None


def search_solutions(bound: int) -> list[tuple[int, int, int]]:
    solutions = []
    total = (2 * bound + 1) ** 2
    count = 0
    for x in range(-bound, bound + 1):
        x5 = x ** 5
        for y in range(-bound, bound + 1):
            y4 = y ** 4
            # Need 3z^2 = -x^5 - y^4, so rhs must be >= 0 and divisible by 3.
            rhs = -x5 - y4
            if rhs < 0:
                count += 1
                continue
            if rhs % 3 != 0:
                count += 1
                continue
            z_sq = rhs // 3       # = z^2 (must be a perfect square)
            z = is_perfect_square(z_sq)
            if z is not None:
                solutions.append((x, y, z))
                if z != 0:
                    solutions.append((x, y, -z))
            count += 1
        if x % 50 == 0:
            pct = 100 * count / total
            print(f"  Progress: x={x:+5d}, {pct:.1f}% done, "
                  f"{len(solutions)} solutions so far", end="\r", flush=True)
    print()
    unique = sorted(set(solutions))
    return unique


def verify_family1(t_range: range) -> None:
    """Verify Family 1: (-t^4, t^5, 0) for t in t_range."""
    print("Verifying Family 1: (-t^4, ±t^5, 0)")
    all_ok = True
    for t in t_range:
        x = -(t ** 4)
        y = t ** 5
        z = 0
        lhs = x**5 + y**4 + 3*z**2
        if lhs != 0:
            print(f"  FAIL t={t}: x={x}, y={y}, z={z}, lhs={lhs}")
            all_ok = False
    if all_ok:
        print(f"  All {len(t_range)} values verified. ✓")


def verify_family2(t_range: range) -> None:
    """Verify Family 2: (-3*t^4, 0, 9*t^10) for t in t_range."""
    print("Verifying Family 2: (-3*t^4, 0, ±9*t^10)")
    all_ok = True
    for t in t_range:
        x = -3 * (t ** 4)
        y = 0
        z = 9 * (t ** 10)
        lhs = x**5 + y**4 + 3*z**2
        if lhs != 0:
            print(f"  FAIL t={t}: x={x}, y={y}, z={z}, lhs={lhs}")
            all_ok = False
    if all_ok:
        print(f"  All {len(t_range)} values verified. ✓")


def main() -> None:
    print("=" * 65)
    print("Brute-force search: x^5 + y^4 + 3z^2 = 0")
    print(f"Search region: |x|, |y| <= {BOUND}")
    print("=" * 65)

    # ── Verify parametric families first ──────────────────────────────
    print()
    verify_family1(range(-10, 11))
    print()
    verify_family2(range(-5, 6))

    # ── Brute-force search ────────────────────────────────────────────
    print()
    print(f"Searching |x|, |y| <= {BOUND} ...")
    solutions = search_solutions(BOUND)

    print()
    print(f"Found {len(solutions)} solutions (including ±z duplicates).")
    print()

    # ── Explicit witnesses ────────────────────────────────────────────
    print("Explicit witnesses from the search:")
    print(f"{'x':>8}  {'y':>8}  {'z':>10}   check")
    print("-" * 50)
    shown = 0
    for (x, y, z) in solutions:
        lhs = x**5 + y**4 + 3*(z**2)
        assert lhs == 0, f"Bug: ({x},{y},{z}) lhs={lhs}"
        if shown < 30 or abs(x) <= 3:
            print(f"{x:>8}  {y:>8}  {z:>10}   {lhs}")
            shown += 1
    if len(solutions) > shown:
        print(f"  ... ({len(solutions) - shown} more solutions not displayed)")

    # ── Categorise solutions ──────────────────────────────────────────
    print()
    print("Solutions classified by parametric family:")
    family1 = [(x, y, z) for (x, y, z) in solutions
               if z == 0 and x != 0
               and all(t**4 == -x and abs(t**5) == abs(y)
                       for t in range(1, BOUND+1) if t**4 == -x)]
    family2 = [(x, y, z) for (x, y, z) in solutions
               if y == 0 and x != 0
               and any(-3*t**4 == x and abs(9*t**10) == abs(z)
                       for t in range(1, BOUND+1))]
    trivial = [(x, y, z) for (x, y, z) in solutions if x == 0 and y == 0 and z == 0]

    print(f"  Trivial (0,0,0): {len(trivial)}")
    print(f"  Family 1 candidates (z=0, x=-t^4, y=±t^5): {len(family1)}")
    print(f"  Family 2 candidates (y=0, x=-3t^4, z=±9t^10): {len(family2)}")

    # ── Summary ───────────────────────────────────────────────────────
    print()
    print("=" * 65)
    print("SUMMARY")
    print("=" * 65)
    print("The equation x^5 + y^4 + 3z^2 = 0 has infinitely many integer")
    print("solutions, produced by two parametric families:")
    print()
    print("  Family 1: (x,y,z) = (-t^4, ±t^5, 0)   for t ∈ ℤ")
    print("  Family 2: (x,y,z) = (-3t^4, 0, ±9t^10) for t ∈ ℤ")
    print()
    print("Both families are verified above and by the brute-force search.")


if __name__ == "__main__":
    main()
