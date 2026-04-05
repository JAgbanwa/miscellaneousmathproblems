#!/usr/bin/env python3
"""
brute_force_search.py — Integer solutions to x^5 + y^4 = 3z^2

Performs an exhaustive search over |x|, |y| <= BOUND and for each (x, y) checks
whether 3z^2 = x^5 + y^4 has an integer solution z (i.e. whether (x^5 + y^4) / 3
is a perfect square and the total is non-negative).

Also verifies the primary parametric family (3a^2, 0, 9a^5) and the secondary
family (2t^4, 2t^5, 4t^10).
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
            lhs = x5 + y4
            if lhs < 0:
                count += 1
                continue
            if lhs % 3 != 0:
                # 3z^2 must be divisible by 3; require x^5 + y^4 ≡ 0 (mod 3)
                count += 1
                continue
            third = lhs // 3       # = z^2 (must be a perfect square)
            z = is_perfect_square(third)
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


def verify_primary_family(a_range: range) -> None:
    print("\n=== Primary family (3a^2, 0, 9a^5) ===")
    print(f"{'a':>5}  {'x=3a^2':>10}  {'y':>4}  {'z=9a^5':>14}  Check")
    for a in a_range:
        x = 3 * a ** 2
        y = 0
        z = 9 * a ** 5
        lhs = x ** 5 + y ** 4
        rhs = 3 * z ** 2
        ok = "✓" if lhs == rhs else "✗"
        print(f"{a:>5}  {x:>10}  {y:>4}  {z:>14}  {ok}")


def verify_secondary_family(t_range: range) -> None:
    print("\n=== Secondary family (2t^4, 2t^5, 4t^10) ===")
    print(f"{'t':>5}  {'x=2t^4':>10}  {'y=2t^5':>12}  {'z=4t^10':>16}  Check")
    for t in t_range:
        x = 2 * t ** 4
        y = 2 * t ** 5
        z = 4 * t ** 10
        lhs = x ** 5 + y ** 4
        rhs = 3 * z ** 2
        ok = "✓" if lhs == rhs else "✗"
        print(f"{t:>5}  {x:>10}  {y:>12}  {z:>16}  {ok}")


def main() -> None:
    print(f"Searching for integer solutions to x^5 + y^4 = 3z^2")
    print(f"Bounds: |x|, |y| <= {BOUND}")
    print()

    print("=== Brute-force search ===")
    sols = search_solutions(BOUND)
    print(f"\nFound {len(sols)} solutions (counting ±z separately):\n")

    # Group by (x, |y|) to display cleanly
    printed = set()
    for x, y, z in sorted(sols):
        key = (x, abs(y))
        if key not in printed:
            printed.add(key)
            # Print with both signs for z if z != 0
            z_str = f"±{abs(z)}" if z != 0 else "0"
            lhs = x**5 + y**4
            rhs_check = "✓" if lhs == 3 * z**2 else "✗"
            print(f"  ({x}, {y}, {z_str}): {x}^5 + {y}^4 = {lhs} = 3·{z**2} {rhs_check}")

    verify_primary_family(range(-5, 6))
    verify_secondary_family(range(-4, 5))

    # Spot-check some specific known solutions
    print("\n=== Spot-check of named solutions ===")
    named = [
        ("(0, 0, 0)",        0,   0,    0),
        ("(3, 0, 9)",        3,   0,    9),
        ("(3, 0, -9)",       3,   0,   -9),
        ("(-1, 1, 0)",      -1,   1,    0),
        ("(-1, -1, 0)",     -1,  -1,    0),
        ("(2, 2, 4)",        2,   2,    4),
        ("(2, -2, 4)",       2,  -2,    4),
        ("(12, 0, 288)",    12,   0,  288),
        ("(12, 0, -288)",   12,   0, -288),
    ]
    for name, x, y, z in named:
        lhs = x**5 + y**4
        rhs = 3 * z**2
        ok = "✓" if lhs == rhs else "✗"
        print(f"  {name}: {lhs} = {rhs}  {ok}")

    # Verify primary family algebraically for symbolic check
    print("\n=== Algebraic verification of primary family ===")
    print("For any integer a: (3a^2)^5 + 0^4 = 3^5 * a^10 = 243*a^10")
    print("                   3 * (9a^5)^2 = 3 * 81 * a^10 = 243*a^10  ✓")
    print()
    print("=== Algebraic verification of secondary family ===")
    print("For any integer t: (2t^4)^5 + (2t^5)^4 = 32*t^20 + 16*t^20 = 48*t^20")
    print("                   3 * (4t^10)^2 = 3 * 16 * t^20 = 48*t^20  ✓")


if __name__ == "__main__":
    main()
