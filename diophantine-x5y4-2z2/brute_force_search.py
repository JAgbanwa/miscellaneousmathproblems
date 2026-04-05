#!/usr/bin/env python3
"""
brute_force_search.py — Integer solutions to x^5 + y^4 = 2z^2

Performs an exhaustive search over |x|, |y| <= BOUND and for each (x, y) checks
whether 2z^2 = x^5 + y^4 has an integer solution z (i.e. whether (x^5 + y^4) / 2
is a perfect square).

Also verifies the parametric family (t^4, t^5, t^10) and the secondary family
(2m^2, 0, 4m^5).
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
            if lhs % 2 != 0:
                # 2z^2 must be even; x^5 + y^4 must be even
                # (requires x and y same parity — already a necessary condition)
                count += 1
                continue
            half = lhs // 2       # = z^2 (must be non-negative)
            z = is_perfect_square(half)
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
    # Remove duplicates (z and -z already added above; deduplicate the list)
    # Keep z >= 0 representatives for display, but list both
    unique = sorted(set(solutions))
    return unique


def verify_parametric_family(t_range: range) -> None:
    print("\n=== Parametric family (t^4, t^5, t^10) ===")
    print(f"{'t':>5}  {'x=t^4':>12}  {'y=t^5':>14}  {'z=t^10':>20}  Check")
    for t in t_range:
        x = t ** 4
        y = t ** 5
        z = t ** 10
        lhs = x ** 5 + y ** 4
        rhs = 2 * z ** 2
        ok = "✓" if lhs == rhs else "✗"
        print(f"{t:>5}  {x:>12}  {y:>14}  {z:>20}  {ok}")


def verify_secondary_family(m_range: range) -> None:
    print("\n=== Secondary family (2m^2, 0, 4m^5) ===")
    print(f"{'m':>5}  {'x=2m^2':>12}  {'y':>6}  {'z=4m^5':>14}  Check")
    for m in m_range:
        x = 2 * m ** 2
        y = 0
        z = 4 * m ** 5
        lhs = x ** 5 + y ** 4
        rhs = 2 * z ** 2
        ok = "✓" if lhs == rhs else "✗"
        print(f"{m:>5}  {x:>12}  {y:>6}  {z:>14}  {ok}")


def classify_solution(x: int, y: int, z: int) -> str:
    """Try to classify a solution into a known family."""
    # Check parametric family: x = t^4, y = t^5, z = t^10
    if x >= 0:
        t = round(x ** 0.25)
        for candidate_t in [t - 1, t, t + 1]:
            for sign_t in ([candidate_t, -candidate_t]
                           if candidate_t > 0 else [0]):
                if (sign_t ** 4 == x and sign_t ** 5 == y
                        and sign_t ** 10 == abs(z)):
                    return f"parametric t={sign_t}"
    # Check secondary family (2m^2, 0, 4m^5)
    if y == 0 and x >= 0:
        if x % 2 == 0:
            half_x = x // 2
            m = round(half_x ** 0.5)
            for cm in [m - 1, m, m + 1]:
                if cm >= 0 and 2 * cm ** 2 == x and abs(4 * cm ** 5) == abs(z):
                    return f"secondary m={cm}"
    return "other"


def main() -> None:
    print("=" * 60)
    print("Brute-force search: x^5 + y^4 = 2z^2")
    print(f"Search bound: |x|, |y| <= {BOUND}")
    print("=" * 60)

    # Verify known families first
    verify_parametric_family(range(-5, 6))
    verify_secondary_family(range(-4, 5))

    # Exhaustive search
    print(f"\n=== Exhaustive search (|x|, |y| <= {BOUND}) ===")
    solutions = search_solutions(BOUND)

    print(f"\nFound {len(solutions)} solution triples (including z and -z).\n")
    print(f"{'x':>12}  {'y':>14}  {'z':>12}  Classification")
    print("-" * 65)
    shown = 0
    MAX_SHOW = 60
    for x, y, z in solutions:
        if z < 0:
            continue   # Show only z >= 0 representative
        label = classify_solution(x, y, z)
        print(f"{x:>12}  {y:>14}  {z:>12}  {label}")
        shown += 1
        if shown >= MAX_SHOW:
            remaining = sum(1 for xx, yy, zz in solutions if zz >= 0) - shown
            if remaining > 0:
                print(f"  ... ({remaining} more solutions not displayed)")
            break

    # Summary statistics
    parametric = sum(
        1 for x, y, z in solutions
        if z >= 0 and classify_solution(x, y, z).startswith("parametric")
    )
    secondary = sum(
        1 for x, y, z in solutions
        if z >= 0 and classify_solution(x, y, z).startswith("secondary")
    )
    other = sum(
        1 for x, y, z in solutions
        if z >= 0 and classify_solution(x, y, z) == "other"
    )
    total_nonneg = sum(1 for _, _, z in solutions if z >= 0)
    print(f"\nClassification summary (z >= 0 solutions):")
    print(f"  Parametric family (t^4, t^5, t^10):  {parametric}")
    print(f"  Secondary family  (2m^2,  0, 4m^5):  {secondary}")
    print(f"  Other:                                {other}")
    print(f"  Total (z >= 0):                       {total_nonneg}")

    print("\nConclusion:")
    print("  The equation x^5 + y^4 = 2z^2 has INFINITELY MANY integer solutions.")
    print("  Primary family: (t^4, t^5, t^10) for any t in Z.")
    print("  Proof: (t^4)^5 + (t^5)^4 = t^20 + t^20 = 2*(t^10)^2. QED.")


if __name__ == "__main__":
    main()
