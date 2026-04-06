#!/usr/bin/env python3
"""
brute_force_search.py — Integer solutions to x^4 + 4*y^3 + z^3 = 0

Performs an exhaustive search over |x|, |y|, |z| <= BOUND and records every
integer triple (x, y, z) satisfying the equation.

Additionally verifies the four parametric families:
  Family 1: (t^3,      0,       -t^4)      for t in Z  [setting y = 0]
  Family 2: (3*t^3,  -3*t^4,   3*t^4)     for t in Z  [setting z = -y]
  Family 3: (-4*t^3, -4*t^4,   0)         for t in Z  [setting z = 0]
  Family 4: (-5*t^3, -5*t^4,  -5*t^4)     for t in Z  [setting y = z]

All four families arise from the weighted-homogeneous structure of the equation
with weights wt(x)=3, wt(y)=4, wt(z)=4 (each term has weighted degree 12).
"""

BOUND = 50  # Search |x|, |y|, |z| <= BOUND


# ── Helpers ───────────────────────────────────────────────────────────────────

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


def eq(x: int, y: int, z: int) -> int:
    return x ** 4 + 4 * y ** 3 + z ** 3


# ── Core search ───────────────────────────────────────────────────────────────

def search_solutions(bound: int) -> list[tuple[int, int, int]]:
    """Return all (x, y, z) with max(|x|,|y|,|z|) <= bound satisfying the eq."""
    solutions: list[tuple[int, int, int]] = []
    for x in range(-bound, bound + 1):
        x4 = x ** 4
        for y in range(-bound, bound + 1):
            rhs = -x4 - 4 * y ** 3  # need z^3 = rhs
            z = icbrt(rhs)
            if z is not None and abs(z) <= bound:
                solutions.append((x, y, z))
    return sorted(set(solutions))


# ── Parametric family verification ───────────────────────────────────────────

def verify_family1(t_range: range) -> bool:
    """Check (t^3, 0, -t^4) for all t in t_range."""
    ok = True
    for t in t_range:
        x, y, z = t ** 3, 0, -(t ** 4)
        val = eq(x, y, z)
        if val != 0:
            print(f"  Family 1 FAILS at t={t}: val={val}")
            ok = False
    return ok


def verify_family2(t_range: range) -> bool:
    """Check (3*t^3, -3*t^4, 3*t^4) for all t in t_range."""
    ok = True
    for t in t_range:
        x, y, z = 3 * t ** 3, -3 * t ** 4, 3 * t ** 4
        val = eq(x, y, z)
        if val != 0:
            print(f"  Family 2 FAILS at t={t}: val={val}")
            ok = False
    return ok


def verify_family3(t_range: range) -> bool:
    """Check (-4*t^3, -4*t^4, 0) for all t in t_range."""
    ok = True
    for t in t_range:
        x, y, z = -4 * t ** 3, -4 * t ** 4, 0
        val = eq(x, y, z)
        if val != 0:
            print(f"  Family 3 FAILS at t={t}: val={val}")
            ok = False
    return ok


def verify_family4(t_range: range) -> bool:
    """Check (-5*t^3, -5*t^4, -5*t^4) for all t in t_range."""
    ok = True
    for t in t_range:
        x, y, z = -5 * t ** 3, -5 * t ** 4, -5 * t ** 4
        val = eq(x, y, z)
        if val != 0:
            print(f"  Family 4 FAILS at t={t}: val={val}")
            ok = False
    return ok


# ── Classification ────────────────────────────────────────────────────────────

def classify(x: int, y: int, z: int) -> str:
    """Try to identify which family a solution belongs to."""
    # Family 1: (t^3, 0, -t^4)
    if y == 0:
        t = icbrt(x)
        if t is not None and t ** 4 == -z:
            return f"Family 1 (t={t})"
    # Family 2: (3t^3, -3t^4, 3t^4)
    if z == -y and y != 0:
        # x = 3t^3, y = -3t^4 → t^3 = x/3, t^4 = -y/3
        if x % 3 == 0 and y % 3 == 0:
            t = icbrt(x // 3)
            if t is not None and 3 * t ** 3 == x and -3 * t ** 4 == y:
                return f"Family 2 (t={t})"
    # Family 3: (-4t^3, -4t^4, 0)
    if z == 0 and y != 0:
        if x % 4 == 0 and y % 4 == 0:
            t = icbrt(-x // 4)
            if t is not None and -4 * t ** 3 == x and -4 * t ** 4 == y:
                return f"Family 3 (t={t})"
    # Family 4: (-5t^3, -5t^4, -5t^4)
    if y == z and y != 0:
        if x % 5 == 0 and y % 5 == 0:
            t = icbrt(-x // 5)
            if t is not None and -5 * t ** 3 == x and -5 * t ** 4 == y:
                return f"Family 4 (t={t})"    # Family 5: (4*t^3, 4*t^4, -8*t^4)
    if z == -2 * y and y != 0:
        if x % 4 == 0 and y % 4 == 0:
            t = icbrt(x // 4)
            if t is not None and 4 * t ** 3 == x and 4 * t ** 4 == y:
                return f"Family 5 (t={t})"
    # Family 6: (12*t^3, -12*t^4, -24*t^4)
    if z == 2 * y and y != 0:
        if x % 12 == 0 and y % 12 == 0:
            t = icbrt(x // 12)
            if t is not None and 12 * t ** 3 == x and -12 * t ** 4 == y:
                return f"Family 6 (t={t})"
    # Family 7: (-5*t^3, -10*t^4, 15*t^4)
    if x % 5 == 0 and y % 10 == 0 and z % 5 == 0:
        t = icbrt(-x // 5)
        if t is not None and -5 * t ** 3 == x and -10 * t ** 4 == y and 15 * t ** 4 == z:
            return f"Family 7 (t={t})"
    if x == 0 and y == 0 and z == 0:
        return "trivial (0,0,0)"
    return "unknown seed"


# ── Main ─────────────────────────────────────────────────────────────────────

def main() -> None:
    t_range = range(-20, 21)

    print("=" * 60)
    print("Verifying parametric families")
    print("=" * 60)
    ok1 = verify_family1(t_range)
    ok2 = verify_family2(t_range)
    ok3 = verify_family3(t_range)
    ok4 = verify_family4(t_range)
    print(f"  Family 1 (t^3, 0, -t^4):              {'OK' if ok1 else 'FAIL'}")
    print(f"  Family 2 (3t^3, -3t^4, 3t^4):         {'OK' if ok2 else 'FAIL'}")
    print(f"  Family 3 (-4t^3, -4t^4, 0):           {'OK' if ok3 else 'FAIL'}")
    print(f"  Family 4 (-5t^3, -5t^4, -5t^4):       {'OK' if ok4 else 'FAIL'}")

    print()
    print("=" * 60)
    print(f"Exhaustive search for |x|, |y|, |z| <= {BOUND}")
    print("=" * 60)
    solutions = search_solutions(BOUND)
    print(f"Found {len(solutions)} solutions.\n")

    seeds: list[tuple[int, int, int]] = []
    for x, y, z in solutions:
        label = classify(x, y, z)
        print(f"  ({x:5d}, {y:5d}, {z:5d})  ->  {label}")
        if label == "unknown seed":
            seeds.append((x, y, z))

    if seeds:
        print(f"\nNEW SEEDS NOT IN ANY KNOWN FAMILY ({len(seeds)}):")
        for s in seeds:
            print(f"  {s}  val={eq(*s)}")
    else:
        print("\nAll found solutions are accounted for by the seven known families.")

    print()
    print("=" * 60)
    print("Weighted-homogeneity check")
    print("=" * 60)
    print("Weights: wt(x)=3, wt(y)=4, wt(z)=4, degree=12.")
    print("For any solution (a,b,c) and integer t,")
    print("  (t^3*a, t^4*b, t^4*c) is also a solution.")
    seed = (1, 0, -1)
    print(f"\nSeed {seed}: eq={eq(*seed)}")
    for t in range(-3, 4):
        a, b, c = seed
        s = (t ** 3 * a, t ** 4 * b, t ** 4 * c)
        print(f"  t={t:2d}: {s}  eq={eq(*s)}")


if __name__ == "__main__":
    main()
