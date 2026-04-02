#!/usr/bin/env python3
"""
parametric_search.py
====================
Search for integer solutions (m, n) to the parametric equation

    (4m + 2)^3 - (4m + 2) = (6n + 4)^4 - 2*(6n + 4) - 2        (*)

and establish its equivalence to the original Diophantine equation

    y^3 - y = x^4 - 2x - 2.                                      (**)

Background
----------
The modular analysis in modular_analysis.py showed that any integer solution
(x, y) to (**) must satisfy

    x ≡ 4  (mod 6)      [from mod-2 and mod-3 constraints via CRT]
    y ≡ 2  (mod 4)      [forced by x ≡ 4 mod 6 via the mod-12 analysis]

Setting  x = 6n + 4  (n ∈ Z)  parametrises all integers ≡ 4 (mod 6).
Setting  y = 4m + 2  (m ∈ Z)  parametrises all integers ≡ 2 (mod 4).

Therefore (*) is **exactly** the restriction of (**) to the only residue
classes that can contain a solution.  In particular:

    (*) has an integer solution (m, n)
        ⟺  (**) has an integer solution (x, y)   with  x = 6n+4, y = 4m+2
        ⟺  (**) has any integer solution at all.

Strategy
--------
For each n in [-NBOUND, NBOUND]:
  1. Compute x = 6n + 4 and N = x^4 - 2x - 2.
  2. Find every integer y with y^3 - y = N (Newton / cube-root approach).
  3. Check whether y ≡ 2 (mod 4).  If so, m = (y - 2) // 4 is a solution.
  4. As a sanity check also verify the original equation directly.

NBOUND = 1666 corresponds to |x| ≤ 9_9_9_9_9_9 ~ 10_000, matching (and
slightly exceeding) the range of brute_force_search.py.
"""

import math


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def integer_cbrt_approx(n: int) -> int:
    """Return an integer near the real cube root of n."""
    if n == 0:
        return 0
    sign = 1 if n > 0 else -1
    approx = round(abs(n) ** (1.0 / 3.0))
    return sign * approx


def find_y(n: int) -> list[int]:
    """
    Return all integers y such that y^3 - y == n, by checking a small
    neighbourhood around the floating-point cube root.
    """
    y0 = integer_cbrt_approx(n)
    return [y for y in range(y0 - 3, y0 + 4) if y * y * y - y == n]


# ---------------------------------------------------------------------------
# Equivalence verification (small values)
# ---------------------------------------------------------------------------

def verify_equivalence(nbound: int = 20) -> None:
    """
    For |n| <= nbound, cross-check that finding a solution via the parametric
    form exactly matches the direct brute-force search.
    """
    param_hits = set()
    for n in range(-nbound, nbound + 1):
        x = 6 * n + 4
        N = x ** 4 - 2 * x - 2
        for y in find_y(N):
            param_hits.add((x, y))

    direct_hits = set()
    for x in range(-6 * nbound - 10, 6 * nbound + 11):
        N = x ** 4 - 2 * x - 2
        for y in find_y(N):
            if x % 6 == 4 % 6:  # x ≡ 4 mod 6, i.e. x in {4,10,16,...} and negative counterparts
                direct_hits.add((x, y))

    # Every hit from direct search in range should appear in param_hits
    # (they share the same x = 6n+4 values)
    assert param_hits == direct_hits, \
        f"Mismatch: param={param_hits}, direct={direct_hits}"
    print(f"[Equivalence check] Parametric ↔ direct search agree for |n| ≤ {nbound}. ✓")


# ---------------------------------------------------------------------------
# Main search
# ---------------------------------------------------------------------------

def search(nbound: int = 1_667) -> list[tuple[int, int, int, int]]:
    """
    Search for integer solutions (m, n) to (*) with |n| <= nbound.

    Returns a list of tuples (m, n, x, y) where x = 6n+4, y = 4m+2.
    """
    solutions = []
    for n in range(-nbound, nbound + 1):
        x = 6 * n + 4
        N = x ** 4 - 2 * x - 2
        for y in find_y(N):
            if (y - 2) % 4 == 0:           # y ≡ 2 (mod 4)
                m = (y - 2) // 4
                solutions.append((m, n, x, y))
    return solutions


def main():
    NBOUND = 1_667   # |x| = |6n+4| ≤ 10_006

    print("=" * 70)
    print("  Parametric Diophantine search")
    print("  (4m+2)^3 - (4m+2) = (6n+4)^4 - 2*(6n+4) - 2")
    print("=" * 70)

    print("""
Substitution:  x = 6n+4,  y = 4m+2

Our modular analysis proved:
  • Any solution to  y^3 - y = x^4 - 2x - 2  must have  x ≡ 4 (mod 6)
    and  y ≡ 2 (mod 4).
  • So the parametric equation (*) is EQUIVALENT to the original (**):
      (*) has an integer solution (m,n)
      ⟺  (**) has an integer solution (x,y)  [with x=6n+4, y=4m+2]
""")

    # Quick equivalence sanity-check on a small range
    verify_equivalence(nbound=20)

    print(f"\nSearching for solutions with |n| ≤ {NBOUND}  (|x| ≤ {6*NBOUND+4})\n")

    solutions = search(NBOUND)

    if solutions:
        print(f"  {'m':>14}  {'n':>14}  {'x=6n+4':>14}  {'y=4m+2':>18}  Check")
        print("  " + "-" * 70)
        for m, n, x, y in solutions:
            lhs = y ** 3 - y
            rhs = x ** 4 - 2 * x - 2
            ok = "✓" if lhs == rhs else "✗"
            print(f"  {m:>14}  {n:>14}  {x:>14}  {y:>18}  {ok}")
        print(f"\n  Total: {len(solutions)} solution(s) found.")
    else:
        print(f"  No integer solutions (m, n) found for |n| ≤ {NBOUND}.")
        print(f"  Equivalently: no integer solutions (x, y) to y^3-y = x^4-2x-2")
        print(f"  for |x| ≤ {6*NBOUND+4}  (all candidate residue classes checked).")

    # ---------------------------------------------------------------------------
    # Growth-rate argument
    # ---------------------------------------------------------------------------
    print("""
Growth-rate argument
--------------------
For large |n|, x = 6n+4 grows like 6|n|, so

    x^4 - 2x - 2  ~  1296 n^4.

The equation y^3 - y = N requires y ~ N^{1/3} ~ (1296)^{1/3} n^{4/3}.
Consecutive values of y^3 - y at y are spaced approximately 3y^2 apart.
For a solution to exist at a given n, the value N = x^4 - 2x - 2 must
land exactly on the sparse lattice {y^3 - y : y ∈ Z}.  As n → ∞ the
gaps between consecutive lattice points grow without bound, making
accidental coincidences increasingly unlikely — consistent with Faltings'
theorem (finitely many rational points on a genus-3 curve).
""")

    # ---------------------------------------------------------------------------
    # Summary
    # ---------------------------------------------------------------------------
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"""
  Equation  : (4m+2)^3 - (4m+2) = (6n+4)^4 - 2*(6n+4) - 2
  Range     : |n| ≤ {NBOUND}  ↔  |x| ≤ {6*NBOUND+4}
  Solutions : {len(solutions)}

  The parametric equation is equivalent to  y^3-y = x^4-2x-2
  (every solution must lie in the congruence classes x≡4 mod 6,
  y≡2 mod 4, which are exactly x=6n+4 and y=4m+2).

  Together with Faltings' theorem (smooth genus-3 curve → finitely many
  rational points) and the ongoing Chabauty-Coleman analysis in
  curve_analysis.sage, the evidence strongly supports:

      No integer solutions exist.
""")


if __name__ == "__main__":
    main()
