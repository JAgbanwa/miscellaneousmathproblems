"""
brute_force_search.py  (diophantine-7x4plus6y4plus4z4-t4)
===========================================================
Exhaustive search for non-zero integer solutions to

    7x^4 + 6y^4 + 4z^4 = t^4.

Since the equation is homogeneous of degree 4, rational solutions correspond
(up to scaling) to integer solutions, and we may restrict to positive primitive
solutions (gcd(x,y,z,t) = 1).

Parity lemma (proved below): any primitive solution must have ALL of x,y,z,t odd.

Search strategy: meet-in-the-middle.
  LHS half: build dict { 7x^4+6y^4 : val -> list of (x,y) }, x,y odd.
  RHS half: iterate over odd (t,z), compute t^4-4z^4, look up in dict.

RESULT: NO primitive solution found for x,y,z,t ODD with max(x,y,z) <= 3000
        (equivalently t <= 6093).
"""

import math
import time


def F(x: int, y: int, z: int, t: int) -> int:
    """Evaluate 7x^4 + 6y^4 + 4z^4 - t^4."""
    return 7*x**4 + 6*y**4 + 4*z**4 - t**4


# ---------------------------------------------------------------------------
# Parity analysis (rigorous)
# ---------------------------------------------------------------------------
def verify_parity_constraints():
    """
    Verify by enumeration that x,y,t must be odd and z must be odd.

    For each choice of parities (even/odd) of x,y,z,t, check whether the
    equation can hold modulo 8.  Since n^4 mod 8 = 0 for n even, 1 for n odd,
    we reduce to a small finite check.
    """
    print("=== Parity verification mod 8 ===")
    # For n in {0,1,...,7}: n^4 mod 8
    fp8 = [n**4 % 8 for n in range(8)]
    print(f"n^4 mod 8 for n=0..7: {fp8}")
    # Any even n: n^4 ≡ 0 (mod 16) and 0 (mod 8).
    # Any odd n: n^4 ≡ 1 (mod 8).
    # Parity class: 0 = even, 1 = odd.
    for px in range(2):
        for py in range(2):
            for pz in range(2):
                for pt in range(2):
                    a = fp8[px]   # representative of x^4 mod 8
                    b = fp8[py]   # y^4
                    c = fp8[pz]   # z^4
                    d = fp8[pt]   # t^4
                    lhs = (7*a + 6*b + 4*c) % 8
                    rhs = d % 8
                    ok = "✓" if lhs == rhs else "✗"
                    parity_str = "({},{},{},{})".format(
                        "odd" if px else "even",
                        "odd" if py else "even",
                        "odd" if pz else "even",
                        "odd" if pt else "even"
                    )
                    print(f"  (x,y,z,t) {parity_str}: LHS≡{lhs}, RHS≡{rhs} {ok}")
    print()
    print("Conclusion: only (odd,odd,odd,odd) satisfies 7x^4+6y^4+4z^4≡t^4 (mod 8)")
    print("when restricting to primitive solutions (otherwise even case forces gcd ≥ 2).")
    print()


# ---------------------------------------------------------------------------
# Main search
# ---------------------------------------------------------------------------
def search(N: int = 3000) -> list:
    """
    Search for primitive solutions (x,y,z,t), all odd, with max(x,y,z) <= N.
    Returns list of found solutions.
    """
    start = time.time()
    print(f"Building LHS dict  7x^4+6y^4  for x,y odd in [1,{N}]...")
    lhs_dict: dict[int, list[tuple[int, int]]] = {}
    for x in range(1, N + 1, 2):
        lx = 7 * x**4
        for y in range(1, N + 1, 2):
            v = lx + 6 * y**4
            lhs_dict.setdefault(v, []).append((x, y))
    print(f"  Dict has {len(lhs_dict)} entries  ({time.time()-start:.1f}s)")

    # Upper bound on t: 7x^4+6y^4+4z^4 <= (7+6+4)*N^4 = 17*N^4, so t <= 17^(1/4)*N
    T_MAX = int(N * 17**0.25) + 2
    print(f"Searching RHS  t^4 - 4z^4  for t,z odd in [1,{max(N, T_MAX)}]...")

    solutions = []
    for t in range(1, T_MAX + 1, 2):
        t4 = t**4
        z_max = min(N, int((t4 / 4)**0.25) + 1)
        for z in range(1, z_max + 1, 2):
            rhs_v = t4 - 4 * z**4
            if rhs_v <= 0:
                break
            if rhs_v in lhs_dict:
                for (x, y) in lhs_dict[rhs_v]:
                    # Extra check: primitive (gcd = 1)?
                    g = math.gcd(math.gcd(x, y), math.gcd(z, t))
                    solutions.append((x, y, z, t, g))
                    tag = "PRIMITIVE" if g == 1 else f"NON-PRIMITIVE (gcd={g})"
                    print(f"  {tag}: (x,y,z,t) = ({x},{y},{z},{t})")
                    print(f"    Check: 7*{x}^4+6*{y}^4+4*{z}^4 = {F(x,y,z,t)+t**4} = {t}^4 = {t**4}")

    elapsed = time.time() - start
    print(f"\nSearch complete in {elapsed:.2f}s.")
    if not solutions:
        print(f"NO solution found.  Covered: x,y,z odd ≤ {N};  t odd ≤ {T_MAX}.")
    return solutions


if __name__ == "__main__":
    verify_parity_constraints()
    solutions = search(N=3000)
    if not solutions:
        print("\nConclusion: 7x^4 + 6y^4 + 4z^4 = t^4 has no known non-zero integer solution.")
