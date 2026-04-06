"""
brute_force_search.py  (diophantine-y2zpyz2-x3x2p3xm1)
=========================================================
Exhaustive search for integer solutions to

    y^2*z + y*z^2 = x^3 + x^2 + 3x - 1,

equivalently  yz(y+z) = x^3 + x^2 + 3x - 1.

Algorithm
---------
For each odd integer x (the parity constraint x odd is proved in analysis_notes.md),
compute N = x^3 + x^2 + 3x - 1 and look for an integer factorisation N = s * p where
s = y + z  and  p = y*z.  Such y, z exist as integers iff the discriminant

    Δ = s^2 - 4p  =  s^2 - 4N/s

is a non-negative perfect square and s + sqrt(Δ) ≡ 0 (mod 2).

For each divisor s of N the value p = N/s is then fixed, so we check whether
Δ = s² - 4p ≥ 0 is a perfect square using integer square root.

This covers ALL integer solutions with x in the search range (not just small y,z),
because every solution gives a divisor s = y+z of N.

RESULT: NO integer solution found for x in [-10 000, 10 000].
"""

import math


# ---------------------------------------------------------------------------
# Core helpers
# ---------------------------------------------------------------------------

def rhs(x: int) -> int:
    """Evaluate x^3 + x^2 + 3x - 1 exactly."""
    return x * x * x + x * x + 3 * x - 1


def isqrt_exact(n: int):
    """Return sqrt(n) if n is a perfect square, else None."""
    if n < 0:
        return None
    k = math.isqrt(n)
    return k if k * k == n else None


def get_divisors(n: int) -> list[int]:
    """
    Return all integer divisors of n (both positive and negative).
    If n == 0 every integer divides it; we return [] and handle that separately.
    """
    if n == 0:
        return []
    n_abs = abs(n)
    pos = []
    i = 1
    while i * i <= n_abs:
        if n_abs % i == 0:
            pos.append(i)
            if i != n_abs // i:
                pos.append(n_abs // i)
        i += 1
    # include both signs
    return pos + [-d for d in pos]


# ---------------------------------------------------------------------------
# Main search
# ---------------------------------------------------------------------------

def search(x_min: int, x_max: int) -> list[tuple[int, int, int]]:
    """
    Return all integer solutions (x, y, z) with x in [x_min, x_max] (odd steps).

    For each odd x, factorise N = rhs(x) and check every divisor s.
    """
    solutions: list[tuple[int, int, int]] = []

    for x in range(x_min | 1, x_max + 1, 2):  # iterate odd integers only
        if (x - x_min) % 2 == 0 and x_min % 2 == 0:
            x += 1  # ensure odd start

    for x in range(x_min, x_max + 1):
        if x % 2 == 0:
            continue  # proved unnecessary: x must be odd
        N = rhs(x)
        if N == 0:
            # x^3+x^2+3x-1=0 has no integer solutions (discriminant < 0, Δ ≈ −176)
            continue

        for s in get_divisors(N):
            if N % s != 0:
                continue
            p = N // s
            disc = s * s - 4 * p
            k = isqrt_exact(disc)
            if k is not None and (s + k) % 2 == 0:
                y = (s + k) // 2
                z = (s - k) // 2
                # Exact integer verification
                assert y * y * z + y * z * z == N, f"Verification failed at ({x},{y},{z})"
                solutions.append((x, y, z))

    return solutions


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    X_LIM = 10_000
    print(f"Searching for integer solutions to  y^2*z + y*z^2 = x^3 + x^2 + 3x - 1")
    print(f"with x in [{-X_LIM}, {X_LIM}]  ({X_LIM + 1} odd values).\n")
    print("Method: exhaustive divisor enumeration — covers ALL solutions in range.\n")

    solutions = search(-X_LIM, X_LIM)

    if solutions:
        print(f"SOLUTIONS FOUND ({len(solutions)}):")
        for sol in solutions[:30]:
            x, y, z = sol
            lhs = y * y * z + y * z * z
            print(f"  (x, y, z) = {sol}   [LHS={lhs}, RHS={rhs(x)}]")
    else:
        print("NO integer solutions found.")

    print(f"\nVerified: x in [{-X_LIM}, {X_LIM}] (odd), ALL divisor factorizations checked.")

    # Quick sanity check for the mod-7 obstruction
    print("\n--- Sanity check: mod-7 obstruction ---")
    g7 = set((y * z * (y + z)) % 7 for y in range(7) for z in range(7))
    print(f"Image of yz(y+z) mod 7: {sorted(g7)}")
    print(f"Residues 3, 4 achievable mod 7: {3 in g7}, {4 in g7}")
    for x in range(14):
        if x % 2 == 1:
            f7 = rhs(x) % 7
            status = "BLOCKED" if f7 not in g7 else "ok"
            print(f"  x ≡ {x:2d} (mod 14): f(x) ≡ {f7} (mod 7)  [{status}]")
