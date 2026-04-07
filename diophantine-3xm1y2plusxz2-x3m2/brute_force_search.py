"""
brute_force_search.py
=====================
Exhaustive integer search for solutions to

    (3x - 1) * y^2 + x * z^2 = x^3 - 2

over integers (x, y, z).

Strategy
--------
Rewrite as:

    x * z^2 = x^3 - 2 - (3x - 1) * y^2

For fixed (x, y), the right-hand side must be non-negative (when x > 0) or
non-positive (when x < 0), and must be divisible by x (when x ≠ 0).
Then z^2 = RHS / x must be a non-negative perfect square.

Separately, for x = 0 the equation reduces to -y^2 = -2, i.e. y^2 = 2,
which has no integer solution.

Pre-filters (derived from modular analysis):
  - x ≡ 0 (mod 3): IMPOSSIBLE  (y^2 ≡ 2 mod 3, not a quadratic residue)
  - x ≡ 2 (mod 3): IMPOSSIBLE  (forces y ≡ z ≡ 0 mod 3, then x^3 ≡ 2 mod 9
                                  but x ≡ 2 mod 3 gives x^3 ≡ 8 mod 9)
  - Therefore only x ≡ 1 (mod 3) needs to be checked.

Search range: |x| ≤ 10,000 (x ≡ 1 mod 3 only).
"""

import math
import sys


def is_perfect_square(n: int):
    """Return (True, sqrt) if n is a non-negative perfect square, else (False, 0)."""
    if n < 0:
        return False, 0
    s = math.isqrt(n)
    if s * s == n:
        return True, s
    return False, 0


def search(x_limit: int = 10_000, verbose: bool = True) -> list:
    solutions = []
    checks = 0

    # Modular proof shows only x ≡ 1 (mod 3) can yield solutions.
    # We iterate x in both positive and negative directions.
    x_candidates = [x for x in range(-x_limit, x_limit + 1) if x % 3 == 1]

    for x in x_candidates:
        if x == 0:
            continue  # x=0 gives y^2=2, impossible

        # For fixed x, determine y bound from (3x-1)*y^2 ≤ |x^3-2| + |x|*z^2
        # A rough bound: |y| ≤ sqrt(|x^3 - 2| / max(1, |3x-1|)) + 2
        denom = abs(3 * x - 1)
        if denom == 0:
            continue  # 3x = 1 not an integer

        num_bound = abs(x**3 - 2) + abs(x) * (abs(x)**2 + 4)
        y_max = int(math.isqrt(num_bound // denom)) + 3

        for y in range(0, y_max + 1):
            # RHS of the equation after isolating x*z^2
            rhs = x**3 - 2 - (3 * x - 1) * y**2

            # Need x | rhs for z^2 = rhs/x to be an integer
            if rhs % x != 0:
                checks += 1
                continue

            z2 = rhs // x
            ok, z = is_perfect_square(z2)
            if ok:
                # Verify (covers both y and -y, z and -z)
                for ys in ([0] if y == 0 else [y, -y]):
                    for zs in ([0] if z == 0 else [z, -z]):
                        val = (3 * x - 1) * ys**2 + x * zs**2 - (x**3 - 2)
                        if val == 0:
                            sol = (x, ys, zs)
                            if sol not in solutions:
                                solutions.append(sol)
                            if verbose:
                                print(f"  SOLUTION: x={x}, y={ys}, z={zs}")
            checks += 1

        if verbose and abs(x) % 1000 == 1:
            print(f"Progress: x={x}, checks so far: {checks}")

    return solutions


if __name__ == "__main__":
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000
    print(f"Searching for solutions to (3x-1)*y^2 + x*z^2 = x^3 - 2")
    print(f"Range: x ≡ 1 (mod 3), |x| ≤ {limit}")
    print(f"Pre-filter: only x ≡ 1 (mod 3) checked (mod-3 obstruction for x ≡ 0,2 mod 3)")
    print()

    sols = search(limit, verbose=True)

    print()
    if sols:
        print(f"Found {len(sols)} solution(s):")
        for s in sols:
            x, y, z = s
            lhs = (3 * x - 1) * y**2 + x * z**2
            rhs = x**3 - 2
            print(f"  (x, y, z) = {s},  LHS={lhs}, RHS={rhs}, check={lhs == rhs}")
    else:
        print(f"No integer solutions found for |x| ≤ {limit}.")
        print()
        print("This is consistent with the theoretical proof that no solutions exist.")
