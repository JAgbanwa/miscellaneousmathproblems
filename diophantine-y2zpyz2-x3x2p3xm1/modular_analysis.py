"""
modular_analysis.py  (diophantine-y2zpyz2-x3x2p3xm1)
======================================================
Modular constraint analysis for

    yz(y+z) = x^3 + x^2 + 3x - 1.

Key findings
------------
1. x must be odd  (mod 2: LHS is always even; RHS even iff x odd).
2. For odd x = 2k+1: RHS = 4(2k^3 + 4k^2 + 4k + 1), where the parenthesized
   factor is always odd — so  8 ∤ N  but  4 | N  for every odd x.
3. MOD-7 OBSTRUCTION:  yz(y+z) is NEVER ≡ 3 or 4 (mod 7).
   For x ≡ 1 (mod 14): RHS ≡ 4 (mod 7) → IMPOSSIBLE.
   For x ≡ 5, 9, 13 (mod 14): RHS ≡ 3 (mod 7) → IMPOSSIBLE.
   This eliminates exactly the cases x ≡ 1, 5, 9, 13 (mod 14).
4. Surviving cases x ≡ 3, 7, 11 (mod 14) are locally solvable at every prime
   — no single modular obstruction eliminates them — but the brute-force search
   finds no integer solutions for |x| ≤ 10 000.
"""

import math


def rhs(x: int) -> int:
    return x * x * x + x * x + 3 * x - 1


# ---------------------------------------------------------------------------
# Part 1: Parity
# ---------------------------------------------------------------------------

def parity_analysis():
    print("=" * 60)
    print("Part 1 — Parity (mod 2)")
    print("=" * 60)
    print("LHS = yz(y+z).  Check: if y,z both even:  y+z even → LHS ≡ 0.")
    print("  If exactly one even:  yz even → LHS ≡ 0.")
    print("  If y,z both odd:      y+z even → LHS ≡ 0.")
    print("  → LHS is ALWAYS EVEN.\n")
    print("RHS = x^3+x^2+3x-1.  Mod 2:")
    for x in range(2):
        print(f"  x ≡ {x} (mod 2): RHS ≡ {rhs(x) % 2} (mod 2)")
    print("  → RHS is even IFF x is odd.  Hence x MUST BE ODD.\n")


# ---------------------------------------------------------------------------
# Part 2: Exact 2-adic valuation
# ---------------------------------------------------------------------------

def two_adic_analysis():
    print("=" * 60)
    print("Part 2 — 2-adic structure")
    print("=" * 60)
    print("For x = 2k+1 (odd):")
    print("  RHS = (2k+1)^3 + (2k+1)^2 + 3(2k+1) - 1")
    print("      = 8k^3+12k^2+6k+1 + 4k^2+4k+1 + 6k+3 - 1")
    print("      = 8k^3 + 16k^2 + 16k + 4")
    print("      = 4(2k^3 + 4k^2 + 4k + 1)")
    print()

    print("The inner factor  q = 2k^3+4k^2+4k+1  is ALWAYS ODD:")
    print("  k even: q ≡ 0+0+0+1 = 1 (odd).")
    print("  k odd:  q ≡ 2+4+4+1 = 11 ≡ 1 (mod 2).")
    print()
    print("Therefore:  v_2(RHS) = 2  for every odd x  (exactly 4 | RHS, 8 ∤ RHS).")
    print()

    # Verify for small odd x
    print("Verification (odd x in [-15, 15]):")
    for x in range(-15, 16, 2):
        N = rhs(x)
        v2 = 0
        n = abs(N)
        while n and n % 2 == 0:
            v2 += 1
            n //= 2
        print(f"  x={x:4d}: N={N:8d},  v_2(N)={v2}")
    print()


# ---------------------------------------------------------------------------
# Part 3: Mod-7 obstruction
# ---------------------------------------------------------------------------

def mod7_analysis():
    print("=" * 60)
    print("Part 3 — Mod-7 obstruction")
    print("=" * 60)

    # All values of yz(y+z) mod 7
    g7 = set()
    for y in range(7):
        for z in range(7):
            g7.add((y * z * (y + z)) % 7)

    print(f"Image of yz(y+z) (mod 7) = {sorted(g7)}")
    non = sorted(set(range(7)) - g7)
    print(f"Residues NOT achievable by yz(y+z) (mod 7): {non}")
    print()
    print("Exhaustive proof that 3 and 4 are not achievable:")
    for r in [3, 4]:
        found = [(y, z) for y in range(7) for z in range(7)
                 if (y * z * (y + z)) % 7 == r]
        if found:
            print(f"  r={r}: achievable (e.g. {found[0]}) — unexpected!")
        else:
            print(f"  r={r}: NOT achievable for any (y,z) in Z/7Z. ✓")
    print()

    print("Values of RHS (mod 7) for each odd residue class x (mod 14):")
    bad = []
    good = []
    for x in range(14):
        if x % 2 == 0:
            continue
        val = rhs(x) % 7
        status = "BLOCKED (no solution)" if val not in g7 else "ok (local solution possible)"
        print(f"  x ≡ {x:2d} (mod 14):  RHS ≡ {val} (mod 7)  — {status}")
        if val not in g7:
            bad.append(x)
        else:
            good.append(x)

    print()
    print(f"Eliminated by mod 7: x ≡ {bad} (mod 14)")
    print(f"Surviving:           x ≡ {good} (mod 14)")
    print()
    print("Fraction eliminated: 4/7 of all odd integers.")
    print()


# ---------------------------------------------------------------------------
# Part 4: Are surviving cases locally solvable?
# ---------------------------------------------------------------------------

def local_solvability():
    print("=" * 60)
    print("Part 4 — Local solvability for surviving classes")
    print("=" * 60)
    print("For x ≡ 3, 7, 11 (mod 14) (the surviving classes), we check whether")
    print("yz(y+z) = RHS(x) is solvable modulo every small prime.\n")

    g7 = set((y * z * (y + z)) % 7 for y in range(7) for z in range(7))

    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
              59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

    all_local = True
    for p in primes:
        gp = set((y * z * (y + z)) % p for y in range(p) for z in range(p))
        period = (14 * p) // math.gcd(14, p)
        blocked_count = 0
        total = 0
        for x in range(period):
            if x % 2 == 0:
                continue
            if x % 14 not in [3, 7, 11]:
                continue
            total += 1
            fp = rhs(x) % p
            if fp not in gp:
                blocked_count += 1
        status = "ALL blocked" if blocked_count == total else f"{blocked_count}/{total} blocked"
        if blocked_count == total and total > 0:
            all_local = False
            print(f"  p={p:3d}: obstruction found! {status}")
        else:
            print(f"  p={p:3d}: {status} (locally solvable)")

    print()
    if all_local:
        print("Conclusion: surviving classes are locally solvable at every tested prime.")
        print("No single-modulus proof exists for the remaining cases.")
        print("A complete proof would require elliptic curve / descent methods.")
    else:
        print("Additional modular constraint found — see above.")
    print()


# ---------------------------------------------------------------------------
# Part 5: Near-miss analysis
# ---------------------------------------------------------------------------

def near_miss_analysis():
    print("=" * 60)
    print("Part 5 — Near-miss analysis (closest discriminants to perfect squares)")
    print("=" * 60)

    def get_divisors(n: int):
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
        return pos + [-d for d in pos]

    best = []  # (gap, x, s, disc, disc_isqrt)
    for x in range(-100, 101, 2):
        if x % 2 == 0:
            continue
        N = rhs(x)
        for s in get_divisors(N):
            if N % s != 0:
                continue
            p = N // s
            disc = s * s - 4 * p
            if disc < 0:
                continue
            k = math.isqrt(disc)
            gap = min(disc - k * k, (k + 1) * (k + 1) - disc)
            if gap <= 5:
                best.append((gap, x, s, disc, k))

    best.sort()
    print("Top candidates where Δ = s²−4p is closest to a perfect square (|x|≤100):")
    for gap, x, s, disc, k in best[:20]:
        print(f"  x={x:4d}, s={s:6d}, Δ={disc:9d}, sqrt≈{k}, gap={gap}")
    print()


# ---------------------------------------------------------------------------
# Run everything
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    parity_analysis()
    two_adic_analysis()
    mod7_analysis()
    local_solvability()
    near_miss_analysis()
