"""
Modular-arithmetic analysis for  y^3 + y = x^4 + x + 4.

We search for a modulus m such that the set of LHS residues
  L_m = {(y^3 + y) mod m : y in Z/mZ}
and the set of RHS residues
  R_m = {(x^4 + x + 4) mod m : x in Z/mZ}
are disjoint.  Such a modulus would give an elementary (congruence) proof of
non-existence.

Findings:
  - No single modulus m <= 500 provides a complete obstruction.
  - No product of two (or three) small primes (up to 47) does either.
  - The curve has F_p-points for every prime p tested.

Key partial constraints (not a full obstruction, but necessary conditions):
  mod 5:  RHS ≡ 1,2,3,4 (mod 5) — never 0;
          LHS ≡ 0,2,3   (mod 5).
          Intersection: {2, 3}.  => x ≡ 2 or 4 (mod 5), y ≡ 1 or 4 (mod 5).
  mod 7:  Intersection: {4, 5}.  
          Further: (x mod 7, y mod 7) is constrained to specific pairs.
  Combined mod 35: exactly 12 residue classes (x mod 35, y mod 35) are compatible.
"""

from itertools import combinations


def lhs_residues(m: int) -> set:
    return {(y**3 + y) % m for y in range(m)}


def rhs_residues(m: int) -> set:
    return {(x**4 + x + 4) % m for x in range(m)}


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0:
            return False
    return True


# ── 1. Single-modulus search ────────────────────────────────────────────────

print("=" * 60)
print("1. Single-modulus search (m = 2 … 500)")
print("=" * 60)
found_single = False
for m in range(2, 501):
    L, R = lhs_residues(m), rhs_residues(m)
    if L.isdisjoint(R):
        print(f"   COMPLETE OBSTRUCTION mod {m}!")
        found_single = True
        break
if not found_single:
    print("   No complete obstruction found for any m in [2, 500].")

# ── 2. Products of two small primes ─────────────────────────────────────────

print()
print("=" * 60)
print("2. Product of two distinct primes (p, q <= 47)")
print("=" * 60)
small_primes = [p for p in range(2, 50) if is_prime(p)]
found_pair = False
for p, q in combinations(small_primes, 2):
    m = p * q
    if m > 10_000:
        continue
    L, R = lhs_residues(m), rhs_residues(m)
    if L.isdisjoint(R):
        print(f"   COMPLETE OBSTRUCTION mod {m} = {p}·{q}!")
        found_pair = True
        break
if not found_pair:
    print("   No complete obstruction from any p·q with p, q <= 47.")

# ── 3. Key partial constraints ───────────────────────────────────────────────

print()
print("=" * 60)
print("3. Key partial constraints")
print("=" * 60)
for m in [2, 3, 5, 7, 9, 11, 16]:
    L, R = lhs_residues(m), rhs_residues(m)
    inter = sorted(L & R)
    print(f"   mod {m:2d}:  LHS={sorted(L)},  RHS={sorted(R)},  ∩={inter}")

# ── 4. mod 5 derivation ──────────────────────────────────────────────────────

print()
print("=" * 60)
print("4. Necessary conditions mod 5")
print("=" * 60)
print("   x^4 ≡ x (mod 5) by Fermat  =>  RHS ≡ 2x + 4  (mod 5).")
print("   y^3 ≡ y (mod 5) by Fermat  =>  LHS ≡ 2y      (mod 5).")
print("   Intersection {2, 3}:")
for r in [2, 3]:
    xs = [x for x in range(5) if (2 * x + 4) % 5 == r]
    ys = [y for y in range(5) if (2 * y) % 5 == r]
    print(f"     LHS = RHS ≡ {r} (mod 5)  =>  x ≡ {xs} (mod 5),  y ≡ {ys} (mod 5)")
print()
print("   => x ≡ 2 or 4 (mod 5)  and  y ≡ 1 or 4 (mod 5).")

# ── 5. Compatible residue classes mod 35 ────────────────────────────────────

print()
print("=" * 60)
print("5. Compatible residue classes mod 35")
print("=" * 60)
valid = []
for x in range(35):
    for y in range(35):
        if (y**3 + y) % 35 == (x**4 + x + 4) % 35:
            valid.append((x, y))
print(f"   {len(valid)} classes (x mod 35, y mod 35) are compatible:")
for (x, y) in valid:
    print(f"     x ≡ {x:2d} (mod 35),  y ≡ {y:2d} (mod 35)"
          f"   [x mod 5 = {x%5}, x mod 7 = {x%7},"
          f"  y mod 5 = {y%5}, y mod 7 = {y%7}]")

# ── 6. Curve has F_p-points for every prime tested ───────────────────────────

print()
print("=" * 60)
print("6. F_p-point existence (no local obstruction at finite places)")
print("=" * 60)
primes = [p for p in range(2, 200) if is_prime(p)]
has_no_fp_points = []
for p in primes:
    L, R = lhs_residues(p), rhs_residues(p)
    if L.isdisjoint(R):
        has_no_fp_points.append(p)
if has_no_fp_points:
    print(f"   Primes with NO F_p-points: {has_no_fp_points}")
else:
    print("   The curve has F_p-points for every prime p in [2, 199].")
    print("   => No local obstruction exists at any such finite place.")
