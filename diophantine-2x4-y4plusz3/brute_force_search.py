"""
Brute-force search for integer solutions to 2*x^4 - y^4 + z^3 = 0.
Equivalently: z^3 = y^4 - 2*x^4.

The equation is weighted-homogeneous of degree 12 with weights
  wt(x) = wt(y) = 3,  wt(z) = 4.
If (x0, y0, z0) is a solution, then (t^3*x0, t^3*y0, t^4*z0) is also
a solution for any integer t.

Six explicit infinite parametric families are discovered below.

Search result (|x|, |y| <= 500): all solutions belong to one of Families 1–5.
Family 6 seed (1922, 961, -29791) appears only for |x|, |y| <= 2500.
No sporadic solutions are found within |x|, |y| <= 2500.
"""
import math


# --------------------------------------------------------------------------
# Cube extraction
# --------------------------------------------------------------------------

def integer_cube_root(n: int):
    """Return (True, c) if n = c^3 for some integer c, else (False, None)."""
    if n == 0:
        return True, 0
    sign = 1 if n > 0 else -1
    abs_n = abs(n)
    c_approx = round(abs_n ** (1 / 3))
    for c in range(max(0, c_approx - 2), c_approx + 3):
        if c ** 3 == abs_n:
            return True, sign * c
    return False, None


# --------------------------------------------------------------------------
# Parametric families
# --------------------------------------------------------------------------

def family1(t: int):
    """Family 1:  (0, t^3, t^4)  --  from x=0, z^3 = y^4 with y=t^3, z=t^4."""
    return (0, t ** 3, t ** 4)


def family2(t: int):
    """Family 2:  (t^3, t^3, -t^4)  --  from y=x, x^4 + z^3 = 0."""
    return (t ** 3, t ** 3, -(t ** 4))


def family3(t: int):
    """Family 3:  (4*t^3, 0, -8*t^4)  --  from y=0, 2x^4 + z^3 = 0.
    With x = 4*t^3:  2*(4*t^3)^4 = 512*t^12 = (8*t^4)^3, so z = -8*t^4."""
    return (4 * t ** 3, 0, -8 * t ** 4)


def family4(t: int):
    """Family 4:  (14*t^3, 21*t^3, 49*t^4)  --  computationally discovered.
    Seed (14, 21, 49): 2*(2*7)^4 - (3*7)^4 + (7^2)^3
                     = 7^4*(2*16 - 81) + 7^6 = 7^4*(-49+49) = 0."""
    return (14 * t ** 3, 21 * t ** 3, 49 * t ** 4)


def family5(t: int):
    """Family 5:  (196*t^3, 392*t^3, 2744*t^4)  --  computationally discovered.
    Seed (196, 392, 2744) = (4*7^2, 8*7^2, 8*7^3).
    Core identity: 2*4^4 - 8^4 + 8^3*7 = 512 - 4096 + 3584 = 0.
    Derivation: setting y=2x gives (2-16)*x^4 + z^3 = 0, i.e. z^3 = 14*x^4;
    taking x = 4*7^2*t^3 yields z = 8*7^3*t^4 = 2744*t^4."""
    return (196 * t ** 3, 392 * t ** 3, 2744 * t ** 4)


def family6(t: int):
    """Family 6:  (1922*t^3, 961*t^3, -29791*t^4)  --  computationally discovered.
    Seed (1922, 961, -29791) = (2*31^2, 31^2, -31^3).
    Core identity: 2*2^4 - 1^4 - 31 = 32 - 1 - 31 = 0.
    Verification: 2*(2*31^2)^4 - (31^2)^4 + (-31^3)^3 = 31^8*(32 - 1 - 31) = 0.
    This seed is found only for |x|, |y| <= 2500 (lies outside the N=500 range)."""
    return (1922 * t ** 3, 961 * t ** 3, -(29791 * t ** 4))


def in_family(x: int, y: int, z: int) -> str:
    """Return a string label if (x, y, z) belongs to one of the six families."""
    for t in range(-200, 201):
        if (x, y, z) == family1(t):
            return f"Family 1 (t={t})"
        if (x, y, z) == family2(t):
            return f"Family 2 (t={t})"
        # Family 2 with y -> -y:  (t^3, -t^3, -t^4)
        if (x, y, z) == (t ** 3, -(t ** 3), -(t ** 4)):
            return f"Family 2b (t={t})"
        if (x, y, z) == family3(t):
            return f"Family 3 (t={t})"
        # Family 3 with x -> -x:  (-4*t^3, 0, -8*t^4)
        if (x, y, z) == (-(4 * t ** 3), 0, -8 * t ** 4):
            return f"Family 3' (t={t})"
        if (x, y, z) == family4(t):
            return f"Family 4 (t={t})"
        # Family 4 with y -> -y:  (14*t^3, -21*t^3, 49*t^4)
        if (x, y, z) == (14 * t ** 3, -(21 * t ** 3), 49 * t ** 4):
            return f"Family 4b (t={t})"
        # Family 4 with x -> -x:  (-14*t^3, 21*t^3, 49*t^4)
        if (x, y, z) == (-(14 * t ** 3), 21 * t ** 3, 49 * t ** 4):
            return f"Family 4c (t={t})"
        # Family 4 with x,y -> -x,-y:  (-14*t^3, -21*t^3, 49*t^4)
        if (x, y, z) == (-(14 * t ** 3), -(21 * t ** 3), 49 * t ** 4):
            return f"Family 4d (t={t})"
        if (x, y, z) == family5(t):
            return f"Family 5 (t={t})"
        # Family 5 with x -> -x:  (-196*t^3, 392*t^3, 2744*t^4)
        if (x, y, z) == (-(196 * t ** 3), 392 * t ** 3, 2744 * t ** 4):
            return f"Family 5b (t={t})"
        # Family 5 with y -> -y:  (196*t^3, -392*t^3, 2744*t^4)
        if (x, y, z) == (196 * t ** 3, -(392 * t ** 3), 2744 * t ** 4):
            return f"Family 5c (t={t})"
        # Family 5 with x,y -> -x,-y:  (-196*t^3, -392*t^3, 2744*t^4)
        if (x, y, z) == (-(196 * t ** 3), -(392 * t ** 3), 2744 * t ** 4):
            return f"Family 5d (t={t})"
        if (x, y, z) == family6(t):
            return f"Family 6 (t={t})"
        # Family 6 with x -> -x:  (-1922*t^3, 961*t^3, -29791*t^4)
        if (x, y, z) == (-(1922 * t ** 3), 961 * t ** 3, -(29791 * t ** 4)):
            return f"Family 6b (t={t})"
    return "SPORADIC"


# --------------------------------------------------------------------------
# Main search
# --------------------------------------------------------------------------

def search(x_max: int) -> list:
    """Return all solutions (x, y, z) with |x|, |y| <= x_max."""
    solutions = []
    for x in range(-x_max, x_max + 1):
        for y in range(-x_max, x_max + 1):
            rhs = y ** 4 - 2 * x ** 4
            ok, z = integer_cube_root(rhs)
            if ok and 2 * x ** 4 - y ** 4 + z ** 3 == 0:
                solutions.append((x, y, z))
    return solutions


# --------------------------------------------------------------------------
# Verification helpers
# --------------------------------------------------------------------------

def verify_family(name, triples):
    """Verify that all listed triples are genuine solutions."""
    failures = []
    for t, (x, y, z) in triples:
        if 2 * x ** 4 - y ** 4 + z ** 3 != 0:
            failures.append((t, x, y, z))
    if failures:
        print(f"  FAILURES in {name}: {failures}")
    else:
        print(f"  All verified for {name}.")


if __name__ == "__main__":
    import sys

    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200

    print("=" * 60)
    print(f"Searching for solutions to  2*x^4 - y^4 + z^3 = 0")
    print(f"with |x|, |y| <= {N}.")
    print("=" * 60)

    solutions = search(N)
    print(f"\nTotal solutions found: {len(solutions)}\n")

    # Classify
    sporadic = []
    family_counts = {}
    for sol in solutions:
        label = in_family(*sol)
        family_counts[label.split(" (")[0]] = family_counts.get(label.split(" (")[0], 0) + 1
        if label == "SPORADIC":
            sporadic.append(sol)

    print("Solution counts by family:")
    for fam, count in sorted(family_counts.items()):
        print(f"  {fam}: {count}")

    if sporadic:
        print(f"\nSPORADIC solutions (outside the four main families): {len(sporadic)}")
        for s in sporadic:
            print(f"  {s}")
    else:
        print(f"\nNo sporadic solutions found for |x|, |y| <= {N}.")

    print()

    # Verify the four families for small t
    print("Verifying families for |t| <= 10:")
    verify_family("Family 1 (0, t^3, t^4)", [(t, family1(t)) for t in range(-10, 11)])
    verify_family("Family 2 (t^3, t^3, -t^4)", [(t, family2(t)) for t in range(-10, 11)])
    verify_family("Family 3 (4t^3, 0, -8t^4)", [(t, family3(t)) for t in range(-10, 11)])
    verify_family("Family 4 (14t^3, 21t^3, 49t^4)", [(t, family4(t)) for t in range(-10, 11)])
    verify_family("Family 5 (196t^3, 392t^3, 2744t^4)", [(t, family5(t)) for t in range(-10, 11)])
    verify_family("Family 6 (1922t^3, 961t^3, -29791t^4)", [(t, family6(t)) for t in range(-10, 11)])

    print()

    # Print small explicit solutions
    print("Small explicit solutions (|x|,|y| <= 15):")
    small = [(x, y, z) for (x, y, z) in solutions if abs(x) <= 15 and abs(y) <= 15]
    small.sort(key=lambda s: (abs(s[0]) + abs(s[1]) + abs(s[2]), s))
    for sol in small:
        fam = in_family(*sol)
        print(f"  {sol}  [{fam}]  check: {2*sol[0]**4 - sol[1]**4 + sol[2]**3}")

    print()
    print("Key algebraic identity for Family 4:")
    print(f"  2*(14)^4 - (21)^4 + (49)^3 = {2*14**4 - 21**4 + 49**3}")
    print(f"  = 7^4 * (2*2^4 - 3^4) + 7^6 = 7^4 * (32 - 81 + 49) = 0")
    print(f"  Identity check: 2*2^4 - 3^4 + 7^2 = {2*2**4 - 3**4 + 7**2}")
    print()
    print("Key algebraic identity for Family 5:")
    print(f"  2*(196)^4 - (392)^4 + (2744)^3 = {2*196**4 - 392**4 + 2744**3}")
    print(f"  = 7^8 * (2*4^4 - 8^4 + 8^3*7) = 7^8 * (512 - 4096 + 3584) = 0")
    print(f"  Identity check: 2*4^4 - 8^4 + 8^3*7 = {2*4**4 - 8**4 + 8**3*7}")
    print()
    print("Key algebraic identity for Family 6:")
    print(f"  2*(1922)^4 - (961)^4 + (-29791)^3 = {2*1922**4 - 961**4 + (-29791)**3}")
    print(f"  = 31^8 * (2*2^4 - 1^4 - 31) = 31^8 * (32 - 1 - 31) = 0")
    print(f"  Identity check: 2*2^4 - 1 - 31 = {2*2**4 - 1 - 31}")
