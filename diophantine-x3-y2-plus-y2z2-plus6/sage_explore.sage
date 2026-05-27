# Extensive search and analysis for the equation
#   6 + x^3 - y^2 + y^2 z^2 = 0
# Equivalently:  X^3 - 6 = (z^2 - 1) y^2  where X = -x

print("=" * 70)
print("Step 1: Brute force search for solutions")
print("=" * 70)

# We have X >= 2, X = 1 (mod 4), y odd >= 1, z even >= 2
# Iterate (z, y) and check if X^3 = (z^2-1) y^2 + 6 is a cube

solutions = []
Z_MAX = 5000
Y_MAX = 50000

for z in range(2, Z_MAX + 1, 2):
    D = z*z - 1
    # for y from 1, X^3 = D y^2 + 6
    # X grows like (D)^{1/3} y^{2/3}; for fixed z, y can be large
    # but we bound y by Y_MAX
    for y in range(1, Y_MAX + 1, 2):
        N = D * y * y + 6
        # check N is a cube
        X = round(N**(1/3))
        for dx in [-1, 0, 1]:
            if (X + dx) > 0 and (X + dx)**3 == N:
                xv = X + dx
                if xv % 4 == 1:
                    print(f"  SOLUTION CANDIDATE: x={-xv}, y={y}, z={z}; N={N}")
                    solutions.append((-xv, y, z))

print(f"\nFound {len(solutions)} solutions in range z<={Z_MAX}, y<={Y_MAX}")
print()

print("=" * 70)
print("Step 2: Mordell curve for z=0 sanity check")
print("=" * 70)

E = EllipticCurve([0,0,0,0,6])
print(f"E: y^2 = x^3 + 6")
print(f"Rank = {E.rank()}, Torsion = {E.torsion_subgroup().order()}")
print(f"Integer points: {E.integral_points()}")
print()

print("=" * 70)
print("Step 3: Mordell curve for the OTHER direction: y^2 = x^3 - 6")
print("=" * 70)

E2 = EllipticCurve([0,0,0,0,-6])
print(f"E2: y^2 = x^3 - 6")
print(f"Rank = {E2.rank()}, Torsion = {E2.torsion_subgroup().order()}")
print(f"Integer points: {E2.integral_points()}")
print()

print("=" * 70)
print("Step 4: Examine field K = Q(6^(1/3))")
print("=" * 70)

K.<a> = NumberField(x^3 - 6)
print(f"K = {K}")
print(f"Class number: {K.class_number()}")
print(f"Unit group: {K.unit_group()}")
print(f"Fundamental units: {K.units()}")
print(f"Discriminant: {K.discriminant()}")
print(f"Ring of integers: {K.ring_of_integers()}")
print()
