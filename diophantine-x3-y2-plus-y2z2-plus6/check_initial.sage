# Verify some baseline facts
print("=== Mordell curve y^2 = x^3 + 6 (the z=0 case) ===")
E = EllipticCurve([0,0,0,0,6])
print("Rank:", E.rank())
print("Torsion:", E.torsion_subgroup())
print("Integral points:", E.integral_points())

print()
print("=== Mordell curve Y^2 = X^3 - 6 (related curve) ===")
E2 = EllipticCurve([0,0,0,0,-6])
print("Rank:", E2.rank())
print("Torsion:", E2.torsion_subgroup())
print("Integral points:", E2.integral_points())

print()
print("=== Check Q(theta), theta^3 = 6 ===")
K.<theta> = NumberField(x^3 - 6)
print("Class number:", K.class_number())
print("Unit group:", K.unit_group())
print("Fundamental units:", K.unit_group().fundamental_units())

