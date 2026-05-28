from sage.all import *
import json

proof.arithmetic(True)


def squarefree_decomp(n):
    n = ZZ(n)
    d = n.squarefree_part()
    u2 = n // d
    u = ZZ(u2).isqrt()
    if u * u != u2:
        raise ValueError(f"Non-square cofactor for n={n}")
    return ZZ(d), ZZ(u)


def original_eq(x, y, z):
    return 6 + x**3 - y**2 + y**2 * z**2 == 0


def certify_bound(B):
    if B < 2:
        raise ValueError("B must be >= 2")

    curves = {}
    witness = []
    checked_z = []

    for z in range(2, B + 1, 2):
        m = z * z - 1
        d, u = squarefree_decomp(m)

        if d not in curves:
            E = EllipticCurve([0, 0, 0, 0, -6 * d**3])
            rank = int(E.rank(proof=True))
            gens = [str(P) for P in E.gens()]
            pts = [tuple(P) for P in E.integral_points(mw_base="mwrank")]
            curves[int(d)] = {
                "rank": rank,
                "gens": gens,
                "integral_points": [(int(X), int(Y)) for (X, Y) in pts],
            }

        for (X, Y) in curves[int(d)]["integral_points"]:
            if X % d != 0:
                continue
            if Y % (d * d * u) != 0:
                continue

            x = -X // d
            y = Y // (d * d * u)

            if X != -d * x:
                raise AssertionError("X transform mismatch")
            if Y != d * d * u * y:
                raise AssertionError("Y transform mismatch")
            if x**3 + d * (u * y) ** 2 != -6:
                raise AssertionError("Twist equation mismatch")
            if z * z - d * u * u != 1:
                raise AssertionError("Pell decomposition mismatch")
            if not original_eq(x, y, z):
                raise AssertionError("Original equation mismatch")

            witness.append((int(x), int(y), int(z)))
            witness.append((int(x), int(y), int(-z)))

        checked_z.append(int(z))

    cert = {
        "bound_B": int(B),
        "checked_even_z_positive": checked_z,
        "curves": curves,
        "solutions_found_in_range": witness,
    }
    out = f"certificate_B{B}.json"
    with open(out, "w") as f:
        json.dump(cert, f, indent=2)
    print(out)
    print("solutions_found", len(witness))


if __name__ == "__main__":
    import sys

    if len(sys.argv) != 2:
        raise SystemExit("Usage: sage -python certify_even_z.sage <B>")
    B = int(sys.argv[1])
    certify_bound(B)
