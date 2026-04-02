#!/usr/bin/env python3
"""
modular_analysis.py
===================
Modular arithmetic analysis for the Diophantine equation

    y^3 - y = x^4 - 2x - 2

For each modulus m this script:
  1. Computes the image of  y -> y^3 - y  in Z/mZ  (the LHS residue set).
  2. Computes the image of  x -> x^4 - 2x - 2  in Z/mZ  (the RHS residue set).
  3. Reports which residues of x are *forbidden* (RHS value not attainable by LHS).
  4. Searches for a single modulus that rules out all solutions (empty intersection).

A modulus m giving an empty intersection  LHS(Z/mZ) ∩ RHS(Z/mZ) = ∅  would
constitute a complete elementary proof of non-existence.
"""


def lhs_residues(m: int) -> set[int]:
    """Image of y^3 - y in Z/mZ."""
    return {(y**3 - y) % m for y in range(m)}


def rhs_residues(m: int) -> set[int]:
    """Image of x^4 - 2x - 2 in Z/mZ."""
    return {(x**4 - 2*x - 2) % m for x in range(m)}


def allowed_x(m: int) -> list[int]:
    """Residues of x mod m that are not immediately ruled out."""
    lhs = lhs_residues(m)
    return [x for x in range(m) if (x**4 - 2*x - 2) % m in lhs]


def forbidden_x(m: int) -> list[int]:
    """Residues of x mod m that are immediately ruled out."""
    lhs = lhs_residues(m)
    return [x for x in range(m) if (x**4 - 2*x - 2) % m not in lhs]


def search_for_empty_modulus(limit: int = 2000) -> int | None:
    """
    Return the first m in [2, limit] for which
        {x^4 - 2x - 2 mod m} ∩ {y^3 - y mod m} = ∅,
    or None if none is found.
    """
    for m in range(2, limit + 1):
        if lhs_residues(m).isdisjoint(rhs_residues(m)):
            return m
    return None


def main():
    # -----------------------------------------------------------------------
    # 1. Search for a single-modulus proof of non-existence
    # -----------------------------------------------------------------------
    print("=" * 70)
    print("SEARCH FOR SINGLE-MODULUS PROOF (empty intersection)")
    print("=" * 70)
    result = search_for_empty_modulus(2000)
    if result is not None:
        m = result
        print(f"\nPROOF: no solutions exist mod {m}")
        print(f"  LHS residues: {sorted(lhs_residues(m))}")
        print(f"  RHS residues: {sorted(rhs_residues(m))}")
    else:
        print("\nNo single modulus up to 2000 produces an empty intersection.")
        print("Non-existence cannot be proved by a single congruence alone.")

    # -----------------------------------------------------------------------
    # 2. Key necessary conditions
    # -----------------------------------------------------------------------
    print("\n" + "=" * 70)
    print("KEY MODULAR CONSTRAINTS")
    print("=" * 70)

    key_moduli = [3, 4, 5, 7, 9, 11, 13]
    for m in key_moduli:
        lhs = sorted(lhs_residues(m))
        rhs_map = {x: (x**4 - 2*x - 2) % m for x in range(m)}
        allow = allowed_x(m)
        forb  = forbidden_x(m)
        frac_eliminated = len(forb) / m
        print(f"\nmod {m}:")
        print(f"  LHS image  = {lhs}")
        print(f"  x -> RHS   = {rhs_map}")
        print(f"  Allowed x  = {allow}")
        print(f"  Forbidden x = {forb}  ({frac_eliminated:.0%} of residues eliminated)")

    # -----------------------------------------------------------------------
    # 3. CRT density estimate
    # -----------------------------------------------------------------------
    print("\n" + "=" * 70)
    print("COMBINED DENSITY ESTIMATE")
    print("=" * 70)

    filter_moduli = [2, 3, 5, 7, 11, 13]
    lcm = 1
    for p in filter_moduli:
        lcm *= p   # they are pairwise coprime so lcm = product = 30030

    forbidden_sets = {m: set(forbidden_x(m)) for m in filter_moduli}

    survivors = [
        x for x in range(lcm)
        if all(x % m not in forbidden_sets[m] for m in filter_moduli)
    ]
    print(f"\nLCM({filter_moduli}) = {lcm}")
    print(f"Survivors:  {len(survivors)} out of {lcm}")
    print(f"Density:    {len(survivors)/lcm:.6f}  ({len(survivors)/lcm:.4%})")
    print(f"\nCombined condition: x ≡ 4 (mod 6) and x ≡ 4 or 22 (mod 30)")
    print("  (mod 6 is the sharpest single-modulus constraint)")

    # -----------------------------------------------------------------------
    # 4. Constraints on y given the constraints on x
    # -----------------------------------------------------------------------
    print("\n" + "=" * 70)
    print("CONSTRAINTS ON y GIVEN CONSTRAINTS ON x")
    print("=" * 70)

    print("\nGiven x ≡ 4 (mod 6), the RHS mod 12 is always ≡ 6 (mod 12):")
    for x_val in [4, 10, 16, 22, 28, 34]:
        r = (x_val**4 - 2*x_val - 2) % 12
        print(f"  x = {x_val:>3}: RHS mod 12 = {r}")

    m = 12
    lhs12 = {y: (y**3 - y) % 12 for y in range(12)}
    y_allowed_mod12 = [y for y, r in lhs12.items() if r == 6]
    print(f"\ny^3 - y ≡ 6 (mod 12) iff y ≡ {y_allowed_mod12} (mod 12)")
    print("i.e. y ≡ 2 or 6 or 10 (mod 12),  equivalently  y ≡ 2 (mod 4)")

    # -----------------------------------------------------------------------
    # 5. Summary table
    # -----------------------------------------------------------------------
    print("\n" + "=" * 70)
    print("SUMMARY TABLE")
    print("=" * 70)
    rows = [
        ("mod 2", "x odd is impossible", "y^3-y ≡ 0,2 mod 4; RHS ≡ 1 mod 4 for odd x"),
        ("mod 3", "x ≡ 1 (mod 3)",       "y^3-y ≡ 0 always; RHS ≡ 0 only for x≡1"),
        ("mod 5", "x ≡ 2 or 4 (mod 5)", "RHS for x≡0,1,3 not in LHS image"),
        ("mod 7", "x ≢ 0 (mod 7)",       "RHS ≡ 5 for x≡0 is not in LHS image"),
        ("mod 11","x ≡ 0,2,6,7,10 (mod 11)","6 out of 11 residues eliminated"),
        ("mod 13","x ≢ 4,8,12 (mod 13)", "3 out of 13 residues eliminated"),
    ]
    print(f"\n  {'Modulus':<10} {'Constraint':<30} {'Reason'}")
    print("  " + "-" * 68)
    for m_str, cond, reason in rows:
        print(f"  {m_str:<10} {cond:<30} {reason}")


if __name__ == "__main__":
    main()
