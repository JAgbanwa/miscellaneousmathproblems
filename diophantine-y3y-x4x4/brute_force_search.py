"""
Brute-force search for integer solutions to y^3 + y = x^4 + x + 4.

The function f(y) = y^3 + y is strictly increasing on Z, so for each x there
is at most one real y satisfying the equation.  We use Newton's method to find
the real root and check whether the integers immediately around it work.

Search result: NO integer solution exists for |x| <= 10,000.
"""


def f(y: int) -> int:
    """LHS: y^3 + y (strictly increasing)."""
    return y * y * y + y


def g(x: int) -> int:
    """RHS: x^4 + x + 4."""
    return x * x * x * x + x + 4


def real_y(rhs: float) -> float:
    """Newton iteration to find the unique real y with y^3 + y = rhs."""
    # Initial guess
    if rhs >= 0:
        y = rhs ** (1.0 / 3.0)
    else:
        y = -((-rhs) ** (1.0 / 3.0))
    for _ in range(60):
        fy = y ** 3 + y
        fpy = 3.0 * y * y + 1.0
        y -= (fy - rhs) / fpy
    return y


def search(x_min: int, x_max: int) -> list:
    """Return list of integer solutions (x, y) in the given x-range."""
    solutions = []
    for x in range(x_min, x_max + 1):
        rhs = g(x)
        yr = real_y(float(rhs))
        # Check the integer(s) nearest to yr
        n = int(yr)
        for candidate_y in range(n - 2, n + 3):
            if f(candidate_y) == rhs:
                solutions.append((x, candidate_y))
                break
    return solutions


if __name__ == "__main__":
    X_LIM = 10_000
    print(f"Searching for integer solutions to  y^3 + y = x^4 + x + 4")
    print(f"with x in [{-X_LIM}, {X_LIM}]  (total {2 * X_LIM + 1} values).\n")

    solutions = search(-X_LIM, X_LIM)

    if solutions:
        print(f"Solutions found: {solutions}")
    else:
        print("No integer solutions found in the search range.")

    print()
    print("Spot checks:")
    spot_cases = [
        (-1, 4,   "g(-1) = 4, f(1)=2, f(2)=10  (4 is skipped)"),
        ( 0, 4,   "g(0)  = 4, same gap"),
        ( 8, 4108, "g(8) = 4108, f(15)=3390, f(16)=4112  (gap above = 4)"),
        (-8, 4092, "g(-8)= 4092, f(15)=3390, f(16)=4112  (gap above = 20)"),
    ]
    for x, expected_rhs, note in spot_cases:
        rhs = g(x)
        yr = real_y(float(rhs))
        n = int(yr)
        gap_below = rhs - f(n)
        gap_above = f(n + 1) - rhs
        print(f"  x={x:4d}: g(x)={rhs}, y_real~{yr:.4f}, "
              f"gap_below={gap_below}, gap_above={gap_above}.  [{note}]")
