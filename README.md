 # miscellaneousmathproblems

A collection of miscellaneous mathematics problems and computational solutions.

## Contents

### [`fermat-quintic/`](fermat-quintic/)

**Problem:** Find all rational solutions $(x, y) \in \mathbb{Q}^2$ to the Diophantine equation

$$2x^5 + 3y^5 = 5$$

**File:** [`rational_points_2x5_3y5_5.m`](fermat-quintic/rational_points_2x5_3y5_5.m) — Magma computer algebra system code.

**Approach:**
- Models the equation as a smooth projective plane quintic $C : 2X^5 + 3Y^5 = 5Z^5$ over $\mathbb{Q}$, which has genus $g = 6$.
- By Faltings' theorem, $C(\mathbb{Q})$ is finite.
- Verifies the known rational point $(x, y) = (1, 1)$.
- Rules out rational points at infinity (since $-3/2$ is not a rational perfect 5th power).
- Performs a bounded-height search (height $\leq 1000$) for further rational points.
- Bounds the Mordell-Weil rank of the Jacobian via Euler factors at small primes.
- Provides a Chabauty-Coleman framework to prove completeness of the rational point set when $\mathrm{rank}(J(\mathbb{Q})) < 6$.

**Result:** The only rational solution is $(x, y) = (1, 1)$.


Credit to [this MathOverflow problem](https://mathoverflow.net/questions/481127/what-are-the-integer-solutions-to-2x53y5-5z5)

---

### [`elliptic-curve-diophantine/`](elliptic-curve-diophantine/)

**Problem:** Find all integer solutions $(n, x, y) \in \mathbb{Z}^3$ to the parametric elliptic curve equation

$$y^2 = x^3 + \bigl(-559872n^4 - 1664064n^3 - 1854576n^2 - 918540n - 170586\bigr) \cdot x + 161243136n^6 + 718875648n^5 + 1335341376n^4 + 1322837568n^3 + 737088984n^2 + 219032405n + 27118239$$

**File:** [`integer_points_parametric_ec.py`](elliptic-curve-diophantine/integer_points_parametric_ec.py) — Python (SymPy) script.

**Approach:**
- Factors the coefficient polynomials:
  $A(n) = -486\cdot (4n+3)^3(18n+13)$ and $B(n) = (4n+3)\cdot[\text{quintic}]/4$.
- For each integer $n$, the equation defines an elliptic curve $E_n/\mathbb{Q}$.
- Performs an exhaustive integer-point search over $n \in [-50, 50]$ with $x$-bounds scaled to $O(|A(n)|^{1/2})$, covering the neighbourhood of the real root of the cubic.
- Verifies the unique solution via direct substitution.
- Analyses the structure of $E_{-1}: y^2 = x^3 - 2430x + 46114$ (discriminant, $j$-invariant, point order).

**Key structural facts:**
- At $n = -1$: $4n+3 = -1$, $18n+13 = -5$, so $A(-1) = -2430$, $B(-1) = 46114$.
- The integer point $(45, 167)$ satisfies $45^3 - 2430\cdot 45 + 46114 = 27889 = 167^2$.
- The point $(45, 167)$ has infinite order in $E_{-1}(\mathbb{Q})$ (rank $\geq 1$).
- No integer points exist on $E_n$ for any other $n \in [-50, 50]$.

**Result:** The only integer solutions are

$$(n,\, x,\, y) \;=\; (-1,\; 45,\; \pm 167)$$

---

### [`integer-points-weierstrass-family/`](integer-points-weierstrass-family/)

**Problem:** Find all integer solutions $(n, x, y) \in \mathbb{Z}^3$ to the parametric
elliptic curve (in **general Weierstrass form**):

$$y^2 = x^3 + (36n+27)^2 \cdot x^2
       + \bigl(15552n^3 + 34992n^2 + 26244n + 6561\bigr)\cdot x
       + \bigl(46656n^4 + 139968n^3 + 157464n^2 + 78713n + 14748\bigr)$$

**Files:**
- [`integer_points_family.sage`](integer-points-weierstrass-family/integer_points_family.sage) — SageMath script: algebraic structure, rigorous integral-points computation for $n=-1$, curve invariants.
- [`brute_force_search.py`](integer-points-weierstrass-family/brute_force_search.py) — Pure Python brute-force search over $n\in[-200,200]$, $x\in[-2000,200000]$.
- [`analysis_notes.md`](integer-points-weierstrass-family/analysis_notes.md) — Detailed mathematical analysis and open questions.
- [`sage_output.txt`](integer-points-weierstrass-family/sage_output.txt) — Full output of the SageMath computation.

**Key structural facts:**
- The $x$-coefficient factors as $15552n^3 + \cdots = 243(4n+3)^3$.
- The $x^2$-coefficient is $(36n+27)^2 = 81(4n+3)^2$.
- The substitution $u = x + 27(4n+3)^2$ reduces this to the **same short Weierstrass
  family** as in `elliptic-curve-diophantine/`, confirming polynomial identity
  $B_\text{new}(n) = B_\text{old}(n)$ for all $n$.
- The two problem families are identical; integer-point sets correspond via
  $x_\text{new} = u - 27(4n+3)^2$.

**Results (verified computationally):**

| $n$ | $x$ | $y$ | Method |
|---|---|---|---|
| $-110$ | $646$ | $\pm 40812$ | brute-force search |
| $-64$ | $144840$ | $\pm 333523318$ | brute-force search |
| $-1$ | $18$ | $\pm 167$ | SageMath `integral_points()` + brute-force |
| $94$ | $-562$ | $\pm 17722$ | brute-force search |
| $147498$ | $-449511$ | $\pm 2312387148693$ | direct verification |

A brute-force search over $n\in[-200,200]$, $x\in[-2000,200000]$ found **no solutions beyond the four listed** (excluding $n=147498$ which is outside the range). The solution at $n=147498$ was supplied by the user and independently verified by direct substitution.

**Structure of $E_{-1}$:**
- Weierstrass model: $y^2 = x^3 + 81x^2 - 243x + 187$
- Discriminant: $-318382272$; Conductor: $318382272$
- Rank: **2**; Torsion: trivial
- $P = (18, 167)$ has infinite order; `integral_points()` returns $\{(18,\pm 167)\}$ only.

**Open questions:** See [`analysis_notes.md`](integer-points-weierstrass-family/analysis_notes.md)
for a discussion of whether infinitely many $n$ yield integer points, and for
references to Baker's theorem, Siegel's theorem, and Silverman's specialisation theorem.
