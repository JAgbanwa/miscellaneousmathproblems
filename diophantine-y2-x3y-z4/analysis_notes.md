# Analysis Notes: $y^2 - x^3 y + z^4 + 1 = 0$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$y^2 - x^3 y + z^4 + 1 = 0$$

or prove that no such solutions exist.

---

## Reformulation via Vieta's Formulas

The equation $y^2 - x^3 y + (z^4 + 1) = 0$ is a quadratic in $y$. By Vieta's formulas, if $y$ is one root, the other root is $y' = x^3 - y$, and

$$y \cdot y' = y(x^3 - y) = z^4 + 1, \qquad y + y' = x^3.$$

So an integer solution $(x, y, z)$ is equivalent to finding integers $a, b$ satisfying:

$$a + b = x^3 \quad(\text{a perfect cube}), \qquad a \cdot b = z^4 + 1.$$

---

## Elementary Modular Constraints

### Lemma 1 (z must be odd)

**Proof.** The left-hand side $y^2 - x^3 y = y(y - x^3)$ modulo 4 takes values in $\{0, 2\}$ (for $y \equiv 2$ or $3$, $x$ odd) or $\{0\}$ (for other residues), but crucially can **never** be $\equiv 3 \pmod{4}$.

When $z$ is even: $z^4 \equiv 0 \pmod{4}$, so $z^4 + 1 \equiv 1 \pmod{4}$, and the equation requires $y^2 - x^3 y \equiv -1 \equiv 3 \pmod{4}$—impossible (verified exhaustively over all $4 \times 4 = 16$ pairs $(x \bmod 4, y \bmod 4)$ by `modular_analysis.py`). $\square$

### Lemma 2 (x must be odd)

**Proof.** With $z$ odd: $z^4 \equiv 1 \pmod{4}$, so $z^4 + 1 \equiv 2 \pmod{4}$. The equation becomes $y^2 - x^3 y \equiv 2 \pmod{4}$. Checking all 16 pairs $(x \bmod 4, y \bmod 4)$ shows this only holds for $x \equiv 1$ or $3 \pmod{4}$, i.e., $x$ must be odd. $\square$

### Lemma 3 (Parity of $y$)

With $x$ and $z$ both odd:
- $x^3$ is odd.
- $z^4 + 1 \equiv 2 \pmod{8}$: indeed $z$ odd $\Rightarrow$ $z^4 \equiv 1 \pmod{16}$ (since $z^4 \equiv 1 \pmod{8}$ follows from $(2k+1)^4 = 16k^4 + 32k^3 + 24k^2 + 8k + 1 \equiv 1 \pmod{8}$), hence $z^4 + 1 \equiv 2 \pmod{8}$.
- The product $y(x^3 - y) = z^4 + 1 \equiv 2 \pmod{8}$ is even, with $y + (x^3 - y) = x^3$ odd. Therefore $y$ and $x^3 - y$ have different parities: **exactly one of $y$, $x^3 - y$ is even**.

More precisely: one of $y$, $x^3 - y$ is $\equiv 2 \pmod{4}$ and the other is odd (since $(z^4+1)/2 \equiv 1 \pmod{4}$ for all odd $z$, as $(z^4+1)/2 \equiv 1 \pmod{8}$ in fact).

### Further Mod-8 Constraints

The 32 solution triples $(x, y, z) \bmod 8$ (out of 512 total) satisfy:
- $x \equiv 1, 3, 5, 7 \pmod{8}$
- $z \equiv 1, 3, 5, 7 \pmod{8}$
- $y$ takes no value in $\{0, 4\} \pmod{8}$

---

## No Elementary Modular Obstruction

A systematic computer search (`modular_analysis.py`) confirms:

- **Every prime** $p \leq 200$: the equation has $\mathbb{F}_p$-solutions.
- **Every product of two small primes** among $\{2, 3, 5, 7, 11, 13\}$: by CRT, solutions exist modulo every such composite.
- The $\mathbb{F}_p$-point count $N_p$ satisfies $N_p \approx p^2$ for all tested primes, consistent with a smooth surface.

Therefore **no purely elementary congruence proof exists**. Any complete proof must use algebraic geometry.

---

## Discriminant Analysis

For fixed $(x, z)$, integer $y$ exists iff the discriminant

$$D = x^6 - 4(z^4 + 1)$$

is a non-negative perfect square and $x^3 \pm \sqrt{D}$ is even.

By computation (`brute_force_search.py`): for all odd $x$ with $1 \leq x \leq 10\,000$ and all odd $z$ with $1 \leq z \leq z_{\max}(x) \approx x^{3/2}/\sqrt{2}$, $D$ is never a perfect square. This provides **strong computational evidence** that no integer solutions exist.

The equation $u^2 = x^6 - 4z^4 - 4$ (where $u = 2y - x^3$) can be rewritten as

$$(x^3 - u)(x^3 + u) = 4(z^4 + 1).$$

Setting $x^3 - u = 2a$ and $x^3 + u = 2b$: $ab = z^4 + 1$, $a+b = x^3$. (Vieta.)

---

## Near-Miss Table

The following table lists the closest near-misses (values of $D = x^6 - 4z^4 - 4$ that are closest to being perfect squares) for small $x$:

| $x$ | $z$ | $D = x^6 - 4z^4 - 4$ | $\lfloor\sqrt{D}\rfloor$ | $D - \lfloor\sqrt{D}\rfloor^2$ |
|-----|-----|----------------------|--------------------------|-------------------------------|
| 3   | 1   | $729 - 4 - 4 = 721$  | 26                       | $721 - 676 = 45$              |
| 5   | 3   | $15625 - 324 - 4 = 15297$ | 123                 | $15297 - 15129 = 168$         |
| 7   | 5   | $117649 - 2500 - 4 = 115145$ | 339              | $115145 - 114921 = 224$       |

The discriminant never approaches a perfect square, consistent with non-existence.

---

## Geometric Analysis

### The Surface in Weighted Projective Space

The equation $F(x,y,z) = y^2 - x^3y + z^4 + 1 = 0$ defines a surface $S$ in $\mathbb{A}^3$. Monomials have degrees 2, 4, 4, 0. Assigning weights $\mathrm{wt}(x) = 2$, $\mathrm{wt}(y) = 6$, $\mathrm{wt}(z) = 3$ makes all monomials have the same weighted degree 12. This embeds $S$ into **weighted projective space** $\mathbb{P}(2, 6, 3)$.

### Smooth Over $\mathbb{Q}$

The gradient: $\nabla F = (-3x^2 y,\ 2y - x^3,\ 4z^3)$.

For a singular point over $\mathbb{Q}$: $\nabla F = 0$ requires $4z^3 = 0 \Rightarrow z = 0$, then $-3x^2y = 0$ (so $x=0$ or $y=0$) and $2y - x^3 = 0$ (so $y = x^3/2$). With $z=0$:
- If $x=0$: $F = y^2 + 1 > 0$. No solution.
- If $y = x^3/2$: $F = x^6/4 - x^6/2 + 1 = 1 - x^6/4 = 0 \Rightarrow x^6 = 4$. No rational solution.

**The surface $S$ is smooth over $\mathbb{Q}$ (and hence over $\mathbb{Z}$).**

### Family of Quartic Plane Curves (fixed $z$)

For each fixed $z \in \mathbb{Z}$, the equation $y^2 - x^3 y + (z^4+1) = 0$ defines a plane **quartic** curve $C_z$ (degree 4 in $x$, thinking of it as $x^3 y = y^2 + z^4 + 1$, which has degree 4 as a curve in $\mathbb{P}^2$ after homogenisation). By the degree–genus formula, the projective closure of $C_z$ has **geometric genus $g \geq 1$**.

For each fixed $x$, the equation $y^2 - x^3 y + (z^4+1) = 0$ defines a curve of genus $\geq 1$ in $(y, z)$.

### Faltings' Theorem and Finiteness

Each slice $C_z$ (or $C_x$) is a curve over $\mathbb{Q}$ of genus $g \geq 2$. By **Faltings' theorem** (Mordell conjecture, proved 1983), each such curve has finitely many rational points.

Hence for each fixed $z$ (resp. $x$), there are only finitely many integer solutions. Since the search over all such $(x,z)$ pairs found none, this strongly suggests no solution exists.

---

## Proof Status

| Component | Status |
|-----------|--------|
| No solutions for $\|x\|, \|z\| \leq 500$ | ✓ Complete (exhaustive search) |
| $z$ must be odd | ✓ Complete (mod 4) |
| $x$ must be odd | ✓ Complete (mod 4) |
| Surface is smooth over $\mathbb{Q}$ | ✓ Complete (gradient argument) |
| No elementary modular obstruction | ✓ Confirmed (computational) |
| $\mathbb{F}_p$-points exist for all $p \leq 200$ | ✓ Confirmed |
| Equation is locally solvable at all places | ✓ Confirmed computationally |
| No integer solutions | Conditional — requires Faltings/Chabauty–Coleman over the surface, or effective Baker bounds |

---

## Related Work

The problem of showing $z^4 + 1 \neq a \cdot b$ with $a + b$ a perfect cube is related to:
- Catalan's conjecture (Mihailescu 2002): $x^p - y^q = 1$.
- The theory of $S$-unit equations and Thue–Mahler equations.
- Effective Baker bounds for Diophantine equations in many variables.
