# Analysis Notes: $x + x^2 y^2 + z^3 = 0$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$x + x^2 y^2 + z^3 = 0$$

or prove the non-existence of integer solutions.

---

## Main Result

The equation has **infinitely many integer solutions**, including two explicit infinite parametric families:

$$\text{Family 1:} \quad (x, y, z) = (0,\; n,\; 0), \qquad n \in \mathbb{Z}.$$

$$\text{Family 2:} \quad (x, y, z) = (-n^3,\; 0,\; n), \qquad n \in \mathbb{Z}.$$

**Verification of Family 1:**

$$0 + 0^2 \cdot n^2 + 0^3 = 0. \checkmark$$

**Verification of Family 2:**

$$(-n^3) + (-n^3)^2 \cdot 0^2 + n^3 = -n^3 + 0 + n^3 = 0. \checkmark$$

---

## Algebraic Structure

Rewrite the equation as

$$x(1 + x y^2) + z^3 = 0 \quad \Longleftrightarrow \quad z^3 = -x(1 + xy^2).$$

The equation is **not** homogeneous (degrees 1, 4, 3 appear), so no simple scaling law
generates all solutions from a seed. However, the two universal substitutions below each yield
a one-parameter family.

### Family 1: $x = 0$

Setting $x = 0$ reduces the equation to $z^3 = 0$, so $z = 0$. For any $n \in \mathbb{Z}$,
the triple $(0, n, 0)$ satisfies the equation. The map $n \mapsto (0, n, 0)$ is injective
(the $y$-component equals $n$), so this family gives infinitely many distinct solutions.

### Family 2: $y = 0$

Setting $y = 0$ reduces the equation to $x + z^3 = 0$, i.e., $x = -z^3$. For any $n \in \mathbb{Z}$,
the triple $(-n^3, 0, n)$ satisfies the equation. The map $n \mapsto (-n^3, 0, n)$ is injective
(the $z$-component equals $n$), giving a second infinite family.

---

## Small Explicit Solutions

| $(x, y, z)$ | $x + x^2y^2 + z^3$ | Family |
|---|---|---|
| $(0, 0, 0)$ | $0$ | trivial |
| $(0, 1, 0)$ | $0$ | Family 1, $n=1$ |
| $(0, -1, 0)$ | $0$ | Family 1, $n=-1$ |
| $(0, 5, 0)$ | $0$ | Family 1, $n=5$ |
| $(-1, 0, 1)$ | $0$ | Family 2, $n=1$ |
| $(1, 0, -1)$ | $0$ | Family 2, $n=-1$ |
| $(-8, 0, 2)$ | $0$ | Family 2, $n=2$ |
| $(8, 0, -2)$ | $0$ | Family 2, $n=-2$ |
| $(-27, 0, 3)$ | $0$ | Family 2, $n=3$ |

---

## Additional Sporadic Solutions (x ≠ 0, y ≠ 0)

Setting $x = -1$ gives $-1 + y^2 + z^3 = 0$, i.e., $z^3 = 1 - y^2$.

We need $1 - y^2 = k^3$ for some integer $k$. This is the Mordell-type equation
$y^2 = 1 - k^3$, equivalently $y^2 + k^3 = 1$. The integer points on $Y^2 = 1 - X^3$
(a twist of the Fermat cubic) are known to be:

| $k = z$ | $y^2 = 1 - k^3$ | $y$ | Solution |
|---|---|---|---|
| $0$ | $1$ | $\pm 1$ | $(-1, \pm 1, 0)$ |
| $1$ | $0$ | $0$ | $(-1, 0, 1)$ (Family 2, $n=1$) |
| $-2$ | $9$ | $\pm 3$ | $(-1, \pm 3, -2)$ |

Beyond these, by Siegel's theorem the curve $y^2 = 1 - z^3$ has finitely many integer
points; a classical result (Baker's method) confirms the list above is complete.

Thus for $x = -1$ there are exactly five solutions:
$(-1, 0, 1)$, $(-1, 1, 0)$, $(-1, -1, 0)$, $(-1, 3, -2)$, $(-1, -3, -2)$.

---

## Modular Analysis

### Mod 2

Fourth powers and squares are odd or even. The equation mod 2:
$x + x^2 y^2 + z^3 \equiv x(1 + xy^2) + z^3 \pmod{2}$.
Setting $x \equiv 0$: $z \equiv 0$. Setting $x \equiv 1$: $1 + y^2 + z^3 \equiv 0 \pmod 2$.
If $y$ even: $z$ odd. If $y$ odd: $z$ even. No obstruction — solutions exist in all cases.

### No Modular Obstruction

A systematic computer search (see `brute_force_search.py`) confirms that for every prime
$p \leq 500$, there exist nonzero $(x, y, z) \not\equiv (0,0,0) \pmod p$ satisfying the equation
modulo $p$. The global solutions in Family 1 and Family 2 certify this for all primes at once.

---

## Infinitude Argument

The map

$$\varphi \colon \mathbb{N} \to \mathbb{Z}^3, \quad n \mapsto (0,\, n,\, 0)$$

is:
- **well-defined:** every image satisfies $0 + 0 \cdot n^2 + 0 = 0$,
- **injective:** $\varphi(n_1) = \varphi(n_2)$ forces $n_1 = n_2$ (the $y$-component),

so the solution set contains a copy of $\mathbb{N}$ and is therefore infinite.

---

## Proof Status

| Component | Status | Method |
|---|---|---|
| Family 1 $(0, n, 0)$ verified | ✓ Complete | Direct substitution / `ring` |
| Family 2 $(-n^3, 0, n)$ verified | ✓ Complete | Direct substitution / `ring` |
| Infinitely many distinct solutions | ✓ Complete | Injectivity of $n \mapsto (0,n,0)$ |
| Lean 4 formalisation (0 sorry) | ✓ **Complete** | Mathlib tactics |
| Full classification of all solutions | Open | Requires algebraic geometry for each fixed $x$ |
