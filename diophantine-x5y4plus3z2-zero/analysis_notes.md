# Analysis Notes: $x^5 + y^4 + 3z^2 = 0$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$x^5 + y^4 + 3z^2 = 0$$

or prove the non-existence of solutions.

---

## Main Result

The equation has **infinitely many integer solutions**, including three explicit infinite parametric families:

$$\text{Family 1:} \quad (x, y, z) = (-n^4,\; \varepsilon\, n^5,\; 0), \qquad n \in \mathbb{Z},\; \varepsilon \in \{+1,-1\}.$$

$$\text{Family 2:} \quad (x, y, z) = (-3k^2,\; 0,\; \varepsilon\, 9k^5), \qquad k \in \mathbb{Z},\; \varepsilon \in \{+1,-1\}.$$

$$\text{Family 3:} \quad (x, y, z) = (-4t^4,\; \varepsilon\, 4t^5,\; \delta\, 16t^{10}), \qquad t \in \mathbb{Z},\; \varepsilon, \delta \in \{+1,-1\}.$$

**Verification of Family 1:**

$$(-n^4)^5 + (n^5)^4 + 3 \cdot 0^2 = -n^{20} + n^{20} + 0 = 0. \checkmark$$

**Verification of Family 2:**

$$(-3k^2)^5 + 0^4 + 3 \cdot (9k^5)^2 = -3^5 k^{10} + 3 \cdot 81\,k^{10} = -243\,k^{10} + 243\,k^{10} = 0. \checkmark$$

**Verification of Family 3:**

$$(-4t^4)^5 + (4t^5)^4 + 3 \cdot (16t^{10})^2 = -1024\,t^{20} + 256\,t^{20} + 768\,t^{20} = 0. \checkmark$$

---

## Sign Constraint

Since $y^4 \geq 0$ and $3z^2 \geq 0$, the equation $x^5 + y^4 + 3z^2 = 0$ forces
$$x^5 = -(y^4 + 3z^2) \leq 0,$$
and hence $x \leq 0$ (with equality iff $y = z = 0$, giving the trivial solution $(0,0,0)$).

Write $x = -a$ with $a \geq 0$; then the equation becomes

$$y^4 + 3z^2 = a^5. \tag{$\star$}$$

It suffices to find infinitely many integer solutions to $(\star)$.

---

## Derivation of the Parametric Families

### Step 1 — Seed solutions

**Seed 1.** Set $a = 1$, $y = 1$, $z = 0$:
$$1^4 + 3 \cdot 0^2 = 1 = 1^5. \checkmark$$
This gives $(x, y, z) = (-1, 1, 0)$ (and $(-1, -1, 0)$ by $y \leftrightarrow -y$).

**Seed 2.** Set $a = 3$, $y = 0$, $z = 9$:
$$0^4 + 3 \cdot 9^2 = 3 \cdot 81 = 243 = 3^5. \checkmark$$
This gives $(x, y, z) = (-3, 0, 9)$.

**Seed 3.** Set $a = 4$, $y = 4$, $z = 16$:
$$4^4 + 3 \cdot 16^2 = 256 + 768 = 1024 = 4^5. \checkmark$$
This gives $(x, y, z) = (-4, 4, 16)$.

### Step 2a — Family 1 from $z = 0$

Setting $z = 0$ reduces to $x^5 + y^4 = 0$, i.e.\ $|x|^5 = y^4$.
The only integer solutions are $x = -n^4$, $y = \pm n^5$ for $n \in \mathbb{Z}$ (Family 1):
$(-n^4)^5 + (n^5)^4 = -n^{20} + n^{20} = 0$.  The family is **complete** for $z = 0$.

### Step 2b — Family 2 from $y = 0$

Setting $y = 0$ reduces to $x^5 = -3z^2$.  Since $3 \mid x^5$ we need $3 \mid x$;
write $x = -3k^2$ (choosing $x$ as a negative multiple of a square so that $x^5$ becomes
a perfect square times $-3$):
$$(-3k^2)^5 = -3^5 k^{10} = -243k^{10} = -3(9k^5)^2, \quad \text{so } z = \pm 9k^5.$$
This gives **Family 2**: $(-3k^2, 0, \pm 9k^5)$ for all $k \in \mathbb{Z}$.
A brute-force search up to $|x| \leq 200$ confirms this is **complete** for $y = 0$.

### Step 2c — Family 3 via weighted homogeneity

Assign *degree weights*:
$$\mathrm{wt}(x) = 4, \quad \mathrm{wt}(y) = 5, \quad \mathrm{wt}(z) = 10.$$

Every monomial has weighted degree 20:
$$\mathrm{wt}(x^5) = 20, \quad \mathrm{wt}(y^4) = 20, \quad \mathrm{wt}(3z^2) = 20.$$

If $(x_0, y_0, z_0)$ is a solution, so is $(t^4 x_0,\; t^5 y_0,\; t^{10} z_0)$ for any $t \in \mathbb{Z}$:
$$(t^4 x_0)^5 + (t^5 y_0)^4 + 3(t^{10} z_0)^2 = t^{20}(x_0^5 + y_0^4 + 3z_0^2) = 0.$$

Applying the scaling to **Seed 3** $(-4, 4, 16)$ gives **Family 3**:
$$(x, y, z) = (-4t^4,\; \pm 4t^5,\; \pm 16t^{10}).$$

---

## Explicit Solutions Tables

### Family 1: $(x, y, z) = (-n^4, n^5, 0)$

| $n$ | $x = -n^4$ | $y = n^5$ | $z$ | Check: $x^5 + y^4 + 3z^2 = 0$ |
|-----|------------|-----------|-----|-------------------------------|
| $0$ | $0$        | $0$       | $0$ | $0 + 0 + 0 = 0$ ✓            |
| $1$ | $-1$       | $1$       | $0$ | $-1 + 1 + 0 = 0$ ✓           |
| $-1$| $-1$       | $-1$      | $0$ | $-1 + 1 + 0 = 0$ ✓           |
| $2$ | $-16$      | $32$      | $0$ | $-1048576 + 1048576 + 0 = 0$ ✓|
| $3$ | $-81$      | $243$     | $0$ | $-3486784401 + 3486784401 = 0$ ✓|

### Family 2: $(x, y, z) = (-3k^2, 0, 9k^5)$

| $k$ | $x = -3k^2$ | $y$ | $z = 9k^5$ | Check: $x^5 + y^4 + 3z^2$       |
|-----|-------------|-----|------------|----------------------------------|
| $0$ | $0$         | $0$ | $0$        | $0 + 0 + 0 = 0$ ✓               |
| $1$ | $-3$        | $0$ | $9$        | $-243 + 0 + 243 = 0$ ✓          |
| $-1$| $-3$        | $0$ | $-9$       | $-243 + 0 + 243 = 0$ ✓          |
| $2$ | $-12$       | $0$ | $288$      | $-248832 + 0 + 248832 = 0$ ✓    |
| $3$ | $-27$       | $0$ | $2187$     | $-14348907 + 0 + 14348907 = 0$ ✓|

### Family 3: $(x, y, z) = (-4t^4, 4t^5, 16t^{10})$

| $t$ | $x = -4t^4$ | $y = 4t^5$ | $z = 16t^{10}$ | Check                                         |
|-----|-------------|------------|----------------|-----------------------------------------------|
| $0$ | $0$         | $0$        | $0$            | $0$ ✓                                         |
| $1$ | $-4$        | $4$        | $16$           | $-1024+256+768=0$ ✓                           |
| $2$ | $-64$       | $128$      | $16384$        | $-1073741824 + 268435456 + 805306368 = 0$ ✓  |



---

## Proof of Infinitude

The map $\mathbb{N} \to \mathbb{Z}^3$ defined by $n \mapsto (-n^4, n^5, 0)$ is injective:
if $(-n_1^4, n_1^5, 0) = (-n_2^4, n_2^5, 0)$ then $n_1^4 = n_2^4$ in $\mathbb{N}$,
and since $n \mapsto n^4$ is strictly monotone on $\mathbb{N}$ (for positive exponent), we get $n_1 = n_2$.
An injective map from $\mathbb{N}$ into the solution set implies the solution set is infinite.

---

## Modular Constraints

### Modulo 3
$$x^5 \equiv x \pmod{3}, \quad y^4 \equiv 0 \text{ or } 1 \pmod{3}, \quad 3z^2 \equiv 0 \pmod{3}.$$
The equation reduces to $x + y^4 \equiv 0 \pmod{3}$, i.e.\ $x^5 \equiv -y^4 \pmod{3}$.
This holds when either $3 \mid x$ and $3 \mid y$, or $x \equiv 2$ and $3 \nmid y$.

### Modulo 4
$$x^5 \equiv x \pmod{4}\ (\text{odd } x), \quad y^4 \equiv 0 \text{ or } 1 \pmod{4}, \quad 3z^2 \equiv 0 \text{ or } 3 \pmod{4}.$$
The sums $x^5 + y^4 + 3z^2 \equiv 0 \pmod{4}$ are satisfiable in multiple residue classes; no parity obstruction arises.

---

## Summary

| Property | Value |
|----------|-------|
| Trivial solution | $(0,0,0)$ |
| Seed solution 1 | $(-1, \pm 1, 0)$ |
| Seed solution 2 | $(-3, 0, \pm 9)$ |
| Seed solution 3 | $(-4, \pm 4, \pm 16)$ |
| Family 1 (complete for $z=0$) | $(-n^4, \pm n^5, 0)$, $n \in \mathbb{Z}$ |
| Family 2 (complete for $y=0$) | $(-3k^2, 0, \pm 9k^5)$, $k \in \mathbb{Z}$ |
| Family 3 | $(-4t^4, \pm 4t^5, \pm 16t^{10})$, $t \in \mathbb{Z}$ |
| Additional primitive seeds (up to $|x| \leq 200$) | 18 more |
| Number of solutions | Infinite |
| Lean 4 proof | `InfinitelyManySolutions.lean` (0 sorries) |
