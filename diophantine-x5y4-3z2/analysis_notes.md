# Analysis Notes: $x^5 + y^4 = 3z^2$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$x^5 + y^4 = 3z^2$$

or prove the non-existence of solutions.

---

## Main Result

The equation has **infinitely many integer solutions**, given by the primary parametric family

$$(x, y, z) = \bigl(3a^2,\; 0,\; 9a^5\bigr), \qquad a \in \mathbb{Z}.$$

**Verification:**

$$\bigl(3a^2\bigr)^5 + 0^4 = 3^5 a^{10} = 243 a^{10} = 3 \cdot 81 a^{10} = 3\bigl(9a^5\bigr)^2. \checkmark$$

---

## Derivation of the Primary Parametric Family

### Step 1 — Set $y = 0$

Setting $y = 0$ reduces the equation to $x^5 = 3z^2$, a two-variable equation.

### Step 2 — Parametrize $x^5 = 3z^2$

We seek integers $x, z$ with $x^5 = 3z^2$.  The key idea is to choose $x$ as a square
times 3 so that $x^5$ acquires both the required factor of 3 and a perfect-square structure.

Take $x = 3a^2$ for $a \in \mathbb{Z}$:

$$x^5 = (3a^2)^5 = 3^5 a^{10} = 243 a^{10}.$$

For the right-hand side:

$$3z^2 = 243 a^{10} \;\Longrightarrow\; z^2 = 81 a^{10} = (9a^5)^2 \;\Longrightarrow\; z = \pm 9a^5.$$

### Step 3 — Family

Thus $(x, y, z) = (3a^2,\, 0,\, 9a^5)$ is a valid integer solution for every $a \in \mathbb{Z}$.

---

## Explicit Solutions Table

| $a$ | $x = 3a^2$ | $y$ | $z = 9a^5$ | Check: $x^5 + y^4 = 3z^2$ |
|-----|----------|-----|-----------|--------------------------|
| $0$  | $0$       | $0$ | $0$        | $0 + 0 = 0$ ✓            |
| $1$  | $3$       | $0$ | $9$        | $243 = 3 \cdot 81$ ✓     |
| $-1$ | $3$       | $0$ | $-9$       | $243 = 3 \cdot 81$ ✓     |
| $2$  | $12$      | $0$ | $288$      | $248832 = 3 \cdot 82944$ ✓ |
| $-2$ | $12$      | $0$ | $-288$     | same ✓                   |
| $3$  | $27$      | $0$ | $2187$     | $14348907 = 3 \cdot 4782969$ ✓ |
| $4$  | $48$      | $0$ | $9216$     | large ✓                  |

---

## Other Solution Families

### Family from the seed $(2, 2, 4)$

Direct check: $2^5 + 2^4 = 32 + 16 = 48 = 3 \cdot 16 = 3 \cdot 4^2$. ✓

The equation $x^5 + y^4 = 3z^2$ has a **weighted-homogeneity symmetry**: assigning weights
$$\mathrm{wt}(x) = 4, \quad \mathrm{wt}(y) = 5, \quad \mathrm{wt}(z) = 10,$$
every monomial has the same weighted degree 20:
$$\mathrm{wt}(x^5) = 5 \times 4 = 20, \quad \mathrm{wt}(y^4) = 4 \times 5 = 20, \quad \mathrm{wt}(3z^2) = 2 \times 10 = 20.$$

Hence if $(x_0, y_0, z_0)$ is a solution, so is $(t^4 x_0,\, t^5 y_0,\, t^{10} z_0)$ for any $t \in \mathbb{Z}$:
$$(t^4 x_0)^5 + (t^5 y_0)^4 = t^{20}(x_0^5 + y_0^4) = t^{20} \cdot 3z_0^2 = 3(t^{10}z_0)^2.$$

Applying this to $(2, 2, 4)$ gives the **secondary parametric family**:
$$(x, y, z) = \bigl(2t^4,\; 2t^5,\; 4t^{10}\bigr), \qquad t \in \mathbb{Z}.$$

**Verification:**
$(2t^4)^5 + (2t^5)^4 = 32t^{20} + 16t^{20} = 48t^{20} = 3 \cdot (4t^{10})^2$. ✓

First few members:

| $t$ | $x = 2t^4$ | $y = 2t^5$ | $z = 4t^{10}$ |
|-----|----------|----------|------------|
| $0$ | $0$       | $0$        | $0$          |
| $1$ | $2$       | $2$        | $4$          |
| $-1$ | $2$      | $-2$       | $4$          |
| $2$ | $32$      | $64$       | $4096$       |

### Trivial $z = 0$ family

The seed $(-1, 1, 0)$: $(-1)^5 + 1^4 = 0 = 3 \cdot 0^2$. ✓

By weighted homogeneity applied to $(-1, 1, 0)$: the family $(-t^4,\, t^5,\, 0)$ satisfies the equation for all $t \in \mathbb{Z}$ (since $(-t^4)^5 + (t^5)^4 = -t^{20} + t^{20} = 0$). However, all members have $z = 0$ and thus make a less interesting family.

---

## Infinitude Argument

The solutions $(3a^2, 0, 9a^5)$ for $a = 0, 1, 2, 3, \ldots$ are pairwise distinct:

For non-negative integers $0 \leq a_1 < a_2$, strict monotonicity of $n \mapsto n^2$ gives
$a_1^2 < a_2^2$, so $3a_1^2 < 3a_2^2$, and the $x$-coordinates differ.

Therefore the solution set is infinite (it contains at least one solution for each non-negative integer $a$).

---

## Modular Analysis

### Mod 3

By Fermat's little theorem applied in $\mathbb{Z}/3\mathbb{Z}$:
$$x^5 \equiv x \pmod{3}, \qquad y^4 \equiv y^2 \pmod{3}.$$
Since $n^2 \equiv 0$ or $1 \pmod{3}$, we have $y^4 \equiv 0$ or $1 \pmod{3}$.

The right-hand side satisfies $3z^2 \equiv 0 \pmod{3}$.  So the equation mod 3 gives:
$$x + y^4\text{-residue} \equiv 0 \pmod{3}.$$

Two compatible cases arise:
- $3 \mid x$ and $3 \mid y$: e.g., $(0,0,0)$ and the primary family (since $x = 3a^2$).
- $x \equiv 2 \pmod{3}$ and $3 \nmid y$: e.g., $(2, 2, 4)$ (since $2 \equiv 2$ and $2 \not\equiv 0 \pmod{3}$).

No mod-3 obstruction.

### Parity (mod 2)

$3z^2$ is odd iff $z$ is odd.  For $x^5 + y^4$: since $y^4$ is always even iff $y$ is even,
and $x^5 \equiv x \pmod{2}$, the parity constraint is $x \equiv 3z^2 - y^4 \pmod{2}$, which
is always satisfiable.  No parity obstruction.

### Conclusion

No modular obstruction exists, consistent with the existence of infinitely many solutions over every $\mathbb{Z}/m\mathbb{Z}$.

---

## Structure of the Solution Set

The equation $x^5 + y^4 = 3z^2$ defines a **weighted projective hypersurface** in
$\mathbb{P}^2_{(4,5,10)}$ (weighted projective plane with weights $(4, 5, 10)$) of
weighted degree 20.  Two distinct rational curves are visibly embedded in this surface:

1. The curve $\{(3t^2 : 0 : 9t^5)\}$ (the primary family).
2. The curve $\{(2t^4 : 2t^5 : 4t^{10})\}$ (the secondary family).

In both cases the rational parametrisation witnesses that these curves are rational, and
in particular have infinitely many integer points.  By contrast, the Diophantine equations
in this repository with no solutions define curves or surfaces of genus $\geq 2$, where
Faltings' theorem guarantees finiteness.

---

## Brute-Force Confirmation

The script [`brute_force_search.py`](brute_force_search.py) exhaustively searches $|x|, |y| \leq 200$ and returns:

- All members of the primary family $(3a^2, 0, 9a^5)$ for small $|a|$.
- Members of the secondary family $(2t^4, 2t^5, 4t^{10})$ for small $|t|$.
- Isolated solutions with $y \neq 0$ not obviously in either family.

Representative output:
```
(0, 0, 0):   0 + 0 = 0 = 3·0² ✓
(3, 0, ±9):  243 + 0 = 243 = 3·81 ✓
(2, ±2, ±4): 32 + 16 = 48 = 3·16 ✓
(12, 0, ±288): 248832 + 0 = 248832 = 3·82944 ✓
(-1, ±1, 0): -1 + 1 = 0 = 3·0 ✓
...
```

---

## Lean 4 Formalisation

See [`InfinitelyManySolutions.lean`](InfinitelyManySolutions.lean) for the Lean 4 / Mathlib 4 proof.

**Sorry count: 0.** The proof is complete.

| Lean name | Statement | Method |
|-----------|-----------|--------|
| `parametric_solution` | $(3a^2)^5 + 0^4 = 3(9a^5)^2$ for all $a : \mathbb{Z}$ | `ring` |
| `parametric_solution2` | $(2t^4)^5 + (2t^5)^4 = 3(4t^{10})^2$ for all $t : \mathbb{Z}$ | `ring` |
| `natMap_mem` | Each $(3n^2, 0, 9n^5)$, $n : \mathbb{N}$, is a solution | `ring` |
| `pow2_strictMono` | $n \mapsto n^2$ is strictly monotone on $\mathbb{N}$ | `Nat.pow_lt_pow_left` |
| `natMap_injective` | $n \mapsto (3n^2, 0, 9n^5)$ is injective | `mul_left_cancel₀` + `pow2_strictMono` |
| `solutions_infinite` | The solution set is infinite | `Set.infinite_range_of_injective` |
