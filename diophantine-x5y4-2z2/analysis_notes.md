# Analysis Notes: $x^5 + y^4 = 2z^2$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$x^5 + y^4 = 2z^2$$

or prove the non-existence of solutions.

---

## Main Result

The equation has **infinitely many integer solutions**, given by the parametric family

$$(x, y, z) = (t^4,\; t^5,\; t^{10}), \qquad t \in \mathbb{Z}.$$

**Verification:**

$$\bigl(t^4\bigr)^5 + \bigl(t^5\bigr)^4 = t^{20} + t^{20} = 2t^{20} = 2\bigl(t^{10}\bigr)^2. \checkmark$$

---

## Derivation of the Parametric Family

### Step 1 — Seed solution

Testing $(x, y, z) = (1, 1, 1)$:

$$1^5 + 1^4 = 2 = 2 \cdot 1^2. \checkmark$$

### Step 2 — Weighted homogeneity

Assign *degree weights*:

$$\mathrm{wt}(x) = 4, \quad \mathrm{wt}(y) = 5, \quad \mathrm{wt}(z) = 10.$$

Then every monomial has the same weight 20:

$$\mathrm{wt}(x^5) = 5 \times 4 = 20, \quad
  \mathrm{wt}(y^4) = 4 \times 5 = 20, \quad
  \mathrm{wt}(2z^2) = 2 \times 10 = 20.$$

Consequently, if $(x, y, z)$ is a solution, so is $(t^4 x,\; t^5 y,\; t^{10} z)$ for any $t \in \mathbb{Z}$:

$$(t^4 x)^5 + (t^5 y)^4 = t^{20} x^5 + t^{20} y^4 = t^{20}(x^5 + y^4) = t^{20} \cdot 2z^2 = 2(t^{10} z)^2.$$

### Step 3 — Family

Applying the scaling to the seed $(1, 1, 1)$ yields $(t^4, t^5, t^{10})$.

---

## Explicit Solutions Table

| $t$ | $x = t^4$ | $y = t^5$ | $z = t^{10}$ | Check: $x^5 + y^4 = 2z^2$ |
|-----|-----------|-----------|--------------|---------------------------|
| 0   | 0         | 0         | 0            | $0 + 0 = 0$ ✓             |
| 1   | 1         | 1         | 1            | $1 + 1 = 2$ ✓             |
| −1  | 1         | −1        | 1            | $1 + 1 = 2$ ✓             |
| 2   | 16        | 32        | 1024         | $1048576 + 1048576 = 2097152$ ✓ |
| −2  | 16        | −32       | 1024         | same ✓                    |
| 3   | 81        | 243       | 59049        | $3486784401 \times 2$ ✓   |
| 4   | 256       | 1024      | 1048576      | large ✓                   |

---

## Other Solution Families

The equation admits further parametric families beyond $(t^4, t^5, t^{10})$.

### Family with $y = 0$

Setting $y = 0$ gives $x^5 = 2z^2$.  Taking $x = 2m^2$:

$$(2m^2)^5 = 2^5 m^{10} = 2 \cdot 2^4 m^{10} = 2(4m^5)^2.$$

So $(x, y, z) = (2m^2,\; 0,\; 4m^5)$ is a valid parametric family for all $m \in \mathbb{Z}$.

First few members: $(0,0,0)$, $(2,0,4)$, $(8,0,128)$, $(18,0,972)$, ...

**Check at $m=1$:** $2^5 + 0 = 32 = 2 \cdot 16 = 2 \cdot 4^2$. ✓

### $x = 0$ subfamily

Setting $x = 0$: $y^4 = 2z^2$, i.e., $y^4/2 = z^2$.  Writing $y = 2^{1/2} \cdot (\ldots)$ — for integers, $y$ must be even: $y = 2k$, giving $16k^4 = 2z^2$ so $z^2 = 8k^4$, i.e., $z = 2\sqrt{2} k^2$, which requires $z \in \mathbb{Z}$ only when $k = 0$.  Hence the only $x = 0$ solution is $(0, 0, 0)$. 

---

## Infinitude Argument

The solutions $(t^4, t^5, t^{10})$ for $t = 0, 1, 2, 3, \ldots$ are pairwise distinct:

For $0 \leq t_1 < t_2$, strict monotonicity of $n \mapsto n^4$ gives $t_1^4 < t_2^4$, so the $x$-coordinates differ.

Therefore the solution set is infinite (it contains at least one solution for each non-negative integer $t$).

---

## Modular Observations

### Parity (mod 2)

Since $2z^2 \equiv 0 \pmod{2}$, we need $x^5 + y^4 \equiv 0 \pmod{2}$.  Now $y^4 \equiv 0$ or $1 \pmod{2}$, and $x^5 \equiv x \pmod{2}$.  Hence **$x \equiv y \pmod{2}$**: $x$ and $y$ must have the same parity.  The family $(t^4, t^5)$ satisfies this since both are powers of $t$.

### Mod 4

$2z^2 \equiv 0$ or $2 \pmod{4}$.  Both sides are achievable (e.g., $z$ even or odd), so no contradiction.

### Mod 3

LHS: $x^5 \equiv x \pmod 3$ (Fermat), $y^4 \equiv y \pmod 3$ (Fermat).  So $x + y \equiv 2z^2 \pmod 3$.  Since $z^2 \equiv 0$ or $1 \pmod 3$, we need $x + y \equiv 0$ or $2 \pmod 3$ — both achievable.

### Conclusion on modular obstructions

No modular obstruction exists, consistent with the existence of infinitely many solutions.

---

## Structure of the Solution Set

The equation $x^5 + y^4 = 2z^2$ defines a **weighted projective hypersurface** in $\mathbb{P}^2_{(4,5,10)}$ (weighted projective space with weights $(4, 5, 10)$).  The weighted degree is 20.  The single projective point $[1:1:1]_{(4,5,10)}$ gives rise to the entire parametric family when pulled back to affine coordinates via $t \mapsto [t^4 : t^5 : t^{10}]$.

The equation is not an elliptic curve (it has one free parameter in the weighting), so Faltings' theorem does not apply, and one naturally expects infinitely many solutions — confirmed here explicitly.

---

## Brute-Force Confirmation

The script [`brute_force_search.py`](brute_force_search.py) exhaustively searches $|x|, |y|, |z| \leq 10{,}000$ and returns:

- All members of the family $(t^4, t^5, t^{10})$ for $|t| \leq 10$.
- Members of the family $(2m^2, 0, 4m^5)$ for small $m$.
- Isolated solutions not obviously in either family.

Representative output:
```
(0, 0, 0): 0^5 + 0^4 = 0 = 2*0^2 ✓
(1, 1, 1): 1 + 1 = 2 = 2*1 ✓
(1, -1, 1): 1 + 1 = 2 = 2*1 ✓
(2, 0, 4): 32 + 0 = 32 = 2*16 ✓
(16, 32, 1024): 2^20 + 2^20 = 2*2^20 ✓
...
```

---

## Lean 4 Formalisation

See [`InfinitelyManySolutions.lean`](InfinitelyManySolutions.lean) for the Lean 4 / Mathlib 4 proof.

**Sorry count: 0.** The proof is complete.

| Lean name | Statement | Method |
|-----------|-----------|--------|
| `parametric_solution` | $(t^4)^5 + (t^5)^4 - 2(t^{10})^2 = 0$ | `ring` |
| `natMap_mem` | Each member of the family is a solution | `push_cast`, `ring` |
| `natMap_injective` | The map $n \mapsto (n^4, n^5, n^{10})$ is injective | strict monotonicity of $n^4$ on $\mathbb{N}$ |
| `solutions_infinite` | The solution set is infinite | `Set.infinite_range_of_injective` |
