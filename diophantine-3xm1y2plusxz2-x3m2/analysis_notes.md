# Analysis Notes: $(3x-1)y^2 + xz^2 = x^3 - 2$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$\boxed{(3x-1)\,y^2 + x\,z^2 \;=\; x^3 - 2}$$

or prove that none exist.

---

## Main Result

The equation has **no integer solutions**.

**Proof:** A complete 3-adic modular obstruction exists at the level of $\mathbb{Z}/9\mathbb{Z}$.
The three residue classes $x \equiv 0, 1, 2 \pmod{3}$ are each shown impossible;
together they exhaust all integers.

---

## Algebraic Reformulation

Rewriting the equation:

$$
(3x-1)\,y^2 + x\,z^2 = x^3 - 2
$$
$$
\Longleftrightarrow \quad 3xy^2 - y^2 + xz^2 = x^3 - 2
$$
$$
\Longleftrightarrow \quad x(3y^2 + z^2 - x^2) = y^2 - 2. \tag{*}
$$

This is the **central identity** used throughout the proof.

---

## Modular Obstruction Proof

### Case 1: $x \equiv 0 \pmod{3}$

From (*), reducing modulo 3 with $x \equiv 0$:

$$
0 \cdot (3y^2 + z^2 - x^2) \equiv y^2 - 2 \pmod{3}
$$
$$
\Longrightarrow \quad y^2 \equiv 2 \pmod{3}.
$$

But the quadratic residues modulo 3 are only $\{0, 1\}$.
The value $2$ is **not a quadratic residue mod 3**. $\Rightarrow$ **IMPOSSIBLE.**

### Case 2: $x \equiv 2 \pmod{3}$

Reducing (*) modulo 3 with $x \equiv -1$:

$$
(-1)(0 + z^2 - x^2) \equiv y^2 - 2 \pmod{3}
\quad\Longrightarrow\quad
x^2 - z^2 \equiv y^2 - 2 \pmod{3}.
$$

Since $x \equiv 2$, we have $x^2 \equiv 1 \pmod{3}$, so:

$$
1 - z^2 \equiv y^2 - 2 \pmod{3}
\quad\Longrightarrow\quad
y^2 + z^2 \equiv 3 \equiv 0 \pmod{3}.
$$

Since squares mod 3 lie in $\{0, 1\}$, the sum $y^2 + z^2 \equiv 0 \pmod{3}$ forces
$y^2 \equiv 0$ and $z^2 \equiv 0$, i.e. $y \equiv 0 \pmod{3}$ and $z \equiv 0 \pmod{3}$.

**Substitution:** Write $y = 3Y$, $z = 3Z$. The original equation becomes:

$$
(3x-1)(9Y^2) + x(9Z^2) = x^3 - 2
\quad\Longrightarrow\quad
9\bigl[(3x-1)Y^2 + xZ^2\bigr] = x^3 - 2.
$$

Hence $9 \mid (x^3 - 2)$, i.e. $x^3 \equiv 2 \pmod{9}$.

But $x \equiv 2 \pmod{3}$ implies $x \in \{2, 5, 8\} \pmod{9}$, and:

| $x \bmod 9$ | $x^3 \bmod 9$ |
|:-----------:|:-------------:|
| $2$         | $8$           |
| $5$         | $8$           |
| $8$         | $8$           |

So $x^3 \equiv 8 \not\equiv 2 \pmod{9}$. $\Rightarrow$ **IMPOSSIBLE.**

### Case 3: $x \equiv 1 \pmod{3}$

Reducing (*) modulo 3 with $x \equiv 1$:

$$
1 \cdot (0 + z^2 - 1) \equiv y^2 - 2 \pmod{3}
\quad\Longrightarrow\quad
z^2 - 1 \equiv y^2 - 2 \pmod{3}
\quad\Longrightarrow\quad
y^2 - z^2 \equiv -1 \equiv 2 \pmod{3}.
$$

Since $y^2, z^2 \in \{0, 1\} \pmod{3}$, the only way $y^2 - z^2 \equiv 2 \pmod{3}$ is
$y^2 \equiv 0$ and $z^2 \equiv 1$, i.e. $y \equiv 0 \pmod{3}$ and $z \not\equiv 0 \pmod{3}$.

**Substitution:** Write $y = 3Y$. The original equation becomes:

$$
(3x-1)(9Y^2) + xz^2 = x^3 - 2
\quad\Longrightarrow\quad
9(3x-1)Y^2 + xz^2 = x^3 - 2.
$$

Reducing modulo 9: $xz^2 \equiv x^3 - 2 \pmod{9}$.

Since $x \equiv 1 \pmod{3}$, we have $x \in \{1, 4, 7\} \pmod{9}$, and:

| $x \bmod 9$ | $x^3 \bmod 9$ | $x^3 - 2 \bmod 9$ |
|:-----------:|:-------------:|:-----------------:|
| $1$         | $1$           | $8$               |
| $4$         | $1$ ($64=63+1$) | $8$             |
| $7$         | $1$ ($343=342+1$) | $8$           |

So in all subclasses we need $xz^2 \equiv 8 \pmod{9}$.

The quadratic residues modulo 9 are $\{0, 1, 4, 7\}$.

- **$x \equiv 1 \pmod{9}$:** $1 \cdot z^2 \equiv 8 \pmod{9}$, i.e. $z^2 \equiv 8$.
  But $8 \notin \{0,1,4,7\}$.  **IMPOSSIBLE.**

- **$x \equiv 4 \pmod{9}$:** $4z^2 \equiv 8 \pmod{9}$, i.e. $z^2 \equiv 2 \pmod{9}$
  (since $4 \cdot 7 = 28 \equiv 1 \pmod{9}$, so $4^{-1} \equiv 7$, and $7 \cdot 8 = 56 \equiv 2 \pmod{9}$).
  But $2 \notin \{0,1,4,7\}$.  **IMPOSSIBLE.**

- **$x \equiv 7 \pmod{9}$:** $7z^2 \equiv 8 \pmod{9}$, i.e. $z^2 \equiv 8 \cdot 7^{-1} \equiv 8 \cdot 4 = 32 \equiv 5 \pmod{9}$
  (since $7 \cdot 4 = 28 \equiv 1 \pmod{9}$, so $7^{-1} \equiv 4$).
  But $5 \notin \{0,1,4,7\}$.  **IMPOSSIBLE.**

### Conclusion

All three residue classes modulo 3 yield contradictions. Therefore the equation
$(3x-1)y^2 + xz^2 = x^3 - 2$ has **no integer solutions**.

$\blacksquare$

---

## Key Facts Used

| Fact | Value |
|------|-------|
| Quadratic residues mod 3 | $\{0, 1\}$ (2 is not a QR mod 3) |
| Cubes mod 9 for $x \equiv 2 \pmod{3}$ | Always $\equiv 8$ |
| Cubes mod 9 for $x \equiv 1 \pmod{3}$ | Always $\equiv 1$ |
| Quadratic residues mod 9 | $\{0, 1, 4, 7\}$ |
| $x^3 - 2 \pmod{9}$ for $x \equiv 1 \pmod{3}$ | Always $\equiv 8$ |

---

## Computational Verification

A brute-force search over $|x| \leq 10{,}000$ (with $x \equiv 1 \pmod{3}$ only,
since the other classes are provably impossible) found **no solutions**.

The search is implemented in [`brute_force_search.py`](brute_force_search.py).

---

## Lean 4 Formalisation

See [`NonExistenceProof.lean`](NonExistenceProof.lean) for the complete Lean 4 proof.

**Axiom count: 0. Sorry count: 0.**

All steps are closed by `decide` on the appropriate `ZMod N` type:

| Step | Modulus | Lean tactic |
|------|---------|-------------|
| $x \equiv 0$: $y^2 \equiv 2 \pmod{3}$, impossible | `ZMod 3` | `decide` |
| $x \equiv 2$: $y \equiv z \equiv 0 \pmod{3}$, then $x^3 \equiv 2 \pmod{9}$, impossible | `ZMod 9` | `decide` |
| $x \equiv 1$, $y \equiv 0 \pmod{3}$: $xz^2 \equiv 8 \pmod{9}$, impossible | `ZMod 9` | `decide` |
| Combined conclusion | — | case analysis |
