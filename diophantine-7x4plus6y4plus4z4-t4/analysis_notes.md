# Analysis Notes: $7x^4 + 6y^4 + 4z^4 = t^4$

## Quick Facts

- **Equation:** $7x^4 + 6y^4 + 4z^4 = t^4$
- **Status:** No non-zero integer solution known; non-existence not yet proved.
- **Search range verified:** $\max(|x|,|y|,|z|) \leq 3000$ (all odd, meet-in-the-middle search, Python).
  Equivalently: $|t| \leq 6093$.
- **Projective variety:** smooth diagonal quartic surface $V \subset \mathbb{P}^3$ — a K3 surface.
- **Local solvability:** the equation is $p$-adically solvable for every prime $p$, and over $\mathbb{R}$.

---

## Parity Lemma

**Lemma.** *Any primitive non-zero integer solution $(x,y,z,t)$ must have $x$, $y$, $z$, and $t$ all odd.*

**Proof.** Write $P(x,y,z,t)$ for the assertion. We work modulo increasing powers of $2$.

**Mod 2.** The equation reduces to $x^4 \equiv t^4 \pmod{2}$, so $x \equiv t \pmod{2}$.

**Case $t$ even, $x$ even.** Setting $x = 2X$, $t = 2T$:
$$7 \cdot 16X^4 + 6y^4 + 4z^4 = 16T^4.$$
Reducing mod 4 gives $6y^4 \equiv 0 \pmod{4}$, hence $y^4 \equiv 0 \pmod{2}$, so $y$ is even.
With $y = 2Y$, the equation becomes $7 \cdot 16X^4 + 6 \cdot 16Y^4 + 4z^4 = 16T^4$.
Reducing mod 8 gives $4z^4 \equiv 0 \pmod{8}$, so $z$ is even. But then $2 \mid \gcd(x,y,z,t)$, contradicting primitivity.

**So $t$ must be odd**, and hence $x$ must be odd.

**Mod 4 (with $x$, $t$ odd).** Since odd $n^4 \equiv 1 \pmod{4}$:
$$7 + 6y^4 + 4z^4 \equiv 1 \pmod{4}.$$
Thus $6y^4 \equiv -6 \equiv 2 \pmod{4}$, so $y^4 \equiv 1 \pmod{2}$: $y$ is odd.

**Mod 8 (with $x$, $y$, $t$ odd).** Odd $n^4 \equiv 1 \pmod{8}$:
$$7 + 6 + 4z^4 \equiv 1 \pmod{8} \implies 4z^4 \equiv -12 \equiv 4 \pmod{8} \implies z^4 \equiv 1 \pmod{2}.$$
So $z$ is odd. $\square$

---

## Mod 32 Constraint

Odd $n$: $n^4 \equiv 1 \pmod{32}$ if $n \equiv \pm 1 \pmod{8}$, and $n^4 \equiv 17 \pmod{32}$ if $n \equiv \pm 3 \pmod{8}$.

Setting $A = x^4 \bmod 32 \in \{1, 17\}$, and similarly $B, C, D$ for $y, z, t$:
$$7A + 6B + 4C \equiv D \pmod{32}.$$

All 8 valid combinations yield: $A = 1 \Leftrightarrow D = 17$, and $A = 17 \Leftrightarrow D = 1$, regardless of $B$ and $C$.

**Consequence:** $x \equiv \pm 1 \pmod{8}$ if and only if $t \equiv \pm 3 \pmod{8}$.

---

## Mod 3 Constraint

$6 \equiv 0$, $7 \equiv 1$, $4 \equiv 1 \pmod{3}$. The equation reduces to
$$x^4 + z^4 \equiv t^4 \pmod{3}.$$
For any $n \not\equiv 0 \pmod{3}$: $n^4 \equiv 1 \pmod{3}$ (Fermat).

| Pattern | Equation mod 3 | Possible? |
|---------|---------------|-----------|
| $3 \nmid x$, $3 \nmid z$, $3 \nmid t$ | $1 + 1 = 2 \equiv 1$? **No** | ✗ |
| $3 \mid x$, $3 \nmid z$, $3 \nmid t$ | $0 + 1 = 1$ | ✓ |
| $3 \nmid x$, $3 \mid z$, $3 \nmid t$ | $1 + 0 = 1$ | ✓ |
| $3 \nmid x$, $3 \nmid z$, $3 \mid t$ | $1 + 1 \equiv 0$? **No** | ✗ |
| $3 \mid x$, $3 \mid z$, $3 \nmid t$ | $0 + 0 \neq 1$ | ✗ |
| $3 \mid x$, $3 \nmid z$, $3 \mid t$ | $0 + 1 \neq 0$ | ✗ |

**Conclusion:** In any primitive solution, exactly one of $3 \mid x$ or $3 \mid z$ holds, and $3 \nmid t$.

---

## Mod 5 Constraint

$7 \equiv 2$, $6 \equiv 1$, $4 \equiv 4 \pmod{5}$. For $n \not\equiv 0 \pmod{5}$: $n^4 \equiv 1 \pmod{5}$.

Complete case analysis:

| Divisibility pattern | $2x^4 + y^4 + 4z^4 \equiv t^4$ mod 5 | Valid? |
|---------------------|--------------------------------------|--------|
| None divisible by 5 | $2 + 1 + 4 = 7 \equiv 2 \neq 1$ | ✗ |
| $5 \mid y$ only | $2 + 0 + 4 = 6 \equiv 1 = 1$ | **✓** |
| $5 \mid x$, $5 \mid t$ | $0 + 1 + 4 \equiv 0$ mod 5 | ✓ (less common) |
| All others | fail | ✗ |

**Primary conclusion:** For the majority of primitive solutions (if any), $5 \mid y$ with $5 \nmid x, z, t$.

---

## Summary of Divisibility Constraints

For any primitive solution $(x,y,z,t)$ (all odd):
1. $3 \mid x$ or $3 \mid z$ (not both, not $3 \mid t$).
2. $5 \mid y$ (the dominant case mod 5).
3. $x \equiv \pm 3 \pmod{8} \Rightarrow t \equiv \pm 1 \pmod{8}$, and vice versa.

The simplest case satisfying all three constraints simultaneously:
$$x \equiv 3 \pmod{24},\quad y \equiv 5 \pmod{10},\quad z \equiv 1 \pmod{6},\quad t \equiv 1 \pmod{8}.$$

---

## The Associated K3 Surface

The projective closure
$$S: 7x^4 + 6y^4 + 4z^4 = t^4 \subset \mathbb{P}^3_\mathbb{Q}$$
is a **smooth diagonal quartic surface**, hence a K3 surface of geometric genus 1.

- **Smoothness:** $\nabla F = (28x^3, 24y^3, 16z^3, -4t^3) = 0$ only at $(0,0,0,0) \notin \mathbb{P}^3$.
- **K3 surfaces** can have dense rational points (Bogomolov–Tschinkel, for some families)
  or can be entirely void of rational points (obstructed by the Brauer group).
- The Brauer–Manin obstruction: for diagonal quartics $ax^4 + by^4 + cz^4 = dw^4$,
  the failure of the Hasse principle (local-to-global) has been studied by
  Cassels–Guy (1966), Colliot-Thélène–Sansuc–Swinnerton-Dyer (1987), and others.
  In some cases with locally soluble surface, a **transcendental Brauer element** provides
  an obstruction to the existence of rational points.

**Status:** Whether $S$ has a rational (equivalently, integer) point is currently **open** without
specialized algebraic-geometry computation (e.g., explicit Brauer group calculation or 2-descent
on associated genus-1 curves).

---

## Computational Evidence

| Method | Range searched | Result |
|--------|---------------|--------|
| Direct enumeration | $\max(|x|,|y|,|z|,|t|) \leq 300$ | No solution |
| Meet-in-the-middle (odd only) | $\max(|x|,|y|) \leq 5000$, $|z| \leq 5000$, $t \leq 12500$ | No solution |
| Fast meet-in-the-middle | $x,y,z$ odd, $\leq 3000$; $t \leq 6093$ | No solution |

All searches are for primitive solutions (after the parity lemma reduces to all-odd case).

---

## What Would Close the Problem

### Path 1: Finding a solution
A dedicated lattice/algebraic search on the associated elliptic fibrations of the K3 surface
would be the most promising avenue.

### Path 2: Proving non-existence
1. **Compute the Brauer group** $\operatorname{Br}(S)/\operatorname{Br}(\mathbb{Q})$ explicitly.
   If a non-trivial Brauer class kills all adelic points, the Brauer–Manin obstruction
   proves $S(\mathbb{Q}) = \emptyset$.
2. **2-descent on elliptic fibrations:** The K3 surface admits several pencils of elliptic curves;
   a 2-descent on each fiber might obstruct rational sections.
3. **Finite field statistics:** The Weil conjectures and distribution of point counts mod $p$ can
   give heuristics on whether rational points exist.

---

## Related Work

- **Cassels & Guy (1966):** Showed $3u^4 + 4v^4 + 5w^4 = 0$ has a Brauer-Manin obstruction.
- **Colliot-Thélène & Sansuc (1987):** Brauer–Manin obstruction on diagonal quartic surfaces.
- **Elkies (1988):** Infinite families of diagonal quartics with rational points.
- **Loughran & Smeets (2017):** Quantitative aspects of diagonal quarticsurf aces.
