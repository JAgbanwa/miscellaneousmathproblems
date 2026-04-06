## Analysis Notes: $2x^4 - y^4 + z^3 = 0$

### Problem

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$2x^4 - y^4 + z^3 = 0. \tag{$\star$}$$

---

### 1. Main Result

The equation $(\star)$ has **infinitely many** integer solutions.  Six explicit
infinite parametric families are:

| Family | Formula | Primitive seed |
|--------|---------|----------------|
| 1 | $(0,\; t^3,\; t^4)$ | $(0, 1, 1)$ |
| 2 | $(t^3,\; t^3,\; -t^4)$ | $(1, 1, -1)$ |
| 3 | $(4t^3,\; 0,\; -8t^4)$ | $(4, 0, -8)$ |
| 4 | $(14t^3,\; 21t^3,\; 49t^4)$ | $(14, 21, 49)$ |
| 5 | $(196t^3,\; 392t^3,\; 2744t^4)$ | $(196, 392, 2744)$ |
| 6 | $(1922t^3,\; 961t^3,\; -29791t^4)$ | $(1922, 961, -29791)$ |

(These also generate families with $x \to -x$ and/or $y \to -y$ independently,
since $x^4 = (-x)^4$ and $y^4 = (-y)^4$.)

A brute-force search over $|x|, |y| \le 500$ finds all solutions belonging to
Families 1–5 (and their sign variants).  Extending to $|x|, |y| \le 2500$ finds
the seed for Family 6 at $(1922, 961, -29791)$.  No sporadic solution is found
within $|x|, |y| \le 2500$.

---

### 2. Weighted Homogeneity

Assign weights $\mathrm{wt}(x) = \mathrm{wt}(y) = 3$ and $\mathrm{wt}(z) = 4$.  Every monomial
has the same weighted degree 12:

$$\mathrm{wt}(x^4) = 4 \cdot 3 = 12, \qquad
  \mathrm{wt}(y^4) = 4 \cdot 3 = 12, \qquad
  \mathrm{wt}(z^3) = 3 \cdot 4 = 12.$$

Consequently, if $(x_0, y_0, z_0)$ is a solution then so is
$(n^3 x_0,\; n^3 y_0,\; n^4 z_0)$ for any integer $n$:

$$2(n^3 x_0)^4 - (n^3 y_0)^4 + (n^4 z_0)^3
  = n^{12}\bigl(2x_0^4 - y_0^4 + z_0^3\bigr) = n^{12} \cdot 0 = 0.$$

This weighted scaling is the mechanism that turns each primitive seed into an
infinite parametric family.

---

### 3. Derivation of the Four Families

#### Family 1 — Setting $x = 0$

With $x = 0$ the equation reduces to $z^3 = y^4$.
The integer solutions to $z^3 = y^4$ are exactly $y = t^3$, $z = t^4$ for
$t \in \mathbb{Z}$ (unique factorisation: if $p^a \| y$ then $p^{4a} \| y^4 = z^3$,
forcing $3 \mid 4a$, so $3 \mid a$; hence $y$ is a perfect cube).

**Family 1:** $(x, y, z) = (0,\; t^3,\; t^4)$ for all $t \in \mathbb{Z}$.

$$2 \cdot 0 - t^{12} + t^{12} = 0. \checkmark$$

#### Family 2 — Setting $y = x$

With $y = x$ the equation becomes $2x^4 - x^4 + z^3 = x^4 + z^3 = 0$,
i.e., $z^3 = -x^4$.  By the same unique-factorisation argument, $x$ must be a
perfect cube: $x = t^3$, $z = -t^4$.

**Family 2:** $(x, y, z) = (t^3,\; t^3,\; -t^4)$ for all $t \in \mathbb{Z}$.

$$2t^{12} - t^{12} + (-t^4)^3 = t^{12} - t^{12} = 0. \checkmark$$

*Note:* Setting $y = -x$ gives the same calculation — since $(-x)^4 = x^4$ —
yielding the family $(t^3, -t^3, -t^4)$, i.e.\ **Family 2** with $y$ negated.

#### Family 3 — Setting $y = 0$

With $y = 0$ the equation becomes $2x^4 + z^3 = 0$, i.e., $z^3 = -2x^4$.
We need $2x^4$ to be a perfect cube.  Writing $x = 4t^3$:

$$2(4t^3)^4 = 2 \cdot 256 \cdot t^{12} = 512 t^{12} = (8t^4)^3,$$

so $z = -8t^4$ works.

**Family 3:** $(x, y, z) = (4t^3,\; 0,\; -8t^4)$ for all $t \in \mathbb{Z}$.

$$2(4t^3)^4 - 0 + (-8t^4)^3 = 512t^{12} - 512t^{12} = 0. \checkmark$$

*Why is $x = 4t^3$ the right form?*  We need $2x^4 = k^3$.
Factoring: $2 x^4 = k^3$.  If $x = 2^a m$ (with $m$ odd), then
$2^{4a+1} m^4 = k^3$; for a perfect cube, $4a+1 \equiv 0 \pmod{3}$
gives $a \equiv 2 \pmod{3}$, so the minimal positive $a$ is $a = 2$,
yielding $x = 4 \cdot m$ where $m$ is a perfect cube.

#### Family 4 — The $x = 2p, y = 3p$ Substitution

Set $x = 2p$, $y = 3p$ for some integer $p$.  The equation becomes:

$$2(2p)^4 - (3p)^4 + z^3 = p^4(2 \cdot 16 - 81) + z^3 = -49p^4 + z^3 = 0,$$

so $z^3 = 49p^4$.  We need $49p^4 = 7^2 p^4$ to be a perfect cube.
Writing $p = 7^{3k+1} \cdot m^3$ (minimal case: $k=0$, $m=1$, $p=7$):

$$z^3 = 7^2 \cdot 7^4 \cdot k^{12} = 7^6 k^{12} = (7^2 k^4)^3 = (49k^4)^3.$$

With $p = 7t^3$: $x = 14t^3$, $y = 21t^3$, $z = 49t^4$.

**Family 4:** $(x, y, z) = (14t^3,\; 21t^3,\; 49t^4)$ for all $t \in \mathbb{Z}$.

**Key algebraic identity:**
$$2(2 \cdot 7)^4 - (3 \cdot 7)^4 + (7^2)^3
  = 7^4(2 \cdot 2^4 - 3^4) + 7^6
  = 7^4 \cdot (-49) + 7^6
  = 7^4(-49 + 49)
  = 0.$$

This rests on the numerical coincidence $2 \cdot 2^4 - 3^4 + 7^2 = 32 - 81 + 49 = 0$.

#### Family 5 — The $y = 2x$ Substitution

Set $y = 2x$.  The equation becomes:
$$2x^4 - (2x)^4 + z^3 = 2x^4 - 16x^4 + z^3 = -14x^4 + z^3 = 0,$$
so $z^3 = 14x^4$.  We need $14x^4 = 2 \cdot 7 \cdot x^4$ to be a perfect cube.
Writing $x = 2^a \cdot 7^b \cdot m^3$ (with $\gcd(m,14)=1$), we get
$z^3 = 2^{4a+1} \cdot 7^{4b+1} \cdot m^{12}$.
For a perfect cube: $4a+1 \equiv 0 \pmod{3}$ gives $a \equiv 2 \pmod{3}$, so
$a = 2$; and $4b+1 \equiv 0 \pmod{3}$ gives $b \equiv 2 \pmod{3}$, so $b = 2$.
With minimal $a = b = 2$, $m = t$:
$$x = 4 \cdot 49 \cdot t^3 = 196t^3, \quad
  y = 392t^3, \quad
  z = 2^3 \cdot 7^3 \cdot t^4 = 2744t^4.$$

**Family 5:** $(x, y, z) = (196t^3,\; 392t^3,\; 2744t^4)$ for all $t \in \mathbb{Z}$.

**Key algebraic identity:**
$$2 \cdot 4^4 - 8^4 + 8^3 \cdot 7 = 512 - 4096 + 3584 = 0.$$
Multiplying by $7^8$:
$$2(4 \cdot 7^2)^4 - (8 \cdot 7^2)^4 + (8 \cdot 7^3)^3 = 7^8(512 - 4096 + 3584) = 0,$$
i.e., $2 \cdot 196^4 - 392^4 + 2744^3 = 0$.

**Verified primitive (weighted):** The seed $(196, 392, 2744)$ has $196 = 4 \cdot 7^2$,
so $8 \nmid 196$, ruling out $t = 2$ in the weighted-primitivity test.

#### Family 6 — The $(x, y) = (2p^2, p^2)$ Substitution with $p = 31$

Set $x = 2p^2$, $y = p^2$, $z = -p^3$ for an integer $p$.  Substituting:
$$2(2p^2)^4 - (p^2)^4 + (-p^3)^3 = p^8(2 \cdot 2^4 - 1 - p) = p^8(31 - p).$$
This vanishes if and only if $p = 0$ or $p = 31$.  Taking $p = 31$:
$$x = 2 \cdot 31^2 = 1922, \quad y = 31^2 = 961, \quad z = -31^3 = -29791.$$

**Family 6:** $(x, y, z) = (1922t^3,\; 961t^3,\; -29791t^4)$ for all $t \in \mathbb{Z}$.

**Key algebraic identity:**
$$2 \cdot 2^4 - 1^4 - 31 = 32 - 1 - 31 = 0.$$
Multiplying by $31^8$:
$$2(2 \cdot 31^2)^4 - (31^2)^4 + (-31^3)^3 = 31^8(32 - 1 - 31) = 0.$$

**Note:** The identity $p^8(31 - p) = 0$ holds only for $p = 31$ (and $p = 0$),
so Family 6 arises from a sporadic algebraic coincidence rather than a
sub-family parametrisation.  The infinite family is produced by weighted scaling
of this primitive seed.

**Verified primitive (weighted):** $961 = 31^2$, so $8 \nmid 961$,
ruling out $t = 2$.

---

### 4. Proof of Infinitude

**Via Family 1.** The map $\varphi : \mathbb{N} \to \mathbb{Z}^3$,
$n \mapsto (0, n^3, n^4)$, is injective: if $n_1^3 = n_2^3$ for natural numbers
$n_1, n_2$, then $n_1 = n_2$ (since $n \mapsto n^3$ is strictly increasing on
$\mathbb{N}$, via $n_1 < n_2 \Rightarrow n_1^3 < n_2^3$).
Every element of $\varphi(\mathbb{N})$ is a solution (Family 1, verified by ring).
Hence the solution set contains the infinite set $\varphi(\mathbb{N})$.

---

### 5. Modular Analysis

Setting $x = 0$ shows the equation has solutions over $\mathbb{F}_p$ for every
prime $p$ (simply take $y = 1$, $z = 1$; or $y = 0$, $z = 0$).  Hence there is
**no modular obstruction** of any kind.  The equation is everywhere locally
solvable, consistent with the existence of global integer solutions.

**Mod 2:** From $2x^4 - y^4 + z^3 \equiv -y^4 + z^3 \equiv y^4 + z^3 \pmod{2}$,
the equation requires $y \equiv z \pmod{2}$ (both odd or both even, with $x$
arbitrary).

**Mod 8:** $z^3 \equiv z \pmod{8}$ for all $z$ (Fermat little theorem extension).
$y^4 \equiv 1$ or $0 \pmod{8}$.  So $z \equiv 2x^4 - 1$ or $z \equiv 2x^4 \pmod{8}$,
which is satisfiable for all $x$.

---

### 6. Explicit Solution Table

| $(x, y, z)$ | $2x^4 - y^4 + z^3$ | Family |
|---|---|---|
| $(0, 0, 0)$ | $0$ | trivial |
| $(0, 1, 1)$ | $0-1+1=0$ | Family 1, $t=1$ |
| $(0, -1, 1)$ | $0-1+1=0$ | Family 1, $t=-1$ |
| $(0, 8, 16)$ | $0-4096+4096=0$ | Family 1, $t=2$ |
| $(1, 1, -1)$ | $2-1-1=0$ | Family 2, $t=1$ |
| $(-1, -1, -1)$ | $2-1-1=0$ | Family 2, $t=-1$ |
| $(1, -1, -1)$ | $2-1-1=0$ | Family 2b, $t=1$ |
| $(4, 0, -8)$ | $512-0-512=0$ | Family 3, $t=1$ |
| $(-4, 0, -8)$ | $512-0-512=0$ | Family 3, $t=-1$ |
| $(32, 0, -128)$ | $2\cdot2^{20}-128^3=0$ | Family 3, $t=2$ |
| $(14, 21, 49)$ | $76832-194481+117649=0$ | Family 4, $t=1$ |
| $(-14, -21, 49)$ | $0$ | Family 4, $t=-1$ |
| $(112, 168, 784)$ | $0$ | Family 4, $t=2$ |
| $(196, 392, 2744)$ | $2\cdot196^4-392^4+2744^3=0$ | Family 5, $t=1$ |
| $(-196, -392, 2744)$ | $0$ | Family 5, $t=-1$ |
| $(1922, 961, -29791)$ | $2\cdot1922^4-961^4+(-29791)^3=0$ | Family 6, $t=1$ |

---

### 7. Geometric Structure

The equation $2x^4 - y^4 + z^3 = 0$ defines a **weighted projective surface**
$S$ in the weighted projective space $\mathbb{P}(3, 3, 4)$ (weights corresponding
to $x$, $y$, $z$ respectively), of weighted degree 12.  The surface is singular
at the origin but smooth over $\mathbb{Q} \setminus \{0\}$ at each of the family
loci.

Unlike the high-genus curves in this repository (for which Faltings' theorem
gives finiteness), $S$ is a surface and Faltings does not apply;
the families 1–4 each trace a rational curve on $S$, confirming the
abundance of rational (hence integer) points.

---

### 8. Proof Status

| Component | Status |
|-----------|--------|
| Family 1 $(0, t^3, t^4)$ verified | ✓ Complete (`ring`) |
| Family 2 $(t^3, t^3, -t^4)$ verified | ✓ Complete (`ring`) |
| Family 3 $(4t^3, 0, -8t^4)$ verified | ✓ Complete (`ring`) |
| Family 4 $(14t^3, 21t^3, 49t^4)$ verified | ✓ Complete (`ring`) |
| Family 5 $(196t^3, 392t^3, 2744t^4)$ verified | ✓ Complete (`ring`) |
| Family 6 $(1922t^3, 961t^3, -29791t^4)$ verified | ✓ Complete (`ring`) |
| Weighted homogeneity | ✓ Complete (`linear_combination`) |
| Infinitely many distinct solutions | ✓ Complete (strict monotonicity of $n^3$ on $\mathbb{N}$) |
| No sporadic solutions for $\|x\|, \|y\| \le 2500$ | ✓ Complete (exhaustive search) |
| Lean 4 formalisation (0 sorry) | ✓ **Complete** |
| Full classification of all integer solutions | Open (requires arithmetic geometry of $S$) |
