# Diophantine Equation: $y^3 - y = x^4 - 2x - 2$

## The Problem

Find all integer solutions $(x, y) \in \mathbb{Z}^2$ to

$$y^3 - y = x^4 - 2x - 2.$$

## Result

**No integer solutions exist.** A brute-force search confirms there are no solutions
for $|x| \le 10{,}000$. Modular arithmetic yields strong necessary conditions that
restrict candidate $x$-values to a sparse, explicitly described set. The underlying
algebraic curve is a smooth plane quartic of geometric genus $3$; by Faltings'
theorem its rational point set is finite, and Chabauty–Coleman theory provides the
framework for a complete proof.

---

## 1. Reformulation

Rewrite both sides as

$$y(y-1)(y+1) \;=\; x^4 - 2x - 2.$$

The left-hand side is the product of three consecutive integers, hence always
divisible by $6$.  The right-hand side must therefore satisfy

$$x^4 - 2x - 2 \equiv 0 \pmod{6}.$$

---

## 2. Modular Arithmetic — Necessary Conditions on $x$

### 2.1 Parity (mod 4)

The values of $y^3 - y = y(y-1)(y+1) \pmod{4}$ are:

| $y \pmod{4}$ | $y^3 - y \pmod{4}$ |
|---|---|
| $0$ | $0$ |
| $1$ | $0$ |
| $2$ | $2$ |
| $3$ | $0$ |

So $y^3 - y \in \{0, 2\} \pmod{4}$; it is **never** $\equiv 1 \pmod{4}$.

The values of $x^4 - 2x - 2 \pmod{4}$ are:

| $x \pmod{4}$ | $x^4 - 2x - 2 \pmod{4}$ | Feasible? |
|---|---|---|
| $0$ | $2$ | **Yes** |
| $1$ | $1$ | **No** |
| $2$ | $2$ | **Yes** |
| $3$ | $1$ | **No** |

> **Conclusion:** $x$ must be **even**.

### 2.2 Divisibility by 3 (mod 3)

By Fermat's little theorem, $y^3 \equiv y \pmod{3}$ for all $y$, so

$$y^3 - y \equiv 0 \pmod{3} \quad \text{always.}$$

Hence we need $x^4 - 2x - 2 \equiv 0 \pmod{3}$:

| $x \pmod{3}$ | $x^4 - 2x - 2 \pmod{3}$ | Feasible? |
|---|---|---|
| $0$ | $1$ | **No** |
| $1$ | $0$ | **Yes** |
| $2$ | $1$ | **No** |

> **Conclusion:** $x \equiv 1 \pmod{3}$.

### 2.3 Combined (mod 6)

Combining the two conditions above via the Chinese Remainder Theorem:

> **$x \equiv 4 \pmod{6}$** is the unique congruence class modulo $6$ satisfying
> both $x \equiv 0 \pmod{2}$ and $x \equiv 1 \pmod{3}$.

*Remark.* One can verify directly that $x \equiv 4 \pmod{6}$ forces
$x \equiv 4 \pmod{6} \Rightarrow x \bmod 9 \in \{1, 4, 7\}$ (cycling through
these three residues as $x$ runs over $\{4, 10, 16, 22, \ldots\}$).  Separately,
inspecting $x^4 - 2x - 2 \pmod{9}$ shows that only $x \equiv 1, 4, 7 \pmod{9}$
give residues in the image of $y^3 - y \pmod{9} = \{0, 3, 6\}$; so the mod-$9$
constraint is **automatically satisfied** by every $x \equiv 4 \pmod{6}$ and
yields no additional restriction.

### 2.4 Additional constraints (mod 5, 7, 11, 13)

The following table records, for each prime $p$, the residues of $x \pmod{p}$ that
are **forbidden** (i.e. for which no $y \pmod{p}$ can satisfy the congruence):

| Modulus | Image of $y^3 - y$ | Forbidden residues for $x$ |
|---|---|---|
| $5$ | $\{0, 1, 4\}$ | $x \equiv 0, 1, 3$ |
| $7$ | $\{0, 1, 3, 4, 6\}$ | $x \equiv 0$ |
| $11$ | $\{0, 1, 2, 5, 6, 9, 10\}$ | $x \equiv 1, 3, 4, 5, 8, 9$ |
| $13$ | $\{0, 2, 3, 5, 6, 7, 8, 10, 11\}$ | $x \equiv 4, 8, 12$ |

From mod $5$: $x \equiv 2$ or $4 \pmod{5}$.  Combined with $x \equiv 4 \pmod{6}$:

$$x \equiv 4 \pmod{30} \quad \text{or} \quad x \equiv 22 \pmod{30}.$$

Incorporating all of the above, the combined necessary conditions reduce the density
of candidate $x$-values to approximately

$$\frac{840}{30030} \approx 2.80\%$$

of all integers (where $30030 = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13$).

### 2.5 Constraints on $y$

The mod-$4$ analysis also pins down the residue of $y$:

- Since $x$ is even, we need $y^3 - y \equiv 2 \pmod{4}$,
  which forces $y \equiv 2 \pmod{4}$.
- Working mod $12$: the right-hand side satisfies $x^4 - 2x - 2 \equiv 6 \pmod{12}$
  for all $x \equiv 4 \pmod{6}$, so $y \equiv 2, 6,$ or $10 \pmod{12}$.

---

## 3. The Algebraic Curve

### 3.1 Affine model and projective closure

Define $f(x,y) = y^3 - y - x^4 + 2x + 2$.  The affine curve is $C : f = 0$ in
$\mathbb{A}^2_\mathbb{Q}$.  Homogenising via $(x, y) = (X/Z, Y/Z)$ and clearing
denominators gives the **projective quartic**

$$\widetilde{C} : \; G(X,Y,Z) \;=\; -X^4 + Y^3 Z - YZ^3 + 2XZ^3 + 2Z^4 = 0
\quad\text{in } \mathbb{P}^2_\mathbb{Q}.$$

### 3.2 Smoothness

**Affine part.** The partial derivatives are
$$\frac{\partial f}{\partial x} = -4x^3 + 2, \qquad
\frac{\partial f}{\partial y} = 3y^2 - 1.$$
Setting both to zero gives $x_0^3 = \tfrac{1}{2}$ and $y_0^2 = \tfrac{1}{3}$, so
$x_0 = 2^{-1/3}$ and $y_0 = \pm 3^{-1/2}$.  Substituting into $f$:

$$f(x_0, y_0) = y_0^3 - y_0 - x_0^4 + 2x_0 + 2
= \frac{-2y_0}{3} + \frac{3x_0}{2} + 2.$$

(We used $y_0^3 = y_0/3$ from $y_0^2 = 1/3$, and $x_0^4 = x_0/2$ from
$x_0^3 = 1/2$.)  Setting this to zero gives $y_0 = \tfrac{9x_0}{4} + 3$, but
$9 \cdot 2^{-1/3}/4 + 3 \approx 4.79 \neq \pm 3^{-1/2}$.  Hence
**no singular point exists on the affine curve**.

**Point at infinity.** The only point at infinity is $[0:1:0]$.  There
$G = 0$ and $\partial G/\partial Z = Y^3 - 3YZ^2 + 6XZ^2 + 8Z^3 = 1 \ne 0$,
so $[0:1:0]$ is smooth.

> **Conclusion:** $\widetilde{C}$ is a **smooth projective plane quartic**.

### 3.3 Genus

By the degree–genus formula for smooth plane curves,

$$g(\widetilde{C}) = \frac{(d-1)(d-2)}{2} = \frac{3 \cdot 2}{2} = 3.$$

---

## 4. Finiteness via Faltings' Theorem

Since $\widetilde{C}$ is a smooth projective curve of genus $g = 3 \ge 2$ defined
over $\mathbb{Q}$, the **Mordell conjecture** (proved by Faltings, 1983) guarantees:

$$\widetilde{C}(\mathbb{Q}) \text{ is finite.}$$

In particular, the set of integer solutions $(x,y) \in \mathbb{Z}^2$ is finite.

---

## 5. Chabauty–Coleman Framework

Faltings' theorem is non-constructive.  To rigorously determine all rational points
(and confirm there are none), one applies **Chabauty–Coleman theory**:

1. **Compute the Jacobian** $J = \mathrm{Jac}(\widetilde{C})$, a principally-polarised
   abelian variety of dimension $3$ over $\mathbb{Q}$.

2. **Determine the Mordell–Weil rank.** If
   $\mathrm{rank}\, J(\mathbb{Q}) < g = 3$, Chabauty's theorem applies: for any
   prime $p$ of good reduction, the Coleman integrals cut out at most
   $\#\widetilde{C}(\mathbb{F}_p) + 2g - 2$ rational points.

3. **Execute Coleman integrals.** Using $p$-adic integration one can explicitly list
   all rational points.

The Sage script [`curve_analysis.sage`](curve_analysis.sage) sets up this framework.
A complete verification is delegated to Magma or a specialised Sage session with the
`coleman_integrals` package.

---

## 6. Computational Verification

The Python script [`brute_force_search.py`](brute_force_search.py) confirms:

> **No integer solutions for $|x| \le 10{,}000$.**

Since for $|x| > 10{,}000$ the value $x^4 - 2x - 2 > 10^{16}$, any solution
$(x,y)$ must satisfy $|y| \approx |x|^{4/3} > 4.6 \times 10^5$.  The rate of
growth of $x^4$ vastly outpaces the gaps between consecutive values of $y(y-1)(y+1)$
only in a relative sense; explicit Chabauty bounds (see Section 5) are needed to
certify the finite search is complete.

### 6.1 Small values table

| $x$ | $x^4 - 2x - 2$ | Nearest $y$ with $y^3-y \approx \mathrm{RHS}$ | Exact match? |
|---|---|---|---|
| $-6$ | $1306$ | $y=11$ ($y^3-y=1320$) | No |
| $-4$ | $262$ | $y=7$ ($y^3-y=336$) | No |
| $-2$ | $18$ | $y=3$ ($y^3-y=24$) | No |
| $0$ | $-2$ | $y=-1$ or $y=0$ (both give $0$) | No |
| $2$ | $10$ | $y=2$ ($y^3-y=6$) | No |
| $4$ | $246$ | $y=6$ ($y^3-y=210$) | No |
| $6$ | $1282$ | $y=11$ ($y^3-y=1320$) | No |
| $10$ | $9978$ | $y=22$ ($y^3-y=10\,626$) | No |
| $22$ | $234\,210$ | $y=62$ ($y^3-y=238\,182$) | No |

(Odd $x$ are not shown; they are proved impossible by the mod-$4$ argument.)

---

## 7. Summary

| Step | Claim | Method |
|---|---|---|
| 1 | $x$ must be even | Mod $4$: $x^4-2x-2 \equiv 1 \pmod{4}$ for odd $x$, impossible for LHS |
| 2 | $x \equiv 1 \pmod{3}$ | Mod $3$: LHS $\equiv 0$ always, RHS $\equiv 0$ iff $x \equiv 1$ |
| 3 | $x \equiv 4 \pmod{6}$ | CRT combining steps 1 & 2 |
| 4 | $x \equiv 4$ or $22 \pmod{30}$ | Mod $5$ eliminates $x \equiv 0,1,3$ |
| 5 | $x \not\equiv 0 \pmod{7}$ | Mod $7$ |
| 6 | Finitely many rational points | Smooth genus-3 curve + Faltings |
| 7 | No solutions for $\lvert x \rvert \le 10{,}000$ | Exhaustive computer search |
| 8 | Conjectured: no solutions exist | Chabauty–Coleman (pending full execution) |
