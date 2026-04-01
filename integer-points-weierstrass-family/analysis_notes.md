# Mathematical Analysis: Integer Points on a Parametric Elliptic Curve Family

## The Problem

We seek all integer solutions $(n, x, y) \in \mathbb{Z}^3$ to

$$y^2 = x^3 + (36n+27)^2\, x^2
         + \bigl(15552n^3 + 34992n^2 + 26244n + 6561\bigr)\, x
         + \bigl(46656n^4 + 139968n^3 + 157464n^2 + 78713n + 14748\bigr).$$

For each integer $n$ this is an elliptic curve $E_n / \mathbb{Q}$.

---

## 1. Factoring the Coefficients

The coefficient polynomials simplify as follows.

**$x^2$-coefficient:**
$$
(36n+27)^2 = 9^2 \cdot (4n+3)^2 = 81(4n+3)^2.
$$

**$x$-coefficient:**
$$
15552n^3 + 34992n^2 + 26244n + 6561
= 243(4n+3)^3 = 3^5 (4n+3)^3.
$$
This identity can be verified by expanding $243(4n+3)^3 = 243(64n^3+144n^2+108n+27)$
$= 15552n^3+34992n^2+26244n+6561$. ✓

**Constant term:**  $a_6(n) = 46656n^4 + 139968n^3 + 157464n^2 + 78713n + 14748$
(does not factor over $\mathbb{Z}$ as a polynomial in $(4n+3)$ alone).

So the family is
$$
E_n : \; y^2 = x^3 + 81(4n+3)^2 x^2 + 243(4n+3)^3 x + a_6(n).
$$

---

## 2. Reduction to Short Weierstrass Form

The substitution $u = x + 27(4n+3)^2$ (i.e., $x = u - a_2/3$) eliminates the $x^2$ term and converts $E_n$ to

$$
E_n : \; y^2 = u^3 + A(n)\,u + B(n),
$$

where

$$
A(n) = a_4 - \frac{a_2^2}{3}
     = 243(4n+3)^3 - \frac{81^2(4n+3)^4}{3}
     = 243(4n+3)^3\bigl(1 - 9(4n+3)\bigr)
     = -486(4n+3)^3(18n+13),
$$

$$
B(n) = \frac{2a_2^3}{27} - \frac{a_2 a_4}{3} + a_6
     = 161243136n^6 + 718875648n^5 + 1335341376n^4
       + 1322837568n^3 + 737088984n^2 + 219032405n + 27118239.
$$

This short Weierstrass model is **identical** to the one studied in
[`../elliptic-curve-diophantine/integer_points_parametric_ec.py`](../elliptic-curve-diophantine/integer_points_parametric_ec.py).

**Correspondence:** An integer solution $(n, x, y)$ of the original equation corresponds
to the integer point $(n, u, y)$ with $u = x + 27(4n+3)^2 \in \mathbb{Z}$ on the
short Weierstrass model.  In particular

| $(n, x, y)$ (this family) | $u = x + 27(4n+3)^2$ | Short-Weierstrass $(n, u, y)$ |
|---|---|---|
| $(-1, 18, \pm 167)$ | $45$ | $(-1, 45, \pm 167)$ |
| $(94, -562, \pm 17722)$ | $3877745$ | $(94, 3877745, \pm 17722)$ |
| $(-110, 646, \pm 40812)$ | $5156809$ | $(-110, 5156809, \pm 40812)$ |
| $(-64, 144840, \pm 333523318)$ | $1873083$ | $(-64, 1873083, \pm 333523318)$ |
| $(147498, -449511, \pm 2312387148693)$ | $9398540251164$ | $(147498, 9398540251164, \pm \cdots)$ |

---

## 3. Structure of Individual Curves

For any specific integer $n$, Siegel's theorem guarantees that $E_n(\mathbb{Z})$ is
**finite**. The relevant curve-theoretic data for the cases with known integer points:

| $n$ | $\Delta(E_n)$ | Conductor | Rank | Torsion |
|---|---|---|---|---|
| $-1$ | $-318382272$ | $318382272$ | $2$ | trivial |
| $94$ | — | $\approx 9.26\times 10^{30}$ | $\geq 1$ | trivial |
| $-110$ | — | $\approx 3.08\times 10^{28}$ | $\geq 1$ | trivial |
| $-64$ | — | $\approx 4.88\times 10^{29}$ | $\geq 1$ | trivial |

(Computed from `integer_points_family.sage`; see `sage_output.txt`.)

For $n = -1$, the full Weierstrass model is:
$$E_{-1} : y^2 = x^3 + 81x^2 - 243x + 187 \quad (\text{Weierstrass, not short form})$$
with $j\text{-invariant} = -918330048000/184249$ and **rank 2**.

The point $P = (18, 167)$ has **infinite order** (verified: $P.order() = +\infty$),
confirming rank $\geq 1$.  The second generator is unknown without further computation.

**Rigorous SageMath result:** `integral_points(E_{-1}) = {(18, ±167)}`.
There are no other integer points on $E_{-1}$.

---

## 4. Computational Results

### 4.1 Verification

All five known solutions were verified by direct substitution (see
`integer_points_family.sage`, Section 2).

### 4.2 Rigorous search for $n = -1$

SageMath's `integral_points()` (Baker's theorem bounds + Tzanakis–de Weger descent)
gives:
$$E_{-1}(\mathbb{Z}) = \{(18, \pm 167)\}.$$
Computation time: **1.57 s**.

### 4.3 Extended brute-force search

`brute_force_search.py` with $n \in [-200, 200]$ and $x \in [-2000, 200000]$
(~81 million checks, 26.7 s):

| $n$ | $x$ | $y$ |
|---|---|---|
| $-110$ | $646$ | $\pm 40812$ |
| $-64$ | $144840$ | $\pm 333523318$ |
| $-1$ | $18$ | $\pm 167$ |
| $94$ | $-562$ | $\pm 17722$ |

**No additional solutions found beyond the four listed above.**

An additional check over $x \in [-50000, -2001]$ for all $n$ in the above range also
found no new solutions.

---

## 5. The Solution at $n = 147498$

The solution $(n, x, y) = (147498, -449511, 2312387148693)$ is remarkable because
$n$ is far outside any feasible search range, yet $|x|$ is only $\approx 4.5 \times 10^5$.

In short Weierstrass coordinates:
$$
u = -449511 + 27 \cdot (4 \cdot 147498 + 3)^2 = -449511 + 27 \cdot 589995^2
  \approx 9.40 \times 10^{12}.
$$

The discovery of this solution likely exploits one of the following mechanisms:

1. **A parametric section.** If there exists a rational curve $\bigl(n(t), x(t), y(t)\bigr)$
   in the surface $y^2 = f_n(x)$ (a section of the family over $\mathbb{Q}$), points on
   that curve specialise to integer solutions at specific $t$.
2. **Descent or 2-isogeny.** Many large-height points on elliptic curves arise from
   the doubling map applied to a generator; the large $y$ value is consistent with
   this interpretation.
3. **Hidden parametrisation.** The family $A(n) = -486(4n+3)^3(18n+13)$ is divisible
   by $(4n+3)^3$, which may allow a specialisation of an isogeny to produce a
   parametric sub-family of solutions.

---

## 6. Open Questions

1. **Are there infinitely many $n$ with $E_n(\mathbb{Z}) \neq \emptyset$?**
   The current evidence (five known $n$-values) is consistent with infinitely many,
   but does not prove it. Proving infinitude would require exhibiting a rational section
   of the surface $\mathcal{E} \to \mathrm{Spec}\,\mathbb{Z}$ (over the parameter $n$).

2. **Is the solution set finite?** By Faltings / Siegel there are finitely many
   integer points for *each fixed* $n$, but the total over all $n$ is not obviously
   finite or infinite.

3. **What is the arithmetic of the surface $y^2 = f_n(x)$ over $\mathbb{Q}(n)$?**
   A positive Mordell–Weil rank for the generic fibre would imply infinitely many
   specialisations with integer points (by a theorem of Silverman).

4. **Is $(n=147498, x=-449511)$ part of a parametric family?** If one can find a
   polynomial/rational map $n \mapsto x(n)$ such that $f_n(x(n))$ is always a perfect
   square, this would yield infinitely many solutions.

---

## 7. References

- **Baker's theorem & integer points:** A. Baker, *Transcendental Number Theory*, 1975;
  N. Tzanakis, *Solving Thue-Mahler Equations*, 1984.
- **Siegel's theorem on integral points:** C.L. Siegel, *Über einige Anwendungen
  Diophantischer Approximationen*, 1929.
- **Silverman's specialisation theorem:** J. Silverman, *The Arithmetic of Elliptic
  Curves*, Thm. IX.6.1, 2009.
- **SageMath `integral_points()`:** Based on the Lenstra–Pethő–Tzanakis algorithm;
  see Cremona's *Algorithms for Modular Elliptic Curves*, Cambridge, 1997.
- **Companion code (short Weierstrass model):**
  [`../elliptic-curve-diophantine/integer_points_parametric_ec.py`](../elliptic-curve-diophantine/integer_points_parametric_ec.py)
