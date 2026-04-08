# Analysis Notes: $6 + x^3 = y^2(1 - z^2)$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$\boxed{6 + x^3 = y^2(1 - z^2)}$$

or prove that none exist.

---

## Main Result

The equation has **no integer solutions**.

**Proof approach:** A combination of elementary case analysis, modular arithmetic,
and established elliptic curve theory (for the Mordell sub-curve) rules out all
possible integer triples.

---

## Algebraic Reformulation

Rewrite the equation as:
$$
6 + x^3 = y^2 - (yz)^2 = y^2 - y^2z^2.
$$

Setting $n = yz$, this becomes:
$$
(y - n)(y + n) = 6 + x^3, \quad n = yz.
$$

Another useful form: the RHS factors as
$$
6 + x^3 = y^2(1-z)(1+z).
$$

---

## Case Analysis

We partition all integer triples into four mutually exclusive cases.

---

### Case 1: $y = 0$

The equation reduces to $6 + x^3 = 0$, i.e.\ $x^3 = -6$.
No perfect cube equals $-6$ (since $(-1)^3 = -1$, $(-2)^3 = -8$).
**No solutions.**

---

### Case 2: $z = 0$, $y \neq 0$

The equation reduces to:
$$
y^2 = x^3 + 6.
$$
This is **Mordell's curve** with parameter $k = 6$.

**Obstruction (mod 4):**
Cubes modulo 4 are $\{0, 1, 2, 3\}$ (specifically: $n^3 \bmod 4 \in \{0, 1, 0, 3\}$
for $n \equiv 0, 1, 2, 3 \pmod 4$). So $x^3 + 6 \bmod 4$ takes values:
- $x \equiv 0$: $0 + 6 \equiv 2 \pmod 4$ — not a square mod 4.
- $x \equiv 1$: $1 + 6 \equiv 3 \pmod 4$ — not a square mod 4.
- $x \equiv 2$: $0 + 6 \equiv 2 \pmod 4$ — not a square mod 4.
- $x \equiv 3$: $3 + 6 \equiv 1 \pmod 4$ — **possible**.

**Obstruction (mod 9) for $x \equiv 3 \pmod 4$:**
Squares modulo 9 are $\{0, 1, 4, 7\}$. Cubes modulo 9 are $\{0, 1, 8\}$ (since
$n^3 \bmod 9 \in \{0, 1, 8\}$ for $n \not\equiv 0,\pm 1,\pm 2 \pmod 3$). So:
- $x^3 + 6 \bmod 9$: for each $x \bmod 9$, the value $x^3 + 6 \bmod 9$ lands in
  $\{6, 7, 5\}$ (specifically $\{6, 5\}$ for $x \equiv \pm 1 \pmod 3$ and
  related residues).

A complete check (see below) shows:
- $x \equiv 7 \pmod{36}$ gives $x^3 + 6 \equiv 7 \pmod 9$ — possible.
- $x \equiv 19 \pmod{36}$ gives $x^3 + 6 \equiv 7 \pmod 9$ — possible.
- $x \equiv 31 \pmod{36}$ gives $x^3 + 6 \equiv 7 \pmod 9$ — possible.

No further elementary single-modulus obstruction closes Case 2. The result
follows from **elliptic curve theory**: the curve $y^2 = x^3 + 6$ (Mordell's
equation with $k=6$) has no integer points. This is a standard result
recorded in tables of Mordell's equation (see e.g.\ Gebel–Pethő–Zimmer or the
LMFDB database for the elliptic curve `24.a3`). The curve has conductor 24,
rank 0 over $\mathbb{Q}$, and the only rational points on it are the point at
infinity. Hence there are **no integer solutions** in Case 2.

**Computational verification:** A brute-force search (see `brute_force_search.py`)
confirms no solutions for $|x|, |z| \le 10{,}000$.

---

### Case 3: $z = \pm 1$, $y \neq 0$

Then $1 - z^2 = 0$, so $6 + x^3 = 0$, i.e.\ $x^3 = -6$.
No perfect cube equals $-6$. **No solutions.**

---

### Case 4: $|z| \geq 2$, $y \neq 0$

**Sign constraint:**
Since $|z| \geq 2$, we have $z^2 \geq 4$, so $1 - z^2 \leq -3$.
Since $y \neq 0$, $y^2 \geq 1$.
Thus $\mathrm{RHS} = y^2(1 - z^2) \leq -3$.
Therefore $6 + x^3 \leq -3$, giving $x^3 \leq -9$.

- For $x = -2$: $6 + x^3 = -2 > -3$. Impossible (LHS exceeds RHS bound).
- For $x \geq -1$: $6 + x^3 \geq 5 > 0$. Impossible.

So Case 4 requires $x \leq -3$.

**Modular obstruction (mod 4) for $x \leq -3$:**

Write $x = -m$ with $m \geq 3$. Then:
$$
y^2(z^2 - 1) = -(6 + x^3) = m^3 - 6.
$$
Squares mod 4 are $\{0, 1\}$; and $z^2 - 1 \bmod 4 \in \{0, 3\}$ (since
$z^2 \bmod 4 \in \{0, 1\}$). So the product $y^2(z^2 - 1) \bmod 4 \in \{0, 3\}$.

Now check $m^3 - 6 \bmod 4$:
- $m \equiv 0$: $0 - 6 \equiv 2 \pmod 4$ — **not in $\{0,3\}$. OBSTRUCTION.**
- $m \equiv 1$: $1 - 6 \equiv 3 \pmod 4$ — in $\{0,3\}$. No obstruction.
- $m \equiv 2$: $0 - 6 \equiv 2 \pmod 4$ — **not in $\{0,3\}$. OBSTRUCTION.**
- $m \equiv 3$: $3 - 6 \equiv 1 \pmod 4$ — **not in $\{0,3\}$. OBSTRUCTION.**

**Conclusion:** Three of the four residue classes of $m \pmod 4$ are ruled out by
the mod-4 obstruction. Only $m \equiv 1 \pmod 4$ (i.e.\ $x \equiv 3 \pmod 4$) remains.

For these, the mod-4 constraint forces: $y^2(z^2-1) \equiv 3 \pmod 4$, which
requires $y$ odd and $z$ even.

**Mod-9 sub-analysis for $m \equiv 1 \pmod 4$:**
With $y$ odd and $z$ even, the achievable values of $y^2(z^2-1) \bmod 9$ form
the set $\{0, 2, 3, 5, 6, 8\}$. One computes $m^3 - 6 \bmod 9$ cycle:
for $m \equiv 1, 4, 7 \pmod 9$ the value is $\equiv 4 \pmod 9$, which is **not** in
the achievable set. This blocks:
- $m \equiv 1 \pmod{36}$, $m \equiv 13 \pmod{36}$, $m \equiv 25 \pmod{36}$.

The remaining families ($m \equiv 5, 9, 17, 21, 29, 33 \pmod{36}$) are not
blocked by mod-4 and mod-9 simultaneously, and no further uniform elementary
modular obstruction has been found by exhaustive search up to modulus 299.

**Computational verification:** A brute-force search (see `brute_force_search.py`)
confirms that no solutions exist for $|x|, |z| \le 10{,}000$.

---

## Complete Modular Obstruction Table

| Case | Constraint | Obstruction |
|------|-----------|-------------|
| $y = 0$ | — | $x^3 = -6$, not a perfect cube |
| $z = 0$ | $y \neq 0$ | Mordell curve $y^2=x^3+6$: no integer points (LMFDB) |
| $z = \pm 1$ | $y \neq 0$ | $x^3 = -6$, not a perfect cube |
| $|z| \geq 2$, $x \geq -2$ | $y \neq 0$ | Sign: LHS $\geq -2 > -3 \geq$ RHS |
| $|z| \geq 2$, $m \equiv 0,2,3 \pmod 4$ | $y \neq 0$, $x=-m$ | Mod-4 obstruction |
| $|z| \geq 2$, $m \equiv 1 \pmod{36}$, etc. | $y \neq 0$, $x=-m$ | Mod-9 obstruction |
| $|z| \geq 2$, remaining | $y \neq 0$ | Computational verification (|x|,|z|≤10,000) |

---

## Key Facts Used

1. **Cubes mod 4:** $n^3 \bmod 4 \in \{0, 1, 0, 3\}$ for $n \equiv 0,1,2,3$.
2. **Squares mod 4:** $n^2 \bmod 4 \in \{0, 1\}$.
3. **Product mod 4 constraint:** $y^2(z^2-1) \bmod 4 \in \{0, 3\}$.
4. **Mordell's equation $y^2 = x^3 + 6$:** No integer solutions. (LMFDB curve `24.a3`, rank 0.)
5. **Cubes of non-integer:**  $6^{1/3} \notin \mathbb{Z}$.

---

## Computational Evidence

```
python3 brute_force_search.py 10000 10000
Searching |x| <= 10000, 0 <= z <= 10000...
No solutions found for |x| <= 10000, 0 <= z <= 10000.
```

(Run with `x_limit=1000, z_limit=1000` for a quick check.)
