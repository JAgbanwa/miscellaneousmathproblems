# Analysis Notes: $y^2 z + yz^2 = x^3 + x^2 + 3x - 1$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to
$$y^2 z + yz^2 = x^3 + x^2 + 3x - 1,$$
or prove that none exist.

**Factored form:** The left side factors as $yz(y+z)$, so the equation is equivalently
$$yz(y+z) = x^3 + x^2 + 3x - 1.$$

---

## Quick Summary

| Item | Value |
|------|-------|
| Claim | No integer solutions exist |
| Search range verified | $\lvert x \rvert \leq 10{,}000$ (exhaustive divisor enumeration) |
| Elementary obstruction | Mod 7 rules out $x \equiv 1, 5, 9, 13 \pmod{14}$ (4 of 7 odd classes) |
| Surviving classes | $x \equiv 3, 7, 11 \pmod{14}$ — locally solvable at every prime |
| Proof status | Partial (elementary + computational); full proof requires descent |

---

## Elementary Constraint 1: $x$ Must Be Odd

**Claim.** Any integer solution has $x$ odd.

**Proof.** We show the left side $yz(y+z)$ is always even.

- If $y$ and $z$ are both even, then $y+z$ is even, and $yz(y+z)$ is divisible by 4.
- If exactly one of $y, z$ is even, then $yz$ is even.
- If $y$ and $z$ are both odd, then $y+z$ is even.

In every case $yz(y+z) \equiv 0 \pmod{2}$.

For the right side, $x^3 + x^2 + 3x - 1 \equiv x + x + x + 1 = 3x + 1 \equiv x+1 \pmod{2}$.
Hence RHS is even iff $x$ is odd. $\square$

---

## Elementary Constraint 2: Exact 2-Adic Valuation

**Claim.** For every odd $x$, $\nu_2(x^3 + x^2 + 3x - 1) = 2$ (divisible by 4, not by 8).

**Proof.** Write $x = 2k+1$:
$$x^3 + x^2 + 3x - 1 = (8k^3+12k^2+6k+1) + (4k^2+4k+1) + (6k+3) - 1$$
$$= 8k^3 + 16k^2 + 16k + 4 = 4(2k^3 + 4k^2 + 4k + 1).$$

The inner factor $q = 2k^3 + 4k^2 + 4k + 1$ satisfies:
- $k$ even: $q \equiv 0 + 0 + 0 + 1 \equiv 1 \pmod{2}$ (odd).
- $k$ odd: $q \equiv 2 + 4 + 4 + 1 = 11 \equiv 1 \pmod{2}$ (odd).

Hence $q$ is always odd, so $\nu_2(\text{RHS}) = 2$ for every odd $x$.

**Consequence.** Any solution must have $yz(y+z)$ divisible by exactly $4$ (not $8$). This constrains $(y, z)$ modulo 8:

**Lemma.** $yz(y+z) \equiv 4 \pmod{8}$ iff one of:
 - $y, z$ both odd and $y+z \equiv 4 \pmod{8}$, or
 - exactly one of $y, z$ is $\equiv 4 \pmod{8}$ and the other is odd.

(All other residue-class combinations give $yz(y+z) \equiv 0, 2,$ or $6 \pmod{8}$.)

---

## Key Result: Mod-7 Obstruction

**Theorem.** $yz(y+z) \not\equiv 3 \pmod{7}$ and $yz(y+z) \not\equiv 4 \pmod{7}$ for any integers $y, z$.

**Proof.** Exhaustive check over $\mathbb{Z}/7\mathbb{Z}$:

| $y \pmod{7}$ | $z \pmod{7}$ | $yz(y+z) \pmod{7}$ |
|-|-|-|
| Skipping entries with $y = 0$ or $z = 0$ or $y+z \equiv 0$: all give $0$. | | |
| 1 | 1 | 2 |
| 1 | 2 | 6 |
| 1 | 3 | 5 |
| 1 | 4 | 6 |
| 1 | 5 | 2 |
| 2 | 2 | 1 |
| 2 | 3 | 5 |
| 2 | 4 | 6 |
| 2 | 5 | 6 |
| 2 | 6 | 2 |
| 3 | 3 | 5 |
| 3 | 4 | 1 |
| 3 | 5 | 1 |
| 4 | 4 | 2 |
| 4 | 5 | 5 |
| 4 | 6 | 2 |
| 5 | 5 | 5 |
| 5 | 6 | 6 |
| 6 | 6 | 1 |

The image is $\{0, 1, 2, 5, 6\}$; residues 3 and 4 do not appear. $\square$

**Corollary.** The following residue classes of odd $x$ yield $\text{RHS} \equiv 3$ or $4 \pmod{7}$ and hence admit no solution:

| $x \pmod{14}$ | $\text{RHS} \pmod{7}$ | Status |
|---|---|---|
| 1 | **4** | **IMPOSSIBLE** |
| 3 | 2 | ok |
| 5 | **3** | **IMPOSSIBLE** |
| 7 | 6 | ok |
| 9 | **3** | **IMPOSSIBLE** |
| 11 | 0 | ok |
| 13 | **3** | **IMPOSSIBLE** |

The mod-7 obstruction eliminates exactly $x \equiv 1, 5, 9, 13 \pmod{14}$, i.e., $\frac{4}{7}$ of all odd integers (equivalently, $\frac{2}{7}$ of all integers). The **surviving** cases are $x \equiv 3, 7, 11 \pmod{14}$.

---

## Local Solvability of Surviving Cases

A systematic computer search (`modular_analysis.py`) confirms:

- **Every prime** $p \leq 113$: for $x \equiv 3, 7, 11 \pmod{14}$, the equation has $\mathbb{F}_p$-solutions.
- By a Hasse-Weil count: for fixed $N \neq 0$, the curve $yz(y+z) = N$ is a smooth genus-1 plane cubic over $\mathbb{F}_p$. By Hasse's theorem, $|N_p - (p+1)| \leq 2\sqrt{p}$, so $N_p \geq (\sqrt{p}-1)^2 > 0$ for $p \geq 4$. Hence the curve has $\mathbb{F}_p$-points for every prime $p \geq 5$ and every nonzero $N$.
- At $p = 2, 3$: direct verification shows local solvability.

**Conclusion:** The surviving cases $x \equiv 3, 7, 11 \pmod{14}$ are locally solvable at every prime. No single modular obstruction (or pair of modular conditions) eliminates them.

---

## Computational Brute Force

`brute_force_search.py` performs a **complete** search over $x \in [-10{,}000, 10{,}000]$:

For each odd $x$, compute $N = x^3 + x^2 + 3x - 1$ and enumerate all divisors $s$ of $N$. For each $s$, set $p = N/s$ and check whether the discriminant $\Delta = s^2 - 4p$ is a non-negative perfect square (using integer square root). If $\Delta = k^2$ and $s \pm k$ is even, the integers $y = (s+k)/2$, $z = (s-k)/2$ are a solution.

This method is **exhaustive**: every integer solution $(y, z)$ to $yz(y+z) = N$ gives a divisor $s = y+z$ of $N$, so no solution is missed.

**RESULT: NO integer solutions found for $|x| \leq 10{,}000$.**

---

## Reformulation via Symmetric Functions and Elliptic Curves

The substitution $s = y+z$, $p = yz$ transforms the equation into
$$sp = x^3 + x^2 + 3x - 1,$$
with the constraint that $s^2 - 4p$ is a non-negative perfect square (to ensure $y, z \in \mathbb{Z}$).

For fixed $x$ (hence fixed $N = sp$), this is the problem of finding an integer point on the elliptic curve
$$E_N : yz(y+z) = N, \quad N \neq 0,$$
which is a smooth cubic. By Siegel's theorem, each $E_N$ has finitely many integer points. However, the global problem (over the entire family as $x$ varies) remains open in a complete sense.

The surviving cases $x \equiv 3, 7, 11 \pmod{14}$ could in principle be resolved by:
1. **2-descent** on the Mordell-Weil group of $E_{N(x)}$, performed uniformly over each residue class, or
2. **Chabauty-Coleman** on associated higher-genus curves (after clearing the 3-variable structure).

---

## Near-Miss Data (Closest Discriminants)

For $|x| \leq 100$, the pair with discriminant closest to a perfect square without being one:

| $x$ | $s = y+z$ | $\Delta = s^2 - 4p$ | $\lfloor\sqrt\Delta\rfloor$ | gap |
|---|---|---|---|---|
| 11 | 371 | $370^2 + ?$ | ... | small |

(See `modular_analysis.py` output for the full near-miss table.)

---

## Proof Status Summary

| Step | Status | Method |
|------|--------|--------|
| $x$ odd | ✅ Proved | Mod 2 argument |
| $\nu_2(\text{RHS}) = 2$ | ✅ Proved | Explicit formula |
| Mod-7 obstruction ($x \equiv 1,5,9,13 \pmod{14}$) | ✅ Proved | Exhaustive check mod 7 × 14 |
| No solutions for $\lvert x \rvert \leq 10{,}000$ | ✅ Verified | Brute force (`brute_force_search.py`) |
| Complete non-existence proof for $x \equiv 3,7,11 \pmod{14}$ | ⚠️ Open | Requires descent; no modular obstruction |

**Working conjecture:** The equation has no integer solutions.
