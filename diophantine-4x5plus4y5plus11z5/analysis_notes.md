# Analysis Notes: $4x^5 + 4y^5 + 11z^5 = 0$

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to

$$4x^5 + 4y^5 + 11z^5 = 0$$

or prove the non-existence of non-trivial solutions.

---

## Main Result

The equation has **infinitely many integer solutions**, given by the explicit parametric family

$$\boxed{(x, y, z) = (t,\; -t,\; 0), \qquad t \in \mathbb{Z}.}$$

**Verification:**
$$4t^5 + 4(-t)^5 + 11 \cdot 0^5 = 4t^5 - 4t^5 + 0 = 0. \checkmark$$

The map $t \mapsto (t, -t, 0)$ is injective (the first component is the identity), so these are infinitely many distinct solutions.

---

## Derivation

### Step 1 — Set $z = 0$

With $z = 0$, the equation becomes:
$$4x^5 + 4y^5 = 0 \implies x^5 = -y^5 \implies x = -y.$$

The last implication holds because $t \mapsto t^5$ is **strictly increasing** over $\mathbb{Z}$ (since $t^5 - s^5 = (t-s)(t^4 + t^3 s + t^2 s^2 + ts^3 + s^4)$ and the second factor is positive for $(t,s) \ne (0,0)$, so $t^5 > s^5 \iff t > s$).  Hence $x^5 = -y^5$ implies $x = -y$.

### Step 2 — Parametric family

The solution $(1, -1, 0)$ is a **seed**. Since the equation is homogeneous of degree 5:
$$4(tx)^5 + 4(ty)^5 + 11(tz)^5 = t^5\bigl(4x^5 + 4y^5 + 11z^5\bigr) = t^5 \cdot 0 = 0,$$
scaling any solution $(x, y, z)$ by any integer $t$ gives another solution $(tx, ty, tz)$.

Scaling the seed $(1, -1, 0)$ by $t$ gives $(t, -t, 0)$. Hence the full primary family is:
$$(x, y, z) = (t, -t, 0), \qquad t \in \mathbb{Z}.$$

### Step 3 — Infinitude

The map $\mathbb{N} \to \mathbb{Z}^3$ given by $n \mapsto (n, -n, 0)$ is injective (the first components are distinct for distinct $n$), so the solution set is infinite.

---

## Degree-5 Homogeneity

The equation $4x^5 + 4y^5 + 11z^5 = 0$ is **homogeneous of degree 5** with uniform weights $\mathrm{wt}(x) = \mathrm{wt}(y) = \mathrm{wt}(z) = 1$.  This is the simplest possible homogeneity structure: every monomial has the same degree 5.

Contrast with $x^5 + y^4 + 3z^2 = 0$ (weighted degree 20 with weights $(4,5,10)$) or $x^5 + 2y^3 + z^3 = 0$ (weighted degree 15 with weights $(3,5,5)$): the present equation has pure degree-5 homogeneity, which means the seed solution lies on a **projective line** $(t:−t:0)$ in $\mathbb{P}^2$ rather than on a more exotic rational curve.

---

## Modular Analysis

### Mod 2

$$4x^5 + 4y^5 + 11z^5 \equiv z^5 \equiv z \pmod{2}.$$
So $z$ must be even. The primary family has $z = 0$ (even). ✓

### Mod 4

With $z = 2w$: $11z^5 = 11 \cdot 32w^5 \equiv 0 \pmod{4}$. No additional constraint.

### Mod 11

$$4x^5 + 4y^5 \equiv 0 \pmod{11} \implies x^5 + y^5 \equiv 0 \pmod{11}.$$

The fifth-power residues modulo 11 are $\{0, 1, -1\}$ (i.e., $\{0, 1, 10\}$), since $a^{10} \equiv 1 \pmod{11}$ for $\gcd(a,11)=1$ by Fermat's little theorem, so $a^5 \equiv \pm 1$.

Hence $x^5 + y^5 \equiv 0 \pmod{11}$ holds in two cases:
1. $11 \mid x$ and $11 \mid y$ (both zero mod 11), or
2. $x^5 \equiv 1$ and $y^5 \equiv -1$ (mod 11), i.e., $x \not\equiv 0$ and $y \not\equiv 0$.

The primary family: $t^5 + (-t)^5 = t^5 - t^5 = 0 \equiv 0 \pmod{11}$. ✓ (Case 2 when $11 \nmid t$; Case 1 when $11 \mid t$.)

### Mod $p$ for small primes

The equation has solutions modulo every prime $p$ (e.g., $(1, -1, 0)$ works for all $p$), so there is **no modular obstruction**.

---

## Solutions with $z \neq 0$

The existence of solutions with $z \neq 0$ is an open question at the level of complete classification; however:

- **Mod 2 constraint:** $z$ must be even for any solution.
- **Reduction:** With $z = 2w$, the equation becomes $x^5 + y^5 = -88w^5$ (dividing by 4).
- For $w = 1$: need $x^5 + y^5 = -88$.  A brute-force check over $|x|, |y| \leq 10$ finds no integer solution.
- For $w = 2$: need $x^5 + y^5 = -88 \cdot 32 = -2816$.  No solution with $|x|, |y| \leq 10$.
- More generally, the projective curve $u^5 + v^5 = c$ over $\mathbb{Q}$ (for any fixed rational $c$) has genus 6; by Faltings' theorem its rational point set is finite.

**Brute-force search** over $|x|, |y| \leq 50$ (with $z$ computed from $(x,y)$) finds **no solutions with $z \neq 0$**.

---

## Explicit Solutions (small $|t|$)

| $(x, y, z)$ | $4x^5 + 4y^5 + 11z^5$ |
|---|---|
| $(0, 0, 0)$ | $0$ |
| $(1, -1, 0)$ | $4 - 4 + 0 = 0$ |
| $(-1, 1, 0)$ | $-4 + 4 + 0 = 0$ |
| $(2, -2, 0)$ | $128 - 128 + 0 = 0$ |
| $(-2, 2, 0)$ | $-128 + 128 + 0 = 0$ |
| $(3, -3, 0)$ | $972 - 972 + 0 = 0$ |
| $(5, -5, 0)$ | $12500 - 12500 + 0 = 0$ |
| $(10, -10, 0)$ | $400000 - 400000 + 0 = 0$ |

---

## Proof Status Summary

| Component | Status |
|-----------|--------|
| Seed solution $(1,-1,0)$ | ✓ Direct substitution |
| Degree-5 homogeneity | ✓ Algebraic identity (`ring`) |
| Primary family $(t,-t,0)$ verified | ✓ `ring` identity |
| Infinitely many distinct solutions | ✓ Injectivity of $n \mapsto n$ on $\mathbb{N}$ |
| No solutions with $z \neq 0$ (search) | ✓ Exhaustive check $|x|,|y| \leq 50$ |
| No solutions with $z \neq 0$ (proof) | Open (Faltings/Chabauty–Coleman on the quintic $u^5+v^5 = c$) |
| Lean 4 formalisation (0 sorry) | ✓ **Complete** — see `InfinitelyManySolutions.lean` |

---

## Lean 4 Formalisation Summary

The file `InfinitelyManySolutions.lean` formally proves:

| Lean name | Statement | Method |
|-----------|-----------|--------|
| `seed_solution` | $(1,-1,0)$ is a solution | `norm_num` |
| `homogeneity` | scaling any solution by $t$ gives a solution | `linear_combination t^5 * h` |
| `family` | $(t,-t,0)$ is a solution for all $t:\mathbb{Z}$ | `ring` |
| `natMap_mem` | $(n,-n,0)$ is a solution for all $n:\mathbb{N}$ | `ring` (via `push_cast`) |
| `natMap_injective` | $n \mapsto (n,-n,0)$ is injective | `exact_mod_cast h.1` |
| `solutions_infinite` | the solution set is infinite | `Set.infinite_range_of_injective` |

**Sorry count: 0. Axiom count: 0.**
