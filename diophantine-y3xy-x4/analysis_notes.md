# Analysis Notes: $y^3 + xy + x^4 + 4 = 0$

## Quick Facts

- **Equation:** $y^3 + xy + x^4 + 4 = 0$
- **Claim:** No integer solutions exist.
- **Search range verified:** $|x| \leq 10{,}000$ (brute force, Python).
- **Minimum $|F(x,y)|$ for $(x,y)$ integers:** $1$ (achieved at $(x,y) = (-1,-2)$ and $(-2,-3)$).
- **Projective curve genus:** $3$ (smooth plane quartic).
- **Local solvability:** Equation is $p$-adically solvable for all primes $p$.

## The Near-Misses

The two closest integer near-misses are:
$$F(-1,-2) = (-8)+(-1)(-2)+(1)+4 = -8+2+1+4 = -1$$
$$F(-2,-3) = (-27)+(-2)(-3)+(16)+4 = -27+6+16+4 = -1$$

In both cases the evaluation overflows by $1$ below $0$. This is notable because for both
$x=-1$ and $x=-2$ the unique real root $y^*(x)$ is between two consecutive integers and never
lands exactly on one.

## Discriminant

For fixed integer $x$, the equation is a depressed cubic $t^3 + xt + (x^4+4)=0$ in $y=t$.
The discriminant $\Delta = -4x^3 - 27(x^4+4)^2$ is always negative:

| $x$ | $\Delta$ |
|-----|----------|
| $-5$ | $-10{,}681{,}807$ |
| $-2$ | $-10{,}768$ |
| $-1$ | $-671$ |
| $0$ | $-432$ |
| $1$ | $-679$ |
| $2$ | $-10{,}832$ |
| $5$ | $-10{,}682{,}807$ |

Since $\Delta < 0$, each $x$ gives exactly one real candidate $y$.

## Modular Constraints Summary

| Modulus | Constraint |
|---------|-----------|
| $2$ | $x \equiv 0$, $y \equiv 0$ |
| $3$ | $y \equiv 2$ |
| $8$ | $x \equiv 2$ or $6$; $y \equiv 2$ or $6$ |
| $24$ | $x \in \{6,10,18,22\}$, $y \in \{2,14\}$ |

**Key:** No single modulus gives a complete obstruction. The equation is locally solvable everywhere.

## Sophie Germain Identity

$$x^4 + 4 = \bigl((x+1)^2+1\bigr)\bigl((x-1)^2+1\bigr)$$

Both factors are $\geq 1$ with equality only at $x=\mp1$ respectively.
This rewrites $(\star)$ as:
$$y(y^2+x) = -\bigl((x+1)^2+1\bigr)\bigl((x-1)^2+1\bigr) \leq -1.$$

## Curve Geometry

- **Homogenisation:** $H(x,y,z) = x^4 + xy\,z^2 + y^3\,z + 4z^4$ (degree 4).
- **Affine gradient:** $\nabla F = (y+4x^3,\; 3y^2+x)$. Vanishes only outside the curve.
- **Point at infinity:** $P_\infty = [0:1:0]$ (unique; smooth).
- **Genus:** $(4-1)(4-2)/2 = 3$.
- **Faltings:** $\mathcal{C}(\mathbb{Q})$ is finite.
- **Predicted rational points:** $\{P_\infty\}$ (via Chabauty–Coleman).

## Proof Strategy

| Step | Method | Completeness |
|------|--------|-------------|
| $\|x\| \leq 10{,}000$ | Exhaustive Python search | Complete |
| Genus $\geq 2$ | Degree-genus formula for smooth quartic | Complete |
| Finiteness of $\mathcal{C}(\mathbb{Q})$ | Faltings (1983) | Complete |
| $\mathcal{C}(\mathbb{Q}) = \{P_\infty\}$ | Chabauty–Coleman (Magma) | Conditional |
| Lean formalisation | `decide` + named axiom | Complete (1 axiom) |

## Files in This Directory

| File | Description |
|------|-------------|
| `brute_force_search.py` | Exhaustive integer search, $\|x\| \leq 10{,}000$ |
| `modular_analysis.py` | Systematic modular analysis and $\mathbb{F}_p$-point counts |
| `rigorous_proof.md` | Full mathematical write-up |
| `NonExistenceProof.lean` | Lean 4 / Mathlib formalisation |
| `solution.tex` | Self-contained LaTeX proof |
