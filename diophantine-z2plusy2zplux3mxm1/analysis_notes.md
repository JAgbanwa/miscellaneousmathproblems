# Diophantine Equation: z² + y²z + x³ − x − 1 = 0

## Problem Statement

Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to:
$$z^2 + y^2 z + x^3 - x - 1 = 0$$

## Main Result

**The equation has infinitely many integer solutions.**

## Key Structural Results

### Factorization Characterization
The equation is equivalent to:
$$z(z + y^2) = 1 + x - x^3$$

So $(x, y, z)$ is a solution iff $z$ and $z + y^2$ form an ordered factor pair of $1 + x - x^3$ whose difference is a perfect square.

### Necessary Conditions (proved by modular arithmetic)
- **Mod 2**: Since $x^3 - x \equiv 0 \pmod{2}$ always, the equation forces $y \equiv 0 \pmod{2}$.
- **Mod 3**: Since $x^3 - x \equiv 0 \pmod{3}$ always, the equation forces $y \equiv 0 \pmod{3}$.
- **Combined**: Every solution satisfies $6 \mid y$.

### Two Branches

**Branch y = 0**: Reduces to the elliptic curve
$$z^2 = -x^3 + x + 1 \quad (\text{i.e., } z^2 = t^3 - t + 1 \text{ with } t = -x)$$
By Siegel's theorem, this has finitely many integer points. Complete list:

| x | y | z |
|---|---|---|
| -56 | 0 | ±419 |
| -5 | 0 | ±11 |
| -3 | 0 | ±5 |
| -1 | 0 | ±1 |
| 0 | 0 | ±1 |
| 1 | 0 | ±1 |

**Branch y ≠ 0**: Solutions exist for infinitely many values of y (all multiples of 6). Selection:

| x | y | z |
|---|---|---|
| -380 | ±210 | -45311, 1211 |
| -267 | ±168 | -28883, 659 |
| -63 | ±24 | -865, 289 |
| -43 | ±24 | -691, 115 |
| -20 | ±18 | -347, 23 |
| -16 | ±24 | -583, 7 |
| 17 | ±12 | -89, -55 |
| 43 | ±24 | -347, -229 |
| 83 | ±228 | -51973, -11 |
| 141 | ±60 | -2461, -1139 |
| 240 | ±288 | -82777, -167 |

## Files

- `solution.tex` — Full rigorous LaTeX proof with all theorems and proofs
- `brute_force_search.py` — Exhaustive integer search script (run with Python 3)
- `analysis_notes.md` — This file

## Running the Search

```bash
python3 brute_force_search.py              # default bounds |x|<=200, |y|<=600
python3 brute_force_search.py 500 1200     # custom bounds
```
