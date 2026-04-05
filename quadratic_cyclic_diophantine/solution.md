# Solution to $x^2 \cdot y + y^2 \cdot z + z^2 \cdot x = 1$

## ⚠️ Correction: The equation has infinitely many integer solutions

The original claim that "all solutions satisfy |x|, |y|, |z| ≤ 1" is **false**.

A brute-force search reveals solutions with arbitrarily large coordinates. The solutions
form cyclic orbits of size 3 under the map (x, y, z) → (y, z, x):

| Orbit representative | Orbit |
|---|---|
| (0, 1, 1) | (0,1,1), (1,1,0), (1,0,1) |
| (0, -1, 1) | (0,-1,1), (-1,1,0), (1,0,-1) |
| (-1, 1, 1) | (-1,1,1), (1,1,-1), (1,-1,1) |
| (-2, 1, -1) | (-2,1,-1), (1,-1,-2), (-1,-2,1) |
| (-2, 3, -1) | (-2,3,-1), (3,-1,-2), (-1,-2,3) |
| (-3, 4, 7) | (-3,4,7), (4,7,-3), (7,-3,4) |
| (-44, 9, -19) | (-44,9,-19), (9,-19,-44), (-19,-44,9) |
| (-118, 169, 307) | (-118,169,307), (169,307,-118), (307,-118,169) |
| (-10, -53, 279) | (-10,-53,279), (-53,279,-10), (279,-10,-53) |
| ... | (infinitely many more) |

## Solutions with a zero coordinate

If any variable is zero, say z = 0, the equation reduces to x²y = 1, forcing
x = ±1 and y = 1/x² = 1. The six solutions (with all cyclic rotations of a zero) are:

- (0, 1, 1), (1, 1, 0), (1, 0, 1)
- (0, -1, 1), (-1, 1, 0), (1, 0, -1)

## Structure of nonzero solutions

The nonzero solutions appear to be governed by a Markov-like recurrence. Given a solution
(x, y, z) with all nonzero entries, one can sometimes produce another solution by fixing two
variables and solving the quadratic in the third (Vieta jumping). However, the divisibility
condition for the jump to yield an integer is not always satisfied, and the orbit structure
is more subtle than classical Markov triples.

Empirically (verified up to max(|x|,|y|,|z|) = 500):

- All nonzero solutions lie in cyclic orbits of size 3 under (x,y,z) → (y,z,x).
- There appear to be infinitely many such orbits.

## Status of the Lean proof

The `LeanProof.lean` file contains a proof attempt for the (false) claim that only 9
solutions exist. That proof cannot be completed because the theorem is false. The file
is kept for reference of the proof structure and tactics used.
