# TaxicabPell.lean — Formal Verification of the Taxicab/Pell Paper

A 989-line Lean 4 / Mathlib formalization of the main results from:

> Jamal Agbanwa, *"A Closed-Form Symbolic Generator and Infinite Families for Aⁿ + Bⁿ = Cⁿ + Dⁿ, n = 2, 3: Divisor Parametrization, Pell Equations, and Combinatorial Structure"*, May 2026.

Every theorem in the file is fully machine-checked — there are no `sorry`s and no unproved axioms.

---

## What is proved

### §2 — n = 2 divisor parametrization (`n2_divisor_param`)

For any non-zero rationals r₁, r₂ and any Δ, the four quantities

```
A = (Δ + r₁²) / (2r₁),   C = (Δ − r₁²) / (2r₁)
B = (Δ − r₂²) / (2r₂),   D = (Δ + r₂²) / (2r₂)
```

satisfy A² + B² = C² + D² identically. Proved by `field_simp; ring`.

---

### §3 — n = 3 divisor identity (`n3_divisor_identity`)

For rationals satisfying the radicand conditions t₁² = 12Δr₁ − 3r₁⁴ and t₂² = 12Δr₂ − 3r₂⁴, setting

```
C = (−3r₁² + t₁) / (6r₁),   B = (−3r₂² + t₂) / (6r₂)
```

gives (C + r₁)³ + B³ = C³ + (B + r₂)³. The proof shows each side differs from C³ + B³ by the same Δ.

---

### §4 — Pell reduction (`pell_poly_identity`, `pell_reduction_iff`)

The algebraic identity

```
4·[(C + 3s)³ + B³ − C³ − (B + 9s)³]
  = 9s·[(2C + 3s)² − 3(2B + 9s)² − 78s²]
```

is verified by `ring`. This gives an exact biconditional (Lemma 5.1):

> (C + 3s)³ + B³ = C³ + (B + 9s)³   **if and only if**   (2C + 3s)² − 3(2B + 9s)² = 78s²

The proof factors out `9s` and uses `mul_eq_zero` to split the two directions.

---

### §5 — The ring ℤ[√3] and the two Pell families

The formalization works inside Mathlib's `Zsqrtd (3 : ℤ)` (written ℤ[√3]).

Key constants defined:

| Name       | Value       | Norm |
|------------|-------------|------|
| `ε₀`       | 2 + √3      | 1    |
| `ε₁`       | 7 + 4√3     | 1    |
| `seed_I`   | 15 + 7√3    | 78   |
| `seed_II`  | 9 + √3      | 78   |

Two infinite families of solutions to x² − 3y² = 78 are defined as:

```
familyI_element  unit n  :=  seed_I  * unit^n
familyII_element unit n  :=  seed_II * unit^n
```

**`family_I_pell_eq` / `family_II_pell_eq`** (Propositions 5.2–5.3): For any unit (norm 1), every element of each family has norm 78, so its components (x, y) satisfy x² − 3y² = 78.

---

### §5 — Completeness (`completeness`, Theorem 5.4)

> Every positive integer solution (x, y) to x² − 3y² = 78 belongs to Family I or Family II for the fundamental unit ε₀ = 2 + √3.

The proof uses strong induction on y. The base step finds exactly two "reduced" solutions (those with x ≥ 2y) via `interval_cases`, giving (9, 1) = seed_II and (15, 7) = seed_I. The inductive step applies the descent map (x, y) ↦ (2x − 3y, 2y − x), which strictly decreases y while preserving the Pell equation, and then lifts the IH solution back up via the recurrence.

---

### §6 — Integrality, the main identity, and positivity (Theorem 6.1)

The four integer sequences are defined for each family, each m ∈ ℕ and n ∈ ℕ:

```
C_m(n) = 3^m · (xₙ − 3) / 2
B_m(n) = 3^m · (yₙ − 9) / 2
A_m(n) = C_m(n) + 3^(m+1)
D_m(n) = B_m(n) + 3^(m+2)
```

**`integrality_family_I`**: The components of every family element are odd (both xₙ and yₙ are ≡ 1 mod 2 for all n), so the factor of 2 in the denominators always divides exactly, making C_m, B_m, A_m, D_m genuine integers. Proved by induction using the helper `mul_preserves_odd_parity`, which shows that multiplying an odd-component element by a unit with u + v odd preserves both components being odd. The parity of u + v follows from the Pell condition u² − 3v² = 1 (`unit_sum_odd`).

**`main_identity_family_I` / `main_identity_family_II`** (core of Theorem 6.1):

> A_m(n)³ + B_m(n)³ = C_m(n)³ + D_m(n)³

Proved by reducing to the Pell condition x² − 3y² = 78 via `pell_reduction_iff`. The scaled Pell identity `(sm·xₙ)² − 3·(sm·yₙ)² = 78·sm²` is derived from the component Pell equation, where sm = 3^m.

**`positivity_family_I`**: For any positive unit and n ≥ 1, all four quantities A_m, B_m, C_m, D_m are strictly positive. Proved by showing xₙ > 3 and yₙ > 9 for all n ≥ 1 by induction, then using the integrality divisibility to extract the positivity of the integer quotients.

**`distinctness_family_I`**: A_m(n) ≠ C_m(n) always, since A = C + 3^(m+1) and 3^(m+1) > 0. Also proved: the solution is not a "swap" (A ≠ D or B ≠ C), ruling out the trivial case A³ + B³ = B³ + A³.

---

### §6 — Hardy–Ramanujan (`hardy_ramanujan`, Corollary 6.3)

> 12³ + 1³ = 9³ + 10³ = 1729

Verified by `norm_num`. The values are also confirmed to come from the generator: (A, B, C, D) = (12, 1, 9, 10) equals (A_m_II ε₀ 0 1, B_m_II ε₀ 0 1, C_m_II ε₀ 0 1, D_m_II ε₀ 0 1), checked by `native_decide`.

---

### §7 — Three-term recurrences (`recurrence_C_family_I`, `recurrence_B_family_I`, Theorem 7.1)

The sequences C_m and B_m satisfy explicit three-term recurrences driven by the underlying Pell recurrence x_{n+2} = 2u·x_{n+1} − xₙ:

```
C_m(n+2) = 2u · C_m(n+1) − C_m(n) + 3^(m+1) · (u − 1)
B_m(n+2) = 2u · B_m(n+1) − B_m(n) + 3^(m+2) · (u − 1)
```

and (by linearity) A_m and D_m satisfy:

```
A_m(n+2) = 2u · A_m(n+1) − A_m(n) − 3^(m+1) · (u − 1)
D_m(n+2) = 2u · D_m(n+1) − D_m(n) − 3^(m+2) · (u − 1)
```

The proofs proceed by: (1) expanding one Zsqrtd multiplication step via the component formulas for ℤ[√3]; (2) deriving the two-step recurrence for the .re and .im components using `ring_nf` together with `nlinarith` and the identity `1 − (u² − 3v²) = 0`; (3) lifting from the component recurrence to the C/B recurrence by cancelling the factor of 2 via `omega`.

---

### §7 — Monotonicity and exponential growth (Theorem 7.2)

**`growth_monotone_re_I`** (Theorem 7.2(i)): The .re-component xₙ is strictly increasing:

> xₙ < xₙ₊₁  for all n ≥ 0.

Proved by showing that xₙ₊₁ = xₙ·u + 3·yₙ·v ≥ 2·xₙ + 3·yₙ·v > xₙ, using positivity of all components and u ≥ 2.

**`growth_exponential`** (Theorem 7.2(ii)): For n ≥ 1, the ratio is bounded below:

> (2u − 1) · xₙ < xₙ₊₁

Since u ≥ 2 implies 2u − 1 ≥ 3, the sequence grows at least geometrically with ratio 3, establishing exponential growth. The proof derives the two-step recurrence x_{k+2} = 2u·x_{k+1} − xₖ (same `ring_nf` / `nlinarith` pattern as the recurrence theorems), then uses strict monotonicity to replace xₖ with < x_{k+1}, giving x_{k+2} > (2u−1)·x_{k+1}.

---

### §8 — Numerical table verifications

Specific entries from Tables 1 and 2 of the paper are verified by `native_decide` and `norm_num`:

| Family | Unit | n | (A, B, C, D)           | A³ + B³      |
|--------|------|---|------------------------|--------------|
| II     | ε₀   | 1 | (12, 1, 9, 10)         | 1729         |
| II     | ε₀   | 2 | (39, 17, 36, 26)       | 64 232       |
| II     | ε₀   | 3 | (141, 76, 138, 85)     | 3 242 197    |
| II     | ε₀   | 4 | (522, 296, 519, 305)   | 168 170 984  |
| I      | ε₁   | 1 | (96, 50, 93, 59)       | 1 009 736    |
| I      | ε₁   | 2 | (1317, 755, 1314, 764) | 2 714 690 888|

---

### §9 — Supporting lemmas

Pascal expansion identities for (C + r)² − C² and (C + r)³ − C³, and a real-analysis bound showing that the radicand 12Δr − 3r⁴ is non-negative whenever r³ ≤ 4Δ, supporting the existence of t₁ and t₂ in the n = 3 parametrization.

---

## Proof techniques used

| Technique | Where |
|-----------|-------|
| `ring` / `ring_nf` | Polynomial identities throughout |
| `norm_num` | Concrete integer arithmetic |
| `native_decide` | Verified computation of specific family values |
| `nlinarith` | Nonlinear integer bounds (positivity, Pell algebra) |
| `omega` | Linear integer arithmetic |
| `linarith` | Linear consequences |
| `interval_cases` | Exhaustive case split for the reduced solution classification |
| Strong induction (`Nat.strong_induction_on`) | Completeness (descent proof) |
| Structural induction | Integrality (parity), positivity, monotonicity |
| `linear_combination` | Exact polynomial derivations from hypotheses |
| Zsqrtd norm multiplicativity | Propagating the Pell equation through the orbit |

## Files

- `TaxicabPell.lean` — the complete formalization (989 lines, `namespace TaxicabPell`)
- `lean-toolchain` — pins `leanprover/lean4 v4.21.0`
- `lakefile.toml` — lake build configuration with `import Mathlib`
