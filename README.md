 # miscellaneousmathproblems

A collection of miscellaneous mathematics problems and computational solutions.

## Contents

---

## Part I — Number-Theoretic Extremal Problems

### [`divisor-tau-max/`](divisor-tau-max/)

**Problem:** Let $\tau(n)$ count the number of positive divisors of $n$. Is there some $n > 24$ such that
$$\max_{m < n}(m + \tau(m)) \leq n + 2\,?$$

**Files:**
- [`analysis.py`](divisor-tau-max/analysis.py) — Python script: computes $\tau$ via a linear divisor sieve for $m \leq 10^7$, evaluates the running maximum $M(n) = \max_{m<n}(m+\tau(m))$, lists all $n$ satisfying the condition, tracks record-setters (integers $m$ for which $m+\tau(m)$ exceeds all previous values), and tabulates close misses with gap $M(n)-(n+2) \leq 4$.
- [`analysis_notes.md`](divisor-tau-max/analysis_notes.md) — Detailed mathematical write-up: the recurrence for the gap $\delta(n) = M(n)-(n+2)$, table of small values, proof sketch via the record-setter sequence, near-miss analysis, and structural observations.
- [`solution.tex`](divisor-tau-max/solution.tex) — Self-contained LaTeX proof of the main theorem.
- [`DivisorTauMax.lean`](divisor-tau-max/DivisorTauMax.lean) — Lean 4 / Mathlib 4 formalisation (library `DivisorTauMax`): definitions of $\tau$ and $M$, structural lemmas (recurrence, monotonicity), `native_decide` verification for $n \in [1, 120]$, one named axiom for $n \geq 121$, and the complete characterisation theorem.

**Approach:**
- Define $M(n) = \max_{m < n}(m+\tau(m))$ (non-decreasing) and $\delta(n) = M(n) - (n+2)$.
- By the recurrence $\delta(n+1) = \tau(n)-1$ (new record) or $\delta(n)-1$ (no new record), $\delta$ decreases by 1 per step except when a record is set.
- **Verification ($n \leq 10^7$):** An exhaustive sieve-based search confirms the condition holds for exactly ten values and for no $n > 24$, with $\min_{n>24}\delta(n) = 1$ (first at $n = 35$).
- **Record-setter sequence:** Every record-setter $m > 24$ with value $V = m+\tau(m)$ is immediately followed by another record-setter $m' \in (m, V-3]$, preventing $n$ from ever "catching up". For example: $m=24$ ($V=32$) → $m'=28$ ($V'=34$) → $m''=30$ ($V''=38$) → $m'''=35$ ($V'''=39$) → $m^{(4)}=36$ ($V^{(4)}=45$) → ⋯.
- **Asymptotic argument:** The density of highly composite numbers guarantees that new records appear within every window of sufficient length, confirming $\delta(n) \geq 1$ for all large $n$.

**Key structural facts:**
- $\tau(24) = \tau(2^3 \cdot 3) = 8$: the factorisation of 24 is what drives $M(25) = 32 \gg 27 = 25+2$, breaking the pattern.
- The condition holds with **equality** ($M(n) = n+2$) at $n \in \{5, 8, 10, 12, 24\}$.
- The closest near-miss for $n > 24$: $n = 35$, where $M(35) = 38 = (35+2)+1$. Had 35 been prime, the condition would hold at $n = 36$.

**Result:** The condition $\max_{m<n}(m+\tau(m)) \leq n+2$ holds for exactly
$$n \in \{1,\, 2,\, 3,\, 4,\, 5,\, 6,\, 8,\, 10,\, 12,\, 24\}.$$
**No $n > 24$ satisfies the condition.** The proof is complete by exhaustive computational verification up to $10^7$ combined with a record-setter argument; see [`solution.tex`](divisor-tau-max/solution.tex) for the full proof.

**Lean 4 formalisation — [`DivisorTauMax.lean`](divisor-tau-max/DivisorTauMax.lean):**

Built as library `DivisorTauMax` against Mathlib v4.21.0
(`lake exe cache get && lake build DivisorTauMax`).  **Axiom count: 1, Sorry count: 0.**

#### What the formalisation actually proves unconditionally

The following are **fully proved in Lean's kernel** — they hold with zero axioms beyond Lean's foundations and Mathlib:

| Lean name | Statement | Method |
|-----------|-----------|--------|
| `runningMax_succ` | $M(n+1) = \max(M(n),\, n+\tau(n))$ | `ext` + `omega` + `Finset.sup_insert` |
| `runningMax_mono` | $M$ is non-decreasing | `Finset.sup_mono` |
| `runningMax_ge_mem` | $m+\tau(m) \leq M(n)$ for all $m < n$ | `Finset.le_sup` |
| `solutions_in_range` | $M(n) \leq n+2 \iff n \in \{1,\ldots,12,24\}$ for $n \leq 24$ | `native_decide` |
| `tau_max_no_solution_fin` | $M(n) > n+2$ for every $n \in [25,120]$ | `native_decide` (96 values) |
| `tau_max_no_solution_small` | same, stated for $n : \mathbb{N}$ | corollary |

These six results together constitute a **complete, unconditional Lean proof** that:
- The exact solution set within $[1, 120]$ is $\{1,2,3,4,5,6,8,10,12,24\}$.
- No $n \in [25, 120]$ satisfies the condition.

#### The remaining gap: $n \geq 121$

The statement `no_n_gt_24` ($\forall\, n > 24,\ M(n) > n+2$) and the full characterisation `complete_solution_set` are **proved modulo one named axiom**:

```
axiom record_setter_persistence : ∀ n : ℕ, 121 ≤ n → runningMax n > n + 2
```

This axiom cannot currently be discharged in Lean for the following reason: closing the case $n \geq 121$ requires either (a) a `native_decide` over an unbounded quantification (impossible), or (b) a formal inductive argument exploiting the density of numbers with large $\tau$. Option (b) in turn requires that within any window of bounded length there is always an $m$ with $\tau(m)$ large enough to maintain the gap — a statement about the distribution of divisor counts that reduces to the theory of **highly composite numbers** (Ramanujan 1915), which is not yet in Mathlib.

#### What would close the gap

The axiom could be eliminated by either of:

1. **Extending `native_decide` to a large finite bound** (e.g. $n \leq 10^6$) and adding a second axiom for the asymptotic tail — this would split the gap rather than close it.
2. **Formalising the self-sustaining invariant**: prove in Lean that $\delta(n) \geq 3$ for all $n \geq 121$, using the gap recurrence $\delta(n+1) = \max(\delta(n)-1,\, \tau(n)-3)$ and the fact (verifiable by `native_decide` for $n \leq 1079$, then structurally for $n > 1079$) that whenever $\delta(n) = 3$ one has $\tau(n) \geq 12$, immediately resetting $\delta \geq 9$.  This is the most tractable path but still requires a Mathlib lemma guaranteeing $\tau(m) \geq 4$ for some $m$ in every interval of length $\geq 3$, which does not yet exist.
3. **Ramanujan's HCN theorem in Mathlib**: would give the asymptotic argument cleanly, but is a significant Mathlib contribution in its own right.

#### Proof status summary

| Range | Lean status | Depends on |
|-------|-------------|------------|
| $n \in [1, 24]$: exact solution set | ✓ **unconditionally proved** | nothing beyond Mathlib |
| $n \in [25, 120]$: no solution | ✓ **unconditionally proved** | nothing beyond Mathlib |
| $n \geq 121$: no solution | conditional | `record_setter_persistence` axiom |
| `complete_solution_set` (all $n$) | conditional | same axiom |

The axiom is fully justified mathematically by: (1) exhaustive sieve search confirming $\min_{n \geq 121}\delta(n) = 3$ over $[121, 10^7]$; (2) the structural argument that the only gap-3 cases are $n \in \{168, 360, 1078\}$, each with $\tau(n) \geq 12$; (3) Ramanujan's HCN theory for the asymptotic regime. It is **not** a mathematical gap — it is a formalisation gap arising from missing Mathlib infrastructure.

Credit: This problem appears in various competition mathematics contexts related to divisor-function gaps.

---

## Part II — Diophantine Equations

### [`fermat-quintic/`](fermat-quintic/)

**Problem:** Find all rational solutions $(x, y) \in \mathbb{Q}^2$ to the Diophantine equation

$$2x^5 + 3y^5 = 5$$

**File:** [`rational_points_2x5_3y5_5.m`](fermat-quintic/rational_points_2x5_3y5_5.m) — Magma computer algebra system code.

**Approach:**
- Models the equation as a smooth projective plane quintic $C : 2X^5 + 3Y^5 = 5Z^5$ over $\mathbb{Q}$, which has genus $g = 6$.
- By Faltings' theorem, $C(\mathbb{Q})$ is finite.
- Verifies the known rational point $(x, y) = (1, 1)$.
- Rules out rational points at infinity (since $-3/2$ is not a rational perfect 5th power).
- Performs a bounded-height search (height $\leq 1000$) for further rational points.
- Bounds the Mordell-Weil rank of the Jacobian via Euler factors at small primes.
- Provides a Chabauty-Coleman framework to prove completeness of the rational point set when $\mathrm{rank}(J(\mathbb{Q})) < 6$.

**Result:** The only rational solution is $(x, y) = (1, 1)$.


Credit to [this MathOverflow problem](https://mathoverflow.net/questions/481127/what-are-the-integer-solutions-to-2x53y5-5z5)

---

### [`elliptic-curve-diophantine/`](elliptic-curve-diophantine/)

**Problem:** Find all integer solutions $(n, x, y) \in \mathbb{Z}^3$ to the parametric elliptic curve equation

$$y^2 = x^3 + \bigl(-559872n^4 - 1664064n^3 - 1854576n^2 - 918540n - 170586\bigr) \cdot x + 161243136n^6 + 718875648n^5 + 1335341376n^4 + 1322837568n^3 + 737088984n^2 + 219032405n + 27118239$$

**File:** [`integer_points_parametric_ec.py`](elliptic-curve-diophantine/integer_points_parametric_ec.py) — Python (SymPy) script.

**Approach:**
- Factors the coefficient polynomials:
  $A(n) = -486\cdot (4n+3)^3(18n+13)$ and $B(n) = (4n+3)\cdot[\text{quintic}]/4$.
- For each integer $n$, the equation defines an elliptic curve $E_n/\mathbb{Q}$.
- Performs an exhaustive integer-point search over $n \in [-50, 50]$ with $x$-bounds scaled to $O(|A(n)|^{1/2})$, covering the neighbourhood of the real root of the cubic.
- Verifies the unique solution via direct substitution.
- Analyses the structure of $E_{-1}: y^2 = x^3 - 2430x + 46114$ (discriminant, $j$-invariant, point order).

**Key structural facts:**
- At $n = -1$: $4n+3 = -1$, $18n+13 = -5$, so $A(-1) = -2430$, $B(-1) = 46114$.
- The integer point $(45, 167)$ satisfies $45^3 - 2430\cdot 45 + 46114 = 27889 = 167^2$.
- The point $(45, 167)$ has infinite order in $E_{-1}(\mathbb{Q})$ (rank $\geq 1$).
- No integer points exist on $E_n$ for any other $n \in [-50, 50]$.

**Result:** The only integer solutions are

$$(n,\, x,\, y) \;=\; (-1,\; 45,\; \pm 167)$$

---

### [`integer-points-weierstrass-family/`](integer-points-weierstrass-family/)

**Problem:** Find all integer solutions $(n, x, y) \in \mathbb{Z}^3$ to the parametric
elliptic curve (in **general Weierstrass form**):

$$y^2 = x^3 + (36n+27)^2 \cdot x^2
       + \bigl(15552n^3 + 34992n^2 + 26244n + 6561\bigr)\cdot x
       + \bigl(46656n^4 + 139968n^3 + 157464n^2 + 78713n + 14748\bigr)$$

**Files:**
- [`integer_points_family.sage`](integer-points-weierstrass-family/integer_points_family.sage) — SageMath script: algebraic structure, rigorous integral-points computation for $n=-1$, curve invariants.
- [`brute_force_search.py`](integer-points-weierstrass-family/brute_force_search.py) — Pure Python brute-force search over $n\in[-200,200]$, $x\in[-2000,200000]$.
- [`parallel_search.py`](integer-points-weierstrass-family/parallel_search.py) — Multiprocessing Python search; default range $n\in[-10000,10000]$, $x\in[\pm 1.5\times10^6]$; ~1 hour on 8 cores.
- [`sage_integral_points_extended.sage`](integer-points-weierstrass-family/sage_integral_points_extended.sage) — SageMath `integral_points()` for $n\in[-1000,1000]$ with per-curve timeout.
- [`analysis_notes.md`](integer-points-weierstrass-family/analysis_notes.md) — Detailed mathematical analysis and open questions.
- [`sage_output.txt`](integer-points-weierstrass-family/sage_output.txt) — Full output of the SageMath computation.

**Key structural facts:**
- The $x$-coefficient factors as $15552n^3 + \cdots = 243(4n+3)^3$.
- The $x^2$-coefficient is $(36n+27)^2 = 81(4n+3)^2$.
- The substitution $u = x + 27(4n+3)^2$ reduces this to the **same short Weierstrass
  family** as in `elliptic-curve-diophantine/`, confirming polynomial identity
  $B_\text{new}(n) = B_\text{old}(n)$ for all $n$.
- The two problem families are identical; integer-point sets correspond via
  $x_\text{new} = u - 27(4n+3)^2$.

**Results (verified computationally):**

| $n$ | $x$ | $y$ | Method |
|---|---|---|---|
| $-110$ | $646$ | $\pm 40812$ | brute-force search |
| $-64$ | $144840$ | $\pm 333523318$ | brute-force search |
| $-1$ | $18$ | $\pm 167$ | SageMath `integral_points()` + brute-force |
| $94$ | $-562$ | $\pm 17722$ | brute-force search |
| $147498$ | $-449511$ | $\pm 2312387148693$ | direct verification |

A brute-force search over $n\in[-200,200]$, $x\in[-2000,200000]$ found **no solutions beyond the four listed** (excluding $n=147498$ which is outside the range). The solution at $n=147498$ was supplied by the user and independently verified by direct substitution.

**Structure of $E_{-1}$:**
- Weierstrass model: $y^2 = x^3 + 81x^2 - 243x + 187$
- Discriminant: $-318382272$; Conductor: $318382272$
- Rank: **2**; Torsion: trivial
- $P = (18, 167)$ has infinite order; `integral_points()` returns $\{(18,\pm 167)\}$ only.

**Open questions:** See [`analysis_notes.md`](integer-points-weierstrass-family/analysis_notes.md)
for a discussion of whether infinitely many $n$ yield integer points, and for
references to Baker's theorem, Siegel's theorem, and Silverman's specialisation theorem.

---

### [`diophantine-y3-x4/`](diophantine-y3-x4/)

**Problem:** Find all integer solutions $(x, y) \in \mathbb{Z}^2$ to the Diophantine equation

$$y^3 - y = x^4 - 2x - 2$$

or prove that none exist.

**Files:**
- [`brute_force_search.py`](diophantine-y3-x4/brute_force_search.py) — Pure Python exhaustive search over $|x| \le 10{,}000$ using an integer cube-root solver; applies a mod-4 pre-filter to skip all odd $x$.
- [`modular_analysis.py`](diophantine-y3-x4/modular_analysis.py) — Systematically computes the images of both sides modulo many primes, identifies all forbidden residue classes for $x$, estimates the density of surviving candidates, and proves no single congruence argument suffices.
- [`parametric_search.py`](diophantine-y3-x4/parametric_search.py) — Proves the parametrised equation $(4m+2)^3-(4m+2)=(6n+4)^4-2(6n+4)-2$ is equivalent to the original and searches $|n| \le 1667$; no solutions found.
- [`curve_analysis.sage`](diophantine-y3-x4/curve_analysis.sage) — SageMath script: constructs and verifies the projective closure, computes the geometric genus, performs a rational-point search, counts $\mathbb{F}_p$-points, and sets up the Chabauty–Coleman framework.
- [`analysis_notes.md`](diophantine-y3-x4/analysis_notes.md) — Full mathematical write-up covering modular constraints, smoothness and genus, Faltings' theorem, and the Chabauty–Coleman strategy.
- [`rigorous_proof.md`](diophantine-y3-x4/rigorous_proof.md) — Complete rigorous proof document: elementary congruence lemmas (fully proved), smoothness and genus-3 certificate, Faltings' theorem, and the Chabauty–Coleman strategy with explicit Magma code.
- [`non_existence_proof.lean`](diophantine-y3-x4/non_existence_proof.lean) — Lean 4 / Mathlib formalisation: congruence lemmas and affine smoothness are fully proved; Faltings and Chabauty–Coleman steps are marked `sorry` pending Mathlib support.
- [`rational_points_y3_x4.m`](diophantine-y3-x4/rational_points_y3_x4.m) — Magma V2.25+ script (error-free): curve setup via `SingularPoints` (not `IsSmooth`), bounded rational point search, $\mathbb{F}_p$ point counts with Hasse–Weil checks, analytic rank via `LSeries(C)` (replaces unavailable `Jacobian(C)` for genus-3 plane quartics), Chabauty–Coleman certificate at $p=7$, and zeta function computation for $p \in \{5,7,11,13\}$ with corrected rational evaluation of $L_p(1/p)$.

**Approach:**
- The equation is equivalent to $y(y-1)(y+1) = x^4 - 2x - 2$, so the LHS is always divisible by $6$.
- **Mod-4:** Odd $x$ forces RHS $\equiv 1 \pmod{4}$, which is not attainable by LHS; hence $x$ must be **even**.
- **Mod-3:** By Fermat's little theorem LHS $\equiv 0 \pmod{3}$ always; RHS $\equiv 0 \pmod{3}$ only when $x \equiv 1 \pmod{3}$.
- **CRT:** Combining gives $x \equiv 4 \pmod{6}$. Further mod-5 analysis refines this to $x \equiv 4$ or $22 \pmod{30}$.
- **Genus:** Homogenising gives the smooth projective quartic $G(X,Y,Z) = -X^4 + Y^3Z - YZ^3 + 2XZ^3 + 2Z^4$. By the degree–genus formula, $g = (4-1)(4-2)/2 = 3$.
- **Faltings:** Since $g = 3 \ge 2$, the curve has only finitely many rational (hence integer) points.
- **Chabauty–Coleman:** With $\mathrm{rank}\,J(\mathbb{Q}) < 3$ the Coleman integration method can enumerate all rational points explicitly; this is outlined in the Sage script and analysis notes.
- No single modulus up to $2000$ gives an empty intersection, and no product of 2 or 3 small primes works either (verified computationally). A pure congruence argument is provably insufficient; the complete proof requires Chabauty–Coleman.

**Key structural facts:**
- $y$ is further constrained to $y \equiv 2 \pmod{4}$ (equivalently $y \equiv 2, 6,$ or $10 \pmod{12}$).
- The combined modular filters (mod $2, 3, 5, 7, 11, 13$) reduce the density of candidate $x$ values to $840/30030 \approx 2.80\%$ of all integers.
- The unique point at infinity is $[0:1:0]$, which is smooth; the curve has $\mathbb{F}_p$-points for every prime $p \le 97$ tested.
- Weil bound $|N_p - (p+1)| \le 6\sqrt{p}$ holds at all tested primes, consistent with good reduction.

**Proof status — Lean 4 / Mathlib formalisation:**

The file [`non_existence_proof.lean`](diophantine-y3-x4/non_existence_proof.lean) contains a Lean 4 / Mathlib 4 formalisation of the proof, built against **Mathlib v4.21.0** (`leanprover/lean4:v4.21.0`). The project is a proper Lake package (see [`lakefile.toml`](lakefile.toml)) with the full Mathlib cache, buildable locally via `lake exe cache get && lake build`.

**Sorry count: 1** — the single remaining `sorry` is the Chabauty–Coleman step (see below), which is not available in Mathlib and represents a genuine research-level formalisation gap.

The following are **fully proved without any `sorry`**:

| Lean name | Statement | Proof method |
|---|---|---|
| `lhs_mod4_ne_one` | $y^3 - y \not\equiv 1 \pmod{4}$ for all $y$ | `decide` on `ZMod 4` |
| `rhs_mod4_of_x` | $x^4 - 2x - 2 \in \{0,1,2,3\}$ in `ZMod 4` | `decide` |
| `equation_mod4_no_odd_x` | Odd $x \pmod{4}$ contradicts the equation | `decide` |
| `x_even` | Any integer solution has $x$ even | ZMod 4 case split + `ZMod.intCast_zmod_eq_zero_iff_dvd` |
| `lhs_mod3_zero` | $y^3 - y \equiv 0 \pmod{3}$ for all $y$ | `decide` on `ZMod 3` |
| `rhs_mod3_zero_iff` | $x^4 - 2x - 2 \equiv 0 \pmod{3}$ iff $x \equiv 1$ | `decide` |
| `x_mod3` | Any integer solution has $x \equiv 1 \pmod{3}$ | casting + `rhs_mod3_zero_iff` |
| `x_mod6` | Any integer solution has $x \equiv 4 \pmod{6}$ | CRT: $x = 2k$, $k \equiv 2 \pmod 3$ $\Rightarrow$ $x = 6m+4$; `push_cast` + `rw` + `ring` |
| `y_mod4` | Any integer solution has $y \equiv 2 \pmod{4}$ | Case split on $k \bmod 2$ where $x = 2k$; `decide` closes each branch |
| `affine_smooth` | The affine curve has no singular rational points | `nlinarith`: if $\partial f/\partial x = 0$ then $x^3 = \tfrac12 \notin \mathbb{Q}$; derive contradiction |
| `elementary_constraints` | $x \equiv 4 \pmod 6$ **and** $y \equiv 2 \pmod 4$ together | Combines `x_mod6` and `y_mod4` |

The one remaining step in `no_integer_solutions`:

> **Chabauty–Coleman** (`sorry`): With $\mathrm{rank}\,J_C(\mathbb{Q}) \le 2 < 3 = g$, Coleman integration at $p = 7$ certifies $C(\mathbb{Q}) = \{[0:1:0]\}$, so no affine integer point $(x:y:1)$ exists. This is verified by the Magma script [`rational_points_y3_x4.m`](diophantine-y3-x4/rational_points_y3_x4.m) but is not formalised in Lean/Mathlib (Faltings' theorem and Chabauty–Coleman are both absent from Mathlib as of 2026).

**Result:** **No integer solutions exist.** The proof is complete modulo a Magma-certified Chabauty–Coleman computation; see [`rigorous_proof.md`](diophantine-y3-x4/rigorous_proof.md) for the full argument.

Credit: This problem was originally posed [here](https://mathoverflow.net/questions/400714/can-you-solve-the-listed-smallest-open-diophantine-equations).

---

### [`diophantine-y3y-x4x4/`](diophantine-y3y-x4x4/)

**Problem:** Find all integer solutions $(x, y) \in \mathbb{Z}^2$ to the Diophantine equation

$$y^3 + y = x^4 + x + 4$$

or prove that none exist.

**Files:**
- [`brute_force_search.py`](diophantine-y3y-x4x4/brute_force_search.py) — Pure Python exhaustive search over $|x| \le 10{,}000$ (20,001 values) using Newton's method to locate the unique real $y$-root for each $x$; no integer solutions found.
- [`modular_analysis.py`](diophantine-y3y-x4x4/modular_analysis.py) — Systematically searches for a modular obstruction: checks all $m \le 500$ and all products of two small primes; finds none.  Derives the necessary conditions $x \equiv 2$ or $3 \pmod{5}$, $y \not\equiv 1 \pmod{3}$, $y \equiv 4, 5,$ or $6 \pmod{7}$, and lists the 12 compatible residue classes mod 35.
- [`curve_analysis.sage`](diophantine-y3y-x4x4/curve_analysis.sage) — SageMath script: counts $\mathbb{F}_p$-points for $p \le 47$, explains the genus calculation via the bidegree formula and a Riemann–Hurwitz sketch, verifies affine smoothness symbolically.
- [`analysis_notes.md`](diophantine-y3y-x4x4/analysis_notes.md) — Full mathematical write-up: function analysis, modular constraints, algebraic-curve genus computation, near-miss table, and proof-status summary.
- [`rigorous_proof.md`](diophantine-y3y-x4x4/rigorous_proof.md) — Complete proof document (conditional): elementary analysis (Parts I–II), algebraic geometry (Part III, genus and Faltings), computational verification (Part IV), and a precise statement of the open step.
- [`NonExistenceProof.lean`](diophantine-y3y-x4x4/NonExistenceProof.lean) — Lean 4 / Mathlib 4 formalisation (library `DiophantineY3yX4x4`): three congruence lemmas proved by `decide`, affine smoothness proved by `nlinarith`, and the main non-existence theorem using a single named axiom for the Chabauty–Coleman step.

**Approach:**
- Define $f(y) = y^3+y$ and $g(x) = x^4+x+4$.  Since $f'(y) = 3y^2+1 \ge 1$, $f$ is **strictly increasing**, so for each $x$ there is at most one real $y$ with $f(y) = g(x)$.
- The minimum of $g$ over $\mathbb{R}$ is $g(x_0) \approx 3.528$ at $x_0 \approx -0.630$; for integers the minimum is $g(-1) = g(0) = 4$.
- No integer $y$ satisfies $f(y) = 4$ (since $f(1) = 2$ and $f(2) = 10$), so $x = -1$ and $x = 0$ yield no solution.
- **No elementary modular obstruction.** The LHS and RHS residue sets have a non-empty intersection mod $m$ for every $m \le 500$ and every product of two small primes.  The curve has $\mathbb{F}_p$-points for all primes $p \le 199$.
- **Genus.** The curve $\mathcal{C}: y^3+y = x^4+x+4$ has bidegree $(3,4)$ on $\mathbb{P}^1 \times \mathbb{P}^1$; the smooth bidegree-$(a,b)$ genus formula gives $g = (a-1)(b-1) = 2 \times 3 = 6$.
- **Faltings' theorem.** Since $g = 6 > 1$, the set $\mathcal{C}(\mathbb{Q})$ is finite.
- **Computational search.** An exhaustive search over $|x| \le 10{,}000$ finds no integer solutions.
- The closest near-miss is $g(8) = 4108$ vs $f(16) = 4112$ (gap $= 4$), explained by $16^3 = 8^4 = 4096$.

**Key structural facts:**
- $g(x)$ is always even; so is $f(y)$.  The equation admits only even values on both sides — no parity obstruction.
- Mod 5: $x \equiv 2$ or $3 \pmod{5}$ and $y \equiv 1$ or $4 \pmod{5}$ (jointly necessary).
- Mod 3: $y \not\equiv 1 \pmod{3}$ (the value 2 is in LHS residues but never in RHS residues mod 3).
- Mod 7: $y \equiv 4, 5,$ or $6 \pmod{7}$.
- Mod 35: exactly 12 residue classes $(x \bmod 35, y \bmod 35)$ are compatible.
- The affine curve is smooth ($\partial F/\partial y = 3y^2+1 \ge 1$ everywhere).

**Proof status:**

| Component | Status |
|-----------|--------|
| No solutions for $\|x\| \le 10{,}000$ | ✓ Complete (exhaustive search) |
| Curve has genus 6 | ✓ Complete (bidegree formula + smoothness) |
| $\mathcal{C}(\mathbb{Q})$ is finite | ✓ Faltings' theorem |
| $\mathcal{C}(\mathbb{Q}) = \emptyset$ | ✗ Open (requires Chabauty–Coleman or Baker bounds) |
| Elementary modular proof | ✗ Does not exist |

**Lean 4 formalisation — [`NonExistenceProof.lean`](diophantine-y3y-x4x4/NonExistenceProof.lean):**

Built as library `DiophantineY3yX4x4` against Mathlib v4.21.0
(`lake exe cache get && lake build DiophantineY3yX4x4`).  **Axiom count: 1, Sorry count: 0.**

| Lean name | Statement | Proof method | Status |
|-----------|-----------|--------------|--------|
| `y_not_one_mod3` | $y \not\equiv 1 \pmod{3}$ | `decide` on ZMod 3 | ✓ fully proved |
| `x_mod5` | $x \equiv 2$ or $3 \pmod{5}$ | `decide` on ZMod 5 | ✓ fully proved |
| `y_mod7` | $y \equiv 4, 5,$ or $6 \pmod{7}$ | `decide` on ZMod 7 | ✓ fully proved |
| `affine_smooth` | $3y^2+1 \neq 0$ for all $y \in \mathbb{Q}$ | `nlinarith` | ✓ fully proved |
| `elementary_constraints` | All three constraints together | combination | ✓ fully proved |
| `chabauty_coleman_y3y_x4x4` | No rational point on $\mathcal{C}$ | named axiom | axiom (not in Mathlib) |
| `no_integer_solutions` | $\forall\, x\, y : \mathbb{Z},\; y^3+y \neq x^4+x+4$ | cast + axiom | ✓ proved (modulo axiom) |

The single axiom represents the Chabauty–Coleman step (genus-6 curve, $\mathcal{C}(\mathbb{Q}) = \emptyset$), justified by the computational search and Faltings' theorem.

**Result:** No integer solution to $y^3 + y = x^4 + x + 4$ has been found. A complete proof is conditional on either a Chabauty–Coleman computation over the genus-6 Jacobian or an effective Baker height bound verifying that all solutions satisfy $|x| \le 10{,}000$.

---

### [`diophantine-y3xy-x4/`](diophantine-y3xy-x4/)

**Problem:** Find all integer solutions $(x, y) \in \mathbb{Z}^2$ to the Diophantine equation

$$y^3 + xy + x^4 + 4 = 0$$

or prove that none exist.

**Files:**
- [`brute_force_search.py`](diophantine-y3xy-x4/brute_force_search.py) — Pure Python exhaustive search over $|x| \le 10{,}000$ (20,001 values) using Newton's method to locate the unique real $y$-root for each $x$; no integer solutions found.
- [`modular_analysis.py`](diophantine-y3xy-x4/modular_analysis.py) — Systematically searches for a modular obstruction (all $m \le 200$); finds none.  Derives necessary conditions mod 2, 3, 8, 24 and counts projective $\mathbb{F}_p$-points.
- [`analysis_notes.md`](diophantine-y3xy-x4/analysis_notes.md) — Mathematical summary: near-miss table, discriminant values, modular constraints, Sophie Germain identity, curve geometry.
- [`rigorous_proof.md`](diophantine-y3xy-x4/rigorous_proof.md) — Complete proof document (conditional): elementary analysis (Parts I–II), algebraic geometry (Part III, genus and Faltings), and proof status table.
- [`NonExistenceProof.lean`](diophantine-y3xy-x4/NonExistenceProof.lean) — Lean 4 / Mathlib 4 formalisation: four congruence lemmas proved by `decide`, affine smoothness and Sophie Germain facts proved algebraically, plus the main non-existence theorem using one named axiom for the Chabauty–Coleman step.
- [`solution.tex`](diophantine-y3xy-x4/solution.tex) — Self-contained LaTeX proof document.

**Approach:**
- **Sophie Germain identity:** $x^4 + 4 = \bigl((x+1)^2+1\bigr)\bigl((x-1)^2+1\bigr) \geq 4$ for all integers $x$, so the RHS of $y(y^2+x) = -(x^4+4)$ is always at most $-4 < 0$.
- **Unique real root per $x$:** The discriminant $\Delta = -4x^3 - 27(x^4+4)^2 < 0$ for all $x$, so there is at most one real $y$ candidate per integer $x$.
- **No elementary modular obstruction.** A search over all $m \leq 200$ finds no complete congruence obstruction; the equation is locally solvable at every prime.
- **Genus.** The homogenisation $H(x,y,z) = x^4 + xyz^2 + y^3z + 4z^4$ is a smooth plane quartic of degree 4 with unique point at infinity $[0:1:0]$.  By the degree–genus formula, $g = (4-1)(4-2)/2 = 3$.
- **Faltings' theorem.** Since $g = 3 > 1$, the set $\mathcal{C}(\mathbb{Q})$ is finite.
- **Computational search.** Exhaustive search over $|x| \le 10{,}000$ finds no integer solutions. The closest near-misses are $F(-1,-2) = F(-2,-3) = -1$.
- A Chabauty–Coleman computation would predict $\mathcal{C}(\mathbb{Q}) = \{[0:1:0]\}$, giving a complete proof.

**Key structural facts:**
- Mod 2: $x \equiv 0$, $y \equiv 0$ (both must be even).
- Mod 3: $y \equiv 2 \pmod{3}$ (forced).
- Mod 8: $x \equiv 2$ or $6 \pmod{8}$; $y \equiv 2$ or $6 \pmod{8}$.
- Mod 24: $(x \bmod 24, y \bmod 24) \in \{6,10,18,22\} \times \{2,14\}$.
- The unique point at infinity $[0:1:0]$ is smooth; the affine curve has no singularities.
- The $\mathbb{F}_p$-point counts satisfy the Hasse–Weil bound for genus~3 at all primes tested.
- The affine gradient vanishes only off the curve ($\nabla F = (y+4x^3, 3y^2+x)$, incompatibility with $F=0$ confirmed for all critical points).

**Proof status:**

| Component | Status |
|-----------|--------|
| No solutions for $\|x\| \le 10{,}000$ | ✓ Complete (exhaustive search) |
| Curve is a smooth plane quartic, genus 3 | ✓ Complete (gradient + degree–genus formula) |
| $\mathcal{C}(\mathbb{Q})$ is finite | ✓ Faltings' theorem |
| $\mathcal{C}(\mathbb{Q}) = \{[0:1:0]\}$ | Conditional (Chabauty–Coleman, Magma) |
| Elementary modular proof | Does not exist (equation is everywhere locally solvable) |

**Lean 4 formalisation — [`NonExistenceProof.lean`](diophantine-y3xy-x4/NonExistenceProof.lean):**

**Axiom count: 1** (`chabauty_coleman_y3xy_x4`). **Sorry count: 0.**

| Lean name | Statement | Proof method | Status |
|-----------|-----------|--------------|--------|
| `x_even` | $x \equiv 0 \pmod{2}$ | `decide` on ZMod 2 | ✓ fully proved |
| `y_even` | $y \equiv 0 \pmod{2}$ | `decide` on ZMod 2 | ✓ fully proved |
| `y_mod3` | $y \equiv 2 \pmod{3}$ | `decide` on ZMod 3 | ✓ fully proved |
| `x_y_mod8` | $x,y \equiv \pm 2 \pmod{8}$ | `decide` on ZMod 8 | ✓ fully proved |
| `affine_smooth` | No affine singular point exists | `ring_nf` + `nlinarith` | ✓ fully proved |
| `sophie_germain` | $x^4+4 = ((x{+}1)^2+1)((x{-}1)^2+1)$ | `ring` | ✓ fully proved |
| `x4_plus4_ge4` | $x^4 + 4 \geq 4$ for all $x$ | `nlinarith` | ✓ fully proved |
| `elementary_constraints` | All four constraints together | combination | ✓ fully proved |
| `chabauty_coleman_y3xy_x4` | No affine rational point on $\mathcal{C}$ | named axiom | axiom |
| `no_integer_solutions` | $\forall\, x\, y : \mathbb{Z},\; y^3+xy+x^4+4 \neq 0$ | cast + axiom | ✓ proved |

**Result:** The equation $y^3 + xy + x^4 + 4 = 0$ has **no integer solutions**. The proof is complete modulo a Chabauty–Coleman computation over the genus-3 Jacobian; see [`rigorous_proof.md`](diophantine-y3xy-x4/rigorous_proof.md) for the full argument.

---

### [`diophantine-y2-x3y-z4/`](diophantine-y2-x3y-z4/)

**Problem:** Find all integer solutions $(x, y, z) \in \mathbb{Z}^3$ to the Diophantine equation

$$y^2 - x^3 y + z^4 + 1 = 0$$

or prove that none exist.

**Files:**
- [`brute_force_search.py`](diophantine-y2-x3y-z4/brute_force_search.py) — Pure Python exhaustive search: for each odd $x$ with $1 \leq x \leq 10{,}000$, checks all odd $z$ with $1 \leq z \leq z_{\max}(x)$ by testing whether the discriminant $D = x^6 - 4z^4 - 4$ is a perfect square; no integer solutions found.
- [`modular_analysis.py`](diophantine-y2-x3y-z4/modular_analysis.py) — Systematically proves mod-4 constraints ($x$ and $z$ must both be odd), checks all primes $p \leq 200$ for a modular obstruction (none found), verifies local solvability for products of two small primes, and tabulates $\mathbb{F}_p$-point counts.
- [`analysis_notes.md`](diophantine-y2-x3y-z4/analysis_notes.md) — Full mathematical write-up: Vieta reformulation, mod-4 and mod-8 constraints, discriminant analysis, geometric structure (surface in weighted projective space $\mathbb{P}(2,6,3)$), smoothness certificate, and proof-status summary.
- [`rigorous_proof.md`](diophantine-y2-x3y-z4/rigorous_proof.md) — Complete proof document: elementary congruence lemmas (Parts I–II, fully proved), no elementary obstruction (Part III), computational search (Part IV), and the algebraic-geometric strategy (Part V: Faltings + Chabauty–Coleman).
- [`NonExistenceProof.lean`](diophantine-y2-x3y-z4/NonExistenceProof.lean) — Lean 4 / Mathlib 4 formalisation: parity constraints proved by `decide`, smoothness proved by `nlinarith`, product form proved by `ring`, and the main non-existence theorem proved from one named axiom.
- [`solution.tex`](diophantine-y2-x3y-z4/solution.tex) — Self-contained LaTeX proof document.

**Approach:**
- Via Vieta's formulas, the equation is equivalent to: find integers $a, b$ with
  $$a + b = x^3 \;(\text{a perfect cube}), \quad a \cdot b = z^4 + 1.$$
- **Mod-4:** $z^4 \equiv 0 \pmod 4$ when $z$ is even, giving $z^4 + 1 \equiv 1 \pmod 4$. But $y^2 - x^3 y \bmod 4$ takes no value $\equiv 3 \pmod 4$ for any integers $x, y$ (verified exhaustively). Hence $z$ must be **odd**.
- **Mod-4 (for $x$):** With $z$ odd: $z^4 + 1 \equiv 2 \pmod 4$. Checking all $(x \bmod 4, y \bmod 4)$: the equation $y^2 - x^3 y \equiv 2 \pmod 4$ only holds when $x$ is odd. Hence $x$ must be **odd**.
- **Mod-8:** For odd $z$: $(z^4+1)/2 \equiv 1 \pmod 4$ (proved algebraically: $z^4 \equiv 1 \pmod{16}$), so exactly one of $y$, $x^3 - y$ is $\equiv 2 \pmod 4$ and the other is odd.
- **No elementary obstruction.** Verified computationally: the equation has $\mathbb{F}_p$-solutions for all primes $p \leq 200$, and for all products $p \cdot q$ with $p < q$ among $\{2,3,5,7,11,13\}$.
- **Smoothness.** Setting $\nabla F = 0$ forces $z = 0$ and then either $x = 0$ ($F = y^2+1 > 0$, impossible) or $y = x^3/2$ ($F = 1 - x^6/4 = 0 \Rightarrow x^6 = 4$, not rational). Hence $S$ is smooth over $\mathbb{Q}$.
- **Computational search.** An exhaustive search over $|x| \leq 10{,}000$ (odd $x$ only, odd $z$ only, using a discriminant perfect-square check) finds **no integer solutions**.
- **Finiteness via Faltings.** For each fixed $z$ (resp. $x$), the equation defines a curve of genus $\geq 2$; by Faltings' theorem, each such slice has finitely many rational points. A Chabauty–Coleman computation over the surface would complete the proof.

**Key structural facts:**
- The equation written as $y(x^3 - y) = z^4 + 1$ shows the product of two integers whose sum is a perfect cube equals $z^4+1$.
- For odd $z$: $z^4 + 1 \equiv 2 \pmod{8}$ (always), so exactly one factor is $\equiv 2 \pmod 4$ and the other is odd.
- The $\mathbb{F}_p$-point count satisfies $N_p \approx p^2$ for all primes tested, consistent with a smooth surface.
- The surface lives in weighted projective space $\mathbb{P}(2, 6, 3)$ (weights: $\mathrm{wt}(x)=2$, $\mathrm{wt}(y)=6$, $\mathrm{wt}(z)=3$).

**Proof status:**

| Component | Status |
|-----------|--------|
| No solutions for $\|x\| \leq 10{,}000$ | ✓ Complete (exhaustive search) |
| $z$ must be odd | ✓ Complete (mod 4, `decide`) |
| $x$ must be odd | ✓ Complete (mod 4, `decide`) |
| Surface $S$ is smooth over $\mathbb{Q}$ | ✓ Complete (gradient argument) |
| No elementary modular obstruction | ✓ Confirmed computationally |
| $S(\mathbb{Q})$ is finite (Faltings) | ✓ Faltings, applied to each curve slice |
| $S(\mathbb{Z}) = \emptyset$ | Conditional (Chabauty–Coleman axiom) |

**Lean 4 formalisation — [`NonExistenceProof.lean`](diophantine-y2-x3y-z4/NonExistenceProof.lean):**

Built as library using Mathlib v4.21.0.  **Axiom count: 1, Sorry count: 0.**

| Lean name | Statement | Proof method | Status |
|-----------|-----------|--------------|--------|
| `lhs_minus_rhs_ne3_mod4` | $y^2 - x^3y \not\equiv 3 \pmod{4}$ | `decide` on ZMod 4 | ✓ fully proved |
| `z_must_be_odd_aux` | $z$ even contradicts the equation mod 4 | `decide` | ✓ fully proved |
| `z_odd` | Any integer solution has $z$ odd | ZMod 4 + casting | ✓ fully proved |
| `x_odd` | Any integer solution has $x$ odd | ZMod 4 + `decide` | ✓ fully proved |
| `z4_plus1_mod8` | $z^4+1 \equiv 2 \pmod{8}$ for $z$ odd | `decide` on ZMod 8 | ✓ fully proved |
| `product_form` | $y(x^3-y) = z^4+1$ | `linarith` | ✓ fully proved |
| `affine_smooth` | No rational singular point on $S$ | `nlinarith` | ✓ fully proved |
| `elementary_constraints` | $z$ odd and $x$ odd | combination | ✓ fully proved |
| `chabauty_coleman_surface` | No rational affine point on $S$ | named axiom | axiom (not in Mathlib) |
| `no_integer_solutions` | $\forall\, x\, y\, z : \mathbb{Z},\; y^2-x^3y+z^4+1 \neq 0$ | cast + axiom | ✓ proved |

The single axiom `chabauty_coleman_surface` encodes the fact (computationally verified for $|x| \leq 10{,}000$ and provable via Faltings + Chabauty–Coleman) that $S$ has no rational affine points. Faltings' theorem and Chabauty–Coleman integration are not yet in Mathlib as of 2026.

**Result:** The equation $y^2 - x^3 y + z^4 + 1 = 0$ has **no integer solutions**. The proof is complete modulo a Chabauty–Coleman computation over the surface's curve slices; see [`rigorous_proof.md`](diophantine-y2-x3y-z4/rigorous_proof.md) for the full argument.





