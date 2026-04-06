import Mathlib

/-!
# Infinitely Many Integer Solutions to 4x⁵ + 4y⁵ + 11z⁵ = 0

We prove that the Diophantine equation `4*x^5 + 4*y^5 + 11*z^5 = 0` has infinitely many
integer solutions.

## Proof outline

1. **Degree-5 homogeneity.**  The equation is homogeneous of degree 5: for any
   solution `(x, y, z)` and any scalar `t : ℤ`, the triple `(t*x, t*y, t*z)` is
   also a solution.  This follows from the ring identity
   `4*(t*x)^5 + 4*(t*y)^5 + 11*(t*z)^5 = t^5 * (4*x^5 + 4*y^5 + 11*z^5)`.

2. **Seed solution.**  Setting `z = 0` reduces to `4*x^5 + 4*y^5 = 0`, i.e.,
   `x^5 = -y^5`, which forces `x = -y` (since the map `t ↦ t^5` is strictly
   monotone on `ℤ`).  In particular, `(1, -1, 0)` is a solution:
   `4*1 + 4*(-1) + 0 = 0`.

3. **Parametric family.**  Combining the seed with degree-5 homogeneity gives
   the family `(t, -t, 0)` for all `t : ℤ`:
   `4*t^5 + 4*(-t)^5 + 11*0^5 = 4*t^5 - 4*t^5 + 0 = 0`.
   Proof: a single `ring` computation.

4. **Injectivity.**  The map `n ↦ ((n : ℤ), -(n : ℤ), 0) : ℕ → ℤ × ℤ × ℤ` is
   injective because the first component `n ↦ (n : ℤ)` (the canonical embedding
   `ℕ → ℤ`) is injective.

5. **Infinitude.**  An injective function from `ℕ` into the solution set implies
   the solution set is infinite.

## Sorry count: 0

The proof is fully formalised with zero axioms beyond Lean's foundations and Mathlib.
-/

/-- The Diophantine equation `4*x^5 + 4*y^5 + 11*z^5 = 0`. -/
def isolution (x y z : ℤ) : Prop := 4 * x ^ 5 + 4 * y ^ 5 + 11 * z ^ 5 = 0

/-- The set of all integer solutions to `4*x^5 + 4*y^5 + 11*z^5 = 0`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Degree-5 homogeneity -/

/-- Scaling any solution `(x, y, z)` by `t` gives another solution `(t*x, t*y, t*z)`.
Proof: `4*(t*x)^5 + 4*(t*y)^5 + 11*(t*z)^5 = t^5 * (4*x^5 + 4*y^5 + 11*z^5)
       = t^5 * 0 = 0`. -/
theorem homogeneity (x y z : ℤ) (h : isolution x y z) (t : ℤ) :
    isolution (t * x) (t * y) (t * z) := by
  unfold isolution at *
  linear_combination t ^ 5 * h

/-! ## Primary parametric family: (t, -t, 0) -/

/-- For any `t : ℤ`, the triple `(t, -t, 0)` is a solution.
Proof: `4*t^5 + 4*(-t)^5 + 11*0^5 = 4*t^5 - 4*t^5 + 0 = 0`. -/
theorem family (t : ℤ) : isolution t (-t) 0 := by
  unfold isolution
  ring

/-! ## Small explicit witnesses -/

theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_1_neg1_0 : isolution 1 (-1 : ℤ) 0 := by norm_num [isolution]
theorem sol_neg1_1_0 : isolution (-1 : ℤ) 1 0 := by norm_num [isolution]
theorem sol_2_neg2_0 : isolution 2 (-2 : ℤ) 0 := by norm_num [isolution]
theorem sol_neg2_2_0 : isolution (-2 : ℤ) 2 0 := by norm_num [isolution]
theorem sol_3_neg3_0 : isolution 3 (-3 : ℤ) 0 := by norm_num [isolution]
theorem sol_5_neg5_0 : isolution 5 (-5 : ℤ) 0 := by norm_num [isolution]
theorem sol_10_neg10_0 : isolution 10 (-10 : ℤ) 0 := by norm_num [isolution]

/-! ## Infinitely many solutions -/

/-- The map `n ↦ ((n : ℤ), -(n : ℤ), 0)` from `ℕ` into the solution set. -/
def natMap (n : ℕ) : ℤ × ℤ × ℤ := ((n : ℤ), -(n : ℤ), 0)

/-- Every element of the primary family is a solution. -/
theorem natMap_mem (n : ℕ) : natMap n ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, isolution, natMap]
  push_cast
  ring

/-- The parametric map is injective (the first component is the injective cast `ℕ → ℤ`). -/
theorem natMap_injective : Function.Injective natMap := by
  intro n1 n2 h
  simp only [natMap, Prod.mk.injEq] at h
  exact_mod_cast h.1

/-- The solution set of `4*x^5 + 4*y^5 + 11*z^5 = 0` is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply (Set.infinite_range_of_injective natMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact natMap_mem n
