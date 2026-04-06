import Mathlib

/-!
# Infinitely Many Integer Solutions to x⁵ + 2y³ + z³ = 0

We prove that the Diophantine equation `x^5 + 2*y^3 + z^3 = 0` has infinitely many
integer solutions.

## Key structural observation — weighted homogeneity

Assign weights `wt(x) = 3`, `wt(y) = 5`, `wt(z) = 5`.  Every term has weighted degree 15:
  `(x^5)`: weighted degree 5·3 = 15,
  `(2*y^3)`: weighted degree 3·5 = 15,
  `(z^3)`: weighted degree 3·5 = 15.

Consequently, if `(a, b, c)` is any integer solution, then `(t^3*a, t^5*b, t^5*c)` is also
a solution for every `t : ℤ`, since
  `(t^3*a)^5 + 2*(t^5*b)^3 + (t^5*c)^3 = t^15 * (a^5 + 2*b^3 + c^3) = 0`.

It therefore suffices to exhibit a single non-trivial **seed** solution, from which the
scaling produces an infinite parametric family.

## Proof outline

1. **Primary parametric family (Family 1).** Setting `z = -y` reduces the equation to
   `x^5 + y^3 = 0`, solved by `x = -n^3`, `y = n^5` for any `n : ℤ`:
   `(-n^3)^5 + 2*(n^5)^3 + (-n^5)^3 = -n^15 + 2*n^15 - n^15 = 0`.
   Seed: `(-1, 1, -1)`.  Proof: a single `ring` computation.

2. **Secondary parametric family (Family 2).** Setting `y = 0` reduces the equation to
   `x^5 + z^3 = 0`, solved by `x = -n^3`, `z = n^5` for any `n : ℤ`:
   `(-n^3)^5 + 0 + (n^5)^3 = -n^15 + n^15 = 0`.
   Seed: `(-1, 0, 1)`.  Proof: a single `ring` computation.

3. **Tertiary parametric family (Family 3).** The triple `(-4, 8, 0)` is a seed:
   `(-4)^5 + 2*8^3 + 0^3 = -1024 + 1024 = 0`.
   By weighted homogeneity: `(-4*n^3, 8*n^5, 0)` is a solution for all `n : ℤ`.
   Proof: a single `ring` computation.

4. **Injectivity.** The map `n ↦ (-(n : ℤ)^3, (n : ℤ)^5, -(n : ℤ)^5) : ℕ → ℤ × ℤ × ℤ`
   is injective, because `n ↦ n^3` is strictly monotone on `ℕ` (positive exponent).

5. **Infinitude.** An injective function from `ℕ` into the solution set implies the
   solution set is infinite.

## Sorry count: 0

The proof is fully formalised.
-/

/-- The Diophantine equation `x^5 + 2*y^3 + z^3 = 0`. -/
def isolution (x y z : ℤ) : Prop := x ^ 5 + 2 * y ^ 3 + z ^ 3 = 0

/-- The set of all integer solutions to `x^5 + 2*y^3 + z^3 = 0`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Family 1: (-n^3, n^5, -n^5)

Setting `z = -y` reduces to `x^5 + y^3 = 0`, solved by `(x, y) = (-n^3, n^5)`.
-/

/-- For any `n : ℤ`, the triple `(-n^3, n^5, -n^5)` is a solution.
Proof: `(-n^3)^5 + 2*(n^5)^3 + (-n^5)^3 = -n^15 + 2*n^15 - n^15 = 0`. -/
theorem family1 (n : ℤ) :
    isolution (-(n ^ 3)) (n ^ 5) (-(n ^ 5)) := by
  unfold isolution; ring

/-! ## Family 2: (-n^3, 0, n^5)

Setting `y = 0` reduces to `x^5 + z^3 = 0`, solved by `(x, z) = (-n^3, n^5)`.
-/

/-- For any `n : ℤ`, the triple `(-n^3, 0, n^5)` is a solution.
Proof: `(-n^3)^5 + 2*0^3 + (n^5)^3 = -n^15 + n^15 = 0`. -/
theorem family2 (n : ℤ) :
    isolution (-(n ^ 3)) 0 (n ^ 5) := by
  unfold isolution; ring

/-! ## Family 3: (-4*n^3, 8*n^5, 0)

Seed `(-4, 8, 0)`: `(-4)^5 + 2*8^3 + 0 = -1024 + 1024 = 0`.
By weighted homogeneity, scaling by `t^{wt}` preserves the equation.
-/

/-- For any `n : ℤ`, the triple `(-4*n^3, 8*n^5, 0)` is a solution.
Proof: `(-4*n^3)^5 + 2*(8*n^5)^3 + 0^3 = -4^5*n^15 + 2*8^3*n^15 = (-1024+1024)*n^15 = 0`. -/
theorem family3 (n : ℤ) :
    isolution (-4 * n ^ 3) (8 * n ^ 5) 0 := by
  unfold isolution; ring

/-! ## Small explicit witnesses -/

theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_neg1_1_neg1 : isolution (-1) 1 (-1) := by norm_num [isolution]
theorem sol_1_neg1_1 : isolution 1 (-1) 1 := by norm_num [isolution]
theorem sol_neg1_0_1 : isolution (-1) 0 1 := by norm_num [isolution]
theorem sol_1_0_neg1 : isolution 1 0 (-1) := by norm_num [isolution]
theorem sol_neg4_8_0 : isolution (-4) 8 0 := by norm_num [isolution]
theorem sol_4_neg8_0 : isolution 4 (-8) 0 := by norm_num [isolution]
theorem sol_neg9_27_27 : isolution (-9) 27 27 := by norm_num [isolution]
theorem sol_9_neg27_neg27 : isolution 9 (-27) (-27) := by norm_num [isolution]
theorem sol_neg5_neg5_15 : isolution (-5) (-5) 15 := by norm_num [isolution]
theorem sol_5_5_neg15 : isolution 5 5 (-15) := by norm_num [isolution]

/-! ## Infinitely many solutions -/

/-- The map `n ↦ (-(n : ℤ)^3, (n : ℤ)^5, -(n : ℤ)^5)` from `ℕ` into the solution set. -/
def natMap (n : ℕ) : ℤ × ℤ × ℤ := (-(n : ℤ) ^ 3, (n : ℤ) ^ 5, -(n : ℤ) ^ 5)

/-- Every element of Family 1 (restricted to `ℕ`) is a solution. -/
theorem natMap_mem (n : ℕ) : natMap n ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, isolution, natMap]
  ring

/-- The map `n ↦ n^3` is strictly monotone on `ℕ`. -/
private theorem pow3_strictMono : StrictMono (fun n : ℕ => n ^ 3) := by
  intro a b hab
  exact Nat.pow_lt_pow_left hab (by norm_num)

/-- The parametric map `natMap` is injective (the first component `n ↦ n^3` is
    strictly increasing, hence injective). -/
theorem natMap_injective : Function.Injective natMap := by
  intro n1 n2 h
  simp only [natMap, Prod.mk.injEq] at h
  have h3 : (n1 : ℤ) ^ 3 = (n2 : ℤ) ^ 3 := neg_inj.mp h.1
  have h3n : n1 ^ 3 = n2 ^ 3 := by exact_mod_cast h3
  exact pow3_strictMono.injective h3n

/-- The solution set of `x^5 + 2*y^3 + z^3 = 0` is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply (Set.infinite_range_of_injective natMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact natMap_mem n
