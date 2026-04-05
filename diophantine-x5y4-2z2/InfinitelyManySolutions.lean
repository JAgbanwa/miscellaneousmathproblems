import Mathlib

/-!
# Infinitely Many Integer Solutions to x⁵ + y⁴ = 2z²

We prove that the Diophantine equation `x^5 + y^4 = 2*z^2` has infinitely many
integer solutions.

## Proof outline

1. **Seed solution.** The triple `(1, 1, 1)` satisfies `1^5 + 1^4 = 2 = 2*1^2`.

2. **Weighted homogeneity.** Assigning weights `wt(x) = 4, wt(y) = 5, wt(z) = 10`,
   every monomial has the same weight 20:
   `wt(x^5) = 20 = wt(y^4) = wt(2*z^2)`.
   Consequently, if `(x, y, z)` is a solution then so is `(t^4*x, t^5*y, t^10*z)`
   for any `t : ℤ`.

3. **Parametric family.** Applying the scaling to `(1, 1, 1)` gives
   `(t^4, t^5, t^10)` for all `t : ℤ`.  Verification:
   `(t^4)^5 + (t^5)^4 = t^20 + t^20 = 2*t^20 = 2*(t^10)^2`.  This is proved
   by a single `ring` computation.

4. **Injectivity.** The map `n ↦ (n^4, n^5, n^10) : ℕ → ℤ × ℤ × ℤ` is injective,
   because `n ↦ n^4` is strictly monotone on `ℕ` (for positive exponent).

5. **Infinitude.** An injective function from `ℕ` into the solution set implies
   the solution set is infinite.

## Sorry count: 0

The proof is fully formalised.
-/

/-- The Diophantine equation `x^5 + y^4 = 2*z^2`. -/
def isolution (x y z : ℤ) : Prop := x ^ 5 + y ^ 4 = 2 * z ^ 2

/-- The set of all integer solutions to `x^5 + y^4 = 2*z^2`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Parametric family -/

/-- For any `t : ℤ`, the triple `(t^4, t^5, t^10)` is a solution.
Proof: `(t^4)^5 + (t^5)^4 = t^20 + t^20 = 2*(t^10)^2`. -/
theorem parametric_solution (t : ℤ) :
    isolution (t ^ 4) (t ^ 5) (t ^ 10) := by
  unfold isolution
  ring

/-! ## Small explicit witnesses -/

theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_1_1_1 : isolution 1 1 1 := by norm_num [isolution]
theorem sol_1_neg1_1 : isolution 1 (-1 : ℤ) 1 := by norm_num [isolution]
theorem sol_16_32_1024 : isolution 16 32 1024 := by norm_num [isolution]
theorem sol_16_neg32_1024 : isolution 16 (-32 : ℤ) 1024 := by norm_num [isolution]
theorem sol_2_0_4 : isolution 2 0 4 := by norm_num [isolution]

/-! ## Infinitely many solutions -/

/-- The parametric map `n ↦ ((n : ℤ)^4, (n : ℤ)^5, (n : ℤ)^10)` from `ℕ` into
    the solution set. -/
def natMap (n : ℕ) : ℤ × ℤ × ℤ := ((n : ℤ) ^ 4, (n : ℤ) ^ 5, (n : ℤ) ^ 10)

/-- Every element of the parametric family is a solution. -/
theorem natMap_mem (n : ℕ) : natMap n ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, isolution, natMap]
  ring

/-- The map `n ↦ n^4` is strictly monotone on `ℕ`. -/
private theorem pow4_strictMono : StrictMono (fun n : ℕ => n ^ 4) := by
  intro a b hab
  exact Nat.pow_lt_pow_left hab (by norm_num)

/-- The parametric map is injective (injectivity follows from the first component
    `n ↦ n^4` being strictly monotone on `ℕ`). -/
theorem natMap_injective : Function.Injective natMap := by
  intro n1 n2 h
  simp only [natMap, Prod.mk.injEq] at h
  have h4 : n1 ^ 4 = n2 ^ 4 := by exact_mod_cast h.1
  exact pow4_strictMono.injective h4

/-- The solution set of `x^5 + y^4 = 2*z^2` is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply (Set.infinite_range_of_injective natMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact natMap_mem n
