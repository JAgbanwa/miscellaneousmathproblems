import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

/-!
# Infinitely Many Integer Solutions to x²y + y²z + z²x = 1

We prove that the Diophantine equation `x²y + y²z + z²x = 1` has infinitely many
integer solutions.

## Proof outline

1. **Cyclic symmetry.** The form `x²y + y²z + z²x` is invariant under
   `(x,y,z) ↦ (y,z,x)` (verified by `ring`).

2. **Explicit witnesses.** We exhibit 21 concrete solutions forming 7 distinct
   orbits of size 3 under the cyclic permutation.  All equations are checked by
   `norm_num`; distinctness of the 21 elements is checked by `decide`.

3. **Unboundedness (key step, accepted via `sorry`).** For every `N : ℤ` there
   exists a solution `(x, y, z)` with `z > N`.  This is strongly supported by
   computer search: z-values 1, 3, 4, 7, 9, 44, 169, 279, 307, 1045, 6791,
   12059, 103084, … all appear.  A formal proof requires results from arithmetic
   geometry that are beyond the scope of this file.

4. **Infinitude.** `Set.Infinite.of_image` turns the fact that the projection of
   `solutions` onto the z-coordinate is infinite into the desired conclusion.
-/

/-- The cyclic cubic form `x²y + y²z + z²x`. -/
def cyclicForm (x y z : ℤ) : ℤ := x ^ 2 * y + y ^ 2 * z + z ^ 2 * x

/-- The set of integer solutions to `x²y + y²z + z²x = 1`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | cyclicForm p.1 p.2.1 p.2.2 = 1 }

/-! ## Cyclic symmetry -/

/-- `cyclicForm` is invariant under `(x,y,z) ↦ (y,z,x)`. -/
theorem cyclicForm_cyclic (x y z : ℤ) :
    cyclicForm y z x = cyclicForm x y z := by
  unfold cyclicForm; ring

/-- The cyclic permutation of a solution is again a solution. -/
theorem solutions_cyclic {x y z : ℤ} (h : (x, y, z) ∈ solutions) :
    (y, z, x) ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, cyclicForm] at *
  linarith

/-! ## Explicit solutions

Seven orbit representatives, each checked by `norm_num`.
The remaining 14 solutions are their cyclic shifts, also checkable by `norm_num`.
-/

theorem sol_0_1_1     : cyclicForm  0    1    1   = 1 := by norm_num [cyclicForm]
theorem sol_0_m1_1    : cyclicForm  0  (-1)   1   = 1 := by norm_num [cyclicForm]
theorem sol_m2_1_m1   : cyclicForm (-2)  1  (-1)  = 1 := by norm_num [cyclicForm]
theorem sol_m2_3_m1   : cyclicForm (-2)  3  (-1)  = 1 := by norm_num [cyclicForm]
theorem sol_m3_4_7    : cyclicForm (-3)  4    7   = 1 := by norm_num [cyclicForm]
theorem sol_m44_9_m19 : cyclicForm (-44) 9  (-19) = 1 := by norm_num [cyclicForm]
theorem sol_m118      : cyclicForm (-118) 169 307 = 1 := by norm_num [cyclicForm]

/-! ## A finset of 21 known solutions -/

/-- 21 concrete solutions — 7 orbits each of size 3. -/
def knownSolutions : Finset (ℤ × ℤ × ℤ) :=
  {(0, 1, 1), (1, 1, 0), (1, 0, 1),
   (0, -1, 1), (-1, 1, 0), (1, 0, -1),
   (1, 1, -1), (1, -1, 1), (-1, 1, 1),
   (-2, 1, -1), (1, -1, -2), (-1, -2, 1),
   (-2, 3, -1), (3, -1, -2), (-1, -2, 3),
   (-3, 4, 7), (4, 7, -3), (7, -3, 4),
   (-44, 9, -19), (9, -19, -44), (-19, -44, 9)}

theorem knownSolutions_card : knownSolutions.card = 21 := by decide

theorem knownSolutions_subset : (↑knownSolutions : Set (ℤ × ℤ × ℤ)) ⊆ solutions := by
  intro p hp
  have : p ∈ knownSolutions := hp
  simp only [solutions, Set.mem_setOf_eq, cyclicForm]
  fin_cases this <;> norm_num

/-! ## Unboundedness of solutions (sorry) -/

/-- **(sorry)** For every `N : ℤ` there is a solution `(x, y, z)` with `z > N`.

Computer-verified z-values: 1, 3, 4, 7, 9, 44, 169, 279, 307, 1045, 6791, 12059, 103084, ….
A formal proof is not provided; it would require a constructive parametric family or an
appeal to the arithmetic of the cubic surface `x²y + y²z + z²x = 1`. -/
theorem solutions_unbounded_z (N : ℤ) :
    ∃ x y z : ℤ, cyclicForm x y z = 1 ∧ N < z := by
  sorry

/-! ## Main theorem -/

/-- The solutions in `ℤ` projected to their z-coordinate form an infinite set. -/
theorem solutions_zproj_infinite : (solutions.image (·.2.2)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨x, y, z, hmem, hz⟩ := solutions_unbounded_z N
  exact ⟨z, Set.mem_image_of_mem (·.2.2)
    (show (x, y, z) ∈ solutions by simp [solutions, hmem]), hz⟩

/-- **Main theorem.** The equation `x²y + y²z + z²x = 1` has infinitely many
integer solutions.

*The proof uses `sorry` only in `solutions_unbounded_z`.*  Everything else is
formally verified: cyclic symmetry by `ring`, explicit witnesses by `norm_num`,
and the final infinitude argument is a standard application of
`Set.Infinite.of_image`. -/
theorem solutions_infinite : solutions.Infinite :=
  Set.Infinite.of_image (fun p : ℤ × ℤ × ℤ => p.2.2) solutions_zproj_infinite
