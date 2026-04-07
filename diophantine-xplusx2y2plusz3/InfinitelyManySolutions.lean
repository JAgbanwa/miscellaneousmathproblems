import Mathlib

/-!
# Infinitely Many Integer Solutions to x + x²y² + z³ = 0

We prove that the Diophantine equation `x + x^2 * y^2 + z^3 = 0` has infinitely many
integer solutions by exhibiting two explicit infinite parametric families.

## Key observations

The equation can be rewritten as `x * (1 + x * y^2) + z^3 = 0`.

### Family 1: set x = 0
  Setting `x = 0` reduces the equation to `z^3 = 0`, so `z = 0`.
  For every `n : ℤ`, the triple `(0, n, 0)` is a solution:
    `0 + 0^2 * n^2 + 0^3 = 0`.
  The map `n ↦ (0, n, 0)` is injective (y-component equals n).

### Family 2: set y = 0
  Setting `y = 0` reduces the equation to `x + z^3 = 0`, so `x = -z^3`.
  For every `n : ℤ`, the triple `(-n^3, 0, n)` is a solution:
    `(-n^3) + (-n^3)^2 * 0^2 + n^3 = -n^3 + 0 + n^3 = 0`.
  The map `n ↦ (-n^3, 0, n)` is injective (z-component equals n).

## Proof outline

1. **Family 1 verified.** `(0, n, 0)` satisfies the equation for all `n : ℤ` — `ring`.
2. **Family 2 verified.** `(-n^3, 0, n)` satisfies the equation for all `n : ℤ` — `ring`.
3. **Injectivity.** The map `ℕ → ℤ × ℤ × ℤ`, `n ↦ (0, ↑n, 0)`, is injective since
   the y-component `↑n : ℤ` determines `n : ℕ` uniquely via `Int.ofNat_inj`.
4. **Infinitude.** An injective function from `ℕ` into the solution set implies the
   solution set is infinite (`Set.infinite_range_of_injective`).

## Sorry count: 0

The proof is fully formalised with no axioms beyond Lean's foundations and Mathlib.
-/

/-- The Diophantine equation `x + x^2 * y^2 + z^3 = 0`. -/
def isolution (x y z : ℤ) : Prop := x + x ^ 2 * y ^ 2 + z ^ 3 = 0

/-- The set of all integer solutions to `x + x^2 * y^2 + z^3 = 0`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Family 1: (0, n, 0)

Setting `x = 0` gives `z^3 = 0`, so `z = 0`, and `y` is free.
-/

/-- For any `n : ℤ`, the triple `(0, n, 0)` is a solution.
Proof: `0 + 0^2 * n^2 + 0^3 = 0`. -/
theorem family1 (n : ℤ) : isolution 0 n 0 := by
  unfold isolution; ring

/-! ## Family 2: (-n^3, 0, n)

Setting `y = 0` gives `x + z^3 = 0`, solved by `x = -z^3`.
-/

/-- For any `n : ℤ`, the triple `(-n^3, 0, n)` is a solution.
Proof: `(-n^3) + (-n^3)^2 * 0^2 + n^3 = -n^3 + 0 + n^3 = 0`. -/
theorem family2 (n : ℤ) : isolution (-(n ^ 3)) 0 n := by
  unfold isolution; ring

/-! ## Small explicit witnesses -/

theorem sol_0_0_0   : isolution 0 0 0   := by norm_num [isolution]
theorem sol_0_1_0   : isolution 0 1 0   := by norm_num [isolution]
theorem sol_0_m1_0  : isolution 0 (-1) 0 := by norm_num [isolution]
theorem sol_m1_0_1  : isolution (-1) 0 1  := by norm_num [isolution]
theorem sol_1_0_m1  : isolution 1 0 (-1) := by norm_num [isolution]
theorem sol_m8_0_2  : isolution (-8) 0 2  := by norm_num [isolution]
theorem sol_8_0_m2  : isolution 8 0 (-2)  := by norm_num [isolution]
theorem sol_m27_0_3 : isolution (-27) 0 3  := by norm_num [isolution]
theorem sol_27_0_m3 : isolution 27 0 (-3)  := by norm_num [isolution]
-- Sporadic solutions found by brute-force search
theorem sol_m1_1_0    : isolution (-1) 1 0    := by norm_num [isolution]
theorem sol_m1_m1_0   : isolution (-1) (-1) 0  := by norm_num [isolution]
theorem sol_m1_3_m2   : isolution (-1) 3 (-2)  := by norm_num [isolution]
theorem sol_m1_m3_m2  : isolution (-1) (-3) (-2) := by norm_num [isolution]
theorem sol_m8_39_m46 : isolution (-8) 39 (-46) := by norm_num [isolution]
theorem sol_m8_m39_m46 : isolution (-8) (-39) (-46) := by norm_num [isolution]

/-! ## Infinitely many solutions (via Family 1) -/

/-- The map `n ↦ (0, ↑n, 0)` from `ℕ` into the solution set. -/
def natMap (n : ℕ) : ℤ × ℤ × ℤ := (0, (n : ℤ), 0)

/-- Every element of `natMap` is a solution. -/
theorem natMap_mem (n : ℕ) : natMap n ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, isolution, natMap]
  ring

/-- The map `natMap` is injective: the y-component `↑n` uniquely determines `n`. -/
theorem natMap_injective : Function.Injective natMap := by
  intro n1 n2 h
  simp only [natMap, Prod.mk.injEq] at h
  exact_mod_cast h.2.1

/-- The solution set of `x + x^2 * y^2 + z^3 = 0` is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply (Set.infinite_range_of_injective natMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact natMap_mem n
