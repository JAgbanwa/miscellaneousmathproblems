import Mathlib

/-!
# Infinitely Many Integer Solutions to x⁴ + 4y³ + z³ = 0

We prove that the Diophantine equation `x^4 + 4*y^3 + z^3 = 0` has infinitely many
integer solutions.

## Key structural observation — weighted homogeneity

Assign weights `wt(x) = 3`, `wt(y) = 4`, `wt(z) = 4`.  Every term has weighted degree 12:
  `(x^4)`: weighted degree 4·3 = 12,
  `(4*y^3)`: weighted degree 3·4 = 12,
  `(z^3)`: weighted degree 3·4 = 12.

Consequently, if `(a, b, c)` is any integer solution, then `(t^3*a, t^4*b, t^4*c)` is also
a solution for every `t : ℤ`, since
  `(t^3*a)^4 + 4*(t^4*b)^3 + (t^4*c)^3 = t^12 * (a^4 + 4*b^3 + c^3) = 0`.

It therefore suffices to exhibit a single non-trivial **seed** solution, from which the
scaling produces an infinite parametric family.

## Proof outline

1. **Primary parametric family (Family 1).** Setting `y = 0` reduces the equation to
   `x^4 + z^3 = 0`, solved by `x = t^3`, `z = -t^4` for any `t : ℤ`:
   `(t^3)^4 + 4*0^3 + (-t^4)^3 = t^12 + 0 - t^12 = 0`.
   Seed: `(1, 0, -1)`.  Proof: a single `ring` computation.

2. **Secondary parametric family (Family 2).** Setting `z = -y` reduces the equation to
   `x^4 + 3*y^3 = 0`, solved by `x = 3*t^3`, `y = -3*t^4` for any `t : ℤ`:
   `(3*t^3)^4 + 4*(-3*t^4)^3 + (3*t^4)^3 = 81*t^12 - 108*t^12 + 27*t^12 = 0`.
   Seed: `(3, -3, 3)`.  Proof: a single `ring` computation.

3. **Tertiary parametric family (Family 3).** Setting `z = 0` reduces the equation to
   `x^4 + 4*y^3 = 0`, solved by `x = -4*t^3`, `y = -4*t^4` for any `t : ℤ`:
   `(-4*t^3)^4 + 4*(-4*t^4)^3 + 0^3 = 256*t^12 - 256*t^12 = 0`.
   Seed: `(-4, -4, 0)`.  Proof: a single `ring` computation.

4. **Quaternary parametric family (Family 4).** Setting `y = z` reduces the equation to
   `x^4 + 5*y^3 = 0`, solved by `x = -5*t^3`, `y = -5*t^4` for any `t : ℤ`:
   `(-5*t^3)^4 + 4*(-5*t^4)^3 + (-5*t^4)^3 = 625*t^12 - 500*t^12 - 125*t^12 = 0`.
   Seed: `(-5, -5, -5)`.  Proof: a single `ring` computation.

5. **Injectivity.** The map `n ↦ ((n : ℤ)^3, 0, -((n : ℤ)^4)) : ℕ → ℤ × ℤ × ℤ`
   is injective, because `n ↦ n^3` is strictly monotone on `ℕ` (positive exponent).

6. **Infinitude.** An injective function from `ℕ` into the solution set implies the
   solution set is infinite.

## Sorry count: 0

The proof is fully formalised.
-/

/-- The Diophantine equation `x^4 + 4*y^3 + z^3 = 0`. -/
def isolution (x y z : ℤ) : Prop := x ^ 4 + 4 * y ^ 3 + z ^ 3 = 0

/-- The set of all integer solutions to `x^4 + 4*y^3 + z^3 = 0`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Family 1: (t^3, 0, -t^4)

Setting `y = 0` reduces to `x^4 + z^3 = 0`, solved by `(x, z) = (t^3, -t^4)`.
-/

/-- For any `t : ℤ`, the triple `(t^3, 0, -t^4)` is a solution.
Proof: `(t^3)^4 + 4*0^3 + (-t^4)^3 = t^12 + 0 - t^12 = 0`. -/
theorem family1 (t : ℤ) :
    isolution (t ^ 3) 0 (-(t ^ 4)) := by
  unfold isolution; ring

/-! ## Family 2: (3*t^3, -3*t^4, 3*t^4)

Setting `z = -y` reduces to `x^4 + 3*y^3 = 0`, solved by `x = 3*t^3`, `y = -3*t^4`.
-/

/-- For any `t : ℤ`, the triple `(3*t^3, -3*t^4, 3*t^4)` is a solution.
Proof: `(3*t^3)^4 + 4*(-3*t^4)^3 + (3*t^4)^3 = 81*t^12 - 108*t^12 + 27*t^12 = 0`. -/
theorem family2 (t : ℤ) :
    isolution (3 * t ^ 3) (-3 * t ^ 4) (3 * t ^ 4) := by
  unfold isolution; ring

/-! ## Family 3: (-4*t^3, -4*t^4, 0)

Setting `z = 0` reduces to `x^4 + 4*y^3 = 0`, solved by `x = -4*t^3`, `y = -4*t^4`.
-/

/-- For any `t : ℤ`, the triple `(-4*t^3, -4*t^4, 0)` is a solution.
Proof: `(-4*t^3)^4 + 4*(-4*t^4)^3 + 0^3 = 256*t^12 - 256*t^12 = 0`. -/
theorem family3 (t : ℤ) :
    isolution (-4 * t ^ 3) (-4 * t ^ 4) 0 := by
  unfold isolution; ring

/-! ## Family 4: (-5*t^3, -5*t^4, -5*t^4)

Setting `y = z` reduces to `x^4 + 5*y^3 = 0`, solved by `x = -5*t^3`, `y = -5*t^4`.
-/

/-- For any `t : ℤ`, the triple `(-5*t^3, -5*t^4, -5*t^4)` is a solution.
Proof: `(-5*t^3)^4 + 4*(-5*t^4)^3 + (-5*t^4)^3 = 625*t^12 - 500*t^12 - 125*t^12 = 0`. -/
theorem family4 (t : ℤ) :
    isolution (-5 * t ^ 3) (-5 * t ^ 4) (-5 * t ^ 4) := by
  unfold isolution; ring

/-! ## Family 5: (4*t^3, 4*t^4, -8*t^4)

Seed `(-4, 4, -8)`: setting `y = -x` and `z = 2x` reduces to `x^3*(x+4) = 0`,
gving seed `x = -4`.  By weighted scaling: `(4*t^3, 4*t^4, -8*t^4)` for all `t`.
-/

/-- For any `t : ℤ`, the triple `(4*t^3, 4*t^4, -8*t^4)` is a solution.
Proof: `(4*t^3)^4 + 4*(4*t^4)^3 + (-8*t^4)^3 = 256*t^12 + 256*t^12 - 512*t^12 = 0`. -/
theorem family5 (t : ℤ) :
    isolution (4 * t ^ 3) (4 * t ^ 4) (-8 * t ^ 4) := by
  unfold isolution; ring

/-! ## Family 6: (12*t^3, -12*t^4, -24*t^4)

Seed `(-12, -12, -24)`: setting `z = 2y` reduces to `x^4 + 12*y^3 = 0`,
solved by `x = -12*t^3`, `y = -12*t^4`.  By weighted scaling: `(12*t^3, -12*t^4, -24*t^4)`.
-/

/-- For any `t : ℤ`, the triple `(12*t^3, -12*t^4, -24*t^4)` is a solution.
Proof: `(12*t^3)^4 + 4*(-12*t^4)^3 + (-24*t^4)^3 = 20736*t^12 - 6912*t^12 - 13824*t^12 = 0`. -/
theorem family6 (t : ℤ) :
    isolution (12 * t ^ 3) (-12 * t ^ 4) (-24 * t ^ 4) := by
  unfold isolution; ring

/-! ## Family 7: (-5*t^3, -10*t^4, 15*t^4)

Seed `(-5, -10, 15)`: setting `y = 2x` and `z = -3x` reduces to `x^3*(x+5) = 0`,
giving seed `x = -5`.  By weighted scaling: `(-5*t^3, -10*t^4, 15*t^4)` for all `t`.
-/

/-- For any `t : ℤ`, the triple `(-5*t^3, -10*t^4, 15*t^4)` is a solution.
Proof: `(-5*t^3)^4 + 4*(-10*t^4)^3 + (15*t^4)^3 = 625*t^12 - 4000*t^12 + 3375*t^12 = 0`. -/
theorem family7 (t : ℤ) :
    isolution (-5 * t ^ 3) (-10 * t ^ 4) (15 * t ^ 4) := by
  unfold isolution; ring

/-! ## Small explicit witnesses -/

theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_1_0_neg1 : isolution 1 0 (-1) := by norm_num [isolution]
theorem sol_neg1_0_neg1 : isolution (-1) 0 (-1) := by norm_num [isolution]
theorem sol_3_neg3_3 : isolution 3 (-3) 3 := by norm_num [isolution]
theorem sol_neg3_neg3_3 : isolution (-3) (-3) 3 := by norm_num [isolution]
theorem sol_neg4_neg4_0 : isolution (-4) (-4) 0 := by norm_num [isolution]
theorem sol_4_neg4_0 : isolution 4 (-4) 0 := by norm_num [isolution]
theorem sol_neg5_neg5_neg5 : isolution (-5) (-5) (-5) := by norm_num [isolution]
theorem sol_5_neg5_neg5 : isolution 5 (-5) (-5) := by norm_num [isolution]
theorem sol_8_0_neg16 : isolution 8 0 (-16) := by norm_num [isolution]
theorem sol_neg8_0_neg16 : isolution (-8) 0 (-16) := by norm_num [isolution]
-- Extra seeds found by brute-force search
theorem sol_neg4_4_neg8 : isolution (-4) 4 (-8) := by norm_num [isolution]
theorem sol_4_4_neg8 : isolution 4 4 (-8) := by norm_num [isolution]
theorem sol_neg5_neg10_15 : isolution (-5) (-10) 15 := by norm_num [isolution]
theorem sol_5_neg10_15 : isolution 5 (-10) 15 := by norm_num [isolution]
theorem sol_neg12_neg12_neg24 : isolution (-12) (-12) (-24) := by norm_num [isolution]
theorem sol_12_neg12_neg24 : isolution 12 (-12) (-24) := by norm_num [isolution]

/-! ## Infinitely many solutions -/

/-- The map `n ↦ ((n : ℤ)^3, 0, -((n : ℤ)^4))` from `ℕ` into the solution set. -/
def natMap (n : ℕ) : ℤ × ℤ × ℤ := ((n : ℤ) ^ 3, 0, -((n : ℤ) ^ 4))

/-- Every element of Family 1 (restricted to `ℕ`) is a solution. -/
theorem natMap_mem (n : ℕ) : natMap n ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, isolution, natMap]
  ring

/-- The map `n ↦ n^3` is strictly monotone on `ℕ`. -/
private theorem pow3_strictMono : StrictMono (fun n : ℕ => n ^ 3) := by
  intro a b hab
  exact Nat.pow_lt_pow_left hab (by norm_num)

/-- The parametric map `natMap` is injective (the first component `n ↦ n^3` is
    strictly increasing on `ℕ`, hence injective). -/
theorem natMap_injective : Function.Injective natMap := by
  intro n1 n2 h
  simp only [natMap, Prod.mk.injEq] at h
  have h3 : (n1 : ℤ) ^ 3 = (n2 : ℤ) ^ 3 := h.1
  have h3n : n1 ^ 3 = n2 ^ 3 := by exact_mod_cast h3
  exact pow3_strictMono.injective h3n

/-- The solution set of `x^4 + 4*y^3 + z^3 = 0` is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply (Set.infinite_range_of_injective natMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact natMap_mem n
