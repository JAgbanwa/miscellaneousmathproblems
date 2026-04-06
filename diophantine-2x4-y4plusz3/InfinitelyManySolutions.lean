import Mathlib

/-!
# Infinitely Many Integer Solutions to 2x⁴ - y⁴ + z³ = 0

We prove that the Diophantine equation `2*x^4 - y^4 + z^3 = 0` has infinitely many
integer solutions.

## Proof outline

1. **Weighted homogeneity.**  Assigning weights `wt(x) = wt(y) = 3` and `wt(z) = 4`,
   every monomial has the same weighted degree 12:
   `wt(x^4) = 12 = wt(y^4) = wt(z^3)`.
   Consequently, if `(x, y, z)` is a solution then so is `(n^3*x, n^3*y, n^4*z)`
   for any `n : ℤ`, since the equation is multiplied by `n^12`.

2. **Six parametric families.**  Six infinite (and independent) families of
   integer solutions are exhibited:
   - **Family 1.** Setting `x = 0` gives `z^3 = y^4`, solved by `(0, t^3, t^4)`.
   - **Family 2.** Setting `y = x` gives `x^4 + z^3 = 0`, solved by `(t^3, t^3, -t^4)`.
   - **Family 3.** Setting `y = 0` gives `2*x^4 + z^3 = 0`; taking `x = 4*t^3`
     gives `z = -8*t^4`, yielding `(4*t^3, 0, -8*t^4)`.
   - **Family 4.** Setting `x = 14*t^3, y = 21*t^3, z = 49*t^4` rests on the
     algebraic identity `2*(14)^4 - (21)^4 + (49)^3 = 0`, equivalently
     `2*2^4 - 3^4 + 7^2 = 32 - 81 + 49 = 0`.
   - **Family 5.** Setting `x = 196*t^3, y = 392*t^3, z = 2744*t^4` rests on the
     identity `2*4^4 - 8^4 + 8^3*7 = 512 - 4096 + 3584 = 0`.
     Seed: `(196, 392, 2744) = (4*7^2, 8*7^2, 8*7^3)`.
   - **Family 6.** Setting `x = 1922*t^3, y = 961*t^3, z = -29791*t^4` rests on
     the identity `2*2^4 - 1^4 - 31 = 32 - 1 - 31 = 0`.
     Seed: `(1922, 961, -29791) = (2*31^2, 31^2, -31^3)`.

3. **Injectivity.**  The map `n ↦ ((0 : ℤ), (n : ℤ)^3, (n : ℤ)^4) : ℕ → ℤ × ℤ × ℤ`
   is injective, because `n ↦ n^3` is strictly monotone on `ℕ`
   (by `Nat.pow_lt_pow_left`).

4. **Infinitude.**  An injective function from `ℕ` into the solution set implies
   the solution set is infinite.

## Sorry count: 0

The proof is fully formalised with zero axioms beyond Lean's foundations and Mathlib.
-/

/-- The Diophantine equation `2*x^4 - y^4 + z^3 = 0`. -/
def isolution (x y z : ℤ) : Prop := 2 * x ^ 4 - y ^ 4 + z ^ 3 = 0

/-- The set of all integer solutions to `2*x^4 - y^4 + z^3 = 0`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Weighted homogeneity -/

/-- Scaling any solution `(x, y, z)` by the weighted factors `(n^3 * x, n^3 * y, n^4 * z)`
gives another solution.
Proof: `2*(n^3*x)^4 - (n^3*y)^4 + (n^4*z)^3 = n^12*(2*x^4 - y^4 + z^3) = n^12*0 = 0`. -/
theorem weightedHomogeneity (x y z : ℤ) (h : isolution x y z) (n : ℤ) :
    isolution (n ^ 3 * x) (n ^ 3 * y) (n ^ 4 * z) := by
  unfold isolution at *
  linear_combination n ^ 12 * h

/-! ## Family 1: (0, t³, t⁴) -/

/-- For any `t : ℤ`, the triple `(0, t^3, t^4)` is a solution.
Derivation: setting `x = 0` gives `z^3 = y^4`; the parametrisation `y = t^3`, `z = t^4`
satisfies this since `(t^4)^3 = t^12 = (t^3)^4`.
Proof: `2*0 - (t^3)^4 + (t^4)^3 = -t^12 + t^12 = 0`. -/
theorem family1 (t : ℤ) : isolution 0 (t ^ 3) (t ^ 4) := by
  unfold isolution
  ring

/-! ## Family 2: (t³, t³, -t⁴) -/

/-- For any `t : ℤ`, the triple `(t^3, t^3, -t^4)` is a solution.
Derivation: setting `y = x` reduces to `x^4 + z^3 = 0`, solved by `x = t^3`, `z = -t^4`.
Proof: `2*t^12 - t^12 + (-t^4)^3 = t^12 - t^12 = 0`. -/
theorem family2 (t : ℤ) : isolution (t ^ 3) (t ^ 3) (-(t ^ 4)) := by
  unfold isolution
  ring

/-! ## Family 3: (4*t³, 0, -8*t⁴) -/

/-- For any `t : ℤ`, the triple `(4*t^3, 0, -8*t^4)` is a solution.
Derivation: setting `y = 0` gives `2*x^4 + z^3 = 0`; taking `x = 4*t^3` gives
`2*(4*t^3)^4 = 512*t^12 = (8*t^4)^3`, so `z = -8*t^4`.
Proof: `2*(4*t^3)^4 + (-8*t^4)^3 = 512*t^12 - 512*t^12 = 0`. -/
theorem family3 (t : ℤ) : isolution (4 * t ^ 3) 0 (-(8 * t ^ 4)) := by
  unfold isolution
  ring

/-! ## Family 4: (14*t³, 21*t³, 49*t⁴) -/

/-- For any `t : ℤ`, the triple `(14*t^3, 21*t^3, 49*t^4)` is a solution.
Key identity: `2*(14)^4 - (21)^4 + (49)^3 = 7^4*(2*16 - 81) + 7^6 = 7^4*(-49+49) = 0`,
i.e.\ the numerical coincidence `2*2^4 - 3^4 + 7^2 = 32 - 81 + 49 = 0`.
General case follows from weighted homogeneity applied to the seed `(14, 21, 49)`. -/
theorem family4 (t : ℤ) : isolution (14 * t ^ 3) (21 * t ^ 3) (49 * t ^ 4) := by
  unfold isolution
  ring

/-! ## Family 5: (196*t³, 392*t³, 2744*t⁴) -/

/-- For any `t : ℤ`, the triple `(196*t^3, 392*t^3, 2744*t^4)` is a solution.
Seed: `(196, 392, 2744) = (4*7^2, 8*7^2, 8*7^3)`.
Key identity: `2*4^4 - 8^4 + 8^3*7 = 512 - 4096 + 3584 = 0`.
Derivation: setting `y = 2*x` gives `(2 - 16)*x^4 + z^3 = 0`, i.e. `z^3 = 14*x^4`;
taking `x = 4*7^2*t^3` forces `z^3 = 14*(4*7^2)^4*t^12 = 8^9*7^9*t^12 / ... = (8*7^3*t^4)^3`. -/
theorem family5 (t : ℤ) : isolution (196 * t ^ 3) (392 * t ^ 3) (2744 * t ^ 4) := by
  unfold isolution
  ring

/-! ## Family 6: (1922*t³, 961*t³, -29791*t⁴) -/

/-- For any `t : ℤ`, the triple `(1922*t^3, 961*t^3, -29791*t^4)` is a solution.
Seed: `(1922, 961, -29791) = (2*31^2, 31^2, -31^3)`.
Key identity: `2*2^4 - 1^4 - 31 = 32 - 1 - 31 = 0`.
Verification: `2*(2*31^2)^4 - (31^2)^4 + (-31^3)^3 = 31^8*(2*2^4 - 1 - 31) = 31^8*0 = 0`. -/
theorem family6 (t : ℤ) : isolution (1922 * t ^ 3) (961 * t ^ 3) (-(29791 * t ^ 4)) := by
  unfold isolution
  ring


theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_0_1_1 : isolution 0 1 1 := by norm_num [isolution]
theorem sol_0_neg1_1 : isolution 0 (-1 : ℤ) 1 := by norm_num [isolution]
theorem sol_1_1_neg1 : isolution 1 1 (-1 : ℤ) := by norm_num [isolution]
theorem sol_neg1_neg1_neg1 : isolution (-1 : ℤ) (-1 : ℤ) (-1 : ℤ) := by norm_num [isolution]
theorem sol_1_neg1_neg1 : isolution 1 (-1 : ℤ) (-1 : ℤ) := by norm_num [isolution]
theorem sol_4_0_neg8 : isolution 4 0 (-8 : ℤ) := by norm_num [isolution]
theorem sol_neg4_0_neg8 : isolution (-4 : ℤ) 0 (-8 : ℤ) := by norm_num [isolution]
theorem sol_14_21_49 : isolution 14 21 49 := by norm_num [isolution]
theorem sol_neg14_neg21_49 : isolution (-14 : ℤ) (-21 : ℤ) 49 := by norm_num [isolution]
theorem sol_0_8_16 : isolution 0 8 16 := by norm_num [isolution]
theorem sol_8_8_neg16 : isolution 8 8 (-16 : ℤ) := by norm_num [isolution]
theorem sol_196_392_2744 : isolution 196 392 2744 := by norm_num [isolution]
theorem sol_neg196_neg392_2744 : isolution (-196 : ℤ) (-392 : ℤ) 2744 := by norm_num [isolution]
theorem sol_1922_961_neg29791 : isolution 1922 961 (-29791 : ℤ) := by norm_num [isolution]
theorem sol_neg1922_961_neg29791 : isolution (-1922 : ℤ) 961 (-29791 : ℤ) := by norm_num [isolution]

/-! ## Infinitely many solutions -/

/-- The parametric map `n ↦ (0, (n : ℤ)^3, (n : ℤ)^4)` from `ℕ` into
    the solution set (Family 1). -/
def natMap (n : ℕ) : ℤ × ℤ × ℤ := (0, (n : ℤ) ^ 3, (n : ℤ) ^ 4)

/-- Every element of Family 1 is a solution. -/
theorem natMap_mem (n : ℕ) : natMap n ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, isolution, natMap]
  ring

/-- The map `n ↦ n^3` is strictly monotone on `ℕ`. -/
private theorem pow3_strictMono : StrictMono (fun n : ℕ => n ^ 3) := by
  intro a b hab
  exact Nat.pow_lt_pow_left hab (by norm_num)

/-- The parametric map is injective (injectivity follows from the second component
    `n ↦ (n : ℤ)^3` being strictly monotone on `ℕ`). -/
theorem natMap_injective : Function.Injective natMap := by
  intro n1 n2 h
  simp only [natMap, Prod.mk.injEq] at h
  have h3 : n1 ^ 3 = n2 ^ 3 := by exact_mod_cast h.2.1
  exact pow3_strictMono.injective h3

/-- The solution set of `2*x^4 - y^4 + z^3 = 0` is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply (Set.infinite_range_of_injective natMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact natMap_mem n
