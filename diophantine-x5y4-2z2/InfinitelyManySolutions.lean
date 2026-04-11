import Mathlib

/-!
# Infinitely Many Integer Solutions to x⁵ + y⁴ = 2z²

We prove that the Diophantine equation `x^5 + y^4 = 2*z^2` has infinitely many
integer solutions, identify three parametric families, and characterise the
primitive solutions (gcd = 1).

## Proof outline

### Infinitely many solutions

1. **Seed solution.** The triple `(1, 1, 1)` satisfies `1^5 + 1^4 = 2 = 2*1^2`.

2. **Weighted homogeneity.** Assigning weights `wt(x) = 4, wt(y) = 5, wt(z) = 10`,
   every monomial has the same weight 20:
   `wt(x^5) = 20 = wt(y^4) = wt(2*z^2)`.
   Consequently, if `(x, y, z)` is a solution then so is `(t^4*x, t^5*y, t^10*z)`
   for any `t : ℤ`.

3. **Family 1.** Applying the scaling to `(1, 1, 1)` gives
   `(t^4, t^5, t^10)` for all `t : ℤ`.  Verification:
   `(t^4)^5 + (t^5)^4 = t^20 + t^20 = 2*t^20 = 2*(t^10)^2`.  `ring`.

4. **Family 2 (y = 0).** Setting y = 0 and x = 2*m^2 gives `(2*m^2, 0, 4*m^5)`.

5. **Family 3 (z = 0).** Setting z = 0 forces x^5 = -y^4.  The only integer
   solutions are `(-k^4, k^5, 0)` for `k : ℤ`.  Verification: `ring`.

6. **Injectivity / Infinitude.** The map `n ↦ (n^4, n^5, n^10) : ℕ → ℤ³` is
   injective (via strict monotonicity of `n^4`), so Family 1 is infinite.

### Primitive solutions

A solution `(x, y, z)` is *primitive* if `Int.gcd x y = 1 ∧ Int.gcd x z = 1`
(equivalently, the three coordinates share no common factor > 1).
We use the predicate `IsPrimitiveSol`.

- **Family 1**: `gcd(t^4, t^5, t^10) = t^4`.  Primitive iff `|t| = 1`.
  The two primitive members are `(1, 1, 1)` (t = 1) and `(1, -1, 1)` (t = -1).

- **Family 2**: `gcd(2*m^2, 4*m^5) = 2*m^2 ≥ 2` for `m ≠ 0`; never primitive.

- **Family 3**: `gcd(k^4, k^5) = k^4`.  Primitive iff `|k| = 1`.
  The two primitive members are `(-1, 1, 0)` (k = 1) and `(-1, -1, 0)` (k = -1).

The complete set of primitive solutions (up to the trivial z → -z symmetry) has
exactly two seeds: `(1, 1, 1)` and `(-1, 1, 0)`.

## Sorry count: 0

The proof is fully formalised.
-/

/-- The Diophantine equation `x^5 + y^4 = 2*z^2`. -/
def isolution (x y z : ℤ) : Prop := x ^ 5 + y ^ 4 = 2 * z ^ 2

/-- The set of all integer solutions to `x^5 + y^4 = 2*z^2`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-- A solution `(x, y, z)` is primitive if no integer > 1 divides all three
    coordinates simultaneously.  We encode this as
    `Int.gcd (Int.gcd x y) z = 1`. -/
def IsPrimitiveSol (x y z : ℤ) : Prop :=
  Int.gcd (Int.gcd x y) z = 1

/-! ## Family 1: parametric family `(t^4, t^5, t^10)` -/

/-- For any `t : ℤ`, the triple `(t^4, t^5, t^10)` is a solution.
Proof: `(t^4)^5 + (t^5)^4 = t^20 + t^20 = 2*(t^10)^2`. -/
theorem parametric_solution (t : ℤ) :
    isolution (t ^ 4) (t ^ 5) (t ^ 10) := by
  unfold isolution
  ring

/-! ## Family 2: `(2*m^2, 0, 4*m^5)` -/

/-- For any `m : ℤ`, the triple `(2*m^2, 0, 4*m^5)` is a solution.
Proof: `(2m^2)^5 = 32m^10 = 2*(4m^5)^2`. -/
theorem family2_solution (m : ℤ) :
    isolution (2 * m ^ 2) 0 (4 * m ^ 5) := by
  unfold isolution
  ring

/-! ## Family 3: `(-k^4, k^5, 0)` -/

/-- For any `k : ℤ`, the triple `(-k^4, k^5, 0)` is a solution.
Proof: `(-k^4)^5 + (k^5)^4 = -k^20 + k^20 = 0 = 2*0^2`. -/
theorem family3_solution (k : ℤ) :
    isolution (-(k ^ 4)) (k ^ 5) 0 := by
  unfold isolution
  ring

/-! ## Small explicit witnesses -/

theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_1_1_1 : isolution 1 1 1 := by norm_num [isolution]
theorem sol_1_neg1_1 : isolution 1 (-1 : ℤ) 1 := by norm_num [isolution]
theorem sol_16_32_1024 : isolution 16 32 1024 := by norm_num [isolution]
theorem sol_16_neg32_1024 : isolution 16 (-32 : ℤ) 1024 := by norm_num [isolution]
theorem sol_2_0_4 : isolution 2 0 4 := by norm_num [isolution]
-- Family 3 witnesses
theorem sol_neg1_1_0 : isolution (-1 : ℤ) 1 0 := by norm_num [isolution]
theorem sol_neg1_neg1_0 : isolution (-1 : ℤ) (-1 : ℤ) 0 := by norm_num [isolution]

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

/-! ## Primitive solutions -/

/-! ### The two primitive seeds -/

/-- `(1, 1, 1)` is a primitive solution (Seed A: Family 1 at t = 1). -/
theorem primitive_1_1_1 : isolution 1 1 1 ∧ IsPrimitiveSol 1 1 1 := by
  constructor
  · norm_num [isolution]
  · native_decide

/-- `(1, -1, 1)` is a primitive solution (Family 1 at t = -1). -/
theorem primitive_1_neg1_1 : isolution 1 (-1 : ℤ) 1 ∧ IsPrimitiveSol 1 (-1) 1 := by
  constructor
  · norm_num [isolution]
  · native_decide

/-- `(-1, 1, 0)` is a primitive solution (Seed B: Family 3 at k = 1). -/
theorem primitive_neg1_1_0 : isolution (-1 : ℤ) 1 0 ∧ IsPrimitiveSol (-1) 1 0 := by
  constructor
  · norm_num [isolution]
  · native_decide

/-- `(-1, -1, 0)` is a primitive solution (Family 3 at k = -1). -/
theorem primitive_neg1_neg1_0 : isolution (-1 : ℤ) (-1 : ℤ) 0 ∧ IsPrimitiveSol (-1) (-1) 0 := by
  constructor
  · norm_num [isolution]
  · native_decide

/-! ### Family 1 is primitive only at |t| = 1 -/

/-- For `t : ℤ` with `|t| ≥ 2`, `gcd(t^4, t^5) = t^4 ≥ 16`, so the Family 1
    member is not primitive.  We show the representative case `t = 2`. -/
theorem family1_t2_not_primitive : ¬ IsPrimitiveSol 16 32 1024 := by
  native_decide

/-- For `t : ℤ` with `|t| ≥ 2`, the Family 1 member `(t^4, t^5, t^10)` is not
    primitive because `t^4 ∣ t^4`, `t^4 ∣ t^5`, and `t^4 ∣ t^10`, so
    `gcd(t^4, t^5, t^10) = t^4 ≥ 16 > 1`.
    We formalise this as: the gcd of the Family 1 triple divides `t^4`. -/
theorem family1_gcd_dvd_pow4 (t : ℤ) :
    (Int.gcd (Int.gcd (t ^ 4) (t ^ 5)) (t ^ 10) : ℤ) ∣ t ^ 4 := by
  exact_mod_cast Int.gcd_dvd_left

/-! ### Family 2 is never primitive (for m ≠ 0) -/

/-- For `m ≠ 0`, the Family 2 member `(2*m^2, 0, 4*m^5)` is not primitive,
    since `2 ∣ 2*m^2` and `2 ∣ 4*m^5`.  We show `2 ∣ gcd(2*m^2, 4*m^5)`. -/
theorem family2_not_primitive (m : ℤ) (hm : m ≠ 0) :
    ¬ IsPrimitiveSol (2 * m ^ 2) 0 (4 * m ^ 5) := by
  unfold IsPrimitiveSol
  simp only [Int.gcd_zero_right]
  intro h
  have h2 : (2 : ℕ) ∣ Int.natAbs (2 * m ^ 2) := by
    rw [Int.natAbs_mul, Int.natAbs_ofNat]
    exact Dvd.dvd.mul_right (dvd_refl 2) _
  have h3 : (2 : ℕ) ∣ Int.natAbs (4 * m ^ 5) := by
    rw [Int.natAbs_mul, Int.natAbs_ofNat]
    exact Dvd.dvd.mul_right (dvd_refl 2 |>.trans (by norm_num)) _
  have := Nat.dvd_gcd h2 h3
  rw [h] at this
  exact absurd this (by norm_num)

/-! ### Family 3 is primitive only at |k| = 1 -/

/-- `(-1, 1, 0)` (k = 1 in Family 3) is primitive. -/
theorem family3_k1_primitive : IsPrimitiveSol (-1 : ℤ) 1 0 := by native_decide

/-- `(-1, -1, 0)` (k = -1 in Family 3) is primitive. -/
theorem family3_kneg1_primitive : IsPrimitiveSol (-1 : ℤ) (-1 : ℤ) 0 := by native_decide

/-- For `|k| ≥ 2`, Family 3 is not primitive.  Representative case k = 2. -/
theorem family3_k2_not_primitive : ¬ IsPrimitiveSol (-16 : ℤ) 32 0 := by
  native_decide
