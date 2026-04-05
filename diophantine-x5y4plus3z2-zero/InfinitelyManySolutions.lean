import Mathlib

/-!
# Infinitely Many Integer Solutions to x⁵ + y⁴ + 3z² = 0

We prove that the Diophantine equation `x^5 + y^4 + 3*z^2 = 0` has infinitely many
integer solutions.

## Proof outline

1. **Sign constraint.**  Since `y^4 ≥ 0` and `3*z^2 ≥ 0`, the equation forces `x ≤ 0`.
   Writing `x = -a` converts the equation to `y^4 + 3*z^2 = a^5`.

2. **Primary parametric family (Family 1).**  Setting `z = 0` reduces to `x^5 + y^4 = 0`,
   solved by `x = -n^4`, `y = n^5` for any `n : ℤ`:
   `(-n^4)^5 + (n^5)^4 = -n^20 + n^20 = 0`.
   Proof: a single `ring` computation.

3. **Secondary parametric family (Family 2).**  Setting `y = 0` and `x = -3*k^2`,
   `z = 9*k^5` for any `k : ℤ`:
   `(-3*k^2)^5 + 0^4 + 3*(9*k^5)^2 = -243*k^10 + 243*k^10 = 0`.
   Proof: a single `ring` computation.

4. **Tertiary parametric family (Family 3).**  The triple `(-4, 4, 16)` is a seed
   solution (verified by `norm_num`).  By the weighted-homogeneity symmetry
   (weights `wt(x) = 4`, `wt(y) = 5`, `wt(z) = 10`, total degree 20), the triple
   `(-4*t^4, 4*t^5, 16*t^10)` satisfies the equation for all `t : ℤ`:
   `(-4*t^4)^5 + (4*t^5)^4 + 3*(16*t^10)^2 = -1024*t^20 + 256*t^20 + 768*t^20 = 0`.
   Proof: a single `ring` computation.

5. **Injectivity.**  The map `n ↦ (-n^4, n^5, 0) : ℕ → ℤ × ℤ × ℤ` is injective,
   because `n ↦ n^4` is strictly monotone on `ℕ` (for positive exponent).

6. **Infinitude.**  An injective function from `ℕ` into the solution set implies
   the solution set is infinite.

## Sorry count: 0

The proof is fully formalised.
-/

/-- The Diophantine equation `x^5 + y^4 + 3*z^2 = 0`. -/
def isolution (x y z : ℤ) : Prop := x ^ 5 + y ^ 4 + 3 * z ^ 2 = 0

/-- The set of all integer solutions to `x^5 + y^4 + 3*z^2 = 0`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Family 1: (-n^4, n^5, 0) -/

/-- For any `n : ℤ`, the triple `(-n^4, n^5, 0)` is a solution.
Proof: `(-n^4)^5 + (n^5)^4 + 3*0^2 = -n^20 + n^20 + 0 = 0`. -/
theorem family1 (n : ℤ) :
    isolution (-(n ^ 4)) (n ^ 5) 0 := by
  unfold isolution
  ring

/-! ## Family 2: (-3*k^2, 0, 9*k^5) -/

/-- For any `k : ℤ`, the triple `(-3*k^2, 0, 9*k^5)` is a solution.
Proof: `(-3*k^2)^5 + 0^4 + 3*(9*k^5)^2 = -243*k^10 + 243*k^10 = 0`. -/
theorem family2 (k : ℤ) :
    isolution (-3 * k ^ 2) 0 (9 * k ^ 5) := by
  unfold isolution
  ring

/-! ## Family 3: (-4*t^4, 4*t^5, 16*t^10) -/

/-- For any `t : ℤ`, the triple `(-4*t^4, 4*t^5, 16*t^10)` is a solution.
Proof: `(-4*t^4)^5 + (4*t^5)^4 + 3*(16*t^10)^2
       = -1024*t^20 + 256*t^20 + 768*t^20 = 0`. -/
theorem family3 (t : ℤ) :
    isolution (-4 * t ^ 4) (4 * t ^ 5) (16 * t ^ 10) := by
  unfold isolution
  ring

/-! ## Small explicit witnesses -/

theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_neg1_1_0 : isolution (-1) 1 0 := by norm_num [isolution]
theorem sol_neg1_neg1_0 : isolution (-1) (-1 : ℤ) 0 := by norm_num [isolution]
theorem sol_neg3_0_9 : isolution (-3) 0 9 := by norm_num [isolution]
theorem sol_neg3_0_neg9 : isolution (-3) 0 (-9 : ℤ) := by norm_num [isolution]
theorem sol_neg4_4_16 : isolution (-4) 4 16 := by norm_num [isolution]
theorem sol_neg4_neg4_16 : isolution (-4) (-4 : ℤ) 16 := by norm_num [isolution]
theorem sol_neg16_32_0 : isolution (-16) 32 0 := by norm_num [isolution]
theorem sol_neg12_0_288 : isolution (-12) 0 288 := by norm_num [isolution]

/-! ## Infinitely many solutions -/

/-- The map `n ↦ (-(n : ℤ)^4, (n : ℤ)^5, 0)` from `ℕ` into the solution set. -/
def natMap (n : ℕ) : ℤ × ℤ × ℤ := (-(n : ℤ) ^ 4, (n : ℤ) ^ 5, 0)

/-- Every element of Family 1 is a solution. -/
theorem natMap_mem (n : ℕ) : natMap n ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, isolution, natMap]
  ring

/-- The map `n ↦ n^4` is strictly monotone on `ℕ`. -/
private theorem pow4_strictMono : StrictMono (fun n : ℕ => n ^ 4) := by
  intro a b hab
  exact Nat.pow_lt_pow_left hab (by norm_num)

/-- The parametric map is injective (the first component `n ↦ n^4` strictly
    increases). -/
theorem natMap_injective : Function.Injective natMap := by
  intro n1 n2 h
  simp only [natMap, Prod.mk.injEq] at h
  have h4 : (n1 : ℤ) ^ 4 = (n2 : ℤ) ^ 4 := neg_inj.mp h.1
  have h4n : n1 ^ 4 = n2 ^ 4 := by exact_mod_cast h4
  exact pow4_strictMono.injective h4n

/-- The solution set of `x^5 + y^4 + 3*z^2 = 0` is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply (Set.infinite_range_of_injective natMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact natMap_mem n
