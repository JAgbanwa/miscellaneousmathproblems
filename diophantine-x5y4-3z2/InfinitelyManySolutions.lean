import Mathlib

/-!
# Infinitely Many Integer Solutions to x⁵ + y⁴ = 3z²

We prove that the Diophantine equation `x^5 + y^4 = 3*z^2` has infinitely many
integer solutions.

## Proof outline

1. **Primary parametric family.**  Setting $y = 0$ reduces the equation to $x^5 = 3z^2$.
   Taking $x = 3a^2$ and $z = 9a^5$ gives:
   $(3a^2)^5 = 3^5 a^{10} = 243 a^{10}$ and $3(9a^5)^2 = 3 \cdot 81 a^{10} = 243 a^{10}$.
   Hence $(3a^2, 0, 9a^5)$ is a solution for every $a : \mathbb{Z}$.
   Proof: a single `ring` computation.

2. **Secondary parametric family.**  The triple $(2, 2, 4)$ is a seed solution:
   $2^5 + 2^4 = 32 + 16 = 48 = 3 \cdot 16 = 3 \cdot 4^2$.
   By weighted homogeneity (weights $\mathrm{wt}(x)=4$, $\mathrm{wt}(y)=5$, $\mathrm{wt}(z)=10$,
   equation degree 20), the family $(2t^4, 2t^5, 4t^{10})$ satisfies the equation
   for all $t : \mathbb{Z}$:
   $(2t^4)^5 + (2t^5)^4 = 32t^{20} + 16t^{20} = 48t^{20} = 3(4t^{10})^2$.
   Proof: a single `ring` computation.

3. **Injectivity.**  The map $n \mapsto (3n^2, 0, 9n^5) : \mathbb{N} \to \mathbb{Z}^3$
   is injective, since $n \mapsto n^2$ is strictly monotone on $\mathbb{N}$.

4. **Infinitude.**  An injective function from $\mathbb{N}$ into the solution set implies
   the solution set is infinite.

## Sorry count: 0

The proof is fully formalised.
-/

/-- The Diophantine equation `x^5 + y^4 = 3*z^2`. -/
def isolution (x y z : ℤ) : Prop := x ^ 5 + y ^ 4 = 3 * z ^ 2

/-- The set of all integer solutions to `x^5 + y^4 = 3*z^2`. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Primary parametric family -/

/-- For any `a : ℤ`, the triple `(3*a^2, 0, 9*a^5)` is a solution.
Proof: `(3*a^2)^5 + 0^4 = 3^5*a^10 = 243*a^10 = 3*(9*a^5)^2`. -/
theorem parametric_solution (a : ℤ) :
    isolution (3 * a ^ 2) 0 (9 * a ^ 5) := by
  unfold isolution
  ring

/-! ## Secondary parametric family -/

/-- For any `t : ℤ`, the triple `(2*t^4, 2*t^5, 4*t^10)` is a solution.
Proof: `(2*t^4)^5 + (2*t^5)^4 = 32*t^20 + 16*t^20 = 48*t^20 = 3*(4*t^10)^2`. -/
theorem parametric_solution2 (t : ℤ) :
    isolution (2 * t ^ 4) (2 * t ^ 5) (4 * t ^ 10) := by
  unfold isolution
  ring

/-! ## Small explicit witnesses -/

theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_3_0_9 : isolution 3 0 9 := by norm_num [isolution]
theorem sol_3_0_neg9 : isolution 3 0 (-9 : ℤ) := by norm_num [isolution]
theorem sol_neg1_1_0 : isolution (-1 : ℤ) 1 0 := by norm_num [isolution]
theorem sol_neg1_neg1_0 : isolution (-1 : ℤ) (-1 : ℤ) 0 := by norm_num [isolution]
theorem sol_2_2_4 : isolution 2 2 4 := by norm_num [isolution]
theorem sol_2_neg2_4 : isolution 2 (-2 : ℤ) 4 := by norm_num [isolution]
theorem sol_12_0_288 : isolution 12 0 288 := by norm_num [isolution]

/-! ## Infinitely many solutions -/

/-- The parametric map `n ↦ (3*(n:ℤ)^2, 0, 9*(n:ℤ)^5)` from `ℕ` into
    the solution set. -/
def natMap (n : ℕ) : ℤ × ℤ × ℤ := (3 * (n : ℤ) ^ 2, 0, 9 * (n : ℤ) ^ 5)

/-- Every element of the primary parametric family is a solution. -/
theorem natMap_mem (n : ℕ) : natMap n ∈ solutions := by
  simp only [solutions, Set.mem_setOf_eq, isolution, natMap]
  ring

/-- The map `n ↦ n^2` is strictly monotone on `ℕ`. -/
private theorem pow2_strictMono : StrictMono (fun n : ℕ => n ^ 2) := by
  intro a b hab
  exact Nat.pow_lt_pow_left hab (by norm_num)

/-- The parametric map is injective (injectivity follows from the first component
    `n ↦ 3*n^2` being strictly monotone on `ℕ`). -/
theorem natMap_injective : Function.Injective natMap := by
  intro n1 n2 h
  simp only [natMap, Prod.mk.injEq] at h
  have h2 : (n1 : ℤ) ^ 2 = (n2 : ℤ) ^ 2 :=
    mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) h.1
  have h3 : n1 ^ 2 = n2 ^ 2 := by exact_mod_cast h2
  exact pow2_strictMono.injective h3

/-- The solution set of `x^5 + y^4 = 3*z^2` is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply (Set.infinite_range_of_injective natMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact natMap_mem n
