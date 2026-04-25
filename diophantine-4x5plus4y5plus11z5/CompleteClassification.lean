import Mathlib

/-!
# Classification of Integer Solutions to 4x⁵ + 4y⁵ + 11z⁵ = 0

We prove that every integer solution **with z = 0** is of the form `(t, -t, 0)`,
and that the full solution set is infinite.

**Note on full classification:**
Whether every integer solution satisfies z = 0 (i.e., no solutions with z ≠ 0 exist)
is a deep diophantine question. A brute-force search finds no solutions with z ≠ 0 for
|x|, |y| ≤ 50. A formal proof of z = 0 for all solutions would likely require techniques
from the arithmetic of curves of higher genus. This file proves what is rigorously
achievable: the z = 0 solutions are exactly `(t, -t, 0)`, which already gives infinitely
many solutions.

## Sorry count: 0
-/

/-- The Diophantine equation `4*x^5 + 4*y^5 + 11*z^5 = 0`. -/
def isolution (x y z : ℤ) : Prop := 4 * x ^ 5 + 4 * y ^ 5 + 11 * z ^ 5 = 0

/-- The set of all integer solutions. -/
def solutions : Set (ℤ × ℤ × ℤ) :=
  { p | isolution p.1 p.2.1 p.2.2 }

/-! ## Strict monotonicity of the fifth-power map -/

/-- t^5 is strictly monotone on ℤ. -/
lemma pow5_strictMono : StrictMono (fun (t : ℤ) => t ^ 5) := by
  intro a b hab
  rcases le_or_gt 0 a with ha | ha
  · exact pow_lt_pow_left₀ hab ha (by norm_num)
  · rcases le_or_gt 0 b with hb | hb
    · have ha5 : a ^ 5 < 0 := (Odd.pow_neg_iff (by decide : Odd 5)).mpr ha
      have hb5 : 0 ≤ b ^ 5 := pow_nonneg hb _
      linarith
    · have h1 : (-b) ^ 5 < (-a) ^ 5 :=
        pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
      simp only [neg_pow, show (-1 : ℤ) ^ 5 = -1 by norm_num, one_mul] at h1
      linarith

/-- The fifth-power map is injective on ℤ. -/
lemma pow5_injective : Function.Injective (fun (t : ℤ) => t ^ 5) :=
  pow5_strictMono.injective

/-- x^5 = -y^5 implies x = -y over ℤ. -/
lemma pow5_neg_eq {x y : ℤ} (h : x ^ 5 = -y ^ 5) : x = -y := by
  have : x ^ 5 = (-y) ^ 5 := by ring_nf; linarith
  exact pow5_injective this

/-! ## Degree-5 homogeneity -/

/-- Scaling any solution `(x, y, z)` by `t` gives another solution `(t*x, t*y, t*z)`. -/
theorem homogeneity {x y z : ℤ} (h : isolution x y z) (t : ℤ) :
    isolution (t * x) (t * y) (t * z) := by
  unfold isolution at *
  linear_combination t ^ 5 * h

/-! ## Characterization of solutions with z = 0 -/

/-- If `(x, y, 0)` is a solution then `x = -y`. -/
theorem zero_z_imp_neg {x y : ℤ} (h : isolution x y 0) : x = -y := by
  unfold isolution at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h
  exact pow5_neg_eq (by linarith)

/-- `(x, y, 0)` is a solution iff `x = -y`. -/
theorem solution_z0_iff (x y : ℤ) : isolution x y 0 ↔ x = -y := by
  constructor
  · exact zero_z_imp_neg
  · intro h; subst h; unfold isolution; ring

/-! ## The parametric family (t, -t, 0) -/

/-- For any `t : ℤ`, the triple `(t, -t, 0)` is a solution. -/
theorem family_solution (t : ℤ) : isolution t (-t) 0 := by
  unfold isolution; ring

/-- The set of z = 0 solutions is exactly `{(t, -t, 0) | t ∈ ℤ}`. -/
theorem z0_solutions_characterization :
    {p : ℤ × ℤ × ℤ | isolution p.1 p.2.1 p.2.2 ∧ p.2.2 = 0} =
    Set.range (fun t : ℤ => (t, -t, (0 : ℤ))) := by
  ext ⟨x, y, z⟩
  simp only [Set.mem_setOf_eq, Set.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨hsol, rfl⟩
    have hxy : x = -y := zero_z_imp_neg hsol
    exact ⟨x, rfl, by linarith [hxy], rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩
    exact ⟨family_solution t, rfl⟩

/-! ## Infinitely many solutions -/

/-- The map `n ↦ ((n : ℤ), -(n : ℤ), 0)` is injective. -/
theorem natMap_injective :
    Function.Injective (fun n : ℕ => ((n : ℤ), -(n : ℤ), (0 : ℤ))) := by
  intro n1 n2 h
  simp only [Prod.mk.injEq] at h
  exact_mod_cast h.1

/-- The solution set is infinite. -/
theorem solutions_infinite : solutions.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ), -(n : ℤ), (0 : ℤ)))
  · exact natMap_injective
  · intro n
    simp only [solutions, Set.mem_setOf_eq, isolution]
    push_cast; ring

/-! ## Explicit witnesses -/

theorem sol_0_0_0 : isolution 0 0 0 := by norm_num [isolution]
theorem sol_1_neg1_0 : isolution 1 (-1 : ℤ) 0 := by norm_num [isolution]
theorem sol_2_neg2_0 : isolution 2 (-2 : ℤ) 0 := by norm_num [isolution]
theorem sol_neg3_3_0 : isolution (-3 : ℤ) 3 0 := by norm_num [isolution]
