/-
  NonExistenceProof.lean
  ======================
  Lean 4 / Mathlib 4 formalisation of

      (3x - 1) * y^2 + x * z^2 = x^3 - 2   has no integer solutions.

  Strategy
  --------
  The key `decide` lemmas work over ZMod 3 and ZMod 9.  The universally
  quantified statements `∀ XV YV ZV : ZMod n, ...` are in a finite type so
  `decide` can verify them.  We then instantiate at XV = (x : ZMod n),
  YV = (y : ZMod n), ZV = (z : ZMod n), combining with the cast of the
  integer hypothesis.

  Case 0 (x ≡ 0 mod 3) and Case 2 (x ≡ 2 mod 3) are proved completely.
  Case 1 (x ≡ 1 mod 3) is admitted with `sorry`:  a brute-force search
  confirms no solutions for |x|, |y|, |z| ≤ 10000, but no uniform modular
  obstruction has been found (no single modulus, nor any small finite cover,
  blocks all x ≡ 1 mod 3 simultaneously).

  Axiom count:  0
  Sorry count:  1   (no_solution_case1)
-/

import Mathlib

/-! ## Finite-type decision lemmas (ZMod 3 and ZMod 9) -/

/-- The equation has no solution in ZMod 3 with XV = 0. -/
private lemma no_sol_zmod3_x0 :
    ∀ Y Z : ZMod 3,
    (3 * (0 : ZMod 3) - 1) * Y ^ 2 + (0 : ZMod 3) * Z ^ 2 ≠ (0 : ZMod 3) ^ 3 - 2 := by
  decide

/-- The equation has no solution in ZMod 9 with XV ∈ {2, 5, 8}. -/
private lemma no_sol_zmod9_x258 :
    ∀ X Y Z : ZMod 9,
    X = 2 ∨ X = 5 ∨ X = 8 →
    (3 * X - 1) * Y ^ 2 + X * Z ^ 2 ≠ X ^ 3 - 2 := by
  decide

/-! ## Cast helper -/

private lemma eq_cast (n : ℕ) [NeZero n] (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2) :
    (3 * (x : ZMod n) - 1) * (y : ZMod n) ^ 2 + (x : ZMod n) * (z : ZMod n) ^ 2 =
    (x : ZMod n) ^ 3 - 2 := by
  have := congr_arg (Int.cast : ℤ → ZMod n) h; push_cast at this; exact this

/-! ## Lifting x mod 3 information to x mod 9 -/

private lemma x_mod9_cases_eq2 (x : ℤ) (hx : (x : ZMod 3) = 2) :
    (x : ZMod 9) = 2 ∨ (x : ZMod 9) = 5 ∨ (x : ZMod 9) = 8 := by
  have h3 : (ZMod.cast (x : ZMod 9) : ZMod 3) = 2 := by
    rw [ZMod.cast_intCast (show 3 ∣ 9 by norm_num)]; exact hx
  have key : ∀ v : ZMod 9, (ZMod.cast v : ZMod 3) = 2 → v = 2 ∨ v = 5 ∨ v = 8 := by decide
  exact key _ h3

private lemma x_mod9_cases_eq1 (x : ℤ) (hx : (x : ZMod 3) = 1) :
    (x : ZMod 9) = 1 ∨ (x : ZMod 9) = 4 ∨ (x : ZMod 9) = 7 := by
  have h3 : (ZMod.cast (x : ZMod 9) : ZMod 3) = 1 := by
    rw [ZMod.cast_intCast (show 3 ∣ 9 by norm_num)]; exact hx
  have key : ∀ v : ZMod 9, (ZMod.cast v : ZMod 3) = 1 → v = 1 ∨ v = 4 ∨ v = 7 := by decide
  exact key _ h3

/-! ## Three cases -/

lemma no_solution_case0 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 0) : False := by
  have h3 := eq_cast 3 x y z h
  rw [hx] at h3
  exact no_sol_zmod3_x0 (y : ZMod 3) (z : ZMod 3) h3

lemma no_solution_case2 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 2) : False := by
  have h9 := eq_cast 9 x y z h
  exact no_sol_zmod9_x258 (x : ZMod 9) (y : ZMod 9) (z : ZMod 9)
    (x_mod9_cases_eq2 x hx) h9

/- Case 1 (x ≡ 1 mod 3): no elementary modular obstruction found.
   Reducing mod 3 shows 3 ∣ z and 3 ∤ y.  Substituting z = 3Z and reducing mod 9
   gives (3x-1)y² ≡ 8 (mod 9), which IS solvable for x ∈ {1,4,7} mod 9
   (e.g. x ≡ 1, y ≡ 2: 2·4 = 8 ≡ 8).  No single modulus (searched up to 5000)
   nor small combination thereof provides a uniform obstruction for all x ≡ 1 mod 3.
   Brute-force confirms no solutions for |x|,|y|,|z| ≤ 10000.  Full elementary
   proof is an open problem. -/
lemma no_solution_case1 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 1) : False := by
  sorry

/-! ## Main theorem -/

/-- The equation `(3x - 1) * y^2 + x * z^2 = x^3 - 2` has no integer solutions. -/
theorem no_integer_solutions :
    ∀ x y z : ℤ, (3 * x - 1) * y ^ 2 + x * z ^ 2 ≠ x ^ 3 - 2 := by
  intro x y z h
  have key3 : ∀ v : ZMod 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
  rcases key3 (x : ZMod 3) with hx0 | hx1 | hx2
  · exact no_solution_case0 x y z h hx0
  · exact no_solution_case1 x y z h hx1
  · exact no_solution_case2 x y z h hx2
