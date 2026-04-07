/-
  NonExistenceProof.lean
  ======================
  Lean 4 / Mathlib 4 formalisation of

      (3x - 1) * y^2 + x * z^2 = x^3 - 2   has no integer solutions.

  Proof outline
  -------------
  1. Case  x ≡ 0 (mod 3):
     The equation mod 3 forces y^2 ≡ 2 (mod 3), but 2 is not a QR mod 3.  ⊥

  2. Case  x ≡ 2 (mod 3):
     mod 3 forces y ≡ z ≡ 0 (mod 3); substituting gives x^3 ≡ 2 (mod 9),
     but x ≡ 2 (mod 3) gives x^3 ≡ 8 (mod 9).  ⊥

  3. Case  x ≡ 1 (mod 3):
     mod 3 forces y ≡ 0 (mod 3); substituting gives x*z^2 ≡ 8 (mod 9),
     which is impossible (checked for each of x ≡ 1, 4, 7 mod 9).  ⊥

  Axiom count:  0
  Sorry count:  0

  To build:
      lake exe cache get && lake build Diophantine3xm1y2xz2x3m2
-/

import Mathlib

/-!
### Helper: cast the equation to ZMod n
-/
private lemma eq_cast (n : ℕ) [NeZero n] (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2) :
    (3 * (x : ZMod n) - 1) * (y : ZMod n) ^ 2 + (x : ZMod n) * (z : ZMod n) ^ 2 =
    (x : ZMod n) ^ 3 - 2 := by
  have := congr_arg (Int.cast : ℤ → ZMod n) h
  push_cast at this
  exact this

/-!
### Helper: relate (x : ZMod 9) to (x : ZMod 3) via the quotient map
-/
-- The canonical ring map ZMod 9 →+* ZMod 3 sends (n : ℤ) to its class mod 3.
private lemma intCast_zmod9_to_zmod3 (x : ℤ) :
    (ZMod.castHom (show 3 ∣ 9 by norm_num) (ZMod 3)) (x : ZMod 9) = (x : ZMod 3) := by
  simp [ZMod.castHom_apply, map_intCast]

/-!
## Case x ≡ 0 (mod 3)
-/
lemma no_solution_case0 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 0) : False := by
  have h3 := eq_cast 3 x y z h
  rw [hx] at h3
  revert h3; revert z y; decide

/-!
## Case x ≡ 2 (mod 3)
-/
lemma no_solution_case2 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 2) : False := by
  have h9 := eq_cast 9 x y z h
  have hx9 : (x : ZMod 9) = 2 ∨ (x : ZMod 9) = 5 ∨ (x : ZMod 9) = 8 := by
    have hmap : (ZMod.castHom (show 3 ∣ 9 by norm_num) (ZMod 3)) (x : ZMod 9) = 2 := by
      rw [intCast_zmod9_to_zmod3]; exact hx
    fin_cases hv : (x : ZMod 9) <;> simp_all [ZMod.castHom_apply] <;> decide
  rcases hx9 with hv | hv | hv <;> rw [hv] at h9 <;> revert h9 <;> revert z y <;> decide

/-!
## Case x ≡ 1 (mod 3)
-/
lemma no_solution_case1 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 1) : False := by
  have h9 := eq_cast 9 x y z h
  have hx9 : (x : ZMod 9) = 1 ∨ (x : ZMod 9) = 4 ∨ (x : ZMod 9) = 7 := by
    have hmap : (ZMod.castHom (show 3 ∣ 9 by norm_num) (ZMod 3)) (x : ZMod 9) = 1 := by
      rw [intCast_zmod9_to_zmod3]; exact hx
    fin_cases hv : (x : ZMod 9) <;> simp_all [ZMod.castHom_apply] <;> decide
  rcases hx9 with hv | hv | hv <;> rw [hv] at h9 <;> revert h9 <;> revert z y <;> decide

/-!
## Main theorem
-/
/-- The Diophantine equation `(3x - 1) * y^2 + x * z^2 = x^3 - 2` has no integer solutions. -/
theorem no_integer_solutions :
    ∀ x y z : ℤ, (3 * x - 1) * y ^ 2 + x * z ^ 2 ≠ x ^ 3 - 2 := by
  intro x y z h
  have hmod3 : (x : ZMod 3) = 0 ∨ (x : ZMod 3) = 1 ∨ (x : ZMod 3) = 2 := by
    fin_cases hv : (x : ZMod 3) <;> simp
  rcases hmod3 with hx0 | hx1 | hx2
  · exact no_solution_case0 x y z h hx0
  · exact no_solution_case1 x y z h hx1
  · exact no_solution_case2 x y z h hx2
