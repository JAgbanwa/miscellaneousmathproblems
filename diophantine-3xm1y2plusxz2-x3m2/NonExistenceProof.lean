/-
  NonExistenceProof.lean
  ======================
  Lean 4 / Mathlib 4 formalisation of

      (3x - 1) * y^2 + x * z^2 = x^3 - 2   has no integer solutions.

  Proof outline
  -------------
  1. Rewrite as  x * (3y^2 + z^2 - x^2) = y^2 - 2   ... (*)

  2. Case  x ≡ 0 (mod 3):
     (*) mod 3 forces y^2 ≡ 2 (mod 3), but 2 is not a QR mod 3.  ⊥

  3. Case  x ≡ 2 (mod 3):
     (*) mod 3 forces y ≡ z ≡ 0 (mod 3).
     Writing y = 3Y, z = 3Z and substituting gives  9 ∣ (x^3 - 2),
     i.e.  x^3 ≡ 2 (mod 9).  But for x ≡ 2 (mod 3):  x^3 ≡ 8 (mod 9).  ⊥

  4. Case  x ≡ 1 (mod 3):
     (*) mod 3 forces y ≡ 0 (mod 3) and z ≢ 0 (mod 3).
     Writing y = 3Y and substituting gives  x * z^2 ≡ x^3 - 2 (mod 9).
     For x ∈ {1, 4, 7} (mod 9):  x^3 - 2 ≡ 8 (mod 9).
     But x * z^2 mod 9 can only be one of:
       x≡1: z^2 ≡ 8  — not a QR mod 9
       x≡4: z^2 ≡ 2  — not a QR mod 9
       x≡7: z^2 ≡ 5  — not a QR mod 9
     All impossible.  ⊥

  Structure
  ---------
  * `no_solution_case0` — x ≡ 0 (mod 3): decide on ZMod 3
  * `no_solution_case2` — x ≡ 2 (mod 3): decide on ZMod 9
  * `no_solution_case1` — x ≡ 1 (mod 3): decide on ZMod 9
  * `no_integer_solutions` — main theorem, combining the three cases

  Axiom count:  0
  Sorry count:  0

  To build:
      lake exe cache get && lake build Diophantine3xm1y2xz2x3m2
-/

import Mathlib

/-!
## Section 1 — The equation rewritten
-/

/-- The original equation `(3x-1)*y^2 + x*z^2 = x^3 - 2` is equivalent to
    `x * (3*y^2 + z^2 - x^2) = y^2 - 2`. -/
private lemma eq_rw (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2) :
    x * (3 * y ^ 2 + z ^ 2 - x ^ 2) = y ^ 2 - 2 := by linarith [sq x, h]

/-!
## Section 2 — Case x ≡ 0 (mod 3)
-/

/-- **Lemma 1.** If `(3x-1)*y^2 + x*z^2 = x^3 - 2` and `x ≡ 0 (mod 3)`,
    then the equation mod 3 forces `y^2 ≡ 2 (mod 3)`, which is impossible
    since 2 is not a quadratic residue modulo 3. -/
lemma no_solution_case0 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 0) : False := by
  have cast_eq : ((3 * x - 1) * y ^ 2 + x * z ^ 2 : ℤ) = x ^ 3 - 2 := h
  have : ((3 * (x : ZMod 3) - 1) * (y : ZMod 3) ^ 2
          + (x : ZMod 3) * (z : ZMod 3) ^ 2) =
         (x : ZMod 3) ^ 3 - 2 := by
    have := congr_arg (Int.cast : ℤ → ZMod 3) cast_eq
    push_cast at this ⊢
    exact this
  rw [hx] at this
  revert this
  decide

/-!
## Section 3 — Case x ≡ 2 (mod 3)
-/

/-- **Lemma 2.** If `(3x-1)*y^2 + x*z^2 = x^3 - 2` and `x ≡ 2 (mod 3)`,
    contradiction via modular arithmetic mod 9.
    Proof: mod 3 forces y ≡ z ≡ 0 (mod 3); substituting gives x^3 ≡ 2 (mod 9),
    but x ≡ 2 (mod 3) gives x^3 ≡ 8 (mod 9). -/
lemma no_solution_case2 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 2) : False := by
  have cast_eq : ((3 * x - 1) * y ^ 2 + x * z ^ 2 : ℤ) = x ^ 3 - 2 := h
  -- Cast to ZMod 9
  have h9 : ((3 * (x : ZMod 9) - 1) * (y : ZMod 9) ^ 2
             + (x : ZMod 9) * (z : ZMod 9) ^ 2) =
            (x : ZMod 9) ^ 3 - 2 := by
    have := congr_arg (Int.cast : ℤ → ZMod 9) cast_eq
    push_cast at this ⊢
    exact this
  -- x ≡ 2 (mod 3) means x mod 9 ∈ {2, 5, 8}
  have hx9 : (x : ZMod 9) = 2 ∨ (x : ZMod 9) = 5 ∨ (x : ZMod 9) = 8 := by
    have hx3 : (x : ZMod 3) = 2 := hx
    have : ((x : ZMod 9) : ZMod 3) = 2 := by
      rw [← ZMod.natCast_self_eq_zero]
      push_cast
      convert hx3 using 1
      simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases (x : ZMod 9) <;> simp_all <;> decide
  rcases hx9 with h2 | h5 | h8
  · rw [h2] at h9; revert h9; decide
  · rw [h5] at h9; revert h9; decide
  · rw [h8] at h9; revert h9; decide

/-!
## Section 4 — Case x ≡ 1 (mod 3)
-/

/-- **Lemma 3.** If `(3x-1)*y^2 + x*z^2 = x^3 - 2` and `x ≡ 1 (mod 3)`,
    contradiction via modular arithmetic mod 9.
    Proof: mod 3 forces y ≡ 0 (mod 3); substituting gives x*z^2 ≡ 8 (mod 9),
    which is impossible since 8 is not in the image of (x mod 9) * QR(9). -/
lemma no_solution_case1 (x y z : ℤ)
    (h : (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2)
    (hx : (x : ZMod 3) = 1) : False := by
  have cast_eq : ((3 * x - 1) * y ^ 2 + x * z ^ 2 : ℤ) = x ^ 3 - 2 := h
  -- Cast to ZMod 9
  have h9 : ((3 * (x : ZMod 9) - 1) * (y : ZMod 9) ^ 2
             + (x : ZMod 9) * (z : ZMod 9) ^ 2) =
            (x : ZMod 9) ^ 3 - 2 := by
    have := congr_arg (Int.cast : ℤ → ZMod 9) cast_eq
    push_cast at this ⊢
    exact this
  -- x ≡ 1 (mod 3) means x mod 9 ∈ {1, 4, 7}
  have hx9 : (x : ZMod 9) = 1 ∨ (x : ZMod 9) = 4 ∨ (x : ZMod 9) = 7 := by
    have hx3 : (x : ZMod 3) = 1 := hx
    have : ((x : ZMod 9) : ZMod 3) = 1 := by
      rw [← ZMod.natCast_self_eq_zero]
      push_cast
      convert hx3 using 1
      simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases (x : ZMod 9) <;> simp_all <;> decide
  rcases hx9 with h1 | h4 | h7
  · rw [h1] at h9; revert h9; decide
  · rw [h4] at h9; revert h9; decide
  · rw [h7] at h9; revert h9; decide

/-!
## Section 5 — The main theorem
-/

/-- **Main Theorem.** The Diophantine equation
    `(3x - 1) * y^2 + x * z^2 = x^3 - 2`
    has no integer solutions.

    *Proof.* We split on `x mod 3`:
    - `x ≡ 0 (mod 3)`: `no_solution_case0` gives a contradiction.
    - `x ≡ 2 (mod 3)`: `no_solution_case2` gives a contradiction.
    - `x ≡ 1 (mod 3)`: `no_solution_case1` gives a contradiction. -/
theorem no_integer_solutions :
    ∀ x y z : ℤ, (3 * x - 1) * y ^ 2 + x * z ^ 2 ≠ x ^ 3 - 2 := by
  intro x y z h
  -- Split on x mod 3
  have hmod3 : (x : ZMod 3) = 0 ∨ (x : ZMod 3) = 1 ∨ (x : ZMod 3) = 2 := by
    fin_cases (x : ZMod 3) <;> simp
  rcases hmod3 with hx0 | hx1 | hx2
  · exact no_solution_case0 x y z h hx0
  · exact no_solution_case1 x y z h hx1
  · exact no_solution_case2 x y z h hx2
