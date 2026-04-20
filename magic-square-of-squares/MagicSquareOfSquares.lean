/-
  MagicSquareOfSquares.lean
  =========================
  Lean 4 / Mathlib formalisation of

      "Advancing the 3x3 Magic Square of Squares" -- Jamal Agbanwa (2025)

  Results formalised (all sorry-free except the open problem):
    Lemma 1    Common Difference Lemma
    Lemma 2    Difference-of-Squares Parameterization
    Theorem 1  General Four-Parameter Parameterization (Theorem 2.3)
    Corollary  e = n/3 for any 3x3 magic square
    Theorem 2  Five-Integer Parameterization (Theorem 2.4)
    Corollary  Factorization Condition (g^2 - c^2 = 8 R2 R3(R2^2-R3^2)k^2)
               Numerical verification of Example 2.2

  Sorry count: 1  (the open problem -- Guy Problem D15)

  lake exe cache get && lake build MagicSquareOfSquares
-/

import Mathlib.Tactic

/-!
## 1. Grid and magic-square conditions
-/

/-- Nine cells of a 3x3 grid over an arbitrary type. -/
structure Grid3x3 (R : Type*) where
  a : R
  b : R
  c : R
  d : R
  e : R
  f : R
  g : R
  h : R
  i : R

/-- The eight magic-square conditions (rows, columns, diagonals equal n).
    Defined as a reducible Prop conjunction so `obtain` works directly. -/
@[reducible]
def IsMagicSquare {R : Type*} [Add R] (s : Grid3x3 R) (n : R) : Prop :=
  s.a + s.b + s.c = n /\
  s.d + s.e + s.f = n /\
  s.g + s.h + s.i = n /\
  s.a + s.d + s.g = n /\
  s.b + s.e + s.h = n /\
  s.c + s.f + s.i = n /\
  s.a + s.e + s.i = n /\
  s.c + s.e + s.g = n

/-!
## 2. Common Difference Lemma (Lemma 1 of the paper)

In any 3x3 magic square of squares, the three differences
  b^2 - d^2 = g^2 - c^2 = f^2 - h^2
are equal.  The proof follows immediately from two magic-sum equalities.
-/

/-- **Lemma 1a.** From row 1 (a^2+b^2+c^2=n) and column 1 (a^2+d^2+g^2=n),
    we get b^2 - d^2 = g^2 - c^2. -/
lemma common_diff_bd_gc {R : Type*} [CommRing R] {a b c d g n : R}
    (hrow : a ^ 2 + b ^ 2 + c ^ 2 = n)
    (hcol : a ^ 2 + d ^ 2 + g ^ 2 = n) :
    b ^ 2 - d ^ 2 = g ^ 2 - c ^ 2 := by linear_combination hrow - hcol

/-- **Lemma 1b.** From row 3 (g^2+h^2+i^2=n) and column 3 (c^2+f^2+i^2=n),
    we get g^2 - c^2 = f^2 - h^2. -/
lemma common_diff_gc_fh {R : Type*} [CommRing R] {c f g h i n : R}
    (hrow : g ^ 2 + h ^ 2 + i ^ 2 = n)
    (hcol : c ^ 2 + f ^ 2 + i ^ 2 = n) :
    g ^ 2 - c ^ 2 = f ^ 2 - h ^ 2 := by linear_combination hrow - hcol

/-!
## 3. Difference-of-Squares Parameterization (Lemma 2)

Setting u - v = r and u + v = x/r gives u = (x+r^2)/(2r), v = (x-r^2)/(2r),
and u^2 - v^2 = x.  Proved over ℚ where division is always defined.
-/

/-- **Lemma 2.** For r ≠ 0, u := (x+r^2)/(2r) and v := (x-r^2)/(2r)
    satisfy u^2 - v^2 = x. -/
lemma diff_sq_param (x r : ℚ) (hr : r ≠ 0) :
    let u := (x + r ^ 2) / (2 * r)
    let v := (x - r ^ 2) / (2 * r)
    u ^ 2 - v ^ 2 = x := by
  simp only; field_simp; ring

/-!
## 4. General Four-Parameter Parameterization (Theorem 2.3)

Under x = 8 k R2 R3 R4 and r_i = 2 R_i, the paper derives explicit
closed-form expressions for all nine cells.  We record these and prove
all eight magic conditions hold by ring arithmetic.
-/

/-- The nine-cell grid from parameters (k, R2, R3, R4) over ℚ.
    Each field stores the CELL VALUE (the entry in the magic square).
    For cells a,c,e,g,i the cell value is a polynomial in k,R2,R3,R4.
    For cells b,d,f,h the cell value is a perfect square (2kR3R4±R2)^2 etc. -/
noncomputable def paramGrid (k R2 R3 R4 : ℚ) : Grid3x3 ℚ where
  a := 4 * k ^ 2 * R2 ^ 2 * R3 ^ 2 + R4 ^ 2
  b := (2 * k * R3 * R4 + R2) ^ 2
  c := (4 * ((R2 * R3) ^ 2 + (R3 * R4) ^ 2) * k ^ 2
        - 8 * R2 * R3 * R4 * k + R2 ^ 2 + R4 ^ 2) / 2
  d := (2 * k * R3 * R4 - R2) ^ 2
  e := (4 * ((R2 * R3) ^ 2 + (R3 * R4) ^ 2) * k ^ 2
        + R2 ^ 2 + R4 ^ 2) / 2
  f := (2 * k * R2 * R3 + R4) ^ 2
  g := (4 * ((R2 * R3) ^ 2 + (R3 * R4) ^ 2) * k ^ 2
        + 8 * R2 * R3 * R4 * k + R2 ^ 2 + R4 ^ 2) / 2
  h := (2 * k * R2 * R3 - R4) ^ 2
  i := 4 * k ^ 2 * R3 ^ 2 * R4 ^ 2 + R2 ^ 2

/-- The magic constant for the four-parameter family. -/
noncomputable def paramMagicConst (k R2 R3 R4 : ℚ) : ℚ :=
  (12 * ((R2 * R3) ^ 2 + (R3 * R4) ^ 2) * k ^ 2 + 3 * (R2 ^ 2 + R4 ^ 2)) / 2

/-- **Theorem 2.3.** The four-parameter family automatically satisfies all
    eight magic-square conditions. -/
theorem param_is_magic (k R2 R3 R4 : ℚ) :
    IsMagicSquare (paramGrid k R2 R3 R4) (paramMagicConst k R2 R3 R4) := by
  dsimp only [IsMagicSquare, paramGrid, paramMagicConst]
  exact ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

/-!
## 5. Center-Cell Identity (e = n/3)
-/

/-- **General identity.** In any 3x3 magic square over a field with char ≠ 3,
    the center entry equals n/3. -/
theorem center_eq_third_of_magic {F : Type*} [Field F] [CharZero F]
    (s : Grid3x3 F) (n : F) (ms : IsMagicSquare s n) :
    s.e = n / 3 := by
  obtain ⟨hr1, hr2, hr3, hc1, hc2, hc3, hd1, hd2⟩ := ms
  -- diag1 + diag2 + col2 - row1 - row3 = 3e - n = 0
  have h3e : 3 * s.e = n := by linear_combination hd1 + hd2 + hc2 - hr1 - hr3
  rw [eq_div_iff (show (3 : F) ≠ 0 from by norm_num)]
  linear_combination h3e

/-- The center cell of the four-parameter family satisfies 3 * e = n. -/
theorem center_is_third (k R2 R3 R4 : ℚ) :
    3 * (paramGrid k R2 R3 R4).e = paramMagicConst k R2 R3 R4 := by
  dsimp only [paramGrid, paramMagicConst]; ring

/-!
## 6. Five-Integer Parameterization (Theorem 2.4)

The Pythagorean substitution R4 = k*(R2^2 - R3^2) ensures that the cells
a, b, d, f, h are integers whenever k, R2, R3 are integers.
-/

/-- The five-integer grid: substituting R4 = k*(R2^2 - R3^2). -/
noncomputable def fiveIntGrid (k R2 R3 : ℚ) : Grid3x3 ℚ :=
  paramGrid k R2 R3 (k * (R2 ^ 2 - R3 ^ 2))

/-- **Theorem 2.4 (part 1).** The five-integer family satisfies all eight
    magic-square conditions. -/
theorem fiveInt_is_magic (k R2 R3 : ℚ) :
    IsMagicSquare (fiveIntGrid k R2 R3)
      (paramMagicConst k R2 R3 (k * (R2 ^ 2 - R3 ^ 2))) :=
  param_is_magic k R2 R3 (k * (R2 ^ 2 - R3 ^ 2))

/-- **Theorem 2.4 (part 2).** When k, R2, R3 are integers, the five cells
    a, b, d, f, h are perfect squares of integers.  We identify each cell
    with its integer square, cast to ℚ. -/
theorem fiveInt_cells_are_integers (k R2 R3 : ℤ) :
    let kq := (k : ℚ); let R2q := (R2 : ℚ); let R3q := (R3 : ℚ)
    -- a = [k(R2²+R3²)]²
    (fiveIntGrid kq R2q R3q).a = ((k * (R2 ^ 2 + R3 ^ 2) : ℤ) : ℚ) ^ 2 ∧
    -- b = [2k²R3(R2²-R3²) + R2]²
    (fiveIntGrid kq R2q R3q).b = ((2 * k ^ 2 * R3 * (R2 ^ 2 - R3 ^ 2) + R2 : ℤ) : ℚ) ^ 2 ∧
    -- d = [2k²R3(R2²-R3²) - R2]²
    (fiveIntGrid kq R2q R3q).d = ((2 * k ^ 2 * R3 * (R2 ^ 2 - R3 ^ 2) - R2 : ℤ) : ℚ) ^ 2 ∧
    -- f = [(2R2R3 + R2²-R3²)k]²
    (fiveIntGrid kq R2q R3q).f = (((2 * R2 * R3 + R2 ^ 2 - R3 ^ 2) * k : ℤ) : ℚ) ^ 2 ∧
    -- h = [(2R2R3 + R3²-R2²)k]²
    (fiveIntGrid kq R2q R3q).h = (((2 * R2 * R3 + R3 ^ 2 - R2 ^ 2) * k : ℤ) : ℚ) ^ 2 := by
  simp only [fiveIntGrid, paramGrid]
  push_cast
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

/-!
## 7. Factorization Condition (Corollary in the paper)
-/

/-- **Factorization Condition.** For the five-integer subfamily, the
    difference of the g-cell and c-cell values equals 8 R2 R3 (R2^2-R3^2) k^2.
    In paper notation: g^2 - c^2 = 8 R2 R3 (R2^2-R3^2) k^2, where
    (fiveIntGrid ...).g stores the cell value g^2 and .c stores c^2. -/
theorem factorization_condition (k R2 R3 : ℚ) :
    (fiveIntGrid k R2 R3).g - (fiveIntGrid k R2 R3).c =
    8 * R2 * R3 * (R2 ^ 2 - R3 ^ 2) * k ^ 2 := by
  simp only [fiveIntGrid, paramGrid]
  ring

/-- **Corollary.** If sqrt_g^2 = cell_g and M^2 = cell_c, then
    (sqrt_g - M)(sqrt_g + M) = 8 R2 R3 (R2^2-R3^2) k^2.  This is the
    criterion for both c and g (as roots of cell values) to be integers. -/
lemma factorization_gives_c (k R2 R3 sqrt_g M : ℚ)
    (hg : sqrt_g ^ 2 = (fiveIntGrid k R2 R3).g)
    (hc : M ^ 2 = (fiveIntGrid k R2 R3).c) :
    (sqrt_g - M) * (sqrt_g + M) = 8 * R2 * R3 * (R2 ^ 2 - R3 ^ 2) * k ^ 2 := by
  have hraw := factorization_condition k R2 R3
  have : (sqrt_g - M) * (sqrt_g + M) = sqrt_g ^ 2 - M ^ 2 := by ring
  rw [this, hg, hc]
  exact hraw

/-!
## 8. Numerical Verification (Example 2.2)

k = 125, R2 = 4, R3 = 2, R4 = 1 gives magic constant 398463.
Center cell e = 132821 = 398463 / 3.
-/

/-- **Example 2.2.** With k=125/4, R2=4, R3=2, R4=1 (equivalently x=2000,
    r2=8, r3=4, r4=2), all eight magic sums equal 398463. -/
theorem example_2_2_magic :
    IsMagicSquare (paramGrid (125/4 : ℚ) 4 2 1) 398463 := by
  dsimp only [IsMagicSquare, paramGrid]
  norm_num

/-- The center cell of Example 2.2 equals 132821. -/
theorem example_2_2_center :
    (paramGrid (125/4 : ℚ) 4 2 1).e = 132821 := by
  dsimp only [paramGrid]; norm_num

/-!
## 9. The Open Problem (Guy Problem D15)
-/

/-- **Open Problem.** Does there exist a 3x3 magic square all nine of whose
    entries are distinct perfect squares of integers?
    This is Problem D15 in Guy's "Unsolved Problems in Number Theory" and
    remains open as of April 2025.  The `sorry` marks a genuine open
    mathematical problem, not a gap in the formalisation. -/
theorem magic_square_of_squares_open_problem :
    ∃ (A B C D E F G H I n : ℤ),
      IsMagicSquare
        ({ a := A ^ 2, b := B ^ 2, c := C ^ 2,
           d := D ^ 2, e := E ^ 2, f := F ^ 2,
           g := G ^ 2, h := H ^ 2, i := I ^ 2 } : Grid3x3 ℤ) n /\
      A ^ 2 ≠ B ^ 2 ∧ A ^ 2 ≠ C ^ 2 ∧ A ^ 2 ≠ D ^ 2 /\
      A ^ 2 ≠ E ^ 2 ∧ A ^ 2 ≠ F ^ 2 ∧ A ^ 2 ≠ G ^ 2 /\
      A ^ 2 ≠ H ^ 2 ∧ A ^ 2 ≠ I ^ 2 ∧ B ^ 2 ≠ C ^ 2 /\
      B ^ 2 ≠ D ^ 2 ∧ B ^ 2 ≠ E ^ 2 ∧ B ^ 2 ≠ F ^ 2 /\
      B ^ 2 ≠ G ^ 2 ∧ B ^ 2 ≠ H ^ 2 ∧ B ^ 2 ≠ I ^ 2 /\
      C ^ 2 ≠ D ^ 2 ∧ C ^ 2 ≠ E ^ 2 ∧ C ^ 2 ≠ F ^ 2 /\
      C ^ 2 ≠ G ^ 2 ∧ C ^ 2 ≠ H ^ 2 ∧ C ^ 2 ≠ I ^ 2 /\
      D ^ 2 ≠ E ^ 2 ∧ D ^ 2 ≠ F ^ 2 ∧ D ^ 2 ≠ G ^ 2 /\
      D ^ 2 ≠ H ^ 2 ∧ D ^ 2 ≠ I ^ 2 ∧ E ^ 2 ≠ F ^ 2 /\
      E ^ 2 ≠ G ^ 2 ∧ E ^ 2 ≠ H ^ 2 ∧ E ^ 2 ≠ I ^ 2 /\
      F ^ 2 ≠ G ^ 2 ∧ F ^ 2 ≠ H ^ 2 ∧ F ^ 2 ≠ I ^ 2 /\
      G ^ 2 ≠ H ^ 2 ∧ G ^ 2 ≠ I ^ 2 ∧ H ^ 2 ≠ I ^ 2 := by
  sorry
