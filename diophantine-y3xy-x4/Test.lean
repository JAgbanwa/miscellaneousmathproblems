import Mathlib

-- Test 1: The cast pattern
example (x y : ℤ) (h : y ^ 3 + x * y + x ^ 4 + 4 = 0) :
    (x : ZMod 2) = 0 := by
  have heq : (y : ZMod 2) ^ 3 + (x : ZMod 2) * (y : ZMod 2) +
             (x : ZMod 2) ^ 4 + 4 = 0 := by
    have := congr_arg (Int.cast : ℤ → ZMod 2) h
    push_cast at this
    convert this using 1
  have key : ∀ (a b : ZMod 2),
      b ^ 3 + a * b + a ^ 4 + 4 = 0 → a = 0 := by decide
  exact key (x : ZMod 2) (y : ZMod 2) heq

-- Test 2: affine_smooth x=0 case
example (x y : ℚ) (hy : y = -4 * x ^ 3) (hx0 : x = 0)
    (hF : (-4 * x ^ 3) ^ 3 + x * (-4 * x ^ 3) + x ^ 4 + 4 = 0) : False := by
  rw [hx0] at hF; norm_num at hF

-- Test 3: affine_smooth x≠0 case with 48x^5 + 1 = 0
-- We have y = -4x^3 and hF : (-4x^3)^3 + x*(-4x^3) + x^4 + 4 = 0
-- and hx5 : 48*x^5 + 1 = 0, so x^5 = -1/48
example (x : ℚ) (hx5 : 48 * x ^ 5 + 1 = 0) 
    (hF : (-4 * x ^ 3) ^ 3 + x * (-4 * x ^ 3) + x ^ 4 + 4 = 0) : False := by
  have hx5' : x ^ 5 = -1 / 48 := by linarith
  -- hF simplifies to -64x^9 - 4x^4 + x^4 + 4 = 0, i.e. -64x^9 - 3x^4 + 4 = 0
  nlinarith [sq_nonneg x, sq_nonneg (x^2), sq_nonneg (x^4), 
             mul_comm (x^5) (x^4), sq_nonneg (x^5 + 1/48)]

