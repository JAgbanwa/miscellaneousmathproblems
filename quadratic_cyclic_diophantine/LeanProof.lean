import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

open Int

theorem diophantine_solution
  (x y z : ℤ)
  (h : x^2 * y + y^2 * z + z^2 * x = 1) :
  (x, y, z) ∈
    ({(0,1,1), (0,-1,1),
      (1,0,1), (1,0,-1),
      (1,1,0), (-1,1,0),
      (1,1,-1), (1,-1,1), (-1,1,1)} : Finset (ℤ × ℤ × ℤ)) := by

  -- Step 1: prove |x|, |y|, |z| ≤ 1.
  --
  -- From h: z^2 * x = 1 - x^2*y - y^2*z, so x | (1 - x^2*y - y^2*z).
  -- But the cleanest route: from h, z*(z*x + y^2) = 1 - x^2*y, so
  --   (i)  z | (1 - x^2*y)
  --   (ii) x | (1 - y^2*z)
  --   (iii) y | (1 - z^2*x)
  -- From (i): if x^2*y = 1, then x^2 | 1, so |x| ≤ 1; and y*(x^2) = 1 forces |y| ≤ 1.
  -- The general case uses all three relations together.
  --
  -- Key lemma: from z | (1 - x^2*y) and x | (1 - y^2*z) and y | (1 - z^2*x),
  -- use that x*y*z | product → but hard.
  --
  -- Simpler: note from h that
  --   1 = x^2*y + y^2*z + z^2*x
  --     = x*(x*y + z^2) + y^2*z
  -- so x*(x*y + z^2) = 1 - y^2*z.  If y = 0: x*z^2 = 1, so x = ±1 and z = ±1.
  -- If y ≠ 0: from the cyclic relation y*(y*z + x^2) = 1 - z^2*x, if z = 0: x^2*y = 1.
  -- We case split on whether each variable is 0.

  -- First, record the three factored forms:
  have hfx : x * (x * y + z^2) = 1 - y^2 * z := by linarith
  have hfy : y * (y * z + x^2) = 1 - z^2 * x := by linarith
  have hfz : z * (z * x + y^2) = 1 - x^2 * y := by linarith

  -- Case split: x = 0 or x ≠ 0, y = 0 or y ≠ 0, z = 0 or z ≠ 0.
  -- For each combination, derive the bounds directly.

  -- Bound for x:
  have hx_bound : x = -1 ∨ x = 0 ∨ x = 1 := by
    by_contra hx_bad
    push_neg at hx_bad
    obtain ⟨hxn1, hx0, hx1⟩ := hx_bad
    -- |x| ≥ 2, so x ≤ -2 or x ≥ 2.
    have hx2 : 2 ≤ |x| := by omega
    -- From hfx: x*(x*y + z^2) = 1 - y^2*z.
    -- From hfz: z*(z*x + y^2) = 1 - x^2*y.
    -- We use these to get |y| and |z| bounds in terms of |x|, then substitute back.
    -- Alternatively: from the equation, x^2 * |y| ≤ x^2 * |y| + y^2 * |z| + z^2 * |x|
    --   = |x^2*y + y^2*z + z^2*x|  (not exactly, need triangle ineq)
    -- Use: 1 = x^2*y + y^2*z + z^2*x. We show |1| < 1, contradiction via size bounds.
    -- From hfx: x*(xy + z^2) = 1 - y^2*z.
    -- If z = 0: x*(x*y) = 1, so x^2*y = 1, so x^2 | 1, contradicting |x| ≥ 2.
    rcases eq_or_ne z 0 with rfl | hz0
    · -- z = 0: hfx becomes x*(x*y) = 1, i.e. x^2*y = 1
      have : x^2 * y = 1 := by linarith
      have hdvx2 : x^2 ∣ 1 := ⟨y, this.symm⟩
      have : x^2 ≤ 1 := Int.le_of_dvd one_pos hdvx2
      nlinarith [sq_nonneg x]
    · -- z ≠ 0. From hfz: z*(z*x + y^2) = 1 - x^2*y.
      -- If y = 0: hfz becomes z*(z*x) = 1, i.e. z^2*x = 1, so z^2 | 1, so z = ±1.
      -- Then z = ±1 and z*x = 1, so x = ±1, contradicting |x| ≥ 2.
      rcases eq_or_ne y 0 with rfl | hy0
      · -- y = 0: hfz becomes z^2*x = 1
        have : z^2 * x = 1 := by linarith
        have hdvz2 : z^2 ∣ 1 := ⟨x, this.symm⟩
        have hz2le : z^2 ≤ 1 := Int.le_of_dvd one_pos hdvz2
        -- z = ±1, so x = 1/z^2 = 1 (if z=1) or -1 (if z=-1). But z*x = 1/z ... wait
        -- z^2 ≤ 1 and z ≠ 0: z = 1 or z = -1.
        have hzcases : z = 1 ∨ z = -1 := by nlinarith [sq_nonneg z]
        rcases hzcases with rfl | rfl
        · -- z=1: 1*x = 1, so x = 1, but |x| ≥ 2
          have : x = 1 := by linarith
          omega
        · -- z=-1: 1*x = 1, so x = 1, but |x| ≥ 2. Wait: z^2*x = (-1)^2*x = x = 1.
          have : x = 1 := by linarith
          omega
      · -- y ≠ 0, z ≠ 0. Now use a size argument.
        -- From hfx: x*(x*y + z^2) = 1 - y^2*z.
        -- |1 - y^2*z| = |x| * |x*y + z^2| ≥ 2 * |x*y + z^2|.
        -- From hfy: y*(y*z + x^2) = 1 - z^2*x.
        -- Since |y| ≥ 1 (y ≠ 0, y ∈ ℤ): |y*z + x^2| ≥ 1 or y*z + x^2 = 0.
        -- This is getting complex. Use nlinarith with many sign cases.
        -- Actually: from h, taking the equation modulo 2:
        -- x^2*y + y^2*z + z^2*x ≡ 1 (mod 2).
        -- Since x^2 ≡ x^2 and so on, this constrains parities.
        -- Alternative: use that from hfx, y^2*z = 1 - x*(x*y+z^2).
        -- From hfy, z^2*x = 1 - y*(y*z+x^2).
        -- From hfz, x^2*y = 1 - z*(z*x+y^2).
        -- So x^2*y + y^2*z + z^2*x = 3 - x*(x*y+z^2) - y*(y*z+x^2) - z*(z*x+y^2).
        -- But x^2*y + y^2*z + z^2*x = 1, so:
        -- 1 = 3 - [x*(xy+z^2) + y*(yz+x^2) + z*(zx+y^2)]
        -- i.e., [x*(xy+z^2) + y*(yz+x^2) + z*(zx+y^2)] = 2.
        -- Also x*(xy+z^2) + y*(yz+x^2) + z*(zx+y^2)
        --    = x^2*y + xz^2 + y^2*z + x^2*y + z^2*x + y^2*z = 2(x^2*y + y^2*z + z^2*x) = 2. ✓
        -- This is consistent but doesn't help bound x.
        -- The real bound: use that y ≠ 0 so |y| ≥ 1, and z ≠ 0 so |z| ≥ 1.
        -- With |x| ≥ 2, |y| ≥ 1, |z| ≥ 1: show 1 = x^2*y + y^2*z + z^2*x is impossible
        -- by checking all sign combinations of x, y, z with these bounds.
        interval_cases x <;> interval_cases y <;> interval_cases z <;>
          simp_all <;> omega

  have hy_bound : y = -1 ∨ y = 0 ∨ y = 1 := by
    by_contra hy_bad
    push_neg at hy_bad
    obtain ⟨hyn1, hy0, hy1⟩ := hy_bad
    rcases eq_or_ne x 0 with rfl | hx0
    · rcases eq_or_ne z 0 with rfl | hz0
      · simp at h
      · have : y^2 * z = 1 := by linarith
        have : y^2 ∣ 1 := ⟨z, this.symm⟩
        have : y^2 ≤ 1 := Int.le_of_dvd one_pos this
        nlinarith [sq_nonneg y]
    · rcases eq_or_ne z 0 with rfl | hz0
      · have : x^2 * y = 1 := by linarith
        have : x^2 ∣ 1 := ⟨y, this.symm⟩
        have hx2le : x^2 ≤ 1 := Int.le_of_dvd one_pos this
        have : (x : ℤ) = 1 ∨ x = -1 := by nlinarith [sq_nonneg x]
        rcases this with rfl | rfl <;> simp_all <;> omega
      · interval_cases y <;> interval_cases x <;> interval_cases z <;>
          simp_all <;> omega

  have hz_bound : z = -1 ∨ z = 0 ∨ z = 1 := by
    by_contra hz_bad
    push_neg at hz_bad
    obtain ⟨hzn1, hz0, hz1⟩ := hz_bad
    rcases eq_or_ne x 0 with rfl | hx0
    · rcases eq_or_ne y 0 with rfl | hy0
      · simp at h
      · have : y^2 * z = 1 := by linarith
        have : y^2 ∣ 1 := ⟨z, this.symm⟩
        have : y^2 ≤ 1 := Int.le_of_dvd one_pos this
        nlinarith [sq_nonneg y]
    · rcases eq_or_ne y 0 with rfl | hy0
      · have : z^2 * x = 1 := by linarith
        have : z^2 ∣ 1 := ⟨x, this.symm⟩
        have hz2le : z^2 ≤ 1 := Int.le_of_dvd one_pos this
        have : (z : ℤ) = 1 ∨ z = -1 := by nlinarith [sq_nonneg z]
        rcases this with rfl | rfl <;> simp_all <;> omega
      · interval_cases z <;> interval_cases x <;> interval_cases y <;>
          simp_all <;> omega

  -- Step 2: brute force all 27 cases
  rcases hx_bound with hx | hx | hx <;>
  rcases hy_bound with hy | hy | hy <;>
  rcases hz_bound with hz | hz | hz <;>
  subst_vars <;>
  norm_num at h ⊢ <;>
  simp [Finset.mem_insert, Finset.mem_singleton]

