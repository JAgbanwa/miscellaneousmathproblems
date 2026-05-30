import Mathlib

/-!
Pythagorean divisor parametrization and its equivalence with the classical
Euclidean parametrization.

This file formalizes the algebraic content of:
* `y = (x^2 - r^2) / (2r)`, `z = (x^2 + r^2) / (2r)`
* equivalence with `x = K (m^2 - n^2)`, `y = 2Kmn`, `z = K (m^2 + n^2)`
  up to swapping the two legs.
-/

namespace DiophantineA2PlusG2ExtraHypothesis

section RationalParametrization

lemma pythagorean_from_divisor_param
    (x r : ℚ) (hr : r ≠ 0) :
    let y : ℚ := (x ^ 2 - r ^ 2) / (2 * r)
    let z : ℚ := (x ^ 2 + r ^ 2) / (2 * r)
    y ^ 2 + x ^ 2 = z ^ 2 ∧ z - y = r := by
  intro y z
  constructor
  · dsimp [y, z]
    field_simp [hr]
    ring
  · dsimp [y, z]
    field_simp [hr]
    ring

lemma divisor_param_injective
    (x r₁ r₂ : ℚ)
    (hr₁ : r₁ ≠ 0)
    (hr₂ : r₂ ≠ 0)
    (hy :
      (x ^ 2 - r₁ ^ 2) / (2 * r₁) =
        (x ^ 2 - r₂ ^ 2) / (2 * r₂))
    (hz :
      (x ^ 2 + r₁ ^ 2) / (2 * r₁) =
        (x ^ 2 + r₂ ^ 2) / (2 * r₂)) :
    r₁ = r₂ := by
  have hdiff₁ :
      (x ^ 2 + r₁ ^ 2) / (2 * r₁) -
          (x ^ 2 - r₁ ^ 2) / (2 * r₁) = r₁ := by
    have hmain := (pythagorean_from_divisor_param x r₁ hr₁).2
    simpa using hmain
  have hdiff₂ :
      (x ^ 2 + r₂ ^ 2) / (2 * r₂) -
          (x ^ 2 - r₂ ^ 2) / (2 * r₂) = r₂ := by
    have hmain := (pythagorean_from_divisor_param x r₂ hr₂).2
    simpa using hmain
  calc
    r₁ = (x ^ 2 + r₁ ^ 2) / (2 * r₁) - (x ^ 2 - r₁ ^ 2) / (2 * r₁) := hdiff₁.symm
    _ = (x ^ 2 + r₂ ^ 2) / (2 * r₂) - (x ^ 2 - r₂ ^ 2) / (2 * r₂) := by simp [hy, hz]
    _ = r₂ := hdiff₂

lemma divisor_param_of_pythagorean
    {x y z : ℚ}
    (hyz : y < z)
    (hpy : y ^ 2 + x ^ 2 = z ^ 2) :
    let r : ℚ := z - y
    r ≠ 0 ∧
      y = (x ^ 2 - r ^ 2) / (2 * r) ∧
      z = (x ^ 2 + r ^ 2) / (2 * r) ∧
      z - y = r := by
  intro r
  have hr : r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hyz)
  have hx : x ^ 2 = (z - y) * (z + y) := by
    nlinarith [hpy]
  refine ⟨hr, ?_, ?_, rfl⟩
  · dsimp [r]
    rw [hx]
    field_simp [hr]
    ring
  · dsimp [r]
    rw [hx]
    field_simp [hr]
    ring

lemma divisor_to_euclid_legs_swapped
    (x r m n : ℚ)
    (hr : r ≠ 0)
    (hn : n ≠ 0)
    (hratio : x / r = m / n) :
    let K : ℚ := r / (2 * n ^ 2)
    let y : ℚ := (x ^ 2 - r ^ 2) / (2 * r)
    let z : ℚ := (x ^ 2 + r ^ 2) / (2 * r)
    y = K * (m ^ 2 - n ^ 2) ∧
      z = K * (m ^ 2 + n ^ 2) ∧
      x = 2 * K * m * n := by
  intro K y z
  have hcross : x * n = r * m := by
    field_simp [hr, hn] at hratio
    linarith
  have hx : x = r * m / n := by
    apply (eq_div_iff hn).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcross
  constructor
  · dsimp [y, K]
    rw [hx]
    field_simp [hr, hn]
    ring
  constructor
  · dsimp [z, K]
    rw [hx]
    field_simp [hr, hn]
    ring
  · dsimp [K]
    rw [hx]
    field_simp [hn]
    ring

theorem divisor_to_euclid
    (x r m n : ℚ)
    (hr : r ≠ 0)
    (hn : n ≠ 0)
    (hratio : x / r = m / n) :
    let K : ℚ := r / (2 * n ^ 2)
    let y : ℚ := (x ^ 2 - r ^ 2) / (2 * r)
    let z : ℚ := (x ^ 2 + r ^ 2) / (2 * r)
    x = 2 * K * m * n ∧
      y = K * (m ^ 2 - n ^ 2) ∧
      z = K * (m ^ 2 + n ^ 2) := by
  intro K y z
  rcases divisor_to_euclid_legs_swapped x r m n hr hn hratio with ⟨hy, hz, hx⟩
  exact ⟨hx, hy, hz⟩

theorem divisor_to_euclid_after_leg_swap
    (x r m n : ℚ)
    (hr : r ≠ 0)
    (hn : n ≠ 0)
    (hratio : x / r = m / n) :
    let K : ℚ := r / (2 * n ^ 2)
    let y : ℚ := (x ^ 2 - r ^ 2) / (2 * r)
    let z : ℚ := (x ^ 2 + r ^ 2) / (2 * r)
    y = K * (m ^ 2 - n ^ 2) ∧
      x = 2 * K * m * n ∧
      z = K * (m ^ 2 + n ^ 2) := by
  intro K y z
  rcases divisor_to_euclid x r m n hr hn hratio with ⟨hx, hy, hz⟩
  exact ⟨hy, hx, hz⟩

end RationalParametrization

section IntegerCorollary

theorem int_solution_produces_divisor_data
    {x y z : ℤ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hyz : y < z)
    (hpy : y ^ 2 + x ^ 2 = z ^ 2) :
    let r : ℤ := z - y
    let q : ℤ := z + y
    0 < r ∧ r ∣ x ^ 2 ∧ x ^ 2 = r * q ∧ r < x ∧ (q - r) % 2 = 0 ∧ z - y = r := by
  intro r q
  have hr : 0 < r := by
    dsimp [r]
    exact sub_pos.mpr hyz
  have hx : x ^ 2 = (z - y) * (z + y) := by
    nlinarith [hpy]
  have hdiv : r ∣ x ^ 2 := by
    refine ⟨q, ?_⟩
    dsimp [r, q]
    simpa [mul_comm] using hx
  have hpar : (q - r) % 2 = 0 := by
    dsimp [r, q]
    have htwo : (z + y) - (z - y) = 2 * y := by ring
    rw [htwo]
    simp
  have hrltx : r < x := by
    have hq_gt_r : r < q := by
      dsimp [r, q]
      linarith [hy]
    have hrr_lt_rq : r * r < r * q := by
      nlinarith [hr, hq_gt_r]
    have hx2 : x ^ 2 = r * q := by
      dsimp [r, q]
      simpa [mul_comm] using hx
    have hr2_lt_x2 : r ^ 2 < x ^ 2 := by
      nlinarith [hrr_lt_rq, hx2]
    nlinarith [hx, hr, hr2_lt_x2]
  refine ⟨hr, hdiv, ?_, hrltx, hpar, rfl⟩
  dsimp [r, q]
  simp [mul_comm, hx]

theorem int_solution_gives_rational_param
    {x y z : ℤ}
    (hyz : y < z)
    (hpy : y ^ 2 + x ^ 2 = z ^ 2) :
    let r : ℚ := (z - y : ℤ)
    ((y : ℚ) = (((x : ℚ) ^ 2 - r ^ 2) / (2 * r))) ∧
      ((z : ℚ) = (((x : ℚ) ^ 2 + r ^ 2) / (2 * r))) ∧
      ((z : ℚ) - (y : ℚ) = r) := by
  intro r
  have hyzQ : (y : ℚ) < (z : ℚ) := by exact_mod_cast hyz
  have hpyQ : (y : ℚ) ^ 2 + (x : ℚ) ^ 2 = (z : ℚ) ^ 2 := by exact_mod_cast hpy
  rcases divisor_param_of_pythagorean (x := (x : ℚ)) (y := (y : ℚ)) (z := (z : ℚ)) hyzQ hpyQ with
    ⟨_, hy, hz, hdiff⟩
  have hr : r = (z : ℚ) - (y : ℚ) := by
    simp [r]
  refine ⟨?_, ?_, ?_⟩
  · simpa [hr] using hy
  · simpa [hr] using hz
  · simp [hr] at hdiff ⊢

end IntegerCorollary

end DiophantineA2PlusG2ExtraHypothesis

