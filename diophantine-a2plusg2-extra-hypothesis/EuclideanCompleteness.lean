import Mathlib

/-!
Completeness of the Euclidean parametrization for rational solutions of
`x^2 + y^2 = z^2`.

This file formalizes:
1. Normalization to the unit circle.
2. The line-through-`(-1,0)` parametrization of rational points on `X^2 + Y^2 = 1`.
3. Conversion to integer parameters `m,n` and rational scale `K`.
-/

namespace DiophantineA2PlusG2ExtraHypothesis

section UnitCircle

lemma normalize_to_unit_circle
    {x y z : ℚ} (hz : z ≠ 0) (hpy : x ^ 2 + y ^ 2 = z ^ 2) :
    (x / z) ^ 2 + (y / z) ^ 2 = 1 := by
  calc
    (x / z) ^ 2 + (y / z) ^ 2 = (x ^ 2 + y ^ 2) / z ^ 2 := by
      field_simp [hz]
    _ = z ^ 2 / z ^ 2 := by rw [hpy]
    _ = 1 := by field_simp [pow_ne_zero 2 hz]

lemma point_from_slope_on_unit_circle (t : ℚ) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  have hden : (1 + t ^ 2) ≠ 0 := by
    nlinarith [sq_nonneg t]
  field_simp [hden]
  ring

lemma slope_param_formula
    {X Y t : ℚ}
    (hline : Y = t * (X + 1))
    (hcircle : X ^ 2 + Y ^ 2 = 1)
    (hX : X ≠ -1) :
    X = (1 - t ^ 2) / (1 + t ^ 2) ∧
      Y = 2 * t / (1 + t ^ 2) := by
  have hden : (1 + t ^ 2) ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hfac : (X + 1) * ((1 + t ^ 2) * X + (t ^ 2 - 1)) = 0 := by
    rw [hline] at hcircle
    nlinarith
  have hsecond : ((1 + t ^ 2) * X + (t ^ 2 - 1)) = 0 := by
    have hX1 : X + 1 ≠ 0 := by
      intro hx1
      apply hX
      linarith
    exact (mul_eq_zero.mp hfac).resolve_left hX1
  have hXformula : X = (1 - t ^ 2) / (1 + t ^ 2) := by
    apply (eq_div_iff hden).2
    linarith [hsecond]
  constructor
  · exact hXformula
  · rw [hline, hXformula]
    field_simp [hden]
    ring

lemma unit_circle_complete_except_minus_one
    {X Y : ℚ}
    (hcircle : X ^ 2 + Y ^ 2 = 1)
    (hX : X ≠ -1) :
    ∃ t : ℚ, X = (1 - t ^ 2) / (1 + t ^ 2) ∧
      Y = 2 * t / (1 + t ^ 2) := by
  refine ⟨Y / (X + 1), ?_, ?_⟩
  · have hX1 : X + 1 ≠ 0 := by
      intro hx1
      apply hX
      linarith
    have hline : Y = (Y / (X + 1)) * (X + 1) := by
      field_simp [hX1]
    exact (slope_param_formula hline hcircle hX).1
  · have hX1 : X + 1 ≠ 0 := by
      intro hx1
      apply hX
      linarith
    have hline : Y = (Y / (X + 1)) * (X + 1) := by
      field_simp [hX1]
    exact (slope_param_formula hline hcircle hX).2

lemma minus_one_point_on_unit_circle
    {X Y : ℚ} (hcircle : X ^ 2 + Y ^ 2 = 1) (hX : X = -1) :
    Y = 0 := by
  rw [hX] at hcircle
  nlinarith

end UnitCircle

section EuclideanParametrization

theorem rational_pythagorean_euclid_complete
    {x y z : ℚ} (hz : z ≠ 0) (hpy : x ^ 2 + y ^ 2 = z ^ 2) :
    ∃ (K : ℚ) (m n : ℤ),
      x = K * ((m : ℚ) ^ 2 - (n : ℚ) ^ 2) ∧
      y = 2 * K * (m : ℚ) * (n : ℚ) ∧
      z = K * ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) := by
  let X : ℚ := x / z
  let Y : ℚ := y / z
  have hcircle : X ^ 2 + Y ^ 2 = 1 := by
    simpa [X, Y] using normalize_to_unit_circle hz hpy

  by_cases hXm1 : X = -1
  · have hY0 : Y = 0 := minus_one_point_on_unit_circle hcircle hXm1
    refine ⟨z, 0, 1, ?_, ?_, ?_⟩
    · have hxz : x = -z := by
        have : x / z = -1 := by simpa [X] using hXm1
        have := (div_eq_iff hz).1 this
        simpa using this
      calc
        x = -z := hxz
        _ = z * (((0 : ℤ) : ℚ) ^ 2 - ((1 : ℤ) : ℚ) ^ 2) := by ring
    · have hy0 : y = 0 := by
        have : y / z = 0 := by simpa [Y] using hY0
        have := (div_eq_iff hz).1 this
        simpa using this
      calc
        y = 0 := hy0
        _ = 2 * z * ((0 : ℤ) : ℚ) * ((1 : ℤ) : ℚ) := by ring
    · ring
  · have hXne : X ≠ -1 := hXm1
    rcases unit_circle_complete_except_minus_one hcircle hXne with ⟨t, hXt, hYt⟩

    let n : ℤ := Rat.num t
    let m : ℤ := Rat.den t
    have hm : m ≠ 0 := by
      have hmnat : (Rat.den t : ℕ) ≠ 0 := Nat.ne_of_gt (Rat.pos t)
      dsimp [m]
      exact_mod_cast hmnat
    have ht : t = (n : ℚ) / (m : ℚ) := by
      simpa [n, m] using (Rat.num_div_den t).symm

    have hXmn :
        X = (((m : ℚ) ^ 2 - (n : ℚ) ^ 2) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2)) := by
      rw [hXt, ht]
      field_simp [hm]
    have hYmn :
        Y = (2 * (m : ℚ) * (n : ℚ)) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) := by
      rw [hYt, ht]
      field_simp [hm]
      ring

    let K : ℚ := z / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2)
    have hmn_den_ne : ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) ≠ 0 := by
      have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
      intro hsum
      have hm_sq : (m : ℚ) ^ 2 = 0 := by
        nlinarith [sq_nonneg (m : ℚ), sq_nonneg (n : ℚ), hsum]
      exact hmq (pow_eq_zero hm_sq)

    refine ⟨K, m, n, ?_, ?_, ?_⟩
    · have hx : x = z * X := by
        dsimp [X]
        have : x / z = X := by rfl
        have hx' : x = X * z := (div_eq_iff hz).1 this
        simpa [mul_comm] using hx'
      have hxScaled :
          z * X = z * (((m : ℚ) ^ 2 - (n : ℚ) ^ 2) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2)) := by
        exact congrArg (fun u : ℚ => z * u) hXmn
      calc
        x = z * X := hx
        _ = z * (((m : ℚ) ^ 2 - (n : ℚ) ^ 2) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2)) := hxScaled
        _ = K * ((m : ℚ) ^ 2 - (n : ℚ) ^ 2) := by
              dsimp [K]
              field_simp [hmn_den_ne]
    · have hy : y = z * Y := by
        dsimp [Y]
        have : y / z = Y := by rfl
        have hy' : y = Y * z := (div_eq_iff hz).1 this
        simpa [mul_comm] using hy'
      have hyScaled :
          z * Y = z * ((2 * (m : ℚ) * (n : ℚ)) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2)) := by
        exact congrArg (fun u : ℚ => z * u) hYmn
      calc
        y = z * Y := hy
        _ = z * ((2 * (m : ℚ) * (n : ℚ)) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2)) := hyScaled
        _ = 2 * K * (m : ℚ) * (n : ℚ) := by
              dsimp [K]
              field_simp [hmn_den_ne]
              ring
    · dsimp [K]
      field_simp [hmn_den_ne]

end EuclideanParametrization

section DivisorSystemCompleteness

theorem divisor_system_sound_rational
    (a r₂ r₃ : ℚ) (hr₂ : r₂ ≠ 0) (hr₃ : r₃ ≠ 0) :
    let b : ℚ := (a ^ 2 - r₂ ^ 2) / (2 * r₂)
    let e : ℚ := (a ^ 2 + r₂ ^ 2) / (2 * r₂)
    let c : ℚ := (a ^ 2 - r₃ ^ 2) / (2 * r₃)
    let f : ℚ := (a ^ 2 + r₃ ^ 2) / (2 * r₃)
    a ^ 2 + b ^ 2 = e ^ 2 ∧ a ^ 2 + c ^ 2 = f ^ 2 := by
  intro b e c f
  constructor
  · dsimp [b, e]
    field_simp [hr₂]
    ring
  · dsimp [c, f]
    field_simp [hr₃]
    ring

theorem divisor_system_sound_rational_with_b_c
    (a r₂ r₃ : ℚ) (hr₂ : r₂ ≠ 0) (hr₃ : r₃ ≠ 0) :
    let b : ℚ := (a ^ 2 - r₂ ^ 2) / (2 * r₂)
    let c : ℚ := (a ^ 2 - r₃ ^ 2) / (2 * r₃)
    a ^ 2 + b ^ 2 = ((a ^ 2 + r₂ ^ 2) / (2 * r₂)) ^ 2 ∧
      a ^ 2 + c ^ 2 = ((a ^ 2 + r₃ ^ 2) / (2 * r₃)) ^ 2 := by
  intro b c
  constructor
  · dsimp [b]
    field_simp [hr₂]
    ring
  · dsimp [c]
    field_simp [hr₃]
    ring

theorem divisor_system_complete_rational
    {a b e c f : ℚ}
    (h₂ : a ^ 2 + b ^ 2 = e ^ 2)
    (h₃ : a ^ 2 + c ^ 2 = f ^ 2)
    (h₂lt : b < e)
    (h₃lt : c < f) :
    ∃ r₂ r₃ : ℚ,
      r₂ ≠ 0 ∧
      r₃ ≠ 0 ∧
      b = (a ^ 2 - r₂ ^ 2) / (2 * r₂) ∧
      e = (a ^ 2 + r₂ ^ 2) / (2 * r₂) ∧
      c = (a ^ 2 - r₃ ^ 2) / (2 * r₃) ∧
      f = (a ^ 2 + r₃ ^ 2) / (2 * r₃) := by
  refine ⟨e - b, f - c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sub_ne_zero.mpr (ne_of_gt h₂lt)
  · exact sub_ne_zero.mpr (ne_of_gt h₃lt)
  · have hr₂ : e - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt h₂lt)
    have ha₂ : a ^ 2 = (e - b) * (e + b) := by nlinarith [h₂]
    rw [ha₂]
    field_simp [hr₂]
    ring
  · have hr₂ : e - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt h₂lt)
    have ha₂ : a ^ 2 = (e - b) * (e + b) := by nlinarith [h₂]
    rw [ha₂]
    field_simp [hr₂]
    ring
  · have hr₃ : f - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt h₃lt)
    have ha₃ : a ^ 2 = (f - c) * (f + c) := by nlinarith [h₃]
    rw [ha₃]
    field_simp [hr₃]
    ring
  · have hr₃ : f - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt h₃lt)
    have ha₃ : a ^ 2 = (f - c) * (f + c) := by nlinarith [h₃]
    rw [ha₃]
    field_simp [hr₃]
    ring

theorem divisor_system_complete_integer
    {a b e c f : ℤ}
    (h₂ : a ^ 2 + b ^ 2 = e ^ 2)
    (h₃ : a ^ 2 + c ^ 2 = f ^ 2)
    (h₂lt : b < e)
    (h₃lt : c < f) :
    ∃ r₂ r₃ : ℚ,
      r₂ ≠ 0 ∧
      r₃ ≠ 0 ∧
      (b : ℚ) = ((a : ℚ) ^ 2 - r₂ ^ 2) / (2 * r₂) ∧
      (e : ℚ) = ((a : ℚ) ^ 2 + r₂ ^ 2) / (2 * r₂) ∧
      (c : ℚ) = ((a : ℚ) ^ 2 - r₃ ^ 2) / (2 * r₃) ∧
      (f : ℚ) = ((a : ℚ) ^ 2 + r₃ ^ 2) / (2 * r₃) := by
  have h₂Q : (a : ℚ) ^ 2 + (b : ℚ) ^ 2 = (e : ℚ) ^ 2 := by
    exact_mod_cast h₂
  have h₃Q : (a : ℚ) ^ 2 + (c : ℚ) ^ 2 = (f : ℚ) ^ 2 := by
    exact_mod_cast h₃
  have h₂ltQ : (b : ℚ) < (e : ℚ) := by
    exact_mod_cast h₂lt
  have h₃ltQ : (c : ℚ) < (f : ℚ) := by
    exact_mod_cast h₃lt
  exact divisor_system_complete_rational h₂Q h₃Q h₂ltQ h₃ltQ

end DivisorSystemCompleteness

end DiophantineA2PlusG2ExtraHypothesis

