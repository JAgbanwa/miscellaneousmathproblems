import Mathlib

/-!
Merged standalone formalization proving non-existence of perfect cuboids under
the extra valuation hypothesis used in this folder.

It contains:
* full divisor-system soundness/completeness (`a,b,c,e,f,g` side),
* the valuation obstruction proving no integer space diagonal (`d` side),
* and a final packaged perfect-cuboid non-existence theorem.
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

theorem divisor_system_with_g_sound_rational
    (a r₂ r₃ g : ℚ)
    (hr₂ : r₂ ≠ 0)
    (hr₃ : r₃ ≠ 0)
    (hg :
      ((a ^ 2 - r₂ ^ 2) / (2 * r₂)) ^ 2 +
        ((a ^ 2 - r₃ ^ 2) / (2 * r₃)) ^ 2 = g ^ 2) :
    let b : ℚ := (a ^ 2 - r₂ ^ 2) / (2 * r₂)
    let e : ℚ := (a ^ 2 + r₂ ^ 2) / (2 * r₂)
    let c : ℚ := (a ^ 2 - r₃ ^ 2) / (2 * r₃)
    let f : ℚ := (a ^ 2 + r₃ ^ 2) / (2 * r₃)
    a ^ 2 + b ^ 2 = e ^ 2 ∧
      a ^ 2 + c ^ 2 = f ^ 2 ∧
      b ^ 2 + c ^ 2 = g ^ 2 := by
  intro b e c f
  have h₂ :
      a ^ 2 + ((a ^ 2 - r₂ ^ 2) / (2 * r₂)) ^ 2 =
        ((a ^ 2 + r₂ ^ 2) / (2 * r₂)) ^ 2 := by
    field_simp [hr₂]
    ring
  have h₃ :
      a ^ 2 + ((a ^ 2 - r₃ ^ 2) / (2 * r₃)) ^ 2 =
        ((a ^ 2 + r₃ ^ 2) / (2 * r₃)) ^ 2 := by
    field_simp [hr₃]
    ring
  refine ⟨by simpa [b, e] using h₂, by simpa [c, f] using h₃, ?_⟩
  simpa [b, c] using hg

theorem divisor_system_with_g_complete_rational
    {a b e c f g : ℚ}
    (h₂ : a ^ 2 + b ^ 2 = e ^ 2)
    (h₃ : a ^ 2 + c ^ 2 = f ^ 2)
    (hg : b ^ 2 + c ^ 2 = g ^ 2)
    (h₂lt : b < e)
    (h₃lt : c < f) :
    ∃ r₂ r₃ : ℚ,
      r₂ ≠ 0 ∧
      r₃ ≠ 0 ∧
      b = (a ^ 2 - r₂ ^ 2) / (2 * r₂) ∧
      e = (a ^ 2 + r₂ ^ 2) / (2 * r₂) ∧
      c = (a ^ 2 - r₃ ^ 2) / (2 * r₃) ∧
      f = (a ^ 2 + r₃ ^ 2) / (2 * r₃) ∧
      ((a ^ 2 - r₂ ^ 2) / (2 * r₂)) ^ 2 +
        ((a ^ 2 - r₃ ^ 2) / (2 * r₃)) ^ 2 = g ^ 2 := by
  let r₂ : ℚ := e - b
  let r₃ : ℚ := f - c
  have hr₂ : r₂ ≠ 0 := by
    dsimp [r₂]
    exact sub_ne_zero.mpr (ne_of_gt h₂lt)
  have hr₃ : r₃ ≠ 0 := by
    dsimp [r₃]
    exact sub_ne_zero.mpr (ne_of_gt h₃lt)
  have hb : b = (a ^ 2 - r₂ ^ 2) / (2 * r₂) := by
    have ha₂ : a ^ 2 = r₂ * (e + b) := by
      dsimp [r₂]
      nlinarith [h₂]
    rw [ha₂]
    field_simp [hr₂]
    dsimp [r₂]
    ring
  have he : e = (a ^ 2 + r₂ ^ 2) / (2 * r₂) := by
    have ha₂ : a ^ 2 = r₂ * (e + b) := by
      dsimp [r₂]
      nlinarith [h₂]
    rw [ha₂]
    field_simp [hr₂]
    dsimp [r₂]
    ring
  have hc : c = (a ^ 2 - r₃ ^ 2) / (2 * r₃) := by
    have ha₃ : a ^ 2 = r₃ * (f + c) := by
      dsimp [r₃]
      nlinarith [h₃]
    rw [ha₃]
    field_simp [hr₃]
    dsimp [r₃]
    ring
  have hf : f = (a ^ 2 + r₃ ^ 2) / (2 * r₃) := by
    have ha₃ : a ^ 2 = r₃ * (f + c) := by
      dsimp [r₃]
      nlinarith [h₃]
    rw [ha₃]
    field_simp [hr₃]
    dsimp [r₃]
    ring
  refine ⟨r₂, r₃, hr₂, hr₃, hb, he, hc, hf, ?_⟩
  calc
    ((a ^ 2 - r₂ ^ 2) / (2 * r₂)) ^ 2 + ((a ^ 2 - r₃ ^ 2) / (2 * r₃)) ^ 2
        = b ^ 2 + c ^ 2 := by rw [hb, hc]
    _ = g ^ 2 := hg

theorem divisor_system_with_g_complete_integer
    {a b e c f g : ℤ}
    (h₂ : a ^ 2 + b ^ 2 = e ^ 2)
    (h₃ : a ^ 2 + c ^ 2 = f ^ 2)
    (hg : b ^ 2 + c ^ 2 = g ^ 2)
    (h₂lt : b < e)
    (h₃lt : c < f) :
    ∃ r₂ r₃ : ℚ,
      r₂ ≠ 0 ∧
      r₃ ≠ 0 ∧
      (b : ℚ) = ((a : ℚ) ^ 2 - r₂ ^ 2) / (2 * r₂) ∧
      (e : ℚ) = ((a : ℚ) ^ 2 + r₂ ^ 2) / (2 * r₂) ∧
      (c : ℚ) = ((a : ℚ) ^ 2 - r₃ ^ 2) / (2 * r₃) ∧
      (f : ℚ) = ((a : ℚ) ^ 2 + r₃ ^ 2) / (2 * r₃) ∧
      ((((a : ℚ) ^ 2 - r₂ ^ 2) / (2 * r₂)) ^ 2) +
        ((((a : ℚ) ^ 2 - r₃ ^ 2) / (2 * r₃)) ^ 2) = (g : ℚ) ^ 2 := by
  have h₂Q : (a : ℚ) ^ 2 + (b : ℚ) ^ 2 = (e : ℚ) ^ 2 := by
    exact_mod_cast h₂
  have h₃Q : (a : ℚ) ^ 2 + (c : ℚ) ^ 2 = (f : ℚ) ^ 2 := by
    exact_mod_cast h₃
  have hgQ : (b : ℚ) ^ 2 + (c : ℚ) ^ 2 = (g : ℚ) ^ 2 := by
    exact_mod_cast hg
  have h₂ltQ : (b : ℚ) < (e : ℚ) := by
    exact_mod_cast h₂lt
  have h₃ltQ : (c : ℚ) < (f : ℚ) := by
    exact_mod_cast h₃lt
  exact divisor_system_with_g_complete_rational h₂Q h₃Q hgQ h₂ltQ h₃ltQ

lemma expanded_numerator_identity (a r2 r3 : ℤ) :
    r3 ^ 2 * (a ^ 2 - r2 ^ 2) ^ 2 + r2 ^ 2 * (a ^ 2 - r3 ^ 2) ^ 2 =
      (r2 ^ 2 + r3 ^ 2) * (a ^ 4 + r2 ^ 2 * r3 ^ 2) - 4 * a ^ 2 * r2 ^ 2 * r3 ^ 2 := by
  ring

theorem derive_product_identity
    (a r2 r3 g : ℤ)
    (hgeom :
      (((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) / (2 * r2)) ^ 2 +
        ((((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) / (2 * r3)) ^ 2) =
          (g : ℚ) ^ 2)
    (hr2 : r2 ∣ a)
    (hr3 : r3 ∣ a) :
    ∃ t : ℤ, 4 * (a ^ 2 + g ^ 2) = (r2 ^ 2 + r3 ^ 2) * (t ^ 2 + 1) := by
  rcases hr2 with ⟨u, hu⟩
  rcases hr3 with ⟨v, hv⟩
  let t : ℤ := u * v

  by_cases hr2z : r2 = 0
  · subst hr2z
    have ha0 : a = 0 := by simpa using hu
    subst ha0
    have hgq : (g : ℚ) ^ 2 = ((r3 : ℚ) ^ 2) / 4 := by
      have h0 : ((-(r3 : ℚ) ^ 2) / (2 * (r3 : ℚ))) ^ 2 = (g : ℚ) ^ 2 := by
        simpa using hgeom
      have hsq : ((-(r3 : ℚ) ^ 2) / (2 * (r3 : ℚ))) ^ 2 = ((r3 : ℚ) ^ 2) / 4 := by
        by_cases hr3q : (r3 : ℚ) = 0
        · simp [hr3q]
        · field_simp [hr3q]
          ring
      calc
        (g : ℚ) ^ 2 = ((-(r3 : ℚ) ^ 2) / (2 * (r3 : ℚ))) ^ 2 := by
          simpa using h0.symm
        _ = ((r3 : ℚ) ^ 2) / 4 := hsq
    have h4gq : (4 : ℚ) * (g : ℚ) ^ 2 = (r3 : ℚ) ^ 2 := by
      calc
        (4 : ℚ) * (g : ℚ) ^ 2 = (4 : ℚ) * (((r3 : ℚ) ^ 2) / 4) := by simp [hgq]
        _ = (r3 : ℚ) ^ 2 := by ring
    have h4g : 4 * g ^ 2 = r3 ^ 2 := by exact_mod_cast h4gq
    refine ⟨0, ?_⟩
    calc
      4 * (0 ^ 2 + g ^ 2) = 4 * g ^ 2 := by ring
      _ = r3 ^ 2 := h4g
      _ = (0 ^ 2 + r3 ^ 2) * (0 ^ 2 + 1) := by ring

  by_cases hr3z : r3 = 0
  · subst hr3z
    have ha0 : a = 0 := by simpa using hv
    subst ha0
    have hgq : (g : ℚ) ^ 2 = ((r2 : ℚ) ^ 2) / 4 := by
      have h0 : ((-(r2 : ℚ) ^ 2) / (2 * (r2 : ℚ))) ^ 2 = (g : ℚ) ^ 2 := by
        simpa using hgeom
      have hsq : ((-(r2 : ℚ) ^ 2) / (2 * (r2 : ℚ))) ^ 2 = ((r2 : ℚ) ^ 2) / 4 := by
        by_cases hr2q : (r2 : ℚ) = 0
        · simp [hr2q]
        · field_simp [hr2q]
          ring
      calc
        (g : ℚ) ^ 2 = ((-(r2 : ℚ) ^ 2) / (2 * (r2 : ℚ))) ^ 2 := by
          simpa using h0.symm
        _ = ((r2 : ℚ) ^ 2) / 4 := hsq
    have h4gq : (4 : ℚ) * (g : ℚ) ^ 2 = (r2 : ℚ) ^ 2 := by
      calc
        (4 : ℚ) * (g : ℚ) ^ 2 = (4 : ℚ) * (((r2 : ℚ) ^ 2) / 4) := by simp [hgq]
        _ = (r2 : ℚ) ^ 2 := by ring
    have h4g : 4 * g ^ 2 = r2 ^ 2 := by exact_mod_cast h4gq
    refine ⟨0, ?_⟩
    calc
      4 * (0 ^ 2 + g ^ 2) = 4 * g ^ 2 := by ring
      _ = r2 ^ 2 := h4g
      _ = (r2 ^ 2 + 0 ^ 2) * (0 ^ 2 + 1) := by ring

  have hr2qz : ((r2 : ℚ) ≠ 0) := by exact_mod_cast hr2z
  have hr3qz : ((r3 : ℚ) ≠ 0) := by exact_mod_cast hr3z

  have ha2 : a ^ 2 = r2 * r3 * t := by
    dsimp [t]
    calc
      a ^ 2 = a * a := by ring
      _ = (r2 * u) * (r3 * v) := by rw [← hu, ← hv]
      _ = r2 * r3 * (u * v) := by ring

  have hclear :
      (4 : ℚ) * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (g : ℚ) ^ 2 =
        (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r2 : ℚ) ^ 2) ^ 2 +
          (r2 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r3 : ℚ) ^ 2) ^ 2 := by
    have hgeom' := hgeom
    field_simp [hr2qz, hr3qz] at hgeom'
    have h16 :
        ((((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) ^ 2) * (r3 : ℚ) ^ 2 +
            (((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) ^ 2) * (r2 : ℚ) ^ 2) * 4 =
          ((r3 : ℚ) ^ 2 * (r2 : ℚ) ^ 2 * (g : ℚ) ^ 2) * 16 := by
      calc
        ((((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) ^ 2) * (r3 : ℚ) ^ 2 +
            (((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) ^ 2) * (r2 : ℚ) ^ 2) * 4
            = 4 * ((r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r2 : ℚ) ^ 2) ^ 2 +
                (r2 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r3 : ℚ) ^ 2) ^ 2) := by
                simp [Int.cast_sub, Int.cast_pow]
                ring
        _ = 4 * ((r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (g : ℚ) ^ 2 * 4) := by
              have htmp := hgeom'
              ring_nf at htmp ⊢
              exact htmp
        _ = ((r3 : ℚ) ^ 2 * (r2 : ℚ) ^ 2 * (g : ℚ) ^ 2) * 16 := by ring
    have hdiv :
        ((((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) ^ 2) * (r3 : ℚ) ^ 2 +
            (((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) ^ 2) * (r2 : ℚ) ^ 2) =
          (r3 : ℚ) ^ 2 * (r2 : ℚ) ^ 2 * (g : ℚ) ^ 2 * 4 := by
      have := congrArg (fun x : ℚ => x / 4) h16
      ring_nf at this ⊢
      exact this
    calc
      (4 : ℚ) * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (g : ℚ) ^ 2
          = (r3 : ℚ) ^ 2 * (r2 : ℚ) ^ 2 * (g : ℚ) ^ 2 * 4 := by ring
      _ = (((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) ^ 2) * (r3 : ℚ) ^ 2 +
            (((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) ^ 2) * (r2 : ℚ) ^ 2 := hdiv.symm
      _ = (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r2 : ℚ) ^ 2) ^ 2 +
            (r2 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r3 : ℚ) ^ 2) ^ 2 := by
            simp [Int.cast_sub, Int.cast_pow]
            ring

  have hexpQ :
      (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r2 : ℚ) ^ 2) ^ 2 +
          (r2 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r3 : ℚ) ^ 2) ^ 2 =
        ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) *
            ((a : ℚ) ^ 4 + (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) -
          4 * (a : ℚ) ^ 2 * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 := by
    exact_mod_cast expanded_numerator_identity a r2 r3

  have hmainQ :
      (4 : ℚ) * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 + (g : ℚ) ^ 2) =
        ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) *
          ((a : ℚ) ^ 4 + (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) := by
    calc
      (4 : ℚ) * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 + (g : ℚ) ^ 2)
          = 4 * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (a : ℚ) ^ 2 +
              4 * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (g : ℚ) ^ 2 := by ring
      _ = 4 * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (a : ℚ) ^ 2 +
            ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) *
                ((a : ℚ) ^ 4 + (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) -
              4 * (a : ℚ) ^ 2 * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 := by
            rw [hclear, hexpQ]
            ring
      _ = ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) *
            ((a : ℚ) ^ 4 + (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) := by ring

  have ha4 : a ^ 4 = r2 ^ 2 * r3 ^ 2 * t ^ 2 := by
    calc
      a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (r2 * r3 * t) ^ 2 := by simp [ha2]
      _ = r2 ^ 2 * r3 ^ 2 * t ^ 2 := by ring

  have ha4Q : (a : ℚ) ^ 4 = (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (t : ℚ) ^ 2 := by
    exact_mod_cast ha4

  have hmainQ' :
      (4 : ℚ) * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 + (g : ℚ) ^ 2) =
        ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) *
          ((r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) * ((t : ℚ) ^ 2 + 1) := by
    calc
      (4 : ℚ) * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 + (g : ℚ) ^ 2)
          = ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) *
              ((a : ℚ) ^ 4 + (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) := hmainQ
      _ = ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) *
            (((r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (t : ℚ) ^ 2) + (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) := by
            simp [ha4Q]
      _ = ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) *
            ((r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) * ((t : ℚ) ^ 2 + 1) := by ring

  have hfacnz : ((r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 hr2qz) (pow_ne_zero 2 hr3qz)

  have htargetQ :
      (4 : ℚ) * ((a : ℚ) ^ 2 + (g : ℚ) ^ 2) =
        ((r2 : ℚ) ^ 2 + (r3 : ℚ) ^ 2) * ((t : ℚ) ^ 2 + 1) := by
    apply (mul_right_injective₀ hfacnz)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmainQ'

  refine ⟨t, ?_⟩
  exact_mod_cast htargetQ

lemma prime_three_mod_four_not_dvd_sq_add_one
    (p : ℕ) (hpprime : Nat.Prime p) (hpmod4 : p % 4 = 3) (t : ℤ) :
    ¬ p ∣ Int.natAbs (t ^ 2 + 1) := by
  intro hdiv
  have hdivInt : (p : ℤ) ∣ (t ^ 2 + 1) := by
    exact (Int.natAbs_dvd_natAbs).1 (by simpa using hdiv)
  have hzmodZero : (((t ^ 2 + 1 : ℤ) : ZMod p) = 0) := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdivInt
  have hsqNegOne : ((t : ZMod p) ^ 2 = -1) := by
    have hzmodZero' : ((t : ZMod p) ^ 2 + 1 = 0) := by
      simpa [pow_two] using hzmodZero
    calc
      (t : ZMod p) ^ 2 = (t : ZMod p) ^ 2 + 1 - 1 := by ring
      _ = 0 - 1 := by simp [hzmodZero']
      _ = -1 := by ring
  have hfact : Fact (Nat.Prime p) := ⟨hpprime⟩
  exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one hsqNegOne) hpmod4

lemma odd_valuation_of_product
    (p : ℕ) (hpprime : Nat.Prime p)
    (A B : ℤ)
    (hodd : Odd (padicValNat p (Int.natAbs A)))
    (hcop : ¬ p ∣ Int.natAbs B) :
    Odd (padicValNat p (Int.natAbs (A * B))) := by
  have hfact : Fact (Nat.Prime p) := ⟨hpprime⟩
  have hA0 : Int.natAbs A ≠ 0 := by
    intro hA0
    have : padicValNat p (Int.natAbs A) = 0 := by simp [hA0]
    exact Nat.not_odd_zero (this ▸ hodd)
  have hB0 : Int.natAbs B ≠ 0 := by
    intro hB0
    apply hcop
    simp [Int.natAbs_eq_zero.mp hB0]
  have hmul :
      padicValNat p (Int.natAbs A * Int.natAbs B) =
        padicValNat p (Int.natAbs A) + padicValNat p (Int.natAbs B) := by
    exact padicValNat.mul (p := p) (a := Int.natAbs A) (b := Int.natAbs B) hA0 hB0
  have hBval0 : padicValNat p (Int.natAbs B) = 0 := padicValNat.eq_zero_of_not_dvd hcop
  have hEq :
      padicValNat p (Int.natAbs (A * B)) = padicValNat p (Int.natAbs A) := by
    calc
      padicValNat p (Int.natAbs (A * B))
          = padicValNat p (Int.natAbs A * Int.natAbs B) := by simp [Int.natAbs_mul]
      _ = padicValNat p (Int.natAbs A) + padicValNat p (Int.natAbs B) := hmul
      _ = padicValNat p (Int.natAbs A) := by simp [hBval0]
  exact hEq ▸ hodd

lemma even_valuation_four_mul_square
    (p : ℕ) (hpprime : Nat.Prime p) (hpodd : p ≠ 2) (d : ℤ) :
    Even (padicValNat p (Int.natAbs (4 * d ^ 2))) := by
  by_cases hd0 : d = 0
  · simp [hd0]
  · have hfact : Fact (Nat.Prime p) := ⟨hpprime⟩
    have hpdvd4 : ¬ p ∣ 4 := by
      intro h4
      have hpdvd2 : p ∣ 2 := by
        have : p ∣ 2 ^ 2 := by simpa using h4
        exact Nat.Prime.dvd_of_dvd_pow hpprime this
      have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hpdvd2
      have hp_eq_two : p = 2 := le_antisymm hp_le_two hpprime.two_le
      exact hpodd hp_eq_two
    have hval4 : padicValNat p 4 = 0 := padicValNat.eq_zero_of_not_dvd hpdvd4
    have hdnatAbs0 : Int.natAbs d ≠ 0 := by
      exact Int.natAbs_ne_zero.mpr hd0
    have hpow :
        padicValNat p ((Int.natAbs d) ^ 2) = 2 * padicValNat p (Int.natAbs d) := by
      simpa using padicValNat.pow (p := p) (a := Int.natAbs d) (n := 2) hdnatAbs0
    have hmul :
        padicValNat p (4 * (Int.natAbs d) ^ 2) =
          padicValNat p 4 + padicValNat p ((Int.natAbs d) ^ 2) := by
      have h4nz : (4 : ℕ) ≠ 0 := by decide
      have hpowNz : (Int.natAbs d) ^ 2 ≠ 0 := pow_ne_zero 2 hdnatAbs0
      exact padicValNat.mul (p := p) (a := 4) (b := (Int.natAbs d) ^ 2) h4nz hpowNz
    have hfinal :
        padicValNat p (Int.natAbs (4 * d ^ 2)) = 2 * padicValNat p (Int.natAbs d) := by
      calc
        padicValNat p (Int.natAbs (4 * d ^ 2))
            = padicValNat p (Int.natAbs 4 * Int.natAbs (d ^ 2)) := by simp [Int.natAbs_mul]
        _ = padicValNat p (4 * Int.natAbs (d ^ 2)) := by simp
        _ = padicValNat p (4 * (Int.natAbs d) ^ 2) := by simp [Int.natAbs_pow]
        _ = padicValNat p 4 + padicValNat p ((Int.natAbs d) ^ 2) := hmul
        _ = 0 + (2 * padicValNat p (Int.natAbs d)) := by simp [hval4, hpow]
        _ = 2 * padicValNat p (Int.natAbs d) := by ring
    refine ⟨padicValNat p (Int.natAbs d), ?_⟩
    simpa [Nat.two_mul] using hfinal

theorem no_integer_hypotenuse
    (a r2 r3 g : ℤ)
    (hgeom :
      (((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) / (2 * r2)) ^ 2 +
        ((((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) / (2 * r3)) ^ 2) =
          (g : ℚ) ^ 2)
    (hr2 : r2 ∣ a)
    (hr3 : r3 ∣ a)
    (hextra :
      ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧
        Odd (padicValNat p (Int.natAbs (r2 ^ 2 + r3 ^ 2)))) :
    ¬ ∃ d : ℤ, a ^ 2 + g ^ 2 = d ^ 2 := by
  intro hd
  rcases hd with ⟨d, hd⟩
  rcases derive_product_identity a r2 r3 g hgeom hr2 hr3 with ⟨t, ht⟩

  have hstar : 4 * d ^ 2 = (r2 ^ 2 + r3 ^ 2) * (t ^ 2 + 1) := by
    calc
      4 * d ^ 2 = 4 * (a ^ 2 + g ^ 2) := by simp [hd]
      _ = (r2 ^ 2 + r3 ^ 2) * (t ^ 2 + 1) := ht

  rcases hextra with ⟨p, hpprime, hpmod4, hodd_rsum⟩

  have hpnodvd : ¬ p ∣ Int.natAbs (t ^ 2 + 1) :=
    prime_three_mod_four_not_dvd_sq_add_one p hpprime hpmod4 t

  have hodd_left : Odd (padicValNat p (Int.natAbs (4 * d ^ 2))) := by
    have hodd_prod :
        Odd (padicValNat p (Int.natAbs ((r2 ^ 2 + r3 ^ 2) * (t ^ 2 + 1)))) :=
      odd_valuation_of_product
        p hpprime (r2 ^ 2 + r3 ^ 2) (t ^ 2 + 1) hodd_rsum hpnodvd
    simpa [hstar] using hodd_prod

  have hp_ne_two : p ≠ 2 := by
    intro hp2
    omega

  have heven_left : Even (padicValNat p (Int.natAbs (4 * d ^ 2))) :=
    even_valuation_four_mul_square p hpprime hp_ne_two d

  exact (Nat.not_odd_iff_even.mpr heven_left) hodd_left

def IsPerfectCuboid (a b c d e f g : ℤ) : Prop :=
  a ^ 2 + b ^ 2 = e ^ 2 ∧
    a ^ 2 + c ^ 2 = f ^ 2 ∧
    b ^ 2 + c ^ 2 = g ^ 2 ∧
    a ^ 2 + g ^ 2 = d ^ 2

theorem no_perfect_cuboid_under_extra_hypothesis
    (a r2 r3 g : ℤ)
    (hgeom :
      (((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) / (2 * r2)) ^ 2 +
        ((((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) / (2 * r3)) ^ 2) =
          (g : ℚ) ^ 2)
    (hr2 : r2 ∣ a)
    (hr3 : r3 ∣ a)
    (hextra :
      ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧
        Odd (padicValNat p (Int.natAbs (r2 ^ 2 + r3 ^ 2)))) :
    ¬ ∃ b c d e f : ℤ, IsPerfectCuboid a b c d e f g := by
  intro h
  rcases h with ⟨b, c, d, e, f, hcuboid⟩
  exact (no_integer_hypotenuse a r2 r3 g hgeom hr2 hr3 hextra) ⟨d, hcuboid.2.2.2⟩

theorem parametrized_faces_and_no_space_diagonal
    (a r2 r3 g : ℤ)
    (hr2nz : r2 ≠ 0)
    (hr3nz : r3 ≠ 0)
    (hgeom :
      (((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) / (2 * r2)) ^ 2 +
        ((((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) / (2 * r3)) ^ 2) =
          (g : ℚ) ^ 2)
    (hr2 : r2 ∣ a)
    (hr3 : r3 ∣ a)
    (hextra :
      ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧
        Odd (padicValNat p (Int.natAbs (r2 ^ 2 + r3 ^ 2)))) :
    ∃ b e c f : ℚ,
      (a : ℚ) ^ 2 + b ^ 2 = e ^ 2 ∧
        (a : ℚ) ^ 2 + c ^ 2 = f ^ 2 ∧
        b ^ 2 + c ^ 2 = (g : ℚ) ^ 2 ∧
        ¬ ∃ d : ℤ, a ^ 2 + g ^ 2 = d ^ 2 := by
  let aq : ℚ := a
  let r2q : ℚ := r2
  let r3q : ℚ := r3
  have hr2q : r2q ≠ 0 := by
    dsimp [r2q]
    exact_mod_cast hr2nz
  have hr3q : r3q ≠ 0 := by
    dsimp [r3q]
    exact_mod_cast hr3nz
  have hgeomQ :
      ((aq ^ 2 - r2q ^ 2) / (2 * r2q)) ^ 2 +
          ((aq ^ 2 - r3q ^ 2) / (2 * r3q)) ^ 2 =
        (g : ℚ) ^ 2 := by
    simpa [aq, r2q, r3q, Int.cast_sub, Int.cast_pow] using hgeom
  have hsys :=
    divisor_system_with_g_sound_rational aq r2q r3q (g : ℚ) hr2q hr3q hgeomQ
  refine ⟨_, _, _, _, hsys.1, hsys.2.1, hsys.2.2, ?_⟩
  exact no_integer_hypotenuse a r2 r3 g hgeom hr2 hr3 hextra

section GlobalBridge

def IsPositivePerfectCuboid (a b c d e f g : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧
    IsPerfectCuboid a b c d e f g

lemma int_lt_of_sq_lt_sq_of_pos {x y : ℤ} (hx : 0 < x) (hy : 0 < y) (hxy : x ^ 2 < y ^ 2) :
    x < y := by
  nlinarith

/-- Global contradiction schema:
if the divisor-parameterized `a^2 + g^2 = d^2` equation has no rational solution
for all inputs, then no positive perfect cuboid exists. -/
theorem no_positive_perfect_cuboid_of_global_no_rational_space_diagonal
    (hNoRat :
      ∀ a r₂ r₃ g : ℚ, r₂ ≠ 0 → r₃ ≠ 0 →
        ((a ^ 2 - r₂ ^ 2) / (2 * r₂)) ^ 2 + ((a ^ 2 - r₃ ^ 2) / (2 * r₃)) ^ 2 = g ^ 2 →
        ¬ ∃ d : ℚ, a ^ 2 + g ^ 2 = d ^ 2) :
    ¬ ∃ a b c d e f g : ℤ, IsPositivePerfectCuboid a b c d e f g := by
  intro h
  rcases h with ⟨a, b, c, d, e, f, g, hpos⟩
  rcases hpos with ⟨ha, hb, hc, hd, he, hf, hgpos, hcuboid⟩
  rcases hcuboid with ⟨h₂, h₃, hg, hspace⟩

  have hbe_sq : b ^ 2 < e ^ 2 := by
    have ha_sq_pos : 0 < a ^ 2 := by nlinarith [ha]
    have hsum : b ^ 2 + a ^ 2 = e ^ 2 := by
      nlinarith [h₂]
    nlinarith [ha_sq_pos, hsum]
  have hcf_sq : c ^ 2 < f ^ 2 := by
    have ha_sq_pos : 0 < a ^ 2 := by nlinarith [ha]
    have hsum : c ^ 2 + a ^ 2 = f ^ 2 := by
      nlinarith [h₃]
    nlinarith [ha_sq_pos, hsum]
  have h₂lt : b < e := int_lt_of_sq_lt_sq_of_pos hb he hbe_sq
  have h₃lt : c < f := int_lt_of_sq_lt_sq_of_pos hc hf hcf_sq

  rcases divisor_system_with_g_complete_integer h₂ h₃ hg h₂lt h₃lt with
    ⟨r₂, r₃, hr₂, hr₃, hbParam, heParam, hcParam, hfParam, hgeom⟩

  have hNoRatHere : ¬ ∃ dQ : ℚ, (a : ℚ) ^ 2 + (g : ℚ) ^ 2 = dQ ^ 2 :=
    hNoRat (a := (a : ℚ)) (r₂ := r₂) (r₃ := r₃) (g := (g : ℚ)) hr₂ hr₃ hgeom

  have hspaceQ : (a : ℚ) ^ 2 + (g : ℚ) ^ 2 = (d : ℚ) ^ 2 := by
    exact_mod_cast hspace

  exact hNoRatHere ⟨(d : ℚ), hspaceQ⟩

/-- Final global form directly aligned with the hypotheses/signature used by
`no_integer_hypotenuse` (from the nonexistence development).

Interpretation: if every hypothetical positive perfect cuboid instance yields
integer parameters satisfying those exact hypotheses, then positive perfect
cuboids do not exist. -/
theorem no_positive_perfect_cuboid_of_no_integer_hypotenuse_schema
    (hSchema :
      ∀ a b c d e f g : ℤ, IsPositivePerfectCuboid a b c d e f g →
        ∃ r2 r3 : ℤ,
          (((a ^ 2 - r2 ^ 2 : ℤ) : ℚ) / (2 * r2)) ^ 2 +
              ((((a ^ 2 - r3 ^ 2 : ℤ) : ℚ) / (2 * r3)) ^ 2) =
            (g : ℚ) ^ 2 ∧
          r2 ∣ a ∧
          r3 ∣ a ∧
          (∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧
            Odd (padicValNat p (Int.natAbs (r2 ^ 2 + r3 ^ 2))))) :
    ¬ ∃ a b c d e f g : ℤ, IsPositivePerfectCuboid a b c d e f g := by
  intro h
  rcases h with ⟨a, b, c, d, e, f, g, hPosCuboid⟩
  rcases hSchema a b c d e f g hPosCuboid with
    ⟨r2, r3, hgeom, hr2, hr3, hextra⟩
  rcases hPosCuboid with ⟨ha, hb, hc, hd, he, hf, hg, hcuboid⟩
  have hNoD : ¬ ∃ d0 : ℤ, a ^ 2 + g ^ 2 = d0 ^ 2 :=
    no_integer_hypotenuse a r2 r3 g hgeom hr2 hr3 hextra
  exact hNoD ⟨d, hcuboid.2.2.2⟩

end GlobalBridge

end DiophantineA2PlusG2ExtraHypothesis
