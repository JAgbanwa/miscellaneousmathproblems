import Mathlib

/-!
Formalization skeleton for the proposition in `proof_with_extra_hypothesis.tex`.

Statement (informal):
If
  ((a^2 - r2^2)/(2r2))^2 + ((a^2 - r3^2)/(2r3))^2 = g^2,
with `r2 ∣ a`, `r3 ∣ a`, and there is a prime `p ≡ 3 (mod 4)` such that
`v_p(r2^2 + r3^2)` is odd, then `a^2 + g^2 = d^2` has no integer solution `d`.

This file encodes the theorem and provides a complete Lean proof.
All bridge lemmas used in the argument are fully formalized.
-/

namespace DiophantineA2PlusG2ExtraHypothesis

open Int

lemma expanded_numerator_identity (a r2 r3 : ℤ) :
    r3 ^ 2 * (a ^ 2 - r2 ^ 2) ^ 2 + r2 ^ 2 * (a ^ 2 - r3 ^ 2) ^ 2 =
      (r2 ^ 2 + r3 ^ 2) * (a ^ 4 + r2 ^ 2 * r3 ^ 2) - 4 * a ^ 2 * r2 ^ 2 * r3 ^ 2 := by
  ring

/-- Algebraic reduction from the geometric hypothesis to the product identity
`4(a^2 + g^2) = (r2^2 + r3^2)(t^2 + 1)`, using `r2 ∣ a` and `r3 ∣ a`. -/
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
      linarith [h0, hsq]
    have h4gq : (4 : ℚ) * (g : ℚ) ^ 2 = (r3 : ℚ) ^ 2 := by nlinarith [hgq]
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
      linarith [h0, hsq]
    have h4gq : (4 : ℚ) * (g : ℚ) ^ 2 = (r2 : ℚ) ^ 2 := by nlinarith [hgq]
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
    have hgeom'' :
        (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r2 : ℚ) ^ 2) ^ 2 +
            (r2 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r3 : ℚ) ^ 2) ^ 2 =
          (r3 : ℚ) ^ 2 * (r2 : ℚ) ^ 2 * (g : ℚ) ^ 2 * 4 := by
      have htmp := hgeom'
      ring_nf at htmp
      nlinarith [htmp]
    calc
      (4 : ℚ) * (r2 : ℚ) ^ 2 * (r3 : ℚ) ^ 2 * (g : ℚ) ^ 2
          = (r3 : ℚ) ^ 2 * (r2 : ℚ) ^ 2 * (g : ℚ) ^ 2 * 4 := by ring
      _ = (r3 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r2 : ℚ) ^ 2) ^ 2 +
            (r2 : ℚ) ^ 2 * ((a : ℚ) ^ 2 - (r3 : ℚ) ^ 2) ^ 2 := by
            exact hgeom''.symm

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
    nlinarith [hclear, hexpQ]

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

/-- For `p ≡ 3 (mod 4)`, `-1` is not a square modulo `p`, hence
`p ∤ (t^2 + 1)`. -/
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

/-- Valuation transfer from the product when the second factor is prime-to-`p`. -/
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

/-- For odd primes `p`, `v_p(4 d^2)` is even. -/
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
      4 * d ^ 2 = 4 * (a ^ 2 + g ^ 2) := by nlinarith [hd]
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
    -- contradiction with `p % 4 = 3`
    omega

  have heven_left : Even (padicValNat p (Int.natAbs (4 * d ^ 2))) :=
    even_valuation_four_mul_square p hpprime hp_ne_two d

  exact (Nat.not_odd_iff_even.mpr heven_left) hodd_left

end DiophantineA2PlusG2ExtraHypothesis
