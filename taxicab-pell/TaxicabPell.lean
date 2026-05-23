import Mathlib

/-!
# Formalization of "A Closed-Form Symbolic Generator and Infinite Families
# for Aⁿ + Bⁿ = Cⁿ + Dⁿ, n = 2, 3"

This file formalizes the main results from:

  Jamal Agbanwa, "A Closed-Form Symbolic Generator and Infinite Families
  for Aⁿ + Bⁿ = Cⁿ + Dⁿ, n = 2, 3: Divisor Parametrization, Pell
  Equations, and Combinatorial Structure", May 2026.

## Results formalized

| Label                    | Paper ref          | Status          |
|--------------------------|--------------------|-----------------|
| `n2_divisor_param`       | §3, Eq (3.2)       | ✓ proved        |
| `n3_divisor_identity`    | Theorem 4.1        | ✓ proved        |
| `pell_poly_identity`     | Lemma 5.1 core     | ✓ ring          |
| `pell_reduction_iff`     | Lemma 5.1          | ✓ proved        |
| `unit_sum_odd`           | integrality helper | ✓ proved        |
| `family_I_pell_eq`       | Proposition 5.2    | ✓ proved        |
| `family_II_pell_eq`      | Proposition 5.3    | ✓ proved        |
| `completeness`           | Theorem 5.4        | ✓ proved        |
| `integrality_family_I`   | Theorem 6.1        | ✓ proved        |
| `main_identity_family_I` | Theorem 6.1        | ✓ proved        |
| `positivity_family_I`    | Theorem 6.1        | ✓ proved        |
| `distinctness_family_I`  | Corollary 6.1      | ✓ proved        |
| `hardy_ramanujan`        | Corollary 6.3      | ✓ norm_num      |
| `recurrence_C_family_I`  | Theorem 7.1        | ✓ proved        |
| `growth_monotone_re_I`   | Theorem 7.2(i)     | ✓ proved        |
| `growth_exponential`     | Theorem 7.2(ii)    | ✓ proved        |
-/

open Int Zsqrtd

namespace TaxicabPell

-- Multiplication component lemmas for ℤ[√3].
-- `zs_mul_re` / `zs_mul_im` are not present in all Mathlib versions;
-- these local aliases prove the same facts by definitional reduction (rfl).
private theorem zs_mul_re (a b : Zsqrtd (3 : ℤ)) :
    (a * b).re = a.re * b.re + 3 * a.im * b.im := rfl
private theorem zs_mul_im (a b : Zsqrtd (3 : ℤ)) :
    (a * b).im = a.re * b.im + a.im * b.re := rfl

-- ============================================================================
-- §1.  The ring ℤ[√3]
-- ============================================================================

/-- The fundamental unit ε₀ = 2 + √3 of ℤ[√3]; Nrm(ε₀) = 1. -/
def ε₀ : Zsqrtd (3 : ℤ) := ⟨2, 1⟩

/-- The squared unit ε₁ = 7 + 4√3 = ε₀²; Nrm(ε₁) = 1. -/
def ε₁ : Zsqrtd (3 : ℤ) := ⟨7, 4⟩

/-- Family I seed: 15 + 7√3; Nrm = 78. -/
def seed_I : Zsqrtd (3 : ℤ) := ⟨15, 7⟩

/-- Family II seed: 9 + √3; Nrm = 78. -/
def seed_II : Zsqrtd (3 : ℤ) := ⟨9, 1⟩

@[simp] lemma norm_ε₀ : Zsqrtd.norm ε₀ = 1 := by native_decide
@[simp] lemma norm_ε₁ : Zsqrtd.norm ε₁ = 1 := by native_decide
@[simp] lemma norm_seed_I : Zsqrtd.norm seed_I = 78 := by native_decide
@[simp] lemma norm_seed_II : Zsqrtd.norm seed_II = 78 := by native_decide
lemma ε₁_eq_ε₀_sq : ε₁ = ε₀ ^ 2 := by native_decide

-- ============================================================================
-- §2.  n = 2 divisor parametrization
-- ============================================================================

theorem n2_divisor_param (Δ r₁ r₂ : ℚ) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
    let A := (Δ + r₁ ^ 2) / (2 * r₁)
    let C := (Δ - r₁ ^ 2) / (2 * r₁)
    let B := (Δ - r₂ ^ 2) / (2 * r₂)
    let D := (Δ + r₂ ^ 2) / (2 * r₂)
    A ^ 2 + B ^ 2 = C ^ 2 + D ^ 2 := by
  simp only; field_simp; ring

-- ============================================================================
-- §3.  n = 3 divisor parametrization
-- ============================================================================

theorem n3_divisor_identity (Δ r₁ r₂ t₁ t₂ : ℚ)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (ht₁_sq : t₁ ^ 2 = 12 * Δ * r₁ - 3 * r₁ ^ 4)
    (ht₂_sq : t₂ ^ 2 = 12 * Δ * r₂ - 3 * r₂ ^ 4) :
    let C := (-3 * r₁ ^ 2 + t₁) / (6 * r₁)
    let B := (-3 * r₂ ^ 2 + t₂) / (6 * r₂)
    (C + r₁) ^ 3 + B ^ 3 = C ^ 3 + (B + r₂) ^ 3 := by
  simp only
  set C := (-3 * r₁ ^ 2 + t₁) / (6 * r₁)
  set B := (-3 * r₂ ^ 2 + t₂) / (6 * r₂)
  have hΔ₁ : (C + r₁) ^ 3 - C ^ 3 = Δ := by
    simp only [C]; field_simp; nlinarith [sq_nonneg t₁, ht₁_sq]
  have hΔ₂ : (B + r₂) ^ 3 - B ^ 3 = Δ := by
    simp only [B]; field_simp; nlinarith [sq_nonneg t₂, ht₂_sq]
  linarith

example : (12 : ℤ) ^ 3 + 1 ^ 3 = 9 ^ 3 + 10 ^ 3 := by norm_num

-- ============================================================================
-- §4.  Pell reduction identity  (Lemma 5.1)
-- ============================================================================

lemma pell_poly_identity (C B s : ℤ) :
    4 * ((C + 3 * s) ^ 3 + B ^ 3 - C ^ 3 - (B + 9 * s) ^ 3) =
    9 * s * ((2 * C + 3 * s) ^ 2 - 3 * (2 * B + 9 * s) ^ 2 - 78 * s ^ 2) := by ring

theorem pell_reduction_iff (C B s : ℤ) (hs : s ≠ 0) :
    (C + 3 * s) ^ 3 + B ^ 3 = C ^ 3 + (B + 9 * s) ^ 3 ↔
    (2 * C + 3 * s) ^ 2 - 3 * (2 * B + 9 * s) ^ 2 = 78 * s ^ 2 := by
  have h9s : 9 * s ≠ 0 := mul_ne_zero (by norm_num) hs
  constructor
  · intro h
    have hcubic : (C + 3 * s) ^ 3 + B ^ 3 - C ^ 3 - (B + 9 * s) ^ 3 = 0 := by linarith
    have hprod : 9 * s * ((2 * C + 3 * s) ^ 2 - 3 * (2 * B + 9 * s) ^ 2 - 78 * s ^ 2) = 0 := by
      linear_combination -(pell_poly_identity C B s) + 4 * hcubic
    linarith [(mul_eq_zero.mp hprod).resolve_left h9s]
  · intro h
    have hquad : (2 * C + 3 * s) ^ 2 - 3 * (2 * B + 9 * s) ^ 2 - 78 * s ^ 2 = 0 := by linarith
    have hprod : 4 * ((C + 3 * s) ^ 3 + B ^ 3 - C ^ 3 - (B + 9 * s) ^ 3) = 0 := by
      linear_combination pell_poly_identity C B s + 9 * s * hquad
    linarith [(mul_eq_zero.mp hprod).resolve_left (by norm_num : (4:ℤ) ≠ 0)]

-- ============================================================================
-- §5.  Pell equation in ℤ[√3]
-- ============================================================================

/-- Every unit solution u² - 3v² = 1 has u + v odd. -/
lemma unit_sum_odd (u v : ℤ) (h : u ^ 2 - 3 * v ^ 2 = 1) : ¬ Even (u + v) := by
  intro ⟨k, hk⟩
  obtain ⟨m, hm⟩ : ∃ m, u = v + 2 * m := ⟨k - v, by omega⟩
  rw [hm] at h
  have : 2 ∣ (v + 2 * m) ^ 2 - 3 * v ^ 2 :=
    ⟨2 * m ^ 2 + 2 * m * v - v ^ 2, by ring⟩
  rw [h] at this
  exact absurd this (by norm_num)

/-- Multiplication by a unit preserves odd parity of both components. -/
lemma mul_preserves_odd_parity (a b u v : ℤ)
    (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hunit : u ^ 2 - 3 * v ^ 2 = 1) :
    (a * u + 3 * b * v) % 2 = 1 ∧ (a * v + b * u) % 2 = 1 := by
  have hodd_sum : ¬ Even (u + v) := unit_sum_odd u v hunit
  have hsum : (u + v) % 2 = 1 := by
    rcases Int.even_or_odd (u + v) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd ⟨k, hk⟩ hodd_sum
    · omega
  obtain ⟨qa, ha'⟩ : ∃ qa, a = 2 * qa + 1 := ⟨a / 2, by omega⟩
  obtain ⟨qb, hb'⟩ : ∃ qb, b = 2 * qb + 1 := ⟨b / 2, by omega⟩
  subst ha'; subst hb'
  constructor
  · have : (2 * qa + 1) * u + 3 * (2 * qb + 1) * v =
           2 * (qa * u + 3 * qb * v + v) + (u + v) := by ring
    rw [this]; omega
  · have : (2 * qa + 1) * v + (2 * qb + 1) * u =
           2 * (qa * v + qb * u) + (u + v) := by ring
    rw [this]; omega

-- ============================================================================
-- §5.2  The two Pell families
-- ============================================================================

def familyI_element (unit : Zsqrtd (3 : ℤ)) (n : ℕ) : Zsqrtd (3 : ℤ) := seed_I * unit ^ n
def familyII_element (unit : Zsqrtd (3 : ℤ)) (n : ℕ) : Zsqrtd (3 : ℤ) := seed_II * unit ^ n

lemma norm_pow_eq_one (unit : Zsqrtd (3 : ℤ)) (hunit : Zsqrtd.norm unit = 1) (n : ℕ) :
    Zsqrtd.norm (unit ^ n) = 1 := by
  induction n with
  | zero => simp [Zsqrtd.norm]
  | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, hunit, mul_one]

theorem family_I_pell_eq (unit : Zsqrtd (3 : ℤ)) (hunit : Zsqrtd.norm unit = 1) (n : ℕ) :
    Zsqrtd.norm (familyI_element unit n) = 78 := by
  simp only [familyI_element, Zsqrtd.norm_mul, norm_seed_I,
             norm_pow_eq_one unit hunit n, mul_one]

theorem family_II_pell_eq (unit : Zsqrtd (3 : ℤ)) (hunit : Zsqrtd.norm unit = 1) (n : ℕ) :
    Zsqrtd.norm (familyII_element unit n) = 78 := by
  simp only [familyII_element, Zsqrtd.norm_mul, norm_seed_II,
             norm_pow_eq_one unit hunit n, mul_one]

lemma family_I_pell_eq_components (unit : Zsqrtd (3 : ℤ))
    (hunit : Zsqrtd.norm unit = 1) (n : ℕ) :
    (familyI_element unit n).re ^ 2 - 3 * (familyI_element unit n).im ^ 2 = 78 := by
  have h := family_I_pell_eq unit hunit n
  simp only [Zsqrtd.norm] at h
  nlinarith [sq_nonneg (familyI_element unit n).re, sq_nonneg (familyI_element unit n).im]

lemma family_II_pell_eq_components (unit : Zsqrtd (3 : ℤ))
    (hunit : Zsqrtd.norm unit = 1) (n : ℕ) :
    (familyII_element unit n).re ^ 2 - 3 * (familyII_element unit n).im ^ 2 = 78 := by
  have h := family_II_pell_eq unit hunit n
  simp only [Zsqrtd.norm] at h
  nlinarith [sq_nonneg (familyII_element unit n).re, sq_nonneg (familyII_element unit n).im]

-- ============================================================================
-- §5.3  Completeness
-- ============================================================================

lemma exactly_two_reduced_solutions :
    ∀ x y : ℤ, 0 < x → 0 < y → x ^ 2 - 3 * y ^ 2 = 78 → 2 * y ≤ x →
    (x = 9 ∧ y = 1) ∨ (x = 15 ∧ y = 7) := by
  intro x y hx hy heq hred
  have hy_bound : y ≤ 8 := by nlinarith [sq_nonneg y]
  have hx_bound : x ≤ 16 := by nlinarith [sq_nonneg y]
  interval_cases x <;> interval_cases y <;> omega

lemma completeness_nat :
    ∀ y : ℕ, 0 < y →
    ∀ x : ℤ, 0 < x → x ^ 2 - 3 * (y : ℤ) ^ 2 = 78 →
    (∃ n : ℕ, (familyI_element ε₀ n).re = x ∧ (familyI_element ε₀ n).im = (y : ℤ)) ∨
    (∃ n : ℕ, (familyII_element ε₀ n).re = x ∧ (familyII_element ε₀ n).im = (y : ℤ)) := by
  intro y
  refine Nat.strong_induction_on y ?_
  intro y ih hy x hx heq
  by_cases hred : 2 * (y : ℤ) ≤ x
  · have hyz : 0 < (y : ℤ) := by exact_mod_cast hy
    have hcls := exactly_two_reduced_solutions x (y : ℤ) hx hyz heq hred
    rcases hcls with hII | hI
    · rcases hII with ⟨hx9, hy1z⟩
      have hy1 : y = 1 := by exact_mod_cast hy1z
      right
      refine ⟨0, ?_, ?_⟩
      · rw [hx9]
        simp [familyII_element, seed_II]
      · rw [hy1]
        simp [familyII_element, seed_II]
    · rcases hI with ⟨hx15, hy7z⟩
      have hy7 : y = 7 := by exact_mod_cast hy7z
      left
      refine ⟨0, ?_, ?_⟩
      · rw [hx15]
        simp [familyI_element, seed_I]
      · rw [hy7]
        simp [familyI_element, seed_I]
  · have hnotred : x < 2 * (y : ℤ) := lt_of_not_ge hred
    set x' : ℤ := 2 * x - 3 * (y : ℤ)
    set y' : ℤ := 2 * (y : ℤ) - x
    have hy'_pos : 0 < y' := by
      dsimp [y']
      linarith
    have hxy : (y : ℤ) < x := by
      nlinarith [heq]
    have hy'_lt : y' < (y : ℤ) := by
      dsimp [y']
      linarith
    have hx'_pos : 0 < x' := by
      have hsq : (2 * x) ^ 2 > (3 * (y : ℤ)) ^ 2 := by
        nlinarith [heq, hy]
      have h2x3y : 3 * (y : ℤ) < 2 * x := by
        nlinarith [hsq, hx, hy]
      dsimp [x']
      linarith
    have heq' : x' ^ 2 - 3 * y' ^ 2 = 78 := by
      dsimp [x', y']
      nlinarith [heq]
    set k : ℕ := Int.toNat y'
    have hy'_nonneg : 0 ≤ y' := le_of_lt hy'_pos
    have hk_eq : (k : ℤ) = y' := by
      simp [k, Int.toNat_of_nonneg hy'_nonneg]
    have hk_pos : 0 < k := by
      have : (0 : ℤ) < (k : ℤ) := by simpa [hk_eq] using hy'_pos
      exact_mod_cast this
    have hk_lt : k < y := by
      have : (k : ℤ) < (y : ℤ) := by simpa [hk_eq] using hy'_lt
      exact_mod_cast this
    have heqk : x' ^ 2 - 3 * (k : ℤ) ^ 2 = 78 := by
      simpa [hk_eq] using heq'
    have hrec := ih k hk_lt hk_pos x' hx'_pos heqk
    rcases hrec with hI | hII
    · rcases hI with ⟨n, hxn, hyn⟩
      left
      refine ⟨n + 1, ?_, ?_⟩
      · have hstep : (familyI_element ε₀ (n + 1)).re =
            2 * (familyI_element ε₀ n).re + 3 * (familyI_element ε₀ n).im := by
          simp [familyI_element, pow_succ, ← mul_assoc, ε₀]
          ring
        have hyn' : (familyI_element ε₀ n).im = y' := by
          calc
            (familyI_element ε₀ n).im = (k : ℤ) := hyn
            _ = y' := hk_eq
        have hxback : x = 2 * x' + 3 * y' := by
          dsimp [x', y']
          ring
        calc
          (familyI_element ε₀ (n + 1)).re
              = 2 * (familyI_element ε₀ n).re + 3 * (familyI_element ε₀ n).im := hstep
          _ = 2 * x' + 3 * y' := by rw [hxn, hyn']
          _ = x := by linarith [hxback]
      · have hstep : (familyI_element ε₀ (n + 1)).im =
            (familyI_element ε₀ n).re + 2 * (familyI_element ε₀ n).im := by
          simp [familyI_element, pow_succ, ← mul_assoc, ε₀]
          ring
        have hyn' : (familyI_element ε₀ n).im = y' := by
          calc
            (familyI_element ε₀ n).im = (k : ℤ) := hyn
            _ = y' := hk_eq
        have hyback : (y : ℤ) = x' + 2 * y' := by
          dsimp [x', y']
          ring
        calc
          (familyI_element ε₀ (n + 1)).im
              = (familyI_element ε₀ n).re + 2 * (familyI_element ε₀ n).im := hstep
          _ = x' + 2 * y' := by rw [hxn, hyn']
          _ = (y : ℤ) := by linarith [hyback]
    · rcases hII with ⟨n, hxn, hyn⟩
      right
      refine ⟨n + 1, ?_, ?_⟩
      · have hstep : (familyII_element ε₀ (n + 1)).re =
            2 * (familyII_element ε₀ n).re + 3 * (familyII_element ε₀ n).im := by
          simp [familyII_element, pow_succ, ← mul_assoc, ε₀]
          ring
        have hyn' : (familyII_element ε₀ n).im = y' := by
          calc
            (familyII_element ε₀ n).im = (k : ℤ) := hyn
            _ = y' := hk_eq
        have hxback : x = 2 * x' + 3 * y' := by
          dsimp [x', y']
          ring
        calc
          (familyII_element ε₀ (n + 1)).re
              = 2 * (familyII_element ε₀ n).re + 3 * (familyII_element ε₀ n).im := hstep
          _ = 2 * x' + 3 * y' := by rw [hxn, hyn']
          _ = x := by linarith [hxback]
      · have hstep : (familyII_element ε₀ (n + 1)).im =
            (familyII_element ε₀ n).re + 2 * (familyII_element ε₀ n).im := by
          simp [familyII_element, pow_succ, ← mul_assoc, ε₀]
          ring
        have hyn' : (familyII_element ε₀ n).im = y' := by
          calc
            (familyII_element ε₀ n).im = (k : ℤ) := hyn
            _ = y' := hk_eq
        have hyback : (y : ℤ) = x' + 2 * y' := by
          dsimp [x', y']
          ring
        calc
          (familyII_element ε₀ (n + 1)).im
              = (familyII_element ε₀ n).re + 2 * (familyII_element ε₀ n).im := hstep
          _ = x' + 2 * y' := by rw [hxn, hyn']
          _ = (y : ℤ) := by linarith [hyback]

theorem completeness :
    ∀ x y : ℤ, 0 < x → 0 < y → x ^ 2 - 3 * y ^ 2 = 78 →
    (∃ n : ℕ, (familyI_element ε₀ n).re = x ∧ (familyI_element ε₀ n).im = y) ∨
    (∃ n : ℕ, (familyII_element ε₀ n).re = x ∧ (familyII_element ε₀ n).im = y) := by
  intro x y hx hy heq
  set yn : ℕ := Int.toNat y
  have hy_eq : (yn : ℤ) = y := by
    simp [yn, Int.toNat_of_nonneg (le_of_lt hy)]
  have hy_nat_pos : 0 < yn := by
    have : (0 : ℤ) < (yn : ℤ) := by simpa [hy_eq] using hy
    exact_mod_cast this
  have heqn : x ^ 2 - 3 * (yn : ℤ) ^ 2 = 78 := by simpa [hy_eq] using heq
  have h := completeness_nat yn hy_nat_pos x hx heqn
  simpa [hy_eq] using h

-- ============================================================================
-- §6.  Integrality
-- ============================================================================

theorem family_I_odd_components (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1) (n : ℕ) :
    (familyI_element unit n).re % 2 = 1 ∧ (familyI_element unit n).im % 2 = 1 := by
  induction n with
  | zero => simp [familyI_element, seed_I]
  | succ k ih =>
    obtain ⟨ih_re, ih_im⟩ := ih
    simp only [familyI_element, pow_succ, ← mul_assoc]
    exact mul_preserves_odd_parity
      (seed_I * unit ^ k).re (seed_I * unit ^ k).im unit.re unit.im
      ih_re ih_im hunit_pell

theorem family_II_odd_components (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1) (n : ℕ) :
    (familyII_element unit n).re % 2 = 1 ∧ (familyII_element unit n).im % 2 = 1 := by
  induction n with
  | zero => simp [familyII_element, seed_II]
  | succ k ih =>
    obtain ⟨ih_re, ih_im⟩ := ih
    simp only [familyII_element, pow_succ, ← mul_assoc]
    exact mul_preserves_odd_parity
      (seed_II * unit ^ k).re (seed_II * unit ^ k).im unit.re unit.im
      ih_re ih_im hunit_pell

-- ============================================================================
-- §6.  Sequence definitions
-- ============================================================================

def C_m_I (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) : ℤ :=
  (3 : ℤ) ^ m * ((familyI_element unit n).re - 3) / 2

def B_m_I (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) : ℤ :=
  (3 : ℤ) ^ m * ((familyI_element unit n).im - 9) / 2

def A_m_I (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) : ℤ :=
  C_m_I unit m n + (3 : ℤ) ^ (m + 1)

def D_m_I (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) : ℤ :=
  B_m_I unit m n + (3 : ℤ) ^ (m + 2)

def C_m_II (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) : ℤ :=
  (3 : ℤ) ^ m * ((familyII_element unit n).re - 3) / 2

def B_m_II (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) : ℤ :=
  (3 : ℤ) ^ m * ((familyII_element unit n).im - 9) / 2

def A_m_II (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) : ℤ :=
  C_m_II unit m n + (3 : ℤ) ^ (m + 1)

def D_m_II (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) : ℤ :=
  B_m_II unit m n + (3 : ℤ) ^ (m + 2)

-- ============================================================================
-- §6.  Integrality theorem
-- ============================================================================

theorem integrality_family_I (unit : Zsqrtd (3 : ℤ)) (m n : ℕ)
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1) :
    2 ∣ (3 : ℤ) ^ m * ((familyI_element unit n).re - 3) ∧
    2 ∣ (3 : ℤ) ^ m * ((familyI_element unit n).im - 9) := by
  obtain ⟨hre, him⟩ := family_I_odd_components unit hunit_pell n
  exact ⟨dvd_mul_of_dvd_right ⟨((familyI_element unit n).re - 3) / 2, by omega⟩ _,
         dvd_mul_of_dvd_right ⟨((familyI_element unit n).im - 9) / 2, by omega⟩ _⟩

theorem integrality_family_II (unit : Zsqrtd (3 : ℤ)) (m n : ℕ)
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1) :
    2 ∣ (3 : ℤ) ^ m * ((familyII_element unit n).re - 3) ∧
    2 ∣ (3 : ℤ) ^ m * ((familyII_element unit n).im - 9) := by
  obtain ⟨hre, him⟩ := family_II_odd_components unit hunit_pell n
  exact ⟨dvd_mul_of_dvd_right ⟨((familyII_element unit n).re - 3) / 2, by omega⟩ _,
         dvd_mul_of_dvd_right ⟨((familyII_element unit n).im - 9) / 2, by omega⟩ _⟩

-- ============================================================================
-- §6.  Main identity
-- ============================================================================

lemma norm_one_to_pell (unit : Zsqrtd (3 : ℤ)) (hunit : Zsqrtd.norm unit = 1) :
    unit.re ^ 2 - 3 * unit.im ^ 2 = 1 := by
  simp only [Zsqrtd.norm] at hunit
  nlinarith [sq_nonneg unit.re, sq_nonneg unit.im]

/-- **Theorem 6.1**: A_m³ + B_m³ = C_m³ + D_m³ for Family I. -/
theorem main_identity_family_I (unit : Zsqrtd (3 : ℤ))
    (hunit_norm : Zsqrtd.norm unit = 1) (m n : ℕ) :
    A_m_I unit m n ^ 3 + B_m_I unit m n ^ 3 =
    C_m_I unit m n ^ 3 + D_m_I unit m n ^ 3 := by
  simp only [A_m_I, D_m_I]
  have hunit_pell := norm_one_to_pell unit hunit_norm
  obtain ⟨hdiv_re, hdiv_im⟩ := integrality_family_I unit m n hunit_pell
  obtain ⟨c_re, hc_re⟩ := hdiv_re
  obtain ⟨c_im, hc_im⟩ := hdiv_im
  set xn := (familyI_element unit n).re
  set yn := (familyI_element unit n).im
  set sm := (3 : ℤ) ^ m with hsm_def
  have hs : sm ≠ 0 := by positivity
  have hpell : xn ^ 2 - 3 * yn ^ 2 = 78 := family_I_pell_eq_components unit hunit_norm n
  have h3m1 : (3 : ℤ) ^ (m + 1) = 3 * sm := by simp only [pow_succ, ← hsm_def]; ring
  have h3m2 : (3 : ℤ) ^ (m + 2) = 9 * sm := by
    rw [show m + 2 = m + 1 + 1 from rfl, pow_succ, h3m1]; ring
  rw [h3m1, h3m2]
  -- Reduce to Pell condition
  have hscaled : (2 * C_m_I unit m n + 3 * sm) ^ 2 -
                 3 * (2 * B_m_I unit m n + 9 * sm) ^ 2 = 78 * sm ^ 2 := by
    have hCeq : C_m_I unit m n = c_re := by show sm * (xn - 3) / 2 = c_re; omega
    have hBeq : B_m_I unit m n = c_im := by show sm * (yn - 9) / 2 = c_im; omega
    have hxn : 2 * c_re + 3 * sm = sm * xn := by
      linarith [show sm * (xn - 3) = sm * xn - 3 * sm from by ring]
    have hyn : 2 * c_im + 9 * sm = sm * yn := by
      linarith [show sm * (yn - 9) = sm * yn - 9 * sm from by ring]
    rw [hCeq, hBeq, hxn, hyn]
    linear_combination sm ^ 2 * hpell
  exact (pell_reduction_iff (C_m_I unit m n) (B_m_I unit m n) sm hs).mpr hscaled

/-- **Theorem 6.1**: A_m³ + B_m³ = C_m³ + D_m³ for Family II. -/
theorem main_identity_family_II (unit : Zsqrtd (3 : ℤ))
    (hunit_norm : Zsqrtd.norm unit = 1) (m n : ℕ) :
    A_m_II unit m n ^ 3 + B_m_II unit m n ^ 3 =
    C_m_II unit m n ^ 3 + D_m_II unit m n ^ 3 := by
  simp only [A_m_II, D_m_II]
  have hunit_pell := norm_one_to_pell unit hunit_norm
  obtain ⟨hdiv_re, hdiv_im⟩ := integrality_family_II unit m n hunit_pell
  obtain ⟨c_re, hc_re⟩ := hdiv_re
  obtain ⟨c_im, hc_im⟩ := hdiv_im
  set xn := (familyII_element unit n).re
  set yn := (familyII_element unit n).im
  set sm := (3 : ℤ) ^ m with hsm_def
  have hs : sm ≠ 0 := by positivity
  have hpell : xn ^ 2 - 3 * yn ^ 2 = 78 := family_II_pell_eq_components unit hunit_norm n
  have h3m1 : (3 : ℤ) ^ (m + 1) = 3 * sm := by simp only [pow_succ, ← hsm_def]; ring
  have h3m2 : (3 : ℤ) ^ (m + 2) = 9 * sm := by
    rw [show m + 2 = m + 1 + 1 from rfl, pow_succ, h3m1]; ring
  rw [h3m1, h3m2]
  have hscaled : (2 * C_m_II unit m n + 3 * sm) ^ 2 -
                 3 * (2 * B_m_II unit m n + 9 * sm) ^ 2 = 78 * sm ^ 2 := by
    have hCeq : C_m_II unit m n = c_re := by show sm * (xn - 3) / 2 = c_re; omega
    have hBeq : B_m_II unit m n = c_im := by show sm * (yn - 9) / 2 = c_im; omega
    have hxn : 2 * c_re + 3 * sm = sm * xn := by
      linarith [show sm * (xn - 3) = sm * xn - 3 * sm from by ring]
    have hyn : 2 * c_im + 9 * sm = sm * yn := by
      linarith [show sm * (yn - 9) = sm * yn - 9 * sm from by ring]
    rw [hCeq, hBeq, hxn, hyn]
    linear_combination sm ^ 2 * hpell
  exact (pell_reduction_iff (C_m_II unit m n) (B_m_II unit m n) sm hs).mpr hscaled

-- ============================================================================
-- §6.  Positivity
-- ============================================================================

theorem positivity_family_I (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1)
    (hu_pos : 0 < unit.re) (hv_pos : 0 < unit.im) (m n : ℕ) (hn : 1 ≤ n) :
    0 < A_m_I unit m n ∧ 0 < B_m_I unit m n ∧
    0 < C_m_I unit m n ∧ 0 < D_m_I unit m n := by
  -- u² = 1 + 3v² ≥ 4, so u ≥ 2
  have hu2 : 2 ≤ unit.re := by nlinarith [sq_nonneg unit.im]
  -- For k ≥ 1: xₖ > 3 and yₖ > 9  (key lower bounds)
  have hbound : ∀ k : ℕ, 1 ≤ k →
      3 < (familyI_element unit k).re ∧ 9 < (familyI_element unit k).im := by
    intro k hk
    induction k with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · -- base case k = 1: x₁ = 15u + 21v ≥ 51 > 3, y₁ = 15v + 7u ≥ 29 > 9
        refine ⟨?_, ?_⟩
        · show 3 < (seed_I * unit ^ 1).re
          rw [pow_one, zs_mul_re]
          show 3 < (15 : ℤ) * unit.re + 3 * 7 * unit.im
          linarith
        · show 9 < (seed_I * unit ^ 1).im
          rw [pow_one, zs_mul_im]
          show 9 < (15 : ℤ) * unit.im + 7 * unit.re
          linarith
      · -- inductive step: use IH
        obtain ⟨ihr, ihi⟩ := ih (by omega)
        simp only [familyI_element] at ihr ihi ⊢
        simp only [pow_succ, ← mul_assoc]
        refine ⟨?_, ?_⟩
        · rw [zs_mul_re]
          -- re·u + 3·im·v ≥ 4·2 + 0 > 3
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ (seed_I * unit ^ j).re from by linarith)
                                (show (0 : ℤ) ≤ unit.re - 2 from by linarith),
                     mul_nonneg (show (0 : ℤ) ≤ (seed_I * unit ^ j).im from by linarith)
                                hv_pos.le]
        · rw [zs_mul_im]
          -- re·v + im·u ≥ 0 + 10·2 > 9
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ (seed_I * unit ^ j).im from by linarith)
                                (show (0 : ℤ) ≤ unit.re - 2 from by linarith),
                     mul_nonneg (show (0 : ℤ) ≤ (seed_I * unit ^ j).re from by linarith)
                                hv_pos.le]
  obtain ⟨hxn, hyn⟩ := hbound n hn
  -- Integrality: 3^m*(xₙ-3) = 2*c_re and 3^m*(yₙ-9) = 2*c_im
  obtain ⟨hdiv_re, hdiv_im⟩ := integrality_family_I unit m n hunit_pell
  obtain ⟨c_re, hc_re⟩ := hdiv_re
  obtain ⟨c_im, hc_im⟩ := hdiv_im
  set xn := (familyI_element unit n).re
  set yn := (familyI_element unit n).im
  set sm := (3 : ℤ) ^ m
  have hsm : 0 < sm := by positivity
  have hC : 0 < C_m_I unit m n := by
    show 0 < sm * (xn - 3) / 2
    have : 0 < sm * (xn - 3) := mul_pos hsm (by linarith)
    omega
  have hB : 0 < B_m_I unit m n := by
    show 0 < sm * (yn - 9) / 2
    have : 0 < sm * (yn - 9) := mul_pos hsm (by linarith)
    omega
  exact ⟨by simp only [A_m_I]; linarith [show (0 : ℤ) < (3 : ℤ) ^ (m + 1) from by positivity],
         hB, hC,
         by simp only [D_m_I]; linarith [show (0 : ℤ) < (3 : ℤ) ^ (m + 2) from by positivity]⟩

theorem positivity_family_II (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1)
    (hu_pos : 0 < unit.re) (hv_pos : 0 < unit.im) (m n : ℕ) (hn : 1 ≤ n) :
    0 < A_m_II unit m n ∧ 0 < B_m_II unit m n ∧
    0 < C_m_II unit m n ∧ 0 < D_m_II unit m n := by
  have hu2 : 2 ≤ unit.re := by nlinarith [sq_nonneg unit.im]
  have hbound : ∀ k : ℕ, 1 ≤ k →
      3 < (familyII_element unit k).re ∧ 9 < (familyII_element unit k).im := by
    intro k hk
    induction k with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · -- base case k = 1: x₁ = 9u + 3v ≥ 21 > 3, y₁ = 9v + u ≥ 11 > 9
        refine ⟨?_, ?_⟩
        · show 3 < (seed_II * unit ^ 1).re
          rw [pow_one, zs_mul_re]
          show 3 < (9 : ℤ) * unit.re + 3 * 1 * unit.im
          linarith
        · show 9 < (seed_II * unit ^ 1).im
          rw [pow_one, zs_mul_im]
          show 9 < (9 : ℤ) * unit.im + 1 * unit.re
          linarith
      · obtain ⟨ihr, ihi⟩ := ih (by omega)
        simp only [familyII_element] at ihr ihi ⊢
        simp only [pow_succ, ← mul_assoc]
        refine ⟨?_, ?_⟩
        · rw [zs_mul_re]
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ (seed_II * unit ^ j).re from by linarith)
                                (show (0 : ℤ) ≤ unit.re - 2 from by linarith),
                     mul_nonneg (show (0 : ℤ) ≤ (seed_II * unit ^ j).im from by linarith)
                                hv_pos.le]
        · rw [zs_mul_im]
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ (seed_II * unit ^ j).im from by linarith)
                                (show (0 : ℤ) ≤ unit.re - 2 from by linarith),
                     mul_nonneg (show (0 : ℤ) ≤ (seed_II * unit ^ j).re from by linarith)
                                hv_pos.le]
  obtain ⟨hxn, hyn⟩ := hbound n hn
  obtain ⟨hdiv_re, hdiv_im⟩ := integrality_family_II unit m n hunit_pell
  obtain ⟨c_re, hc_re⟩ := hdiv_re
  obtain ⟨c_im, hc_im⟩ := hdiv_im
  set xn := (familyII_element unit n).re
  set yn := (familyII_element unit n).im
  set sm := (3 : ℤ) ^ m
  have hsm : 0 < sm := by positivity
  have hC : 0 < C_m_II unit m n := by
    show 0 < sm * (xn - 3) / 2
    have : 0 < sm * (xn - 3) := mul_pos hsm (by linarith)
    omega
  have hB : 0 < B_m_II unit m n := by
    show 0 < sm * (yn - 9) / 2
    have : 0 < sm * (yn - 9) := mul_pos hsm (by linarith)
    omega
  exact ⟨by simp only [A_m_II]; linarith [show (0 : ℤ) < (3 : ℤ) ^ (m + 1) from by positivity],
         hB, hC,
         by simp only [D_m_II]; linarith [show (0 : ℤ) < (3 : ℤ) ^ (m + 2) from by positivity]⟩

-- ============================================================================
-- §6.  Distinctness
-- ============================================================================

theorem distinctness_family_I (unit : Zsqrtd (3 : ℤ)) (m n : ℕ) :
    A_m_I unit m n ≠ C_m_I unit m n := by
  simp only [A_m_I]
  have : (0 : ℤ) < (3 : ℤ) ^ (m + 1) := by positivity
  linarith

theorem distinctness_no_swap_family_I (unit : Zsqrtd (3 : ℤ))
    (_hunit_norm : Zsqrtd.norm unit = 1) (m n : ℕ) :
    ¬ (A_m_I unit m n = D_m_I unit m n ∧ B_m_I unit m n = C_m_I unit m n) := by
  intro ⟨hAD, hBC⟩
  simp only [A_m_I, D_m_I, B_m_I, C_m_I] at hAD hBC
  have h1 : (0 : ℤ) < (3 : ℤ) ^ (m + 1) := by positivity
  have h3 : (3 : ℤ) ^ (m + 2) = 3 * (3 : ℤ) ^ (m + 1) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ]; ring
  linarith

-- ============================================================================
-- §6.  Hardy–Ramanujan
-- ============================================================================

theorem hardy_ramanujan :
    (12 : ℤ) ^ 3 + 1 ^ 3 = 9 ^ 3 + 10 ^ 3 ∧ (12 : ℤ) ^ 3 + 1 ^ 3 = 1729 := by
  constructor <;> norm_num

example : A_m_II ε₀ 0 1 = 12 := by native_decide
example : B_m_II ε₀ 0 1 = 1  := by native_decide
example : C_m_II ε₀ 0 1 = 9  := by native_decide
example : D_m_II ε₀ 0 1 = 10 := by native_decide

example : A_m_I ε₁ 0 1 = 96  := by native_decide
example : B_m_I ε₁ 0 1 = 50  := by native_decide
example : C_m_I ε₁ 0 1 = 93  := by native_decide
example : D_m_I ε₁ 0 1 = 59  := by native_decide
example : (96 : ℤ) ^ 3 + 50 ^ 3 = 93 ^ 3 + 59 ^ 3 := by norm_num

-- ============================================================================
-- §7.  Recurrence relations (Theorem 7.1)
-- ============================================================================

theorem recurrence_C_family_I (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1) (m n : ℕ) :
    C_m_I unit m (n + 2) =
    2 * unit.re * C_m_I unit m (n + 1) - C_m_I unit m n +
    (3 : ℤ) ^ (m + 1) * (unit.re - 1) := by
  set sm : ℤ := (3 : ℤ) ^ m
  have h3m1 : (3 : ℤ) ^ (m + 1) = 3 * sm := by
    calc
      (3 : ℤ) ^ (m + 1) = (3 : ℤ) ^ m * 3 := by simp [pow_succ]
      _ = 3 * (3 : ℤ) ^ m := by ring
      _ = 3 * sm := by simp [sm]
  have hx1 : (familyI_element unit (n + 1)).re =
      (familyI_element unit n).re * unit.re + 3 * (familyI_element unit n).im * unit.im := by
    simp only [familyI_element, pow_succ, ← mul_assoc, zs_mul_re]
  have hy1 : (familyI_element unit (n + 1)).im =
      (familyI_element unit n).re * unit.im + (familyI_element unit n).im * unit.re := by
    simp only [familyI_element, pow_succ, ← mul_assoc, zs_mul_im]
  have hx2 : (familyI_element unit (n + 2)).re =
      (familyI_element unit (n + 1)).re * unit.re +
      3 * (familyI_element unit (n + 1)).im * unit.im := by
    have hn2 : n + 2 = (n + 1) + 1 := by omega
    rw [hn2]
    simp only [familyI_element, pow_succ, ← mul_assoc, zs_mul_re]
  have hrec_re : (familyI_element unit (n + 2)).re =
      2 * unit.re * (familyI_element unit (n + 1)).re - (familyI_element unit n).re := by
    rw [hx2, hy1, hx1]
    ring_nf
    have hp : 1 - (unit.re ^ 2 - 3 * unit.im ^ 2) = 0 := by linarith [hunit_pell]
    have hmul : 2 * (familyI_element unit n).re * (1 - (unit.re ^ 2 - 3 * unit.im ^ 2)) = 0 := by
      rw [hp]
      ring
    nlinarith [hmul]

  obtain ⟨hdiv0, _⟩ := integrality_family_I unit m n hunit_pell
  obtain ⟨hdiv1, _⟩ := integrality_family_I unit m (n + 1) hunit_pell
  obtain ⟨hdiv2, _⟩ := integrality_family_I unit m (n + 2) hunit_pell
  obtain ⟨c0, hc0⟩ := hdiv0
  obtain ⟨c1, hc1⟩ := hdiv1
  obtain ⟨c2, hc2⟩ := hdiv2
  have hc0' : sm * ((familyI_element unit n).re - 3) = 2 * c0 := by simpa [sm] using hc0
  have hc1' : sm * ((familyI_element unit (n + 1)).re - 3) = 2 * c1 := by simpa [sm] using hc1
  have hc2' : sm * ((familyI_element unit (n + 2)).re - 3) = 2 * c2 := by simpa [sm] using hc2

  have hnum : sm * ((familyI_element unit (n + 2)).re - 3) =
      2 * unit.re * (sm * ((familyI_element unit (n + 1)).re - 3)) -
      sm * ((familyI_element unit n).re - 3) +
      2 * ((3 : ℤ) ^ (m + 1) * (unit.re - 1)) := by
    calc
      sm * ((familyI_element unit (n + 2)).re - 3)
          = sm * (2 * unit.re * (familyI_element unit (n + 1)).re - (familyI_element unit n).re - 3) := by
              rw [hrec_re]
      _ = 2 * unit.re * (sm * ((familyI_element unit (n + 1)).re - 3)) -
          sm * ((familyI_element unit n).re - 3) +
          sm * (6 * (unit.re - 1)) := by ring
      _ = 2 * unit.re * (sm * ((familyI_element unit (n + 1)).re - 3)) -
          sm * ((familyI_element unit n).re - 3) +
          2 * ((3 : ℤ) ^ (m + 1) * (unit.re - 1)) := by
            rw [h3m1]
            ring

  have hc_rec : c2 = 2 * unit.re * c1 - c0 + (3 : ℤ) ^ (m + 1) * (unit.re - 1) := by
    have h2 : 2 * c2 = 2 * (2 * unit.re * c1 - c0 + (3 : ℤ) ^ (m + 1) * (unit.re - 1)) := by
      calc
        2 * c2 = sm * ((familyI_element unit (n + 2)).re - 3) := by simpa [sm] using hc2.symm
        _ = 2 * unit.re * (sm * ((familyI_element unit (n + 1)).re - 3)) -
            sm * ((familyI_element unit n).re - 3) +
            2 * ((3 : ℤ) ^ (m + 1) * (unit.re - 1)) := hnum
        _ = 2 * unit.re * (2 * c1) - (2 * c0) +
          2 * ((3 : ℤ) ^ (m + 1) * (unit.re - 1)) := by rw [hc1', hc0']
        _ = 2 * (2 * unit.re * c1 - c0 + (3 : ℤ) ^ (m + 1) * (unit.re - 1)) := by ring
    omega

  have hC0 : C_m_I unit m n = c0 := by
    show sm * ((familyI_element unit n).re - 3) / 2 = c0
    have : sm * ((familyI_element unit n).re - 3) = 2 * c0 := hc0'
    omega
  have hC1 : C_m_I unit m (n + 1) = c1 := by
    show sm * ((familyI_element unit (n + 1)).re - 3) / 2 = c1
    have : sm * ((familyI_element unit (n + 1)).re - 3) = 2 * c1 := hc1'
    omega
  have hC2 : C_m_I unit m (n + 2) = c2 := by
    show sm * ((familyI_element unit (n + 2)).re - 3) / 2 = c2
    have : sm * ((familyI_element unit (n + 2)).re - 3) = 2 * c2 := hc2'
    omega

  rw [hC2, hC1, hC0]
  exact hc_rec

theorem recurrence_A_family_I (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1) (m n : ℕ) :
    A_m_I unit m (n + 2) =
    2 * unit.re * A_m_I unit m (n + 1) - A_m_I unit m n -
    (3 : ℤ) ^ (m + 1) * (unit.re - 1) := by
  simp only [A_m_I]; linarith [recurrence_C_family_I unit hunit_pell m n]

theorem recurrence_B_family_I (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1) (m n : ℕ) :
    B_m_I unit m (n + 2) =
    2 * unit.re * B_m_I unit m (n + 1) - B_m_I unit m n +
    (3 : ℤ) ^ (m + 2) * (unit.re - 1) := by
  set sm : ℤ := (3 : ℤ) ^ m
  have h3m2 : (3 : ℤ) ^ (m + 2) = 9 * sm := by
    calc
      (3 : ℤ) ^ (m + 2) = 9 * (3 : ℤ) ^ m := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ, pow_succ]
        ring
      _ = 9 * sm := by simp [sm]
  have hx1 : (familyI_element unit (n + 1)).re =
      (familyI_element unit n).re * unit.re + 3 * (familyI_element unit n).im * unit.im := by
    simp only [familyI_element, pow_succ, ← mul_assoc, zs_mul_re]
  have hy1 : (familyI_element unit (n + 1)).im =
      (familyI_element unit n).re * unit.im + (familyI_element unit n).im * unit.re := by
    simp only [familyI_element, pow_succ, ← mul_assoc, zs_mul_im]
  have hy2 : (familyI_element unit (n + 2)).im =
      (familyI_element unit (n + 1)).re * unit.im +
      (familyI_element unit (n + 1)).im * unit.re := by
    have hn2 : n + 2 = (n + 1) + 1 := by omega
    rw [hn2]
    simp only [familyI_element, pow_succ, ← mul_assoc, zs_mul_im]
  have hrec_im : (familyI_element unit (n + 2)).im =
      2 * unit.re * (familyI_element unit (n + 1)).im - (familyI_element unit n).im := by
    rw [hy2, hx1, hy1]
    ring_nf
    have hp : 1 - (unit.re ^ 2 - 3 * unit.im ^ 2) = 0 := by linarith [hunit_pell]
    have hmul : 2 * (familyI_element unit n).im * (1 - (unit.re ^ 2 - 3 * unit.im ^ 2)) = 0 := by
      rw [hp]
      ring
    nlinarith [hmul]

  obtain ⟨_, hdiv0⟩ := integrality_family_I unit m n hunit_pell
  obtain ⟨_, hdiv1⟩ := integrality_family_I unit m (n + 1) hunit_pell
  obtain ⟨_, hdiv2⟩ := integrality_family_I unit m (n + 2) hunit_pell
  obtain ⟨b0, hb0⟩ := hdiv0
  obtain ⟨b1, hb1⟩ := hdiv1
  obtain ⟨b2, hb2⟩ := hdiv2
  have hb0' : sm * ((familyI_element unit n).im - 9) = 2 * b0 := by simpa [sm] using hb0
  have hb1' : sm * ((familyI_element unit (n + 1)).im - 9) = 2 * b1 := by simpa [sm] using hb1
  have hb2' : sm * ((familyI_element unit (n + 2)).im - 9) = 2 * b2 := by simpa [sm] using hb2

  have hnum : sm * ((familyI_element unit (n + 2)).im - 9) =
      2 * unit.re * (sm * ((familyI_element unit (n + 1)).im - 9)) -
      sm * ((familyI_element unit n).im - 9) +
      2 * ((3 : ℤ) ^ (m + 2) * (unit.re - 1)) := by
    calc
      sm * ((familyI_element unit (n + 2)).im - 9)
          = sm * (2 * unit.re * (familyI_element unit (n + 1)).im - (familyI_element unit n).im - 9) := by
              rw [hrec_im]
      _ = 2 * unit.re * (sm * ((familyI_element unit (n + 1)).im - 9)) -
          sm * ((familyI_element unit n).im - 9) +
          sm * (18 * (unit.re - 1)) := by ring
      _ = 2 * unit.re * (sm * ((familyI_element unit (n + 1)).im - 9)) -
          sm * ((familyI_element unit n).im - 9) +
          2 * ((3 : ℤ) ^ (m + 2) * (unit.re - 1)) := by
            rw [h3m2]
            ring

  have hb_rec : b2 = 2 * unit.re * b1 - b0 + (3 : ℤ) ^ (m + 2) * (unit.re - 1) := by
    have h2 : 2 * b2 = 2 * (2 * unit.re * b1 - b0 + (3 : ℤ) ^ (m + 2) * (unit.re - 1)) := by
      calc
        2 * b2 = sm * ((familyI_element unit (n + 2)).im - 9) := by simpa [sm] using hb2.symm
        _ = 2 * unit.re * (sm * ((familyI_element unit (n + 1)).im - 9)) -
            sm * ((familyI_element unit n).im - 9) +
            2 * ((3 : ℤ) ^ (m + 2) * (unit.re - 1)) := hnum
        _ = 2 * unit.re * (2 * b1) - (2 * b0) +
          2 * ((3 : ℤ) ^ (m + 2) * (unit.re - 1)) := by rw [hb1', hb0']
        _ = 2 * (2 * unit.re * b1 - b0 + (3 : ℤ) ^ (m + 2) * (unit.re - 1)) := by ring
    omega

  have hB0 : B_m_I unit m n = b0 := by
    show sm * ((familyI_element unit n).im - 9) / 2 = b0
    have : sm * ((familyI_element unit n).im - 9) = 2 * b0 := hb0'
    omega
  have hB1 : B_m_I unit m (n + 1) = b1 := by
    show sm * ((familyI_element unit (n + 1)).im - 9) / 2 = b1
    have : sm * ((familyI_element unit (n + 1)).im - 9) = 2 * b1 := hb1'
    omega
  have hB2 : B_m_I unit m (n + 2) = b2 := by
    show sm * ((familyI_element unit (n + 2)).im - 9) / 2 = b2
    have : sm * ((familyI_element unit (n + 2)).im - 9) = 2 * b2 := hb2'
    omega

  rw [hB2, hB1, hB0]
  exact hb_rec

theorem recurrence_D_family_I (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1) (m n : ℕ) :
    D_m_I unit m (n + 2) =
    2 * unit.re * D_m_I unit m (n + 1) - D_m_I unit m n -
    (3 : ℤ) ^ (m + 2) * (unit.re - 1) := by
  simp only [D_m_I]; linarith [recurrence_B_family_I unit hunit_pell m n]

-- Numerical check of B recurrence for Family II
example : B_m_II ε₀ 0 3 =
    2 * ε₀.re * B_m_II ε₀ 0 2 - B_m_II ε₀ 0 1 + (3 : ℤ) ^ (0 + 2) * (ε₀.re - 1) := by
  native_decide

-- ============================================================================
-- §7.  Growth and monotonicity
-- ============================================================================

theorem growth_monotone_re_I (unit : Zsqrtd (3 : ℤ))
    (_hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1)
    (hu : 2 ≤ unit.re) (hv : 1 ≤ unit.im) (n : ℕ) :
    (familyI_element unit n).re < (familyI_element unit (n + 1)).re := by
  simp only [familyI_element, pow_succ, ← mul_assoc]
  have hu' : (0 : ℤ) < unit.re := by linarith
  have hv' : (0 : ℤ) < unit.im := by linarith
  have hxy_pos : 0 < (seed_I * unit ^ n).re ∧ 0 < (seed_I * unit ^ n).im := by
    induction n with
    | zero => constructor <;> simp [seed_I]
    | succ k ih =>
      obtain ⟨ihx, ihy⟩ := ih
      simp only [pow_succ, ← mul_assoc]
      constructor
      · rw [zs_mul_re]; linarith [mul_pos ihx hu', mul_pos ihy hv']
      · rw [zs_mul_im]; linarith [mul_pos ihx hv', mul_pos ihy hu']
  have hre_expand : (seed_I * unit ^ n * unit).re =
      (seed_I * unit ^ n).re * unit.re + 3 * (seed_I * unit ^ n).im * unit.im :=
    zs_mul_re _ _
  rw [hre_expand]
  have h_bound : (seed_I * unit ^ n).re * unit.re ≥ 2 * (seed_I * unit ^ n).re := by
    have hmul := mul_nonneg (show (0 : ℤ) ≤ unit.re - 2 from by linarith)
                             (le_of_lt hxy_pos.1)
    linarith [show (unit.re - 2) * (seed_I * unit ^ n).re =
                  (seed_I * unit ^ n).re * unit.re - 2 * (seed_I * unit ^ n).re from by ring]
  have h3 : 0 < 3 * (seed_I * unit ^ n).im * unit.im :=
    mul_pos (by linarith [hxy_pos.2]) hv'
  linarith [h_bound, hxy_pos.1, h3]

/-- **Theorem 7.2(ii)** (Exponential growth): For n ≥ 1, the .re-component of
    `familyI_element` grows with multiplicative ratio at least `2·unit.re − 1`:
      (2·unit.re − 1) · xₙ < xₙ₊₁.
    Since `unit.re ≥ 2` gives `2·unit.re − 1 ≥ 3`, the sequence grows at least
    geometrically with ratio 3, establishing exponential growth. -/
theorem growth_exponential (unit : Zsqrtd (3 : ℤ))
    (hunit_pell : unit.re ^ 2 - 3 * unit.im ^ 2 = 1)
    (hu : 2 ≤ unit.re) (hv : 1 ≤ unit.im) (n : ℕ) (hn : 1 ≤ n) :
    (2 * unit.re - 1) * (familyI_element unit n).re <
    (familyI_element unit (n + 1)).re := by
  cases n with
  | zero => omega
  | succ k =>
    -- n = k + 1.  Derive the Pell 2-step recurrence x_{k+2} = 2u·x_{k+1} − x_k.
    have hrec : (familyI_element unit (k + 2)).re =
        2 * unit.re * (familyI_element unit (k + 1)).re -
        (familyI_element unit k).re := by
      have hx1 : (familyI_element unit (k + 1)).re =
          (familyI_element unit k).re * unit.re +
          3 * (familyI_element unit k).im * unit.im := by
        simp only [familyI_element, pow_succ, ← mul_assoc, zs_mul_re]
      have hy1 : (familyI_element unit (k + 1)).im =
          (familyI_element unit k).re * unit.im +
          (familyI_element unit k).im * unit.re := by
        simp only [familyI_element, pow_succ, ← mul_assoc, zs_mul_im]
      have hx2 : (familyI_element unit (k + 2)).re =
          (familyI_element unit (k + 1)).re * unit.re +
          3 * (familyI_element unit (k + 1)).im * unit.im := by
        simp only [show k + 2 = k + 1 + 1 from rfl,
                   familyI_element, pow_succ, ← mul_assoc, zs_mul_re]
      rw [hx2, hy1, hx1]
      ring_nf
      have hp : 1 - (unit.re ^ 2 - 3 * unit.im ^ 2) = 0 := by linarith
      have hmul : 2 * (familyI_element unit k).re *
          (1 - (unit.re ^ 2 - 3 * unit.im ^ 2)) = 0 := by rw [hp]; ring
      nlinarith [hmul]
    -- Strict monotonicity: x_k < x_{k+1}
    have hmon : (familyI_element unit k).re < (familyI_element unit (k + 1)).re :=
      growth_monotone_re_I unit hunit_pell hu hv k
    -- x_{k+2} = 2u·x_{k+1} − x_k > 2u·x_{k+1} − x_{k+1} = (2u−1)·x_{k+1}
    show (2 * unit.re - 1) * (familyI_element unit (k + 1)).re <
        (familyI_element unit (k + 1 + 1)).re
    rw [show k + 1 + 1 = k + 2 from by omega]
    linarith

-- ============================================================================
-- §8.  Numerical table verifications
-- ============================================================================

-- Table 2: Family II, m=0, unit=ε₀
example : A_m_II ε₀ 0 1 = 12 ∧ B_m_II ε₀ 0 1 = 1  ∧ C_m_II ε₀ 0 1 = 9  ∧
          D_m_II ε₀ 0 1 = 10 ∧ (12:ℤ)^3 + 1^3 = 1729 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide, by norm_num⟩

example : A_m_II ε₀ 0 2 = 39 ∧ B_m_II ε₀ 0 2 = 17 ∧ C_m_II ε₀ 0 2 = 36 ∧
          D_m_II ε₀ 0 2 = 26 ∧ (39:ℤ)^3 + 17^3 = 64232 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide, by norm_num⟩

example : A_m_II ε₀ 0 3 = 141 ∧ B_m_II ε₀ 0 3 = 76 ∧ C_m_II ε₀ 0 3 = 138 ∧
          D_m_II ε₀ 0 3 = 85 ∧ (141:ℤ)^3 + 76^3 = 3242197 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide, by norm_num⟩

example : A_m_II ε₀ 0 4 = 522 ∧ B_m_II ε₀ 0 4 = 296 ∧ C_m_II ε₀ 0 4 = 519 ∧
          D_m_II ε₀ 0 4 = 305 ∧ (522:ℤ)^3 + 296^3 = 168170984 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide, by norm_num⟩

-- Table 1: Family I, m=0, unit=ε₁
example : A_m_I ε₁ 0 1 = 96 ∧ B_m_I ε₁ 0 1 = 50 ∧ C_m_I ε₁ 0 1 = 93 ∧
          D_m_I ε₁ 0 1 = 59 ∧ (96:ℤ)^3 + 50^3 = 1009736 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide, by norm_num⟩

example : A_m_I ε₁ 0 2 = 1317 ∧ B_m_I ε₁ 0 2 = 755 ∧ C_m_I ε₁ 0 2 = 1314 ∧
          D_m_I ε₁ 0 2 = 764 ∧ (1317:ℤ)^3 + 755^3 = 2714690888 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide, by norm_num⟩

-- ============================================================================
-- §9.  Pascal and divisor bound
-- ============================================================================

lemma pascal_n2 (C r : ℤ) : (C + r) ^ 2 - C ^ 2 = 2 * r * C + r ^ 2 := by ring
lemma pascal_n3 (C r : ℤ) : (C + r) ^ 3 - C ^ 3 = 3 * r * C ^ 2 + 3 * r ^ 2 * C + r ^ 3 := by ring

lemma radicand_nonneg_bound (Δ r : ℝ) (_hΔ : 0 < Δ) (hr : 0 < r) (hbnd : r ^ 3 ≤ 4 * Δ) :
    12 * Δ * r - 3 * r ^ 4 ≥ 0 := by nlinarith [sq_nonneg r, mul_nonneg hr.le (by linarith : (0:ℝ) ≤ 4 * Δ - r ^ 3)]

end TaxicabPell
