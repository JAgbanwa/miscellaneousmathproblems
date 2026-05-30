import Mathlib

/-!
Completeness for the full three-equation system:

* `a^2 + b^2 = e^2`
* `a^2 + c^2 = f^2`
* `b^2 + c^2 = g^2`

with divisor parameters

* `b = (a^2 - r₂^2) / (2 r₂)`, `e = (a^2 + r₂^2) / (2 r₂)`
* `c = (a^2 - r₃^2) / (2 r₃)`, `f = (a^2 + r₃^2) / (2 r₃)`.
-/

namespace DiophantineA2PlusG2ExtraHypothesis

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

end DiophantineA2PlusG2ExtraHypothesis
