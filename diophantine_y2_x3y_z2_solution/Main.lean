import Mathlib
open scoped BigOperators
open scoped Nat
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
/-!
# A complete integer solution of `y² + x³y + z² + 1 = 0`
This file formalizes the classification of the integer solutions of the Diophantine equation
`y² + x³y + z² + 1 = 0`, following the note *A Complete Integer Solution of
`y² + x³y + z² + 1 = 0`*.
The classical two-squares criterion (proved in the note from first principles via the Gaussian
integers) is available in Mathlib as `Nat.eq_sq_add_sq_iff`, so we use that directly.
The main results are:
* `Diophantine.square_completion` (Lemma 2): the square-completion identity.
* `Diophantine.sol_odd`, `Diophantine.sol_three_dvd` (Lemma 3): congruence obstructions.
* `Diophantine.rep_parity` (Lemma 4): parity of representations.
* `Diophantine.necessary_form` (Lemma 14): the necessary form of `|x|`.
* `Diophantine.complete_solution` (Theorem 1): the complete parametrization of the solutions.
* `Diophantine.Rrep_nonempty_iff` (Lemma 16): the non-emptiness criterion for `Rₙ`.
-/
namespace Diophantine
/-- The Diophantine equation under study. -/
def IsSol (x y z : ℤ) : Prop := y ^ 2 + x ^ 3 * y + z ^ 2 + 1 = 0
/-- Admissibility of a positive integer `n`: the conditions defining the set `N` from the note,
i.e. `n ≡ 3 (mod 12)` and every prime `p ≡ 3 (mod 4)` occurs to an even exponent in `n⁶ - 4`. -/
def Adm (n : ℕ) : Prop :=
  n ≡ 3 [MOD 12] ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValNat p (n ^ 6 - 4))
/-- The representation set `Rₙ`: pairs `(a, b)` of positive integers with `a² + b² = n⁶ - 4`,
`a` odd and `b` even. -/
def Rrep (n : ℕ) (a b : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = (n : ℤ) ^ 6 - 4 ∧ Odd a ∧ Even b
/-! ### Elementary reduction to a sum of two squares -/
/-
Lemma 2 (square-completion identity).
-/
theorem square_completion (x y z : ℤ) :
    IsSol x y z ↔ (2 * y + x ^ 3) ^ 2 + (2 * z) ^ 2 = x ^ 6 - 4 := by
  constructor <;> intro h <;> unfold IsSol at * <;> linarith
/-
A sum of two integer squares is never congruent to `3` modulo `4`.
-/
theorem sumsq_mod_four_ne_three (a b : ℤ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  rcases Int.even_or_odd' a with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' b with ⟨ l, rfl | rfl ⟩ <;> ring_nf <;> norm_num
/-
Lemma 3, first part: in any solution, `x` is odd.
-/
theorem sol_odd {x y z : ℤ} (h : IsSol x y z) : Odd x := by
  by_contra hx_even
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := by
    exact even_iff_two_dvd.mp <| by simpa using hx_even;
  obtain ⟨ m, rfl | rfl ⟩ := Int.even_or_odd' y <;> obtain ⟨ n, rfl | rfl ⟩ := Int.even_or_odd' z <;> ring_nf at h <;> have := congr_arg ( · % 4 ) h <;> norm_num [ Int.add_emod, Int.mul_emod ] at this;
  · norm_num [ mul_pow, Int.add_emod, Int.mul_emod ] at this;
  · ring_nf at this; norm_num [ Int.add_emod, Int.mul_emod ] at this;
  · grind +locals;
  · ring_nf at this; norm_num [ Int.add_emod, Int.mul_emod ] at this;
/-
Lemma 3, second part: in any solution, `3 ∣ x`.
-/
theorem sol_three_dvd {x y z : ℤ} (h : IsSol x y z) : (3 : ℤ) ∣ x := by
  have h_mod9 : (2 * y + x ^ 3) ^ 2 + (2 * z) ^ 2 ≡ x ^ 6 - 4 [ZMOD 9] := by
    exact Int.modEq_of_dvd ⟨ 0, by linarith [ h.symm ] ⟩;
  contrapose! h_mod9;
  rw [ Int.ModEq ] ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ ];
  rw [ Int.dvd_iff_emod_eq_zero ] at h_mod9; ( rw [ ← Int.emod_emod_of_dvd x ( by decide : ( 3 : ℤ ) ∣ 9 ) ] at h_mod9; have := Int.emod_nonneg x ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg y ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg z ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos x ( by decide : ( 9 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos y ( by decide : ( 9 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos z ( by decide : ( 9 : ℤ ) > 0 ) ; interval_cases x % 9 <;> interval_cases y % 9 <;> interval_cases z % 9 <;> trivial; )
/-
Lemma 4 (parity of representations). If `n` is odd and `a² + b² = n⁶ - 4`, then neither `a`
nor `b` is zero and exactly one of them is odd.
-/
theorem rep_parity {n : ℕ} (hn : Odd n) {a b : ℤ}
    (h : a ^ 2 + b ^ 2 = (n : ℤ) ^ 6 - 4) :
    a ≠ 0 ∧ b ≠ 0 ∧ (Even a ↔ Odd b) := by
  -- First, we show that $n^6 - 4$ is congruent to $5 \pmod{8}$.
  have h_mod8 : (n ^ 6 - 4 : ℤ) % 8 = 5 := by
    obtain ⟨ k, rfl ⟩ := hn; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ ] ; have := Int.emod_nonneg k ( by norm_num1 : ( 8 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos k ( by norm_num1 : ( 0 : ℤ ) < 8 ) ; interval_cases ( k % 8 : ℤ ) <;> trivial;
  refine' ⟨ _, _, _ ⟩;
  · rintro rfl; norm_num [ ← h, Int.add_emod, Int.mul_emod, sq ] at h_mod8; have := Int.emod_nonneg b ( by norm_num : ( 8 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos b ( by norm_num : 0 < ( 8 : ℤ ) ) ; interval_cases b % 8 <;> trivial;
  · rintro rfl; norm_num [ ← h ] at h_mod8; ( rw [ ← @Int.emod_add_mul_ediv a 8 ] at *; have := congr_arg ( · % 8 ) h_mod8; norm_num [ sq, Int.add_emod, Int.sub_emod, Int.mul_emod ] at this; have := Int.emod_nonneg a ( by decide : ( 8 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos a ( by decide : ( 0 : ℤ ) < 8 ) ; interval_cases a % 8 <;> trivial; );
  · replace h := congr_arg Even h; simp_all +decide [ parity_simps ] ;
    grind
/-! ### The two-squares criterion, packaged for our use -/
/-
An integer value `m` is a sum of two integer squares iff (as a natural number) it is a sum of
two natural squares.
-/
theorem sumsq_int_iff_nat (m : ℕ) :
    (∃ a b : ℤ, a ^ 2 + b ^ 2 = (m : ℤ)) ↔ (∃ a b : ℕ, m = a ^ 2 + b ^ 2) := by
  constructor <;> intro h;
  · obtain ⟨ a, b, h ⟩ := h; exact ⟨ a.natAbs, b.natAbs, by simpa [ ← Int.natCast_inj ] using h.symm ⟩ ;
  · obtain ⟨ a, b, rfl ⟩ := h; exact ⟨ a, b, by norm_cast ⟩ ;
/-
The two-squares criterion in the form we use: `m` is a sum of two integer squares iff every
prime `p ≡ 3 (mod 4)` occurs to an even exponent in `m`.
-/
theorem sumsq_iff_even_exp (m : ℕ) :
    (∃ a b : ℤ, a ^ 2 + b ^ 2 = (m : ℤ)) ↔
      (∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValNat p m)) := by
  rcases eq_or_ne m 0 <;> simp_all +decide;
  · exists 0, 0;
  · rw [ sumsq_int_iff_nat m ];
    convert Nat.eq_sq_add_sq_iff using 1;
    constructor <;> intro h p hp <;> by_cases h3 : p ∣ m <;> simp_all +decide [ Nat.mem_primeFactors ];
    rw [ padicValNat.eq_zero_of_not_dvd h3 ] ; norm_num
/-
A natural number congruent to `3` modulo `4` contains a prime `p ≡ 3 (mod 4)` to an odd
exponent.
-/
theorem exists_odd_exp_of_mod_four_three {m : ℕ} (hm : m % 4 = 3) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ Odd (padicValNat p m) := by
  by_contra h_no_prime;
  -- By `sumsq_iff_even_exp m`, this means `∃ a b : ℤ, a^2 + b^2 = (m:ℤ)`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a^2 + b^2 = (m : ℤ) := by
    exact sumsq_iff_even_exp m |>.2 fun p hp hp' => by aesop;
  exact absurd ( congr_arg ( · % 4 ) hab ) ( by norm_num [ sq, Int.add_emod, Int.mul_emod ] ; have := Int.emod_nonneg a four_ne_zero; have := Int.emod_nonneg b four_ne_zero; have := Int.emod_lt_of_pos a four_pos; have := Int.emod_lt_of_pos b four_pos; interval_cases a % 4 <;> interval_cases b % 4 <;> norm_cast <;> simp +decide [ hm ] )
/-! ### Completion of the Diophantine solution -/
/-
The factorization argument from Lemma 14: if `n ≥ 2` is odd with `n ≡ 1 (mod 4)`, then
`n⁶ - 4 = (n³ - 2)(n³ + 2)` has a prime `p ≡ 3 (mod 4)` to an odd exponent.
-/
theorem factor_odd_exp {n : ℕ} (h1 : n % 4 = 1) (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ Odd (padicValNat p (n ^ 6 - 4)) := by
  -- Let $m = n^6 - 4$. Since $n \geq 2$, $n^3 \geq 8 \geq 2$, so in ℕ we have the factorization $n^6 - 4 = (n^3 - 2) * (n^3 + 2)$.
  set m : ℕ := n^6 - 4
  have h_factor : m = (n^3 - 2) * (n^3 + 2) := by
    exact Nat.sub_eq_of_eq_add <| by nlinarith [ Nat.sub_add_cancel <| show 2 ≤ n ^ 3 from Nat.le_trans ( by decide ) <| Nat.pow_le_pow_left hn 3 ] ;
  obtain ⟨ p, hp_prime, hp_mod, hp_odd ⟩ := exists_odd_exp_of_mod_four_three ( by
    zify at *;
    rw [ Int.ofNat_sub ( by nlinarith [ pow_succ' n 2 ] ) ] ; norm_num [ pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h1 ] ; : ( n ^ 3 - 2 ) % 4 = 3 ) ; use p; simp_all +decide ;
  haveI := Fact.mk hp_prime; rw [ padicValNat.mul ( by exact Nat.sub_ne_zero_of_lt ( by nlinarith [ pow_succ' n 2 ] ) ) ( by positivity ) ] ; simp_all +decide [ parity_simps ] ;
  rw [ padicValNat.eq_zero_of_not_dvd ] <;> norm_num;
  intro h_div
  have h_div_four : p ∣ 4 := by
    convert Nat.dvd_sub h_div ( show p ∣ n ^ 3 - 2 from ?_ ) using 1;
    · exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show 2 ≤ n ^ 3 from le_trans ( by decide ) ( Nat.pow_le_pow_left hn 3 ) ) ] );
    · contrapose! hp_odd; simp_all +decide [ padicValNat.eq_zero_of_not_dvd ] ;
  have := Nat.le_of_dvd ( by decide ) h_div_four; interval_cases p <;> trivial;
/-
Lemma 14 (necessary form of `|x|`). Every integer solution forces `|x|` to be admissible.
-/
theorem necessary_form {x y z : ℤ} (h : IsSol x y z) : Adm x.natAbs := by
  constructor;
  · -- By `sol_odd` and `sol_three_dvd`, we know `Odd x` and `3 ∣ x`. Hence `x.natAbs % 2 = 1` and `3 ∣ x.natAbs`.
    have h_mod_2 : x.natAbs % 2 = 1 := by
      exact Nat.odd_iff.mp ( by simpa using sol_odd h )
    have h_mod_3 : x.natAbs % 3 = 0 := by
      exact Nat.mod_eq_zero_of_dvd <| Int.natAbs_dvd_natAbs.mpr <| sol_three_dvd h;
    -- By `square_completion`, we know that `∃ a b : ℤ, a^2 + b^2 = x.natAbs^6 - 4`.
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a^2 + b^2 = x.natAbs^6 - 4 := by
      grind +suggestions;
    by_contra h_contra;
    -- If `x.natAbs % 4 = 1`, then by `factor_odd_exp`, there exists a prime `p ≡ 3 (mod 4)` with `Odd (padicValNat p (x.natAbs^6 - 4))`.
    obtain ⟨p, hp_prime, hp_mod, hp_odd⟩ : ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ Odd (padicValNat p (x.natAbs^6 - 4)) := by
      apply factor_odd_exp;
      · rw [ Nat.ModEq ] at h_contra; omega;
      · contrapose! h_contra; interval_cases _ : Int.natAbs x <;> simp_all +decide ;
    have := sumsq_iff_even_exp ( x.natAbs ^ 6 - 4 );
    rw [ Nat.cast_sub ] at this <;> norm_num at *;
    · exact absurd ( this.mp ⟨ a, b, hab ⟩ p hp_prime hp_mod ) ( by simpa using hp_odd );
    · exact le_trans ( by decide ) ( Nat.pow_le_pow_left ( show x.natAbs ≥ 2 by contrapose! h_contra; interval_cases x.natAbs <;> trivial ) 6 );
  · have h_even_exp : ∃ a b : ℤ, a ^ 2 + b ^ 2 = x.natAbs ^ 6 - 4 := by
      unfold IsSol at h;
      exact ⟨ 2 * y + x ^ 3, 2 * z, by cases abs_cases x <;> simp +decide [ * ] <;> linarith ⟩;
    have := sumsq_iff_even_exp ( x.natAbs ^ 6 - 4 ) ; simp_all +decide [ Nat.cast_sub ( show 4 ≤ x.natAbs ^ 6 from le_trans ( by decide ) ( Nat.pow_le_pow_left ( show x.natAbs ≥ 2 by
                                                                                                                                                                    contrapose! h; interval_cases _ : x.natAbs <;> simp_all +decide; all_goals exact absurd h_even_exp ( by rintro ⟨ a, b, h ⟩ ; nlinarith ) ) 6 ) ) ] ;
/-
Lemma 15 (sufficiency / reconstruction, forward direction): the parametrized triples are
solutions.
-/
theorem sufficiency {n : ℕ} {a b ε σ τ : ℤ}
    (hab : Rrep n a b)
    (hε : ε = 1 ∨ ε = -1) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    {x y z : ℤ} (hx : x = ε * (n : ℤ)) (hy : 2 * y = σ * a - ε * (n : ℤ) ^ 3)
    (hz : 2 * z = τ * b) :
    IsSol x y z := by
  convert ( square_completion x y z ).mpr _;
  rcases hε with ( rfl | rfl ) <;> rcases hσ with ( rfl | rfl ) <;> rcases hτ with ( rfl | rfl ) <;> norm_num [ hx, hy, hz ] at hab ⊢;
  all_goals linarith [ hab.2.2.1 ] ;
/-
Theorem 1 (complete solution). The integer solutions are exactly the parametrized triples.
-/
theorem complete_solution (x y z : ℤ) :
    IsSol x y z ↔
    ∃ (n : ℕ) (a b ε σ τ : ℤ),
      Adm n ∧ Rrep n a b ∧
      (ε = 1 ∨ ε = -1) ∧ (σ = 1 ∨ σ = -1) ∧ (τ = 1 ∨ τ = -1) ∧
      x = ε * (n : ℤ) ∧ 2 * y = σ * a - ε * (n : ℤ) ^ 3 ∧ 2 * z = τ * b := by
  refine ⟨ ?_, fun ⟨ n, a, b, ε, σ, τ, hn, hab, hε, hσ, hτ, hx, hy, hz ⟩ ↦ sufficiency hab hε hσ hτ hx hy hz ⟩;
  intro h;
  refine' ⟨ Int.natAbs x, Int.natAbs ( 2 * y + x ^ 3 ), Int.natAbs ( 2 * z ), x.sign, ( 2 * y + x ^ 3 ).sign, ( 2 * z ).sign, _, _, _, _, _ ⟩;
  · grind +suggestions;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · by_contra h_contra;
      norm_num at h_contra;
      apply_fun Even at * ; simp_all +decide [ parity_simps ];
      exact absurd ( sol_odd h ) ( by simpa using h_contra );
    · simp +zetaDelta at *;
      rintro rfl;
      exact absurd h ( by rw [ show IsSol x y 0 ↔ y ^ 2 + x ^ 3 * y + 0 ^ 2 + 1 = 0 by rfl ] ; exact ne_of_apply_ne ( fun n => n % 4 ) <| by norm_num [ Int.add_emod, Int.mul_emod, pow_succ ] ; have := Int.emod_nonneg x four_pos.ne'; have := Int.emod_nonneg y four_pos.ne'; have := Int.emod_lt_of_pos x four_pos; have := Int.emod_lt_of_pos y four_pos; interval_cases x % 4 <;> interval_cases y % 4 <;> trivial );
    · cases abs_cases x <;> cases abs_cases z <;> simp +decide [ * ] <;> linarith [ square_completion x y z |>.1 h ];
    · have := sol_odd h; simp_all +decide [ parity_simps ] ;
      cases abs_cases ( 2 * y + x ^ 3 ) <;> simp +decide [ *, parity_simps ];
      exact iff_of_false ( by simp +decide [ parity_simps ] ) ( by simpa using this );
    · norm_num [ parity_simps ];
  · cases eq_or_ne x 0 <;> simp_all +decide;
    · unfold IsSol at h; nlinarith;
    · grind;
  · have h_odd : Odd (2 * y + x ^ 3) := by
      have := sol_odd h; simp_all +decide [ parity_simps ] ;
      exact iff_of_false ( by simp +decide [ parity_simps ] ) ( by simpa using this );
    grind +qlia;
  · have := sol_odd h; have := sol_three_dvd h; simp_all +decide [ Int.sign_eq_one_of_pos ] ;
    refine' ⟨ _, _, _, _ ⟩;
    · rintro rfl; simp_all +decide [ IsSol ];
      obtain ⟨ k, rfl ⟩ := this; replace h := congr_arg ( · % 9 ) h; ring_nf at h; norm_num [ Int.add_emod, Int.mul_emod, sq ] at h; have := Int.emod_nonneg y ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos y ( by decide : ( 9 : ℤ ) > 0 ) ; interval_cases y % 9 <;> trivial;
    · cases abs_cases x <;> simp +decide [ * ];
    · grind +splitIndPred;
    · grind +suggestions
/-
Lemma 16 (non-emptiness of `Rₙ`). For any natural number `n`, the set `Rₙ` is nonempty iff `n`
is admissible.
-/
theorem Rrep_nonempty_iff (n : ℕ) :
    (∃ a b : ℤ, Rrep n a b) ↔ Adm n := by
  constructor <;> intro h;
  · -- By definition of $Rrep$, we know that $a^2 + b^2 = n^6 - 4$.
    obtain ⟨a, b, hab⟩ := h;
    have h_sum : a^2 + b^2 = (n : ℤ)^6 - 4 := by
      exact hab.2.2.1;
    obtain ⟨x, y, z, hx, hy, hz⟩ : ∃ x y z : ℤ, IsSol x y z ∧ x = n := by
      use n, (a - n^3) / 2, b / 2;
      have := hab.2.2.2.1; ( have := hab.2.2.2.2; ( norm_num [ Int.even_iff ] at *; ) );
      obtain ⟨ k, rfl ⟩ := this; simp_all +decide [ IsSol ] ;
      cases abs_cases a <;> nlinarith [ Int.ediv_mul_cancel ( show 2 ∣ a - ↑n ^ 3 from even_iff_two_dvd.mp ( by apply_fun Even at *; simp_all +decide [ parity_simps ] ) ) ];
    convert necessary_form hx using 1;
  · obtain ⟨c, d, hcd⟩ : ∃ c d : ℤ, c ^ 2 + d ^ 2 = (n : ℤ) ^ 6 - 4 ∧ c ≠ 0 ∧ d ≠ 0 ∧ (Odd c ↔ Even d) := by
      have h_sum_sq : ∃ c d : ℤ, c ^ 2 + d ^ 2 = (n : ℤ) ^ 6 - 4 := by
        have := sumsq_iff_even_exp ( n ^ 6 - 4 );
        convert this.mpr h.2;
        rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith [ Nat.pow_le_pow_left ( show n ≥ 2 by contrapose! h; interval_cases n <;> simp_all +decide [ Adm ] ) 6 ];
      obtain ⟨ c, d, hcd ⟩ := h_sum_sq; use c, d; have := rep_parity ( show Odd n from by
                                                                        exact Nat.odd_iff.mpr ( h.1.of_dvd <| by decide ) ) hcd; simp_all +decide [ parity_simps ] ;
      grind;
    cases' em ( Odd c ) with hc hc <;> simp_all +decide [ parity_simps ];
    · use |c|, |d|;
      constructor <;> simp_all +decide [ parity_simps ];
      cases abs_cases c <;> cases abs_cases d <;> simp +decide [ *, parity_simps ];
    · use |d|, |c|;
      constructor <;> simp_all +decide;
      exact ⟨ by linarith, by cases abs_cases d <;> simp +decide [ *, parity_simps ], by cases abs_cases c <;> simp +decide [ *, parity_simps ] ⟩
end Diophantine
