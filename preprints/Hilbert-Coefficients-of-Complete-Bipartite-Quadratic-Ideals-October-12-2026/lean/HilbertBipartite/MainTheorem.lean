import HilbertBipartite.CoefficientIdentification

open Finset Polynomial
namespace HilbertBipartite

/-- Full statement of Theorem 1.1 of the fixed 12 October 2026 release.
The length and eventual-polynomial fields refer to the actual polynomial-ring quotient. -/
structure ReleaseMainTheorem (K : Type*) [Field K] (p q : ℕ) : Prop where
  length_formula : ∀ s : ℕ, 1 ≤ s →
    Module.length (MvPolynomial (Fin p ⊕ Fin q) K)
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) =
      ((2*s+p+q-1).choose (p+q) + correction p q s + correction q p s : ℕ)
  hilbert_coefficients : IsHilbertCoefficientFamily K p q (hilbertCoefficient p q)
  coefficients_unique : ∀ e : ℕ → ℚ, IsHilbertCoefficientFamily K p q e →
    ∀ i ≤ p+q, e i = hilbertCoefficient p q i
  all_powers_expansion : ∀ s : ℕ, 1 ≤ s →
    ((Module.length (MvPolynomial (Fin p ⊕ Fin q) K)
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s)).toNat : ℚ) =
      ∑ i ∈ range (p+q+1), (-1 : ℚ)^i * hilbertCoefficient p q i *
        ((s+p+q-i-1).choose (p+q-i) : ℚ)
  explicit_coefficients : ∀ i : ℕ, hilbertCoefficient p q i = coefficientFormula p q i
  leading_coefficient : hilbertCoefficient p q 0 = 2^(p+q)
  initial_coefficients : ∀ i ≤ p,
    hilbertCoefficient p q i = 2^(p+q-2*i)*((p+q-i).choose i : ℚ) ∧
      0 < hilbertCoefficient p q i
  last_coefficient : hilbertCoefficient p q (p+q) = 0
  higher_sign : ∀ i : ℕ, p+1 ≤ i → i ≤ p+q-1 →
    0 < (-1 : ℚ)^(p+1)*hilbertCoefficient p q i
  all_nonnegative_iff : (∀ i ≤ p+q, 0 ≤ hilbertCoefficient p q i) ↔ Odd p
  consecutive_negative : Even p →
    1 ≤ q-1 ∧ (Icc (p+1) (p+q-1)).card = q-1 ∧
      ∀ i ∈ Icc (p+1) (p+q-1), hilbertCoefficient p q i < 0

/-- The complete original theorem, over every field and for every `1 ≤ p ≤ q`. -/
theorem release_main_theorem (K : Type*) [Field K]
    (p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) : ReleaseMainTheorem K p q := by
  have hq : 1 ≤ q := by omega
  refine {
    length_formula := fun s hs => compositionLength_formula K p q s hp hq hs
    hilbert_coefficients := hilbertCoefficient_is_family K p q hp hq
    coefficients_unique := fun e he => hilbertCoefficient_unique K p q hp hq e he
    all_powers_expansion := fun s hs => compositionLength_hilbertExpansion K p q s hp hq hs
    explicit_coefficients := fun i => hilbertCoefficient_eq_formula p q i hp hq
    leading_coefficient := hilbertCoefficient_zero p q
    initial_coefficients := fun i hi => ⟨hilbertCoefficient_low p q i hpq hi,
      hilbertCoefficient_low_pos p q i hpq hi⟩
    last_coefficient := hilbertCoefficient_high p q (p+q) hp hq (by omega)
    higher_sign := ?_
    all_nonnegative_iff := ?_
    consecutive_negative := ?_ }
  · intro i hpi hi
    rw [hilbertCoefficient_eq_formula p q i hp hq]
    exact coefficientFormula_high_signed_pos p q i hp hpq (by omega) (by omega)
  · simp_rw [hilbertCoefficient_eq_formula p q _ hp hq]
    exact coefficientFormula_nonneg_iff p q hp hpq
  · intro he
    have hpe := Nat.even_iff.mp he
    refine ⟨by omega, ?_, ?_⟩
    · rw [Nat.card_Icc]
      omega
    · intro i hi
      have hmem := mem_Icc.mp hi
      rw [hilbertCoefficient_eq_formula p q i hp hq]
      exact coefficientFormula_high_neg_of_even p q i hp hpq (by omega) (by omega) he

/-- Direct all-s formula using the explicit coefficients, without any unproved invariant. -/
theorem actual_length_explicit_expansion (K : Type*) [Field K]
    (p q s : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) (hs : 1 ≤ s) :
    ((Module.length (MvPolynomial (Fin p ⊕ Fin q) K)
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s)).toNat : ℚ) =
      ∑ i ∈ range (p+q+1), (-1 : ℚ)^i * coefficientFormula p q i *
        ((s+p+q-i-1).choose (p+q-i) : ℚ) := by
  have h := (release_main_theorem K p q hp hpq).all_powers_expansion s hs
  simpa only [hilbertCoefficient_eq_formula p q _ hp (by omega)] using h

end HilbertBipartite
