import GenericValueSemigroups.JetPolynomials
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Algebra.MvPolynomial.Funext

namespace GenericValueSemigroups

/-- Rational algebraic independence prevents every nonzero integer jet polynomial from vanishing. -/
theorem jetEvaluation_ne_zero_of_algebraicIndependent {d N : ℕ}
    (a : JetVariable d N → ℂ) (ha : AlgebraicIndependent ℚ a)
    (p : MvPolynomial (JetVariable d N) ℤ) (hp : p ≠ 0) :
    jetEvaluation a p ≠ 0 := by
  have h : AlgebraicIndependent ℤ a := ha.restrictScalars (R := ℤ) (by
    intro x y he
    exact_mod_cast he)
  change MvPolynomial.aeval a p ≠ 0
  exact fun he => hp (h.eq_zero_of_aeval_eq_zero p he)

/-- The nonvanishing locus of a nonzero integer jet polynomial has a complex point. -/
theorem exists_jetEvaluation_ne_zero {d N : ℕ}
    (p : MvPolynomial (JetVariable d N) ℤ) (hp : p ≠ 0) :
    ∃ a : JetVariable d N → ℂ, jetEvaluation a p ≠ 0 := by
  classical
  by_contra h
  have hall : ∀ a : JetVariable d N → ℂ, jetEvaluation a p = 0 := by simpa using h
  have he : MvPolynomial.map (Int.castRingHom ℂ) p = 0 := by
    apply MvPolynomial.funext
    intro a
    simpa [jetEvaluation, MvPolynomial.eval_map] using hall a
  apply hp
  apply MvPolynomial.map_injective (Int.castRingHom ℂ) (by
    intro x y hxy
    change (x : ℂ) = (y : ℂ) at hxy
    exact_mod_cast hxy)
  simpa using he

/-- A finite family of nonzero integer jet conditions can be satisfied simultaneously. -/
theorem exists_all_jetConditions {d N : ℕ} {ι : Type*} (S : Finset ι)
    (p : ι → MvPolynomial (JetVariable d N) ℤ) (hp : ∀ i ∈ S, p i ≠ 0) :
    ∃ a : JetVariable d N → ℂ, ∀ i ∈ S, jetEvaluation a (p i) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_jetEvaluation_ne_zero (∏ i ∈ S, p i) (Finset.prod_ne_zero_iff.mpr hp)
  refine ⟨a, ?_⟩
  rw [map_prod] at ha
  exact Finset.prod_ne_zero_iff.mp ha

end GenericValueSemigroups
