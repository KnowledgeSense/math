import EmbeddingDimensionStrata.UniversalPolynomials
import Mathlib.Algebra.MvPolynomial.Variables

/-! # Positive grading gives exact linearity in equal-weight coordinates -/
noncomputable section
namespace EmbeddingDimensionStrata

lemma coordinate_weight_eq_zero_iff (d : NormalCoordinate →₀ ℕ) :
    Finsupp.weight coordinateWeight d = 0 ↔ d = 0 := by
  constructor
  · intro hd
    ext j
    by_contra hj
    have hj' : d j ≠ 0 := by simpa using hj
    have hle := Finsupp.le_weight_of_ne_zero
      (fun j => le_of_lt (coordinateWeight_pos j)) hj'
    rw [hd] at hle
    exact (not_le_of_gt (coordinateWeight_pos j)) hle
  · rintro rfl
    exact map_zero _

/-- A monomial of weight equal to that of an occurring variable is exactly
that variable to the first power. -/
lemma monomial_eq_single_of_weight {d : NormalCoordinate →₀ ℕ} {j : NormalCoordinate}
    (hj : d j ≠ 0) (hd : Finsupp.weight coordinateWeight d = coordinateWeight j) :
    d = Finsupp.single j 1 := by
  have hs := Finsupp.weight_sub_single_add (w := coordinateWeight) hj
  have hz : Finsupp.weight coordinateWeight (d - Finsupp.single j 1) = 0 := by omega
  have hz' := (coordinate_weight_eq_zero_iff _).mp hz
  have hsplit := Finsupp.sub_add_single_one_cancel hj
  rw [hz', zero_add] at hsplit
  exact hsplit.symm

/-- No variable of weight above the degree can occur in a homogeneous
polynomial. -/
theorem weighted_not_mem_vars {Q : CoordinatePolynomial} {δ : ℤ}
    (hQ : Q.IsWeightedHomogeneous coordinateWeight δ)
    (j : NormalCoordinate) (hj : δ < coordinateWeight j) : j ∉ Q.vars := by
  intro hmem
  obtain ⟨d,hd,hjd⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hmem
  have hw := hQ (MvPolynomial.mem_support_iff.mp hd)
  have hle := Finsupp.le_weight_of_ne_zero
    (fun k => le_of_lt (coordinateWeight_pos k)) (Finsupp.mem_support_iff.mp hjd)
  omega

/-- Remove exactly the linear term in one coordinate. -/
def removeLinearTerm (Q : CoordinatePolynomial) (j : NormalCoordinate) : CoordinatePolynomial :=
  Q - MvPolynomial.monomial (Finsupp.single j 1) (Q.coeff (Finsupp.single j 1))

theorem removeLinearTerm_weighted {Q : CoordinatePolynomial} (j : NormalCoordinate)
    (hQ : Q.IsWeightedHomogeneous coordinateWeight (coordinateWeight j)) :
    (removeLinearTerm Q j).IsWeightedHomogeneous coordinateWeight (coordinateWeight j) := by
  apply hQ.sub
  apply MvPolynomial.isWeightedHomogeneous_monomial
  simp only [Finsupp.weight_single, one_smul]

theorem removeLinearTerm_not_mem_vars {Q : CoordinatePolynomial} (j : NormalCoordinate)
    (hQ : Q.IsWeightedHomogeneous coordinateWeight (coordinateWeight j)) :
    j ∉ (removeLinearTerm Q j).vars := by
  classical
  intro hmem
  obtain ⟨d,hd,hjd⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hmem
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  have hweight := removeLinearTerm_weighted j hQ hcoeff
  have heq := monomial_eq_single_of_weight (Finsupp.mem_support_iff.mp hjd) hweight
  subst d
  simp [removeLinearTerm] at hcoeff

theorem polynomial_linear_decomposition (Q : CoordinatePolynomial) (j : NormalCoordinate) :
    Q = MvPolynomial.C (Q.coeff (Finsupp.single j 1)) * MvPolynomial.X j +
      removeLinearTerm Q j := by
  rw [MvPolynomial.C_mul_X_eq_monomial, removeLinearTerm]
  abel

/-- The point at which just coordinate j is one. -/
def coordinateUnitPoint (j : NormalCoordinate) : NormalCoordinate → ℤ :=
  fun k => if k = j then 1 else 0

/-- For homogeneous positive-degree polynomials, the linear coefficient of a
variable of the same weight is evaluated at the corresponding unit point. -/
theorem weighted_linear_coefficient {Q : CoordinatePolynomial} (j : NormalCoordinate)
    (hQ : Q.IsWeightedHomogeneous coordinateWeight (coordinateWeight j)) :
    MvPolynomial.eval (coordinateUnitPoint j) Q = Q.coeff (Finsupp.single j 1) := by
  classical
  have hrem : MvPolynomial.eval (coordinateUnitPoint j) (removeLinearTerm Q j) = 0 := by
    have heval := MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars (RingHom.id ℤ)
      (p := removeLinearTerm Q j) (g := coordinateUnitPoint j) (by
        intro k hk
        have hkj : k ≠ j := by intro h; subst k; exact removeLinearTerm_not_mem_vars j hQ hk
        exact ite_eq_right hkj)
    have hconst : MvPolynomial.constantCoeff (removeLinearTerm Q j) = 0 := by
      apply (removeLinearTerm_weighted j hQ).coeff_eq_zero
      rw [map_zero]
      exact ne_of_lt (coordinateWeight_pos j)
    rw [hconst] at heval
    exact heval
  conv_lhs => rw [polynomial_linear_decomposition Q j]
  rw [map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, hrem]
  simp [coordinateUnitPoint]

end EmbeddingDimensionStrata
