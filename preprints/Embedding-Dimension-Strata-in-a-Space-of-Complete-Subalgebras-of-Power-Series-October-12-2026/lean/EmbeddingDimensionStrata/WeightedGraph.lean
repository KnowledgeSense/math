import EmbeddingDimensionStrata.AffineParameters
import Mathlib.Algebra.MvPolynomial.Monad

/-! # Weighted homogeneity of the actual solved graph polynomials -/
noncomputable section
namespace EmbeddingDimensionStrata

/-- Substitution of homogeneous polynomials of the appropriate weights
preserves weighted homogeneity. -/
theorem weighted_bind {σ τ : Type*} (w : σ → ℤ) (v : τ → ℤ)
    (q : σ → MvPolynomial τ ℤ)
    (hq : ∀ i, (q i).IsWeightedHomogeneous v (w i))
    (P : MvPolynomial σ ℤ) (d : ℤ) (hP : P.IsWeightedHomogeneous w d) :
    (MvPolynomial.bind₁ q P).IsWeightedHomogeneous v d := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact MvPolynomial.isWeightedHomogeneous_zero ℤ v d
  | add P Q hP hQ ihP ihQ => rw [map_add]; exact ihP.add ihQ
  | monomial e r he =>
    rw [MvPolynomial.bind₁_monomial]
    have hh := MvPolynomial.IsWeightedHomogeneous.prod e.support
      (fun i => q i ^ e i) (fun i => e i • w i) (fun i _ => (hq i).pow (e i))
    have hw : (∑ i ∈ e.support, e i • w i) = d := by
      exact he
    rw [hw] at hh
    exact hh.C_mul r

def freeCoordinateWeight (j : FreeCoordinate) : ℤ := coordinateWeight j.val

theorem integral_evaluation_eq_bind {σ : Type*} (p : NormalCoordinate → MvPolynomial σ ℤ)
    (Q : CoordinatePolynomial) : evaluateCoordinatePolynomial p Q = MvPolynomial.bind₁ p Q := by
  unfold evaluateCoordinatePolynomial MvPolynomial.bind₁
  rw [MvPolynomial.aeval_def]
  congr 2

theorem solveFreePoint_weighted (N : ℕ) (j : NormalCoordinate) :
    (solveFreePoint (MvPolynomial.X : FreeCoordinate → MvPolynomial FreeCoordinate ℤ) N j).IsWeightedHomogeneous freeCoordinateWeight (coordinateWeight j) := by
  classical
  induction N generalizing j with
  | zero =>
    change (initialFreePoint MvPolynomial.X j).IsWeightedHomogeneous _ _
    unfold initialFreePoint
    by_cases hj : j ∉ eliminatedCoordinates
    · rw [dite_eq_left hj]
      exact MvPolynomial.isWeightedHomogeneous_X ℤ freeCoordinateWeight ⟨j,hj⟩
    · rw [dite_eq_right hj]
      exact MvPolynomial.isWeightedHomogeneous_zero ℤ freeCoordinateWeight _
  | succ n ih =>
    rw [solveFreePoint]
    split_ifs with hn
    · by_cases hj : j = solvedCoordinate ⟨n,hn⟩
      · subst j
        rw [Function.update_self,integral_evaluation_eq_bind]
        exact weighted_bind coordinateWeight freeCoordinateWeight _ (fun k => ih k)
          (solutionRemainder ⟨n,hn⟩) _ (solutionRemainder_weighted _)
      · rw [Function.update_of_ne hj]
        exact ih j
    · exact ih j

/-- Every coordinate of the actual polynomial inverse has its expected
weight, including all five solved coordinates in the paper's original order. -/
theorem freeParameterPolynomial_weighted (j : NormalCoordinate) :
    (freeParameterPolynomial j).IsWeightedHomogeneous freeCoordinateWeight (coordinateWeight j) :=
  solveFreePoint_weighted 5 j

/-- The homogeneous solved P_k of Theorem affine, in the original order. -/
theorem solvedGraphPolynomial_weighted (i : Fin 5) :
    (freeParameterPolynomial (eliminatedCoordinate i)).IsWeightedHomogeneous
      freeCoordinateWeight (equationWeight i) := by
  have hh := freeParameterPolynomial_weighted (eliminatedCoordinate i)
  rw [eliminatedCoordinate_weight] at hh
  exact hh

/-- Base change gives the same homogeneous solved P_k over the coefficient
field of the paper (and, in fact, over every commutative coefficient ring). -/
theorem solvedGraphPolynomial_baseChange_weighted (K : Type*) [CommRing K] (i : Fin 5) :
    (MvPolynomial.map (Int.castRingHom K) (freeParameterPolynomial (eliminatedCoordinate i))).IsWeightedHomogeneous freeCoordinateWeight (equationWeight i) := by
  intro d hd
  apply solvedGraphPolynomial_weighted i
  intro hz
  apply hd
  rw [MvPolynomial.coeff_map,hz,map_zero]

end EmbeddingDimensionStrata
