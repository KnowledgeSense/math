import MainTheorems.WishartBlocks.WishartDifferentialLaplace

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise SchwartzMap ContDiff

theorem oneRowWishart_schwartz_differential_identity {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p)) (f : 𝓢(MatrixEuclidean p, ℂ)) :
    (∑ i : WishartDifferentialIndex p, ∫ x,
      (wishartDifferenceCoefficient q S v s i x : ℂ) *
        functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p))
          (fun y => exponentialDamping (coordinateTrace p) y * f y)
            (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂(oneRowInputLaw q S)) = 0 := by
  let : IsProbabilityMeasure (oneRowInputLaw q S) := oneRowInput_probability hq S
  have hW : ∀ᵐ x ∂(oneRowInputLaw q S),
      (oneRowWishartValue S (s • v) x).PosSemidef := by
    filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
    exact oneRowWishartValue_positive S v s hx
  have hc (i : WishartDifferentialIndex p) : Measurable
      (fun x => (wishartDifferenceCoefficient q S v s i x : ℂ)) :=
    (wishartDifferenceCoefficient_measurable q S v s i).complex_ofReal
  have hi (i : WishartDifferentialIndex p) : Integrable
      (fun x => (wishartDifferenceCoefficient q S v s i x : ℂ)) (oneRowInputLaw q S) :=
    (wishartDifferenceCoefficient_integrable hq hs S v i).ofReal
  have hci (i : WishartDifferentialIndex p) : Integrable
      (fun x => ‖oneRowWishartValue S (s • v) x‖ *
        ‖(wishartDifferenceCoefficient q S v s i x : ℂ)‖) (oneRowInputLaw q S) := by
    simpa only [Complex.norm_real] using
      wishartDifferenceCoefficient_matrix_growth_integrable hq hs S v i
  exact matrix_laplace_differential_unique (oneRowInputLaw q S)
    (oneRowWishartValue S (s • v)) (measurable_oneRowWishartValue S (s • v)) hW
    (fun i x => (wishartDifferenceCoefficient q S v s i x : ℂ)) hc hi hci
    wishartDifferenceDirections wishartDifferenceDirections_hermitian
    (fun T hT => wishart_difference_laplace_zero hq hs hS v hT) f

theorem oneRowWishart_compact_differential_identity {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p))
    (f : MatrixEuclidean p → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∑ i : WishartDifferentialIndex p, ∫ x,
      (wishartDifferenceCoefficient q S v s i x : ℂ) *
        functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p)) f
          (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂(oneRowInputLaw q S)) = 0 := by
  let g := fun y : MatrixEuclidean p => Complex.exp (coordinateTrace p y : ℂ) * f y
  have hgc : HasCompactSupport g := hfc.mul_left
  have hg : ContDiff ℝ ∞ g := by
    exact ((Complex.ofRealCLM.comp (coordinateTrace p)).contDiff.cexp).mul hf
  let F : 𝓢(MatrixEuclidean p, ℂ) := hgc.toSchwartzMap hg
  have he : (fun y => exponentialDamping (coordinateTrace p) y * F y) = f := by
    funext y
    change Complex.exp (-(coordinateTrace p y : ℂ)) *
      (Complex.exp (coordinateTrace p y : ℂ) * f y) = f y
    rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  have h := oneRowWishart_schwartz_differential_identity hq hs hS v F
  rwa [he] at h

end ResearchMain.WishartBlocks
