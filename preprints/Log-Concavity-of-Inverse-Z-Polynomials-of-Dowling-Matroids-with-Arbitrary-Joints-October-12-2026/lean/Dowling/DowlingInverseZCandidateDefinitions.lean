import Dowling.DowlingLeadingRankOne

noncomputable section
namespace Dowling
open PowerSeries

/-- The actual braid Z candidate, before the full-Dowling group scaling. -/
def dowlingBraidZ : PowerSeries (Polynomial ℝ) := candidateExp braidLogZCandidate

/-- A block on j vertices contributes the primitive, not the braid series itself. -/
def dowlingBraidPrimitive : PowerSeries (Polynomial ℝ) := candidatePrimitive dowlingBraidZ

/-- The exponential series of a nonempty balanced labeled block. -/
def dowlingBlockCoordinate (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  C (Polynomial.C m⁻¹)*dowlingBraidPrimitive.subst (C (Polynomial.C m)*X)

/-- The unsigned inverse-Z factor in the source Lambert coordinate. -/
def dowlingInverseZBase (a : ℝ) : PowerSeries (Polynomial ℝ) :=
  candidateExp (-C (Polynomial.C a)*candidateLogZInU.subst (-X))

/-- Full-Dowling unsigned inverse-Z candidate, with the actual group scaling. -/
def dowlingInverseZCandidate (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  (dowlingInverseZBase m⁻¹).subst
    (dowlingLambertInverse.subst (C (Polynomial.C m)*X))

@[simp] theorem dowlingBraidPrimitive_constantCoeff : dowlingBraidPrimitive.constantCoeff=0 := by
  exact candidatePrimitive_constantCoeff _

@[simp] theorem dowlingBlockCoordinate_constantCoeff (m : ℝ) :
    (dowlingBlockCoordinate m).constantCoeff=0 := by
  rw [dowlingBlockCoordinate,map_mul,constantCoeff_C,
    candidate_subst_constantCoeff _ _ (by simp),dowlingBraidPrimitive_constantCoeff,mul_zero]

 theorem candidateLogZInU_constantCoeff : PowerSeries.constantCoeff candidateLogZInU=0 := by
  rw [← braidLogZCandidate_subst_coordinate,
    candidate_subst_constantCoeff _ _ dowlingLogCoordinate_constantCoeff,
    braidLogZCandidate_constantCoeff]

 theorem dowlingInverseZBase_argument_constantCoeff (a : ℝ) :
    PowerSeries.constantCoeff (-C (Polynomial.C a)*candidateLogZInU.subst (-X))=0 := by
  rw [map_mul,candidate_subst_constantCoeff _ _ (by simp),candidateLogZInU_constantCoeff,mul_zero]

@[simp] theorem dowlingInverseZBase_constantCoeff (a : ℝ) :
    (dowlingInverseZBase a).constantCoeff=1 :=
  candidateExp_constantCoeff (dowlingInverseZBase_argument_constantCoeff a)

 theorem dowlingBraidZ_eq_candidate_one : dowlingBraidZ=dowlingZCandidate 1 := by
  simp only [dowlingZCandidate,inv_one,map_one,one_mul,
    X_subst,dowlingBraidZ,candidateExp]

end Dowling
