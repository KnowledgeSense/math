import Dowling.JointlessActualSeriesCoordinate
import Dowling.DowlingInverseZCandidateFixedRows

noncomputable section
namespace Dowling
open PowerSeries

/-- Source fixed-total kernel before eliminating the linear coordinate term. -/
def jointlessRawKernel (a : ℝ) (n : ℕ) : PowerSeries (Polynomial ℝ) :=
  dowlingFixedKernel (((n : ℝ)+a)/2) a-
    C (Polynomial.C a)*C (1+Polynomial.X)*X*dowlingFixedKernel (((n : ℝ)+a-1)/2) a+
    C (Polynomial.C (a^2))*C Polynomial.X*X^2*dowlingFixedKernel (((n : ℝ)+a-1)/2) a-
    C (Polynomial.C (a^2/3))*C (Polynomial.X^2)*X^4*dowlingFixedKernel (((n : ℝ)+a-1)/2) a

theorem jointlessBase_kernel (m : ℝ) (n : ℕ) :
    jointlessBase m*(candidateExp (-dowlingQuadraticExponent))^n*(1-C Polynomial.X*X^2)=
      jointlessRawKernel m⁻¹ n := by
  let a := m⁻¹
  let F := dowlingBinomialSeries a*(dowlingBinomialSeries a).subst (C Polynomial.X*X)
  let J : PowerSeries (Polynomial ℝ) := 1-C Polynomial.X*X^2
  have hneg : candidateExp dowlingQuadraticExponent=dowlingQuadraticExp (-1/2) := by
    apply congrArg candidateExp
    dsimp [dowlingQuadraticExponent]
    rw [show (-1/2 : ℝ)=-(1/2 : ℝ) by ring,map_neg,map_neg]
    ring
  have h0 : dowlingInverseZBase a*(candidateExp (-dowlingQuadraticExponent))^n*J=
      dowlingFixedKernel (((n : ℝ)+a)/2) a := by
    rw [dowlingInverseZBase_factorization,dowlingQuadraticExp_power]
    have he := dowlingQuadraticExp_add (a/2) ((n : ℝ)/2)
    rw [show a/2+(n : ℝ)/2=((n : ℝ)+a)/2 by ring] at he
    calc
      _ = J*(dowlingQuadraticExp (a/2)*dowlingQuadraticExp ((n : ℝ)/2))*F := by dsimp [F]; ring
      _ = _ := by rw [he]; dsimp [dowlingFixedKernel,dowlingFixedGaussianProduct,F]; ring
  have h1 : dowlingInverseZBase a*(candidateExp (-dowlingQuadraticExponent))^n*
      candidateExp dowlingQuadraticExponent*J=dowlingFixedKernel (((n : ℝ)+a-1)/2) a := by
    rw [dowlingInverseZBase_factorization,dowlingQuadraticExp_power,hneg]
    have he := dowlingQuadraticExp_add (a/2) ((n : ℝ)/2)
    have he' := dowlingQuadraticExp_add (a/2+(n : ℝ)/2) (-1/2)
    rw [show a/2+(n : ℝ)/2+(-1/2)=((n : ℝ)+a-1)/2 by ring] at he'
    calc
      _ = J*((dowlingQuadraticExp (a/2)*dowlingQuadraticExp ((n : ℝ)/2))*
          dowlingQuadraticExp (-1/2))*F := by dsimp [F]; ring
      _ = _ := by rw [he,he']; dsimp [dowlingFixedKernel,dowlingFixedGaussianProduct,F]; ring
  have hc : C (Polynomial.C (a^2/3))=C (Polynomial.C a)*C (Polynomial.C a)*C (Polynomial.C (1/3 : ℝ)) := by
    rw [← map_mul,← map_mul,← map_mul,← map_mul]
    congr 2
    ring
  have hc2 : C (Polynomial.C (a^2))=C (Polynomial.C a)*C (Polynomial.C a) := by
    rw [← map_mul,← map_mul,pow_two]
  have ht2 : C (Polynomial.X^2)=(C Polynomial.X : PowerSeries (Polynomial ℝ))^2 := map_pow _ _ _
  dsimp only [jointlessBase,jointlessComparison,dowlingLeadingLog,dowlingLambertCoordinate,jointlessRawKernel]
  change _=dowlingFixedKernel (((n : ℝ)+a)/2) a-
    C (Polynomial.C a)*C (1+Polynomial.X)*X*dowlingFixedKernel (((n : ℝ)+a-1)/2) a+
    C (Polynomial.C (a^2))*C Polynomial.X*X^2*dowlingFixedKernel (((n : ℝ)+a-1)/2) a-
    C (Polynomial.C (a^2/3))*C (Polynomial.X^2)*X^4*dowlingFixedKernel (((n : ℝ)+a-1)/2) a
  rw [← h0,← h1,hc,hc2,ht2]
  dsimp [a,J]
  ring

theorem jointlessSeries_raw_kernel (m : ℝ) (hm : m≠0) (n : ℕ) :
    coeff n (jointlessSeries m)=Polynomial.C (m^n)*coeff n (jointlessRawKernel m⁻¹ n) := by
  rw [jointlessSeries_coeff_change m hm n,jointlessBase_kernel]

end Dowling
