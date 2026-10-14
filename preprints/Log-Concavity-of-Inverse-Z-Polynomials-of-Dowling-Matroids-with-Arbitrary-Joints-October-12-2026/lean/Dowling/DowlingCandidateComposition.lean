import Dowling.DowlingCandidateFlatCoordinate

noncomputable section
namespace Dowling
open PowerSeries

 theorem candidate_subst_injective {q : PowerSeries (Polynomial ℝ)}
    (hq : q.constantCoeff=0) (hu : IsUnit (coeff 1 q)) :
    Function.Injective (fun f : PowerSeries (Polynomial ℝ) => f.subst q) := by
  intro f g h
  have hi := HasSubst.substInvOfIsUnit q hu
  have hq' := HasSubst.of_constantCoeff_zero' hq
  have he := congrArg (fun f : PowerSeries (Polynomial ℝ) => f.subst (q.substInvOfIsUnit hu)) h
  rw [subst_comp_subst_apply hq' hi,subst_comp_subst_apply hq' hi,
    subst_substInvOfIsUnit_right q hq hu] at he
  simpa only [X_subst] using he

theorem candidate_subst_constantCoeff (f g : PowerSeries (Polynomial ℝ))
    (hg : g.constantCoeff=0) : PowerSeries.constantCoeff (f.subst g)=f.constantCoeff := by
  rw [PowerSeries.constantCoeff_eq,constantCoeff_subst_of_constantCoeff_zero hg]
  rfl

 theorem candidate_scalar_inverse (m : ℝ) (hm : m≠0) :
    (C (Polynomial.C m) : PowerSeries (Polynomial ℝ))*C (Polynomial.C m⁻¹)=1 := by
  have h := congrArg (fun r : ℝ => (C (Polynomial.C r) : PowerSeries (Polynomial ℝ)))
    (mul_inv_cancel₀ hm)
  simpa only [map_mul,map_one] using h

 theorem candidate_subst_C_mul {f g : PowerSeries (Polynomial ℝ)}
    (hg : g.constantCoeff=0) (c : Polynomial ℝ) :
    (C c*f).subst g=C c*(f.subst g) := by
  have hs := HasSubst.of_constantCoeff_zero' hg
  rw [← coe_substAlgHom hs,map_mul,coe_substAlgHom,subst_C]
  rfl

 theorem candidate_subst_C_mul_X {g : PowerSeries (Polynomial ℝ)}
    (hg : g.constantCoeff=0) (c : Polynomial ℝ) : (C c*X).subst g=C c*g := by
  rw [candidate_subst_C_mul hg,subst_X (HasSubst.of_constantCoeff_zero' hg)]

theorem candidate_subst_rescale (f : PowerSeries (Polynomial ℝ))
    {g : PowerSeries (Polynomial ℝ)} (hg : g.constantCoeff=0) (c : Polynomial ℝ) :
    PowerSeries.subst g (f.subst (C c*X))=f.subst (C c*g) := by
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by simp))
    (HasSubst.of_constantCoeff_zero' hg),candidate_subst_C_mul_X hg]

def dowlingComparisonCoordinate (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  C (Polynomial.C m⁻¹)*candidateGofU

@[simp] theorem dowlingComparisonCoordinate_constantCoeff (m : ℝ) :
    (dowlingComparisonCoordinate m).constantCoeff=0 := by simp [dowlingComparisonCoordinate]

 theorem candidateGofU_coeff_one : coeff 1 candidateGofU=1 := by
  rw [candidateGofU,candidate_coeff_subst _ _ candidateU_constantCoeff]
  norm_num [Finset.sum_range_succ,candidateU_coeff_one]

 theorem dowlingComparisonCoordinate_linear_unit (m : ℝ) (hm : m≠0) :
    IsUnit (coeff 1 (dowlingComparisonCoordinate m)) := by
  rw [dowlingComparisonCoordinate,coeff_C_mul,candidateGofU_coeff_one,mul_one]
  exact (isUnit_iff_ne_zero.mpr (inv_ne_zero hm)).map Polynomial.C

 theorem dowlingComparisonCoordinate_cancel (m : ℝ) (hm : m≠0) :
    C (Polynomial.C m)*dowlingComparisonCoordinate m=candidateGofU := by
  rw [dowlingComparisonCoordinate,← mul_assoc,candidate_scalar_inverse m hm,one_mul]

end Dowling
