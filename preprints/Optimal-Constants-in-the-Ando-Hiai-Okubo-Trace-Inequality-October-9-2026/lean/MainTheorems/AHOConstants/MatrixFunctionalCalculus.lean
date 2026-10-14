import MainTheorems.AHOConstants.SpectralPowers

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrix_cfc_add (A : Matrix I I ℂ) (f g : ℝ → ℝ) :
    cfc (fun x => f x + g x) A = cfc f A + cfc g A :=
  cfc_add A f g ((Matrix.finite_real_spectrum (A := A)).continuousOn f)
    ((Matrix.finite_real_spectrum (A := A)).continuousOn g)

theorem matrix_cfc_sub (A : Matrix I I ℂ) (f g : ℝ → ℝ) :
    cfc (fun x => f x - g x) A = cfc f A - cfc g A :=
  cfc_sub f g A ((Matrix.finite_real_spectrum (A := A)).continuousOn f)
    ((Matrix.finite_real_spectrum (A := A)).continuousOn g)

theorem matrix_cfc_mul (A : Matrix I I ℂ) (f g : ℝ → ℝ) :
    cfc (fun x => f x * g x) A = cfc f A * cfc g A :=
  cfc_mul f g A ((Matrix.finite_real_spectrum (A := A)).continuousOn f)
    ((Matrix.finite_real_spectrum (A := A)).continuousOn g)

theorem matrix_cfc_const_mul (A : Matrix I I ℂ) (r : ℝ) (f : ℝ → ℝ) :
    cfc (fun x => r * f x) A = r • cfc f A :=
  cfc_const_mul r f A ((Matrix.finite_real_spectrum (A := A)).continuousOn f)

end ResearchMain.AHOConstants
