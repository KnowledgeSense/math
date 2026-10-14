import CircleKernel.BellPolynomials
import CircleResidues.SourceBridge

noncomputable section
open PowerSeries Finset
namespace CircleKernel

theorem ordinaryBell_odd (j ell : ℕ) (hj : Odd j) : CircleResidues.ordinaryBell j ell = 0 := by
  have hs := CircleResidues.sourceExponent_even 1
  simp only [one_mul] at hs
  rw [CircleResidues.ordinaryBell, hs,
    ← subst_pow (HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0)),
    coeff_subst_X_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hnd : ¬ 2 ∣ j := fun h => (Nat.not_even_iff_odd.mpr hj) (even_iff_two_dvd.mpr h)
  simp [hnd]

theorem complexResiduePolynomial_odd (j : ℕ) (hj : Odd j) : complexResiduePolynomial j = 0 := by
  simp [complexResiduePolynomial, ordinaryBell_odd j _ hj]

@[simp] theorem complexResiduePolynomial_zero : complexResiduePolynomial 0 = 1 := by
  simp [complexResiduePolynomial, CircleResidues.ordinaryBell]

end CircleKernel
