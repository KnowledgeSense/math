import CircleKernel.KernelResidue
import CircleKernel.MeromorphicContinuation
import CircleResidues.Main

noncomputable section
open Filter
open scoped Topology
namespace CircleKernel

theorem residue_factor_eq (m : ℕ) :
    (complexResiduePolynomial (2*m)).eval (polePoint m) =
      (CircleResidues.residuePolynomial (1/2-(m : ℚ)) (2*m) : ℂ) := by
  simpa only [polePoint, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_natCast] using complexResiduePolynomial_rat (2*m) (1/2-(m : ℚ))

theorem residue_factor_ne_zero (m : ℕ) :
    (complexResiduePolynomial (2*m)).eval (polePoint m) ≠ 0 := by
  rw [residue_factor_eq]
  exact_mod_cast CircleResidues.residuePolynomial_ne_zero m

theorem kernelResidue_ne_zero (m : ℕ) : kernelResidue m ≠ 0 := by
  apply mul_ne_zero _ (residue_factor_ne_zero m)
  apply div_ne_zero (Complex.exp_ne_zero _)
  exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)

theorem kernelResidue_source_formula (m : ℕ) :
    kernelResidue m = (1/(2*Real.pi : ℂ))*Complex.exp (-(spectralConstant : ℂ)/2)*
      Complex.exp ((spectralConstant : ℂ)*(m : ℂ))*
        (CircleResidues.residuePolynomial (1/2-(m : ℚ)) (2*m) : ℂ) := by
  have he : Complex.exp (-(spectralConstant : ℂ)*polePoint m) =
      Complex.exp (-(spectralConstant : ℂ)/2)*Complex.exp ((spectralConstant : ℂ)*(m : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [polePoint]
    ring
  rw [kernelResidue, residue_factor_eq, he]
  ring

theorem continuedKernel_not_continuousAt_pole (m : ℕ) :
    ¬ ContinuousAt continuedKernel (polePoint m) := by
  intro hc
  have ht : Tendsto (fun t : ℂ => t-polePoint m) (𝓝[≠] polePoint m) (𝓝 0) := by
    simpa only [sub_self,id_eq] using (tendsto_id.sub_const (polePoint m)).mono_left
      (nhdsWithin_le_nhds (a := polePoint m) (s := ({polePoint m}ᶜ : Set ℂ)))
  have hzero := ht.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hzero
  exact kernelResidue_ne_zero m (tendsto_nhds_unique (continuedKernel_residue m) hzero)

end CircleKernel
