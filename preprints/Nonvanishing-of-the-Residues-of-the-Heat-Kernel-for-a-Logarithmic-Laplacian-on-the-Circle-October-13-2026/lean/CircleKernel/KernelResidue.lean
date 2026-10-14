import CircleKernel.FiniteZetaResidue

noncomputable section
open Filter Finset
open scoped Topology
namespace CircleKernel

def kernelResidue (m : ℕ) : ℂ :=
  Complex.exp (-(spectralConstant : ℂ)*polePoint m)/(2*Real.pi)*
    (complexResiduePolynomial (2*m)).eval (polePoint m)

theorem polePoint_regularization_domain (m : ℕ) :
    1 < 2*(polePoint m).re+((2*m+2 : ℕ) : ℝ) := by
  norm_num [polePoint, Complex.sub_re, Complex.div_re]
  linarith

theorem regularizedKernel_residue (m : ℕ) :
    Tendsto (fun t : ℂ => (t-polePoint m)*regularizedKernel (2*m+2) t)
      (𝓝[≠] polePoint m) (𝓝 (kernelResidue m)) := by
  let p := polePoint m
  let M := 2*m+2
  have hdom : 1 < 2*p.re+(M : ℝ) := polePoint_regularization_domain m
  have ht : Tendsto (fun t : ℂ => t-p) (𝓝[≠] p) (𝓝 0) := by
    simpa only [sub_self, id_eq] using (tendsto_id.sub_const p).mono_left
      (nhdsWithin_le_nhds (a := p) (s := ({p}ᶜ : Set ℂ)))
  have he : Tendsto (fun t : ℂ => Complex.exp (-(spectralConstant : ℂ)*t))
      (𝓝[≠] p) (𝓝 (Complex.exp (-(spectralConstant : ℂ)*p))) :=
    (show Continuous (fun t : ℂ => Complex.exp (-(spectralConstant : ℂ)*t)) by fun_prop).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hr := (spectralRemainder_differentiableAt M (by dsimp [M]; omega) p hdom).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (a := p) (s := ({p}ᶜ : Set ℂ)))
  have hz := finite_zeta_residue m M (by dsimp [M]; omega)
  have h := (ht.const_mul (1/(2*Real.pi : ℂ))).add
    (((he.mul hz).add (ht.mul hr)).const_mul (1/(Real.pi : ℂ)))
  have hval : (1/(2*Real.pi : ℂ))*0 + (1/(Real.pi : ℂ))*
      (Complex.exp (-(spectralConstant : ℂ)*p)*
        ((complexResiduePolynomial (2*m)).eval p/2)+0*spectralRemainder M p) = kernelResidue m := by
    dsimp [kernelResidue,p]
    ring
  rw [hval] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [regularizedKernel]
  ring

theorem continuedKernel_residue (m : ℕ) :
    Tendsto (fun t : ℂ => (t-polePoint m)*continuedKernel t)
      (𝓝[≠] polePoint m) (𝓝 (kernelResidue m)) := by
  apply (regularizedKernel_residue m).congr'
  filter_upwards [(continuedKernel_eventuallyEq (2*m+2) (by omega) (polePoint m)
    (polePoint_regularization_domain m)).filter_mono nhdsWithin_le_nhds] with t ht
  rw [ht]

end CircleKernel
