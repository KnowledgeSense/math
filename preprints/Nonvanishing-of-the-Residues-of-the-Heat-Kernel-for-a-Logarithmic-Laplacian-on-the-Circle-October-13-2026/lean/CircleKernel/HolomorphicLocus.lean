import CircleKernel.Continuation
import CircleKernel.OddResidues

noncomputable section
open Filter Finset
open scoped Topology
namespace CircleKernel

def polePoint (m : ℕ) : ℂ := 1/2-(m : ℂ)

theorem regularizedKernel_differentiableAt (M : ℕ) (hM : 0 < M) (t : ℂ)
    (hdom : 1 < 2*t.re+(M : ℝ)) (ht : ∀ m : ℕ, t ≠ polePoint m) :
    DifferentiableAt ℂ (regularizedKernel M) t := by
  have hterms : ∀ j ∈ range M, DifferentiableAt ℂ
      (fun w => (complexResiduePolynomial j).eval w*riemannZeta (2*w+j)) t := by
    intro j hj
    rcases Nat.even_or_odd j with he | ho
    · have hne : 2*t+(j : ℂ) ≠ 1 := by
        intro h
        obtain ⟨m,hm⟩ := he
        apply ht m
        simp only [polePoint]
        rw [hm, Nat.cast_add] at h
        linear_combination (1/2 : ℂ)*h
      exact ((complexResiduePolynomial j).differentiableAt).mul
        ((differentiableAt_riemannZeta hne).comp t (by fun_prop))
    · simp only [complexResiduePolynomial_odd j ho, Polynomial.eval_zero, zero_mul]
      exact differentiableAt_const 0
  have hs := DifferentiableAt.fun_sum hterms
  have hr := spectralRemainder_differentiableAt M hM t hdom
  have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(spectralConstant : ℂ)*w)) t := by fun_prop
  exact (differentiableAt_const _).add ((he.mul hs |>.add hr).const_mul _)

theorem continuedKernel_differentiableAt (t : ℂ) (ht : ∀ m : ℕ, t ≠ polePoint m) :
    DifferentiableAt ℂ continuedKernel t := by
  obtain ⟨hM,hdom⟩ := regularizationOrder_spec t
  exact (regularizedKernel_differentiableAt _ hM t hdom ht).congr_of_eventuallyEq
    (continuedKernel_eventuallyEq _ hM t hdom)

end CircleKernel
