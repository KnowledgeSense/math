import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace ResearchMain.WishartBlocks

open MeasureTheory BoundedContinuousFunction

variable {E ι : Type*} [TopologicalSpace E] [AddMonoid ι]

noncomputable def kernelMonoidHom (K : ι → E →ᵇ ℝ) (h0 : K 0 = 1)
    (hadd : ∀ i j, K (i + j) = K i * K j) : Multiplicative ι →* (E →ᵇ ℝ) where
  toFun i := K i.toAdd
  map_one' := h0
  map_mul' := hadd

noncomputable def kernelAlgHom (K : ι → E →ᵇ ℝ) (h0 : K 0 = 1)
    (hadd : ∀ i j, K (i + j) = K i * K j) :
    AddMonoidAlgebra ℝ ι →ₐ[ℝ] (E →ᵇ ℝ) :=
  AddMonoidAlgebra.lift ℝ (E →ᵇ ℝ) ι (kernelMonoidHom K h0 hadd)

theorem kernelAlgHom_apply (K : ι → E →ᵇ ℝ) (h0 : K 0 = 1)
    (hadd : ∀ i j, K (i + j) = K i * K j) (w : AddMonoidAlgebra ℝ ι) (x : E) :
    kernelAlgHom K h0 hadd w x = w.coeff.sum (fun i a => a * K i x) := by
  simp [kernelAlgHom, kernelMonoidHom, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  rfl

noncomputable def kernelPolynomial (K : ι → E →ᵇ ℝ) (h0 : K 0 = 1)
    (hadd : ∀ i j, K (i + j) = K i * K j) : StarSubalgebra ℝ (E →ᵇ ℝ) where
  toSubalgebra := (kernelAlgHom K h0 hadd).range
  star_mem' {x} hx := by
    have he : star x = x := by
      ext z
      simp only [BoundedContinuousFunction.star_apply, star_trivial]
    rwa [he]

theorem kernel_mem_polynomial (K : ι → E →ᵇ ℝ) (h0 : K 0 = 1)
    (hadd : ∀ i j, K (i + j) = K i * K j) (i : ι) :
    K i ∈ kernelPolynomial K h0 hadd := by
  refine ⟨AddMonoidAlgebra.single i 1, ?_⟩
  ext x
  simp [kernelAlgHom_apply]

theorem kernelPolynomial_separatesPoints (K : ι → E →ᵇ ℝ) (h0 : K 0 = 1)
    (hadd : ∀ i j, K (i + j) = K i * K j)
    (hsep : ∀ x y : E, x ≠ y → ∃ i, K i x ≠ K i y) :
    ((kernelPolynomial K h0 hadd).map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ := hsep x y hxy
  use K i
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  exact ⟨⟨K i, kernel_mem_polynomial K h0 hadd i, rfl⟩, hi⟩

theorem measure_eq_of_kernel_integrals [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : ι → E →ᵇ ℝ) (h0 : K 0 = 1) (hadd : ∀ i j, K (i + j) = K i * K j)
    (hsep : ∀ x y : E, x ≠ y → ∃ i, K i x ≠ K i y)
    (heq : ∀ i, ∫ x, K i x ∂μ = ∫ x, K i x ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (kernelPolynomial_separatesPoints K h0 hadd hsep)
  intro g hg
  obtain ⟨w, rfl⟩ := hg
  change (∫ x, kernelAlgHom K h0 hadd w x ∂μ) =
    ∫ x, kernelAlgHom K h0 hadd w x ∂ν
  simp_rw [kernelAlgHom_apply]
  have hsum (ρ : Measure E) [IsFiniteMeasure ρ] :
      ∫ x, w.coeff.sum (fun i a => a * K i x) ∂ρ =
        w.coeff.sum (fun i a => ∫ x, a * K i x ∂ρ) := by
    exact integral_finsetSum _ (fun i _ => ((K i).integrable ρ).const_mul _)
  rw [hsum μ, hsum ν]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [integral_const_mul, integral_const_mul, heq]

end ResearchMain.WishartBlocks
