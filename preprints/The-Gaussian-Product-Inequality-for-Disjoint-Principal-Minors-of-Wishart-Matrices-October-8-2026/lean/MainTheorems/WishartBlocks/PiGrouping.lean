import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Probability.Independence.Basic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem finite_pi_curry {ι : Type*} {κ : ι → Type*}
    [Fintype ι] [∀ i, Fintype (κ i)]
    {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]
    (μ : (i : ι) → (j : κ i) → Measure (X i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi fun ij : Sigma κ => μ ij.1 ij.2)
      (Measure.pi fun i => Measure.pi (μ i)) := by
  apply MeasurePreserving.symm (MeasurableEquiv.piCurry X).symm
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply (MeasurableEquiv.piCurry X).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i, j⟩)) := by
    ext x
    simp only [Set.mem_preimage, MeasurableEquiv.coe_piCurry_symm,
      Sigma.uncurry, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h i j
      exact h ⟨i, j⟩
    · intro h ⟨i, j⟩
      exact h i j
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_sigma]

theorem finite_pi_injection {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (e : κ → ι) (he : Function.Injective e) :
    (Measure.pi μ).map (fun x k => x (e k)) = Measure.pi (fun k => μ (e k)) := by
  have hi := iIndepFun_pi (μ := μ) (X := fun _ : ι => (id : X → X))
    (fun _ => aemeasurable_id)
  have heI := iIndepFun.precomp (g := e) he hi
  rw [iIndepFun.map_fun_eq_pi_map (fun k => (measurable_pi_apply (e k)).aemeasurable) heI]
  congr 1
  funext k
  exact (measurePreserving_eval μ (e k)).map_eq

end ResearchMain.WishartBlocks
