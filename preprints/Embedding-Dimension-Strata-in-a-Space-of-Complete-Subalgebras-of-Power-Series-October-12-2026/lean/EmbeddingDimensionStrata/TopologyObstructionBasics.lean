import EmbeddingDimensionStrata.GeometryPrincipalOpens
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Classical-topology constructions for the punctured product

All spaces carry their ordinary complex Euclidean/product/subspace topologies.
-/
noncomputable section
namespace EmbeddingDimensionStrata
namespace TopologyObstructions
open scoped ContinuousMap
open GeometryObstructions

/-- The classical space `C^m × (C³ \\ {0})`. -/
abbrev ClassicalPuncturedProduct (m : ℕ) :=
  (Fin m → ℂ) × {z : Fin 3 → ℂ // z ≠ 0}

/-- The comparison space `C* × C^m`, with its ordinary product topology. -/
abbrev ClassicalPredictedProduct (m : ℕ) :=
  {z : ℂ // z ≠ 0} × (Fin m → ℂ)

/-- Split the free and the distinguished coordinates without changing topology. -/
def puncturedProductHomeomorph (m : ℕ) :
    puncturedProduct (K := ℂ) m ≃ₜ ClassicalPuncturedProduct m where
  toFun x := (fun i => x.val (Sum.inl i), ⟨fun i => x.val (Sum.inr i), by
    intro h
    obtain ⟨i, hi⟩ := x.property
    exact hi (congrFun h i)⟩)
  invFun x := ⟨Sum.elim x.1 x.2.val, by
    change ∃ i, x.2.val i ≠ 0
    by_contra! h
    exact x.2.property (funext h)⟩
  left_inv x := by ext i; cases i <;> rfl
  right_inv x := by rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun i => (continuous_apply (Sum.inl i)).comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_pi fun i => (continuous_apply (Sum.inr i)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact (continuous_apply i).comp continuous_fst
    | inr i => exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)

/-- The ordinary punctured complex plane has a nontrivial fundamental group,
proved via the exponential covering rather than an assumed obstruction. -/
theorem complex_punctured_not_simply_connected :
    ¬ SimplyConnectedSpace {z : ℂ // z ≠ 0} := by
  intro h
  let e := Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
    (x := (⟨1, one_ne_zero⟩ : {z : ℂ // z ≠ 0})) ⟨0, by simp⟩
  have : Subsingleton ((Multiplicative
      (AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)))ᵐᵒᵖ) :=
    e.toEquiv.subsingleton_congr.mp inferInstance
  let a : AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ) :=
    ⟨2 * Real.pi * Complex.I, AddSubgroup.mem_zmultiples _⟩
  have hh := Subsingleton.elim
    (MulOpposite.op (Multiplicative.ofAdd a))
    (MulOpposite.op (Multiplicative.ofAdd (0 : AddSubgroup.zmultiples
      (2 * Real.pi * Complex.I : ℂ))))
  have hz : (2 * Real.pi * Complex.I : ℂ) = 0 :=
    congrArg (fun z => ((Multiplicative.toAdd (MulOpposite.unop z) :
      AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)) : ℂ)) hh
  have hn : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  exact hn hz

/-- A contractible affine factor can be removed by an actual homotopy equivalence. -/
def predictedProductHomotopyEquiv (m : ℕ) :
    ClassicalPredictedProduct m ≃ₕ {z : ℂ // z ≠ 0} :=
  ((ContinuousMap.HomotopyEquiv.refl _).prodCongr
    (ContractibleSpace.hequiv_unit (Fin m → ℂ)).some).trans
    (Homeomorph.prodUnique _ Unit).toHomotopyEquiv

/-- Thus the proposed product is not simply connected in its classical topology. -/
theorem predictedProduct_not_simply_connected (m : ℕ) :
    ¬ SimplyConnectedSpace (ClassicalPredictedProduct m) := by
  intro h
  exact complex_punctured_not_simply_connected
    ((predictedProductHomotopyEquiv m).symm.simplyConnectedSpace)

/-- A punctured complex three-space is homotopy equivalent to its unit sphere. -/
def puncturedTripleSphereHomotopyEquiv :
    {z : Fin 3 → ℂ // z ≠ 0} ≃ₕ Metric.sphere (0 : Fin 3 → ℂ) 1 := by
  haveI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  exact (homeomorphUnitSphereProd (Fin 3 → ℂ)).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl _).prodCongr
      (ContractibleSpace.hequiv_unit (Set.Ioi (0 : ℝ))).some).trans
      (Homeomorph.prodUnique _ Unit).toHomotopyEquiv)

/-- The free affine factor does not affect the homotopy type. -/
def puncturedProductSphereHomotopyEquiv (m : ℕ) :
    ClassicalPuncturedProduct m ≃ₕ Metric.sphere (0 : Fin 3 → ℂ) 1 :=
  (((ContractibleSpace.hequiv_unit (Fin m → ℂ)).some.prodCongr
      (ContinuousMap.HomotopyEquiv.refl _)).trans
      (Homeomorph.uniqueProd Unit _).toHomotopyEquiv).trans
    puncturedTripleSphereHomotopyEquiv

end TopologyObstructions
end EmbeddingDimensionStrata
