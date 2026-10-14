import FourGeneratedSemigroups.StaircaseSlices

noncomputable section
namespace FourGeneratedSemigroups
open PlaneStaircase

lemma card_by_slices (C : Set Factorization) (k : ℕ) (hf : C.Finite)
    (hzero : ∀ a ∈ C,a 0=0) (hbound : ∀ a ∈ C,a 3<k) :
    Nat.card C = ∑ z ∈ Finset.range k,
      Nat.card {p : Point | slicePoint p.1 p.2 z ∈ C} := by
  classical
  let F (z : Fin k) := {p : Point // slicePoint p.1 p.2 z.val ∈ C}
  let f : (Σ z : Fin k,F z) → C := fun a =>
    ⟨slicePoint a.2.val.1 a.2.val.2 a.1.val,a.2.property⟩
  have hfbij : Function.Bijective f := by
    constructor
    · rintro ⟨z,p⟩ ⟨w,q⟩ h
      have he := congrArg Subtype.val h
      have hzw : z=w := by
        apply Fin.ext
        simpa only [f,slicePoint_third] using congrArg (fun a : Factorization => a 3) he
      subst w
      have hpq : p=q := by
        apply Subtype.ext
        exact slicePoint_injective z.val he
      subst q
      rfl
    · intro a
      refine ⟨⟨⟨a.val 3,hbound a.val a.property⟩,⟨(a.val 1,a.val 2),?_⟩⟩,?_⟩
      · change slicePoint (a.val 1) (a.val 2) (a.val 3) ∈ C
        simpa only [slicePoint_reconstruct a.val (hzero a.val a.property)] using a.property
      · exact Subtype.ext (slicePoint_reconstruct a.val (hzero a.val a.property))
  let (z : Fin k) : Finite (F z) := (hf.preimage (slicePoint_injective z.val).injOn).to_subtype
  have he := (Nat.card_eq_of_bijective f hfbij).symm
  rw [Nat.card_sigma] at he
  change Nat.card C = ∑ z : Fin k, Nat.card {p : Point | slicePoint p.1 p.2 z.val ∈ C} at he
  exact he.trans (Fin.sum_univ_eq_sum_range
    (fun z => Nat.card {p : Point | slicePoint p.1 p.2 z ∈ C}) k)

variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma corners_card_eq_slice_sum :
    Nat.card (staircaseCorners G) =
      ∑ z ∈ Finset.range (criticalExponent G.generators G.positive 3),
        Nat.card (LostCorners (planeSlice G z) (planeSlice G (z+1))) := by
  have he := card_by_slices (staircaseCorners G) (criticalExponent G.generators G.positive 3)
    ((finite_staircase G).subset (fun _ h => h.1)) (fun _ h => h.1.1) (fun _ h => h.1.2.1)
  simpa only [slicePoint_corner_iff,Set.ofPred_mem_eq] using he

lemma generatorNumber_eq_slice_sum :
    staircaseGeneratorNumber G = Nat.card (Boundary (planeSlice G 0)) +
      ∑ z ∈ Finset.range (criticalExponent G.generators G.positive 3),
        Nat.card (Generators (planeSlice G z) (planeSlice G (z+1))) := by
  have he := card_by_slices {a | a∈staircaseBoundary G ∧ a 0=0}
    (criticalExponent G.generators G.positive 3+1)
    ((finite_staircaseBoundary G (finite_staircase G)).subset (fun _ h => h.1))
    (fun _ h => h.2) (fun _ h => by have := boundary_third_le_top G h.1; omega)
  simp only [Set.mem_ofPred_eq,slicePoint_zero,and_true] at he
  rw [Finset.sum_range_succ'] at he
  simpa only [Set.coe_ofPred,Set.ofPred_mem_eq,staircaseGeneratorNumber,slicePoint_boundary_zero_iff,slicePoint_boundary_succ_iff,
    Nat.add_comm] using he

lemma fullSupport_eq_slice_sum :
    fullSupportGeneratorNumber G =
      ∑ z ∈ Finset.range (criticalExponent G.generators G.positive 3),
        Nat.card (InteriorGenerators (planeSlice G z) (planeSlice G (z+1))) := by
  have he := card_by_slices {a | a∈staircaseBoundary G ∧ a 0=0 ∧ 0<a 1 ∧ 0<a 2 ∧ 0<a 3}
    (criticalExponent G.generators G.positive 3+1)
    ((finite_staircaseBoundary G (finite_staircase G)).subset (fun _ h => h.1))
    (fun _ h => h.2.1) (fun _ h => by have := boundary_third_le_top G h.1; omega)
  simp only [Set.mem_ofPred_eq,slicePoint_zero,slicePoint_first,slicePoint_second,slicePoint_third,
    true_and] at he
  rw [Finset.sum_range_succ'] at he
  simpa only [Set.coe_ofPred,Set.ofPred_mem_eq,Nat.card_coe_set_eq,Set.ncard_empty,fullSupportGeneratorNumber,slicePoint_boundary_succ_iff,InteriorGenerators,
    Nat.zero_lt_succ,and_true,lt_self_iff_false,and_false,Set.ofPred_false,
    Nat.add_zero] using he

end FourGeneratedSemigroups
