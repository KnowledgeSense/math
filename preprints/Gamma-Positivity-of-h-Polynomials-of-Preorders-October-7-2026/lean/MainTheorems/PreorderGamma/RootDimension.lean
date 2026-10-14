import MainTheorems.PreorderGamma.RootExposedFaces
import Mathlib.Data.Fintype.BigOperators

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def zeroSumLift : (E → ℝ) →ₗ[ℝ] (Option E → ℝ) where
  toFun x i := i.elim (-(∑ a, x a)) x
  map_add' := by
    intro x y
    funext i
    cases i with
    | none => simp only [Option.elim_none, Pi.add_apply, Finset.sum_add_distrib]; ring
    | some a => rfl
  map_smul' := by
    intro c x
    funext i
    cases i <;> simp [smul_eq_mul, ← Finset.mul_sum]

omit [DecidableEq E] [Preorder E] in
@[simp] theorem zeroSumLift_some (x : E → ℝ) (a : E) :
    zeroSumLift x (some a) = x a := rfl

omit [DecidableEq E] [Preorder E] in
@[simp] theorem zeroSumLift_none (x : E → ℝ) :
    zeroSumLift x none = -(∑ a, x a) := rfl

omit [DecidableEq E] [Preorder E] in
theorem zeroSumLift_sum (x : E → ℝ) : ∑ i, zeroSumLift x i = 0 := by
  rw [Fintype.sum_option]
  simp

omit [Preorder E] in
theorem zeroSumLift_single (a : E) :
    zeroSumLift (Pi.single a 1) = Pi.single (some a) 1 - Pi.single none 1 := by
  funext i
  cases i <;> simp [Pi.single_apply, eq_comm]

omit [Preorder E] in
theorem zeroSumLift_eq_sum (x : E → ℝ) :
    zeroSumLift x = ∑ a, x a • zeroSumLift (Pi.single a 1) := by
  funext i
  cases i with
  | none => simp [Finset.sum_apply, Pi.single_apply]
  | some a => simp [Finset.sum_apply, Pi.single_apply]

noncomputable def rootDirection : Submodule ℝ ((Option E → ℝ) × (Option E → ℝ)) where
  carrier := {x | (∑ i, x.1 i) = 0 ∧ (∑ j, x.2 j) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    simp [Finset.sum_add_distrib, hx, hy]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simp [smul_eq_mul, ← Finset.mul_sum, hx]

omit [DecidableEq E] [Preorder E] in
@[simp] theorem mem_rootDirection {x : (Option E → ℝ) × (Option E → ℝ)} :
    x ∈ rootDirection ↔ (∑ i, x.1 i) = 0 ∧ (∑ j, x.2 j) = 0 := Iff.rfl

noncomputable def rootDirectionLift :
    ((E → ℝ) × (E → ℝ)) →ₗ[ℝ] rootDirection (E := E) :=
  (zeroSumLift.prodMap zeroSumLift).codRestrict rootDirection
    (fun x => ⟨zeroSumLift_sum x.1, zeroSumLift_sum x.2⟩)

omit [DecidableEq E] [Preorder E] in
theorem rootDirectionLift_bijective : Function.Bijective (rootDirectionLift (E := E)) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    apply Prod.ext
    · funext a
      exact congrArg (fun z => z.1 (some a)) hv
    · funext a
      exact congrArg (fun z => z.2 (some a)) hv
  · intro x
    refine ⟨(fun a => x.val.1 (some a), fun a => x.val.2 (some a)), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext i
      cases i with
      | none =>
        change -(∑ a, x.val.1 (some a)) = x.val.1 none
        have h := x.property.1
        rw [Fintype.sum_option] at h
        linarith
      | some a => rfl
    · funext i
      cases i with
      | none =>
        change -(∑ a, x.val.2 (some a)) = x.val.2 none
        have h := x.property.2
        rw [Fintype.sum_option] at h
        linarith
      | some a => rfl

noncomputable def rootDirectionEquiv :
    ((E → ℝ) × (E → ℝ)) ≃ₗ[ℝ] rootDirection (E := E) :=
  LinearEquiv.ofBijective rootDirectionLift rootDirectionLift_bijective

omit [DecidableEq E] [Preorder E] in
theorem rootDirection_finrank : Module.finrank ℝ (rootDirection (E := E)) =
    2 * Fintype.card E := by
  simpa [Module.finrank_prod, two_mul] using (rootDirectionEquiv (E := E)).finrank_eq.symm

theorem rootPolytope_direction :
    (affineSpan ℝ (rootPolytope (E := E))).direction = rootDirection := by
  classical
  let p := rootVertex (none : Option E) none
  let a := affineSpan ℝ (rootPolytope (E := E))
  have hp : p ∈ a :=
    subset_affineSpan ℝ _ (rootVertex_mem_rootPolytope ⟨(none, none), trivial⟩)
  apply le_antisymm
  · have ha : a ≤ AffineSubspace.mk' p rootDirection := by
      change affineSpan ℝ (convexHull ℝ (rootVertices (E := E))) ≤ _
      rw [affineSpan_convexHull]
      apply affineSpan_le.mpr
      rintro v ⟨e, rfl⟩
      change rootVertex e.val.1 e.val.2 ∈ AffineSubspace.mk' p (rootDirection (E := E))
      rw [AffineSubspace.mem_mk']
      change (∑ i, (rootVertex e.val.1 e.val.2 - p).1 i) = 0 ∧
        (∑ j, (rootVertex e.val.1 e.val.2 - p).2 j) = 0
      simp [rootVertex, p, Finset.sum_sub_distrib, Pi.single_apply]
    have h := AffineSubspace.direction_le ha
    rwa [AffineSubspace.direction_mk'] at h
  · have hl : ∀ b : E, (zeroSumLift (Pi.single b 1), 0) ∈ a.direction := by
      intro b
      have hb : rootVertex (some b) none ∈ a :=
        subset_affineSpan ℝ _ (rootVertex_mem_rootPolytope ⟨(some b, none), trivial⟩)
      convert AffineSubspace.vsub_mem_direction hb hp using 1
      rw [zeroSumLift_single]
      ext <;> simp [rootVertex, p]
    have hr : ∀ b : E, (0, zeroSumLift (Pi.single b 1)) ∈ a.direction := by
      intro b
      have hb : rootVertex none (some b) ∈ a :=
        subset_affineSpan ℝ _ (rootVertex_mem_rootPolytope ⟨(none, some b), trivial⟩)
      convert AffineSubspace.vsub_mem_direction hb hp using 1
      rw [zeroSumLift_single]
      ext <;> simp [rootVertex, p]
    intro v hv
    obtain ⟨x, hx⟩ := rootDirectionEquiv.surjective (⟨v, hv⟩ : rootDirection)
    have hleft := a.direction.sum_mem (fun b (_ : b ∈ (Finset.univ : Finset E)) =>
      a.direction.smul_mem (x.1 b) (hl b))
    have hright := a.direction.sum_mem (fun b (_ : b ∈ (Finset.univ : Finset E)) =>
      a.direction.smul_mem (x.2 b) (hr b))
    have hsum := a.direction.add_mem hleft hright
    have hdecomp :
        (∑ b, x.1 b • (zeroSumLift (Pi.single b 1), (0 : Option E → ℝ))) +
          (∑ b, x.2 b • ((0 : Option E → ℝ), zeroSumLift (Pi.single b 1))) =
        (zeroSumLift x.1, zeroSumLift x.2) := by
      change
        (∑ b, (x.1 b • zeroSumLift (Pi.single b 1), x.1 b • (0 : Option E → ℝ))) +
          (∑ b, (x.2 b • (0 : Option E → ℝ), x.2 b • zeroSumLift (Pi.single b 1))) = _
      simp only [smul_zero, ← prod_mk_sum, Finset.sum_const_zero,
        Prod.mk_add_mk, add_zero, zero_add]
      rw [← zeroSumLift_eq_sum, ← zeroSumLift_eq_sum]
    rw [hdecomp] at hsum
    have hv' : (zeroSumLift x.1, zeroSumLift x.2) = v := congrArg Subtype.val hx
    rwa [hv'] at hsum

theorem rootPolytope_dimension :
    Module.finrank ℝ (affineSpan ℝ (rootPolytope (E := E))).direction =
      2 * Fintype.card E := by
  rw [rootPolytope_direction]
  exact rootDirection_finrank

end ResearchMain.PreorderGamma
