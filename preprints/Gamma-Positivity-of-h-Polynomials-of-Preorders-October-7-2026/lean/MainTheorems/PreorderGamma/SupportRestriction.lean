import MainTheorems.PreorderGamma.PositivePatternDemands
import Mathlib.Data.Fintype.BigOperators

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {L R : Type*} [Fintype L] [Fintype R]

omit [Fintype L] in
theorem graphNeighbors_restrict_left (r : L → R → Prop) (I : Finset L) (A : Finset I) :
    graphNeighbors (fun a : I => r a.val) A = graphNeighbors r (A.image Subtype.val) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := mem_graphNeighbors.mp hb
    exact mem_graphNeighbors.mpr ⟨a.val, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hab⟩
  · intro hb
    obtain ⟨a, ha, hab⟩ := mem_graphNeighbors.mp hb
    obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
    exact mem_graphNeighbors.mpr ⟨c, hc, hca.symm ▸ hab⟩

omit [Fintype L] in
theorem restrict_left_isDemand (r : L → R → Prop) (I : Finset L) (d : L → ℕ)
    (hd : IsDemand r d) : IsDemand (fun a : I => r a.val) (fun a => d a.val) := by
  classical
  intro A
  have h := hd (A.image Subtype.val)
  rw [← graphNeighbors_restrict_left r I A, Finset.sum_image] at h
  · exact h
  · intro a ha c hc hac
    exact Subtype.ext hac

omit [Fintype L] in
theorem extend_left_isDemand (r : L → R → Prop) (I : Finset L) (d : I → ℕ)
    (hd : IsDemand (fun a : I => r a.val) d) : IsDemand r (extendDemand I d) := by
  classical
  intro A
  let T : Finset I := Finset.univ.filter fun a => a.val ∈ A
  have hT : T.image Subtype.val = A ∩ I := by
    ext a
    constructor
    · intro ha
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hc).2, c.property⟩
    · intro ha
      obtain ⟨haA, haI⟩ := Finset.mem_inter.mp ha
      exact Finset.mem_image.mpr
        ⟨⟨a, haI⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haA⟩, rfl⟩
  have hsum : (∑ a ∈ A, extendDemand I d a) = ∑ a ∈ T, d a := by
    calc
      _ = ∑ a ∈ A ∩ I, extendDemand I d a := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro a ha hnot
        have haI : a ∉ I := fun h => hnot (Finset.mem_inter.mpr ⟨ha, h⟩)
        exact extendDemand_not_mem I d haI
      _ = ∑ a ∈ T, extendDemand I d a.val := by
        rw [← hT, Finset.sum_image]
        intro a ha c hc hac
        exact Subtype.ext hac
      _ = _ := by simp only [extendDemand_mem]
  have h := hd T
  rw [graphNeighbors_restrict_left, hT] at h
  rw [hsum]
  exact h.trans (Finset.card_le_card (graphNeighbors_mono r Finset.inter_subset_left))

noncomputable def extendBoundedDemand (I : Finset L)
    (d : I → Fin (Fintype.card R + 1)) : L → Fin (Fintype.card R + 1) := by
  classical
  exact fun a => if ha : a ∈ I then d ⟨a, ha⟩ else 0

omit [Fintype L] in
@[simp] theorem extendBoundedDemand_mem (I : Finset L)
    (d : I → Fin (Fintype.card R + 1)) (a : I) : extendBoundedDemand I d a.val = d a := by
  classical
  simp [extendBoundedDemand, a.property]

omit [Fintype L] in
theorem extendBoundedDemand_val (I : Finset L) (d : I → Fin (Fintype.card R + 1)) :
    (fun a => (extendBoundedDemand I d a).val) = extendDemand I (fun a => (d a).val) := by
  classical
  funext a
  by_cases ha : a ∈ I <;> simp [extendBoundedDemand, extendDemand, ha]

theorem extendBoundedDemand_support (I : Finset L)
    (d : I → Fin (Fintype.card R + 1)) (hpos : ∀ a, 0 < (d a).val) :
    demandSupport (fun a => (extendBoundedDemand I d a).val) = I := by
  classical
  ext a
  simp only [demandSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : a ∈ I
  · simp only [extendBoundedDemand, dite_eq_left ha]
    exact ⟨fun _ => ha, fun _ => hpos ⟨a, ha⟩⟩
  · simp [extendBoundedDemand, ha]

noncomputable def demandPositiveSupportEquiv (r : L → R → Prop) :
    ↥(demandVectors r) ≃ Σ I : Finset L, PositiveDemand (fun a : I => r a.val) := by
  classical
  refine
    { toFun := fun d =>
        ⟨demandSupport (fun a => (d.val a).val), ⟨fun a => d.val a.val, ?_, ?_⟩⟩
      invFun := fun q => ⟨extendBoundedDemand q.1 q.2.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact restrict_left_isDemand r _ _ (Finset.mem_filter.mp d.property).2
  · intro a
    exact (Finset.mem_filter.mp a.property).2
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [extendBoundedDemand_val]
    exact extend_left_isDemand r _ _ q.2.property.1
  · intro d
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ demandSupport (fun c => (d.val c).val)
    · simp [extendBoundedDemand, ha]
    · have hz : (d.val a).val = 0 := by
        have hn : ¬0 < (d.val a).val := fun h => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        omega
      have hfin : d.val a = 0 := Fin.ext hz
      simp [extendBoundedDemand, ha, hfin]
  · rintro ⟨I, d⟩
    have hs := extendBoundedDemand_support I d.val d.property.2
    have hrec : ∀ (J : Finset L) (hJ : J = I)
        (hD : IsDemand (fun a : J => r a.val)
          (fun a => (extendBoundedDemand I d.val a.val).val))
        (hP : ∀ a : J, 0 < (extendBoundedDemand I d.val a.val).val),
        HEq (⟨fun a => extendBoundedDemand I d.val a.val, hD, hP⟩ :
          PositiveDemand (fun a : J => r a.val)) d := by
      intro J hJ hD hP
      subst J
      apply heq_of_eq
      apply Subtype.ext
      funext a
      exact extendBoundedDemand_mem I d.val a
    apply Sigma.ext hs
    apply hrec _ hs
    · exact restrict_left_isDemand r _
        (fun a => (extendBoundedDemand I d.val a).val) (by
          rw [extendBoundedDemand_val]
          exact extend_left_isDemand r I (fun a => (d.val a).val) d.property.1)
    · intro a
      exact (Finset.mem_filter.mp a.property).2

theorem supportEnumerator_eq_positive_support_sum (r : L → R → Prop) :
    supportEnumerator r = ∑ I : Finset L,
      (Fintype.card (PositiveDemand (fun a : I => r a.val)) : Polynomial ℕ) *
        Polynomial.X ^ I.card := by
  classical
  calc
    _ = ∑ d : demandVectors r,
        (Polynomial.X : Polynomial ℕ) ^ (demandSupport (fun a => (d.val a).val)).card := by
      exact (Finset.sum_coe_sort (demandVectors r)
        (fun d => (Polynomial.X : Polynomial ℕ) ^
          (demandSupport (fun a => (d a).val)).card)).symm
    _ = ∑ q : (Σ I : Finset L, PositiveDemand (fun a : I => r a.val)),
        (Polynomial.X : Polynomial ℕ) ^ q.1.card := by
      apply Fintype.sum_equiv (demandPositiveSupportEquiv r)
      intro d
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem supportEnumerator_coeff_eq_positive_support_sum (r : L → R → Prop) (k : ℕ) :
    (supportEnumerator r).coeff k = ∑ I : Finset L,
      if I.card = k then Fintype.card (PositiveDemand (fun a : I => r a.val)) else 0 := by
  classical
  rw [supportEnumerator_eq_positive_support_sum]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_natCast_mul,
    Polynomial.coeff_X_pow]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp_all

end ResearchMain.PreorderGamma
