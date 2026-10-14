import Dowling.JointDelta

noncomputable section
namespace Dowling
open Finset Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {X : Set (Fin n)}

def allMarkedJointZeroSets (X : Set (Fin n)) (i : Fin n) : Finset (Finset (Fin n)) :=
  univ.powerset.filter (fun Z => i∈Z ∧ ∃ j∈X,j≠i ∧ j∈Z)

theorem allMarkedJointZeroSets_mem (X : Set (Fin n)) (i : Fin n) (Z : Finset (Fin n)) :
    Z∈allMarkedJointZeroSets X i ↔ i∈Z ∧ ∃ j∈X,j≠i ∧ j∈Z := by
  simp [allMarkedJointZeroSets]

theorem markedJointZeroSets_sum {R : Type*} [CommSemiring R]
    (X : Set (Fin n)) (i : Fin n) (f : ℕ→R) :
    (∑ Z∈allMarkedJointZeroSets X i,f Z.card)=
      ∑ r∈range (n+1),(markedJointZeroSets X i r).card*f r := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun Z _ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ Z)))]
  simp only [Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro r hr
  have he : {Z∈allMarkedJointZeroSets X i | Z.card=r}=markedJointZeroSets X i r := by
    ext Z
    simp only [mem_filter,allMarkedJointZeroSets_mem,markedJointZeroSets_mem]
    tauto
  rw [he]
  have ht : ∀ Z∈markedJointZeroSets X i r,f Z.card=f r := fun Z hZ =>
    congrArg f ((markedJointZeroSets_mem X i r Z).mp hZ).1
  rw [Finset.sum_congr rfl ht,Finset.sum_const,nsmul_eq_mul]

theorem jointCorrectionTerm_trivial_pointwise [Subsingleton G]
    (i : Fin n) (hiX : i∈X) (p : Configuration G X) :
    (if IsJointCorrection X i p.val then jointCorrectionTerm i hiX p else 0)=
      if (∀ r : Fin n,(p.val.fiber (some r)).card≤1) ∧
        p.val.fiber none∈allMarkedJointZeroSets X i then
        jointRankCorrection G n (p.val.fiber none).card else 0 := by
  have hc : IsJointCorrection X i p.val ↔
      p.val.code i=none ∧ ∃ j∈X,j≠i ∧ p.val.code j=none :=
    joint_correction_flats_trivial X p.val i hiX
  have hm : p.val.fiber none∈allMarkedJointZeroSets X i ↔ IsJointCorrection X i p.val := by
    simp only [allMarkedJointZeroSets_mem,mem_zero_fiber,hc]
  simp only [hm]
  by_cases hp : IsJointCorrection X i p.val
  · obtain ⟨hi,j,hjX,hji,hj⟩ := hc.mp hp
    by_cases hs : ∀ r : Fin n,(p.val.fiber (some r)).card≤1
    · rw [ite_eq_left hp,ite_eq_left ⟨hs,hp⟩]
      exact jointCorrectionTerm_singleton i hiX p hi hs
    · have hb : ∃ r : Fin n,2≤(p.val.fiber (some r)).card := by
        by_contra h
        apply hs
        intro r
        have : ¬2≤(p.val.fiber (some r)).card := fun hr => h ⟨r,hr⟩
        omega
      rw [ite_eq_left hp,ite_eq_right (fun h => hs h.1)]
      exact jointCorrectionTerm_nonsingleton i hiX p hi
        (zero_fiber_card_two p.val i hi ⟨j,hji,hj⟩) hb
  · simp [hp]

theorem joint_correction_sum_trivial [Subsingleton G] (i : Fin n) (hiX : i∈X) :
    (∑ p : Configuration G X,if IsJointCorrection X i p.val then jointCorrectionTerm i hiX p else 0)=
      ∑ r∈range (n+1),(markedJointZeroSets X i r).card*jointRankCorrection G n r := by
  simp_rw [jointCorrectionTerm_trivial_pointwise i hiX]
  rw [configuration_singleton_sum i hiX _
    (fun Z hZ => ((allMarkedJointZeroSets_mem X i Z).mp hZ).1)
    (fun Z => jointRankCorrection G n Z.card)]
  exact markedJointZeroSets_sum X i _

end Dowling
