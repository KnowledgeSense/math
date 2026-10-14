import Dowling.ZeroSetCounting
import Dowling.JointDeletionFlats
import Dowling.JointDeletionTrivialFlats

noncomputable section
namespace Dowling
open Finset
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem zeroSetPartition_injective : Function.Injective (zeroSetPartition (G := G) (n := n)) := by
  intro Z W h
  simpa only [zeroSetPartition_zero_fiber] using congrArg (fun p => p.fiber none) h

/-- A literal image, with no gain-label multiplicity left after tau vanishing. -/
def zeroSetSurvivors (A : Finset (Finset (Fin n))) : Finset (GainPartition G n) :=
  A.image zeroSetPartition

theorem zeroSetSurvivors_mem (A : Finset (Finset (Fin n))) (p : GainPartition G n) :
    p∈zeroSetSurvivors (G := G) A ↔
      (∀ r : Fin n, (p.fiber (some r)).card≤1) ∧ p.fiber none∈A := by
  constructor
  · intro h
    obtain ⟨Z,hZ,rfl⟩ := mem_image.mp h
    exact ⟨zeroSetPartition_singletons Z,by simpa only [zeroSetPartition_zero_fiber] using hZ⟩
  · rintro ⟨hs,hZ⟩
    exact mem_image.mpr ⟨p.fiber none,hZ,(eq_zeroSetPartition_of_singletons p hs).symm⟩

theorem zeroSetSurvivors_card (A : Finset (Finset (Fin n))) :
    (zeroSetSurvivors (G := G) A).card=A.card :=
  card_image_of_injective _ zeroSetPartition_injective

theorem jointSurvivors_mem (i : Fin n) (r : ℕ) (p : GainPartition G n) :
    p∈zeroSetSurvivors (G := G) (jointZeroSets i r) ↔
      p.code i=none ∧ partitionRank p=r ∧ ∀ j : Fin n, (p.fiber (some j)).card≤1 := by
  rw [zeroSetSurvivors_mem,jointZeroSets_mem,mem_zero_fiber]
  constructor
  · rintro ⟨hs,hr,hi⟩
    exact ⟨hi,(partitionRank_singleton_outside p hs).trans hr,hs⟩
  · rintro ⟨hi,hr,hs⟩
    exact ⟨hs,⟨(partitionRank_singleton_outside p hs).symm.trans hr,hi⟩⟩

theorem jointSurvivors_card (i : Fin n) (r : ℕ) (hr : 1≤r) :
    (zeroSetSurvivors (G := G) (jointZeroSets i r)).card=(n-1).choose (r-1) := by
  rw [zeroSetSurvivors_card,jointZeroSets_card i r hr]

theorem markedJointSurvivors_mem (X : Set (Fin n)) (i : Fin n) (r : ℕ) (p : GainPartition G n) :
    p∈zeroSetSurvivors (G := G) (markedJointZeroSets X i r) ↔
      p.code i=none ∧ partitionRank p=r ∧
      (∀ j : Fin n, (p.fiber (some j)).card≤1) ∧ ∃ j∈X, j≠i ∧ p.code j=none := by
  rw [zeroSetSurvivors_mem,markedJointZeroSets_mem]
  simp only [mem_zero_fiber]
  constructor
  · rintro ⟨hs,hr,hi,hj⟩
    exact ⟨hi,(partitionRank_singleton_outside p hs).trans hr,hs,hj⟩
  · rintro ⟨hi,hr,hs,hj⟩
    exact ⟨hs,(partitionRank_singleton_outside p hs).symm.trans hr,hi,hj⟩

theorem markedJointSurvivors_card (X : Set (Fin n)) (i : Fin n) (hiX : i∈X)
    (r : ℕ) (hr : 1≤r) :
    (zeroSetSurvivors (G := G) (markedJointZeroSets X i r)).card=
      (n-1).choose (r-1)-(n-X.toFinset.card).choose (r-1) := by
  rw [zeroSetSurvivors_card,markedJointZeroSets_card X i hiX r hr]

/-- Every survivor is an actual retained-joint flat, since it contains the
chosen retained zero vertex. -/
theorem jointSurvivor_admissible (X : Set (Fin n)) (i : Fin n) (hiX : i∈X)
    (r : ℕ) (p : GainPartition G n) (hp : p∈zeroSetSurvivors (G := G) (jointZeroSets i r)) :
    Admissible X p := by
  have hi := (jointSurvivors_mem i r p).mp hp
  intro j _
  exact Or.inl ⟨i,hiX,hi.1⟩

end Dowling
