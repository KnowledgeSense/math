import Dowling.JointDeletionIdentity
import Dowling.JointSurvivorSums

noncomputable section
namespace Dowling
open Finset Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {X : Set (Fin n)}

omit [Fintype G] in
theorem zero_fiber_card_two (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (hj : ∃ j,j≠i ∧ p.code j=none) : 2≤(p.fiber none).card := by
  obtain ⟨j,hji,hj⟩ := hj
  apply Finset.one_lt_card.mpr
  exact ⟨i,(mem_zero_fiber p i).mpr hi,j,(mem_zero_fiber p j).mpr hj,Ne.symm hji⟩

omit [Fintype G] in
theorem zero_fiber_singleton (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (hj : ¬∃ j,j≠i ∧ p.code j=none) : p.fiber none={i} := by
  ext j
  rw [mem_zero_fiber,Finset.mem_singleton]
  constructor
  · intro hz
    by_contra hji
    exact hj ⟨j,hji,hz⟩
  · rintro rfl
    exact hi

theorem jointCorrectionTerm_nontrivial_pointwise [Nontrivial G]
    (i : Fin n) (hiX : i∈X) (p : Configuration G X) :
    (if IsJointCorrection X i p.val then jointCorrectionTerm i hiX p else 0)=
      if (∀ r : Fin n,(p.val.fiber (some r)).card≤1) ∧
        p.val.fiber none∈univ.powerset.filter (i∈·) then
        jointRankCorrection G n (p.val.fiber none).card else 0 := by
  have hc : IsJointCorrection X i p.val ↔ p.val.code i=none ∧ ∃ j,j≠i ∧ p.val.code j=none :=
    joint_correction_flats_nontrivial X p.val i hiX
  have hm : p.val.fiber none∈univ.powerset.filter (i∈·) ↔ p.val.code i=none := by
    simp [mem_zero_fiber]
  simp only [hc,hm]
  by_cases hi : p.val.code i=none
  · by_cases hj : ∃ j,j≠i ∧ p.val.code j=none
    · by_cases hs : ∀ r : Fin n,(p.val.fiber (some r)).card≤1
      · rw [ite_eq_left ⟨hi,hj⟩,ite_eq_left ⟨hs,hi⟩]
        exact jointCorrectionTerm_singleton i hiX p hi hs
      · have hb : ∃ r : Fin n,2≤(p.val.fiber (some r)).card := by
          by_contra h
          apply hs
          intro r
          have : ¬2≤(p.val.fiber (some r)).card := fun hr => h ⟨r,hr⟩
          omega
        rw [ite_eq_left ⟨hi,hj⟩,ite_eq_right (fun h => hs h.1)]
        exact jointCorrectionTerm_nonsingleton i hiX p hi (zero_fiber_card_two p.val i hi hj) hb
    · have hz := zero_fiber_singleton p.val i hi hj
      simp [hi,hj,hz,jointRankCorrection]
  · simp [hi]

theorem joint_correction_sum_nontrivial [Nontrivial G] (i : Fin n) (hiX : i∈X) :
    (∑ p : Configuration G X,if IsJointCorrection X i p.val then jointCorrectionTerm i hiX p else 0)=
      ∑ r∈range (n+1),(jointZeroSets i r).card*jointRankCorrection G n r := by
  simp_rw [jointCorrectionTerm_nontrivial_pointwise i hiX]
  rw [configuration_singleton_sum i hiX _ (fun Z hZ => (Finset.mem_filter.mp hZ).2)
    (fun Z => jointRankCorrection G n Z.card)]
  exact jointZeroSets_sum i _

end Dowling
