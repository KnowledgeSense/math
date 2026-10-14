import Dowling.JointCorrectionTerms
import Dowling.JointNoncoloop
import Dowling.DeletionIncidenceMatroid

noncomputable section
namespace Dowling
open Polynomial MatroidInverseZ Finset
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {X : Set (Fin n)}

theorem configuration_actual_kl (p q : Configuration G X) :
    kl (flatRank (matroid G n X)) (configurationOrderIso X q) (configurationOrderIso X p)=
      kl (configurationRank X) q p := by
  let e := configurationOrderIso (G := G) X
  exact kl_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
    (configurationRank X) (flatRank (matroid G n X))
    (fun a b => by
      change flatRank (matroid G n X) (configurationOrderIso X b)-
        flatRank (matroid G n X) (configurationOrderIso X a)=_
      rw [configurationOrderIso_rank,configurationOrderIso_rank]) p q

theorem configuration_actual_tau (p q : Configuration G X) :
    deletionTau (flatRank (matroid G n X)) (configurationOrderIso X p) (configurationOrderIso X q)=
      deletionTau (configurationRank X) p q := by
  simp only [deletionTau,(configurationOrderIso X).le_iff_le,configurationOrderIso_rank,
    configuration_actual_kl]

theorem configuration_actual_upperY (p : Configuration G X) :
    inverseZ (flatRank (matroid G n X)) (configurationOrderIso X p) (topFlat (matroid G n X))=
      inverseZ (configurationRank X) p ⊤ := by
  let e := configurationOrderIso (G := G) X
  have h := inverseZ_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
    (configurationRank X) (flatRank (matroid G n X))
    (fun a b => by
      change flatRank (matroid G n X) (configurationOrderIso X b)-
        flatRank (matroid G n X) (configurationOrderIso X a)=_
      rw [configurationOrderIso_rank,configurationOrderIso_rank]) p ⊤
  change inverseZ (flatRank (matroid G n X)) (configurationOrderIso X p)
    (configurationOrderIso X ⊤)=_ at h
  rw [configurationOrderIso_top] at h
  exact h

theorem configurationOrderIso_joint (i : Fin n) (hiX : i∈X) :
    configurationOrderIso X (jointConfiguration (G := G) i hiX)=
      deletionSingletonFlat (matroid G n X) (Sum.inl i) (joint_isFlat i hiX) := by
  apply Subtype.ext
  exact flatEdges_jointPartition i hiX

/-- Actual correction flats, retaining all outside balanced blocks. -/
def IsJointCorrection (X : Set (Fin n)) (i : Fin n) (p : GainPartition G n) : Prop :=
  Sum.inl i∈flatEdges X p ∧ ¬(matroid G n X).IsFlat (flatEdges X p\{Sum.inl i})

/-- The proved general finite-matroid deletion identity specialized to the
literal retained-joint matroid and its actual configuration intervals. -/
theorem joint_deletion_identity (i : Fin n) (hiX : i∈X)
    (hc : ¬(matroid G n X).IsColoop (Sum.inl i)) :
    configurationY (G := G) X=configurationY (G := G) (X\{i})+
      (1+Polynomial.X)*fullY G (n-1)-
      ∑ p : Configuration G X, if IsJointCorrection X i p.val then jointCorrectionTerm i hiX p else 0 := by
  have h := matroid_inverseZ_deletion (matroid G n X) (Sum.inl i)
    (matroid_empty_isFlat X) (joint_isFlat i hiX) hc
  rw [matroid_delete_joint,actual_inverseZ_eq_configurationY,actual_inverseZ_eq_configurationY,
    ← configurationOrderIso_joint i hiX,configuration_actual_upperY,joint_upper_inverseZ] at h
  rw [Finset.sum_filter] at h
  let e := configurationOrderIso (G := G) X
  rw [← e.toEquiv.sum_comp] at h
  convert h using 2
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : IsJointCorrection X i p.val
  · have hc' : Sum.inl i∈(e.toEquiv p).val ∧
        ¬(matroid G n X).IsFlat ((e.toEquiv p).val\{Sum.inl i}) := hc
    rw [ite_eq_left hc,ite_eq_left hc']
    change jointCorrectionTerm i hiX p=
      C (deletionTau (flatRank (matroid G n X)) (configurationOrderIso X (jointConfiguration i hiX))
        (configurationOrderIso X p))*Polynomial.X^(flatRank (matroid G n X) (configurationOrderIso X p)/2)*
        inverseZ (flatRank (matroid G n X)) (configurationOrderIso X p) (topFlat (matroid G n X))
    rw [configuration_actual_tau,configurationOrderIso_rank,configuration_actual_upperY]
    rfl
  · have hc' : ¬(Sum.inl i∈(e.toEquiv p).val ∧
        ¬(matroid G n X).IsFlat ((e.toEquiv p).val\{Sum.inl i})) := hc
    rw [ite_eq_right hc,ite_eq_right hc']

end Dowling
