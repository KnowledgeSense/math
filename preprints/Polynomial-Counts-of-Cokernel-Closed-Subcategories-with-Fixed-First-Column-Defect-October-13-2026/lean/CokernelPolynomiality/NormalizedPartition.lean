import CokernelPolynomiality.FamilyNormalization
import CokernelPolynomiality.FamilyPartitionMaps
import CokernelPolynomiality.OrderedFamilyCokernel

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

theorem familyNormalization_partition {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (hab : a ≤ b) (hbn : b ≤ n)
    (R : EndpointReduction m (familyActive f) c d)
    (eQ : Fin (Finset.univ \ R.P).card ≃ {p // p∈Finset.univ \ R.P})
    (hac : ∀ j, a ≤ c (R.enumeration j).val)
    (hbd : ∀ j, b ≤ d (R.enumeration j).val) :
    f ≫ (familyNormalization f hab hbn R).hom ≫
      (intervalFamilyPartitionIso n m c d R.P R.enumeration eQ).hom=
    directPairLift
      (orderedFamilySource n a b (fun j => c (R.enumeration j).val)
        (fun j => d (R.enumeration j).val) hac hbd) 0 := by
  apply directPair_hom_ext
  · rw [directPairLift_fst]
    apply intervalFamily_hom_ext
    intro j
    simp only [Category.assoc,intervalFamilyPartition_fst,orderedFamilySource,intervalFamilyLift_proj]
    exact familyNormalization_pivot f hab hbn R _ (R.enumeration j).property (hac j) (hbd j)
  · rw [directPairLift_snd]
    apply intervalFamily_hom_ext
    intro j
    simp only [Category.assoc,intervalFamilyPartition_snd,zero_comp]
    exact familyNormalization_nonpivot f hab hbn R _ (Finset.mem_sdiff.mp (eQ j).property).2

end CokernelPolynomiality
