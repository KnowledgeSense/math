import CokernelPolynomiality.FamilySplitting
import CokernelPolynomiality.FamilyMatrix

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

theorem directPair_hom_ext {n : ℕ} {X V W : ChainRep n} {f g : X ⟶ directPair V W}
    (hV : f ≫ directPairFst V W=g ≫ directPairFst V W)
    (hW : f ≫ directPairSnd V W=g ≫ directPairSnd V W) : f=g := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun h => (h.app i).hom.hom x) hV
  · exact congrArg (fun h => (h.app i).hom.hom x) hW

@[simp] theorem directPairLift_fst {n : ℕ} {X V W : ChainRep n} (f : X ⟶ V) (g : X ⟶ W) :
    directPairLift f g ≫ directPairFst V W=f := rfl
@[simp] theorem directPairLift_snd {n : ℕ} {X V W : ChainRep n} (f : X ⟶ V) (g : X ⟶ W) :
    directPairLift f g ≫ directPairSnd V W=g := rfl

theorem intervalFamilyPartition_fst (n m : ℕ) (c d : Fin m → ℕ) (P : Finset (Fin m))
    (eP : Fin P.card ≃ {p // p∈P})
    (eQ : Fin (Finset.univ \ P).card ≃ {p // p∈Finset.univ \ P}) (j : Fin P.card) :
    (intervalFamilyPartitionIso n m c d P eP eQ).hom ≫ directPairFst _ _ ≫
      intervalFamilyProj n P.card (fun k => c (eP k).val) (fun k => d (eP k).val) j=
        intervalFamilyProj n m c d (eP j).val := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem intervalFamilyPartition_snd (n m : ℕ) (c d : Fin m → ℕ) (P : Finset (Fin m))
    (eP : Fin P.card ≃ {p // p∈P})
    (eQ : Fin (Finset.univ \ P).card ≃ {p // p∈Finset.univ \ P})
    (j : Fin (Finset.univ \ P).card) :
    (intervalFamilyPartitionIso n m c d P eP eQ).hom ≫ directPairSnd _ _ ≫
      intervalFamilyProj n (Finset.univ \ P).card (fun k => c (eQ k).val) (fun k => d (eQ k).val) j=
        intervalFamilyProj n m c d (eQ j).val := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end CokernelPolynomiality
