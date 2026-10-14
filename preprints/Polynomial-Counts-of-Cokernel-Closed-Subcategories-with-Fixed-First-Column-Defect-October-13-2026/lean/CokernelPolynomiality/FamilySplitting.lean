import CokernelPolynomiality.IndexedFamilies

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def intervalFamilySplitIso (n m a b : ℕ) (c d : Fin m → ℕ)
    (e : Fin a ⊕ Fin b ≃ Fin m) :
    intervalFamily n m c d ≅ directPair
      (intervalFamily n a (fun j => c (e (Sum.inl j))) (fun j => d (e (Sum.inl j))))
      (intervalFamily n b (fun j => c (e (Sum.inr j))) (fun j => d (e (Sum.inr j)))) :=
  indexedFamilyReindex n c d e.symm ≪≫ indexedFamilySum n (c ∘ e) (d ∘ e)

def complementaryIndexEquiv {m : ℕ} (P : Finset (Fin m))
    (eP : Fin P.card ≃ {p // p∈P})
    (eQ : Fin (Finset.univ \ P).card ≃ {p // p∈Finset.univ \ P}) :
    Fin P.card ⊕ Fin (Finset.univ \ P).card ≃ Fin m :=
  (Equiv.sumCongr eP (eQ.trans (Equiv.subtypeEquivRight (by
    intro x; simp)))).trans (Equiv.sumCompl (fun x => x∈P))

def intervalFamilyPartitionIso (n m : ℕ) (c d : Fin m → ℕ) (P : Finset (Fin m))
    (eP : Fin P.card ≃ {p // p∈P})
    (eQ : Fin (Finset.univ \ P).card ≃ {p // p∈Finset.univ \ P}) :
    intervalFamily n m c d ≅ directPair
      (intervalFamily n P.card (fun j => c (eP j).val) (fun j => d (eP j).val))
      (intervalFamily n (Finset.univ \ P).card (fun j => c (eQ j).val) (fun j => d (eQ j).val)) :=
  intervalFamilySplitIso n m _ _ c d (complementaryIndexEquiv P eP eQ)

end CokernelPolynomiality
