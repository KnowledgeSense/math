import SumsetRanges.OrdinaryLiftedBlocks

open Finset
namespace SumsetRanges

abbrev OrdinaryRelationAtom (r u : ℕ → ℕ) : ℕ → Type
  | 0 => Fin 0
  | n+1 => (Fin (r (n+2)) ⊕ Fin (u (n+2))) ⊕ OrdinaryRelationAtom r u n

abbrev OrdinaryRelationTag : ℕ → Type
  | 0 => Fin 0
  | n+1 => (Fin 1 ⊕ Fin 1) ⊕ OrdinaryRelationTag n

instance ordinaryRelationAtomFintype (r u : ℕ → ℕ) : (n : ℕ) → Fintype (OrdinaryRelationAtom r u n)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | n+1 => @instFintypeSum _ _ inferInstance (ordinaryRelationAtomFintype r u n)

instance ordinaryRelationTagFintype : (n : ℕ) → Fintype (OrdinaryRelationTag n)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | n+1 => @instFintypeSum _ _ inferInstance (ordinaryRelationTagFintype n)

noncomputable def ordinaryRelationBlocks (r u : ℕ → ℕ) : (n : ℕ) →
    Finset (OrdinarySpace (OrdinaryRelationAtom r u n) (OrdinaryRelationTag n))
  | 0 => ∅
  | n+1 => mixedJoin (ordinaryPair (n+2) (r (n+2)) (u (n+2))) (ordinaryRelationBlocks r u n)

theorem MixedBound.mono {ι τ : Type*} [Fintype ι] [Fintype τ] {H K : ℕ}
    {a : OrdinarySpace ι τ} (ha : MixedBound H a) (hHK : H≤K) : MixedBound K a :=
  ⟨ha.1.trans hHK,ha.2⟩

theorem ordinaryRelationBlocks_bound (r u : ℕ → ℕ) (n : ℕ) :
    ∀a∈ordinaryRelationBlocks r u n,MixedBound (n+2) a := by
  induction n with
  | zero => simp [ordinaryRelationBlocks]
  | succ n ih =>
      apply mixedJoin_bound
      · exact ordinaryPair_bound _ _ _ (by omega)
      · intro a ha
        exact (ih a ha).mono (by omega)

theorem ordinaryRelationBlocks_degree (r u : ℕ → ℕ) (n : ℕ) :
    ∀a∈ordinaryRelationBlocks r u n,mixedDegree _ _ a=1 :=
  fun a ha => (ordinaryRelationBlocks_bound r u n a ha).2.2

theorem card_ordinaryRelationBlocks (r u : ℕ → ℕ) (n : ℕ) :
    (ordinaryRelationBlocks r u n).card=∑j∈range n,(2*r (j+2)+1+2*u (j+2)) := by
  induction n with
  | zero => simp [ordinaryRelationBlocks]
  | succ n ih =>
      rw [ordinaryRelationBlocks,card_mixedJoin _ _ (fun a ha => (ordinaryPair_bound _ _ _ (by omega) a ha).2.2),
        card_ordinaryPair _ _ _ (by omega),ih,Finset.sum_range_succ]
      omega

theorem ordinarySeries_relationBlocks (r u : ℕ → ℕ) (n : ℕ) :
    ordinarySeries (ordinaryRelationBlocks r u n)=∏j∈range n,
      ordinarySeries (carryG (j+3) (r (j+2)))*ordinarySeries (carryH (j+2) (u (j+2))) := by
  induction n with
  | zero => simp [ordinaryRelationBlocks,ordinarySeries_empty_generic]
  | succ n ih =>
      rw [ordinaryRelationBlocks,ordinarySeries_mixedJoin _ _ (fun a ha => (ordinaryPair_bound _ _ _ (by omega) a ha).2.2),
        ordinarySeries_ordinaryPair,ih,Finset.prod_range_succ]
      ring

theorem ordinaryRelationAtom_card (r u : ℕ → ℕ) (n : ℕ) :
    Fintype.card (OrdinaryRelationAtom r u n)≤(ordinaryRelationBlocks r u n).card := by
  induction n with
  | zero => simp [OrdinaryRelationAtom,ordinaryRelationBlocks]
  | succ n ih =>
      change Fintype.card ((Fin (r (n+2)) ⊕ Fin (u (n+2))) ⊕ OrdinaryRelationAtom r u n)≤_
      rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,Fintype.card_fin,ordinaryRelationBlocks,
        card_mixedJoin _ _ (fun a ha => (ordinaryPair_bound _ _ _ (by omega) a ha).2.2),
        card_ordinaryPair _ _ _ (by omega)]
      omega

theorem ordinaryRelationTag_card (n : ℕ) : Fintype.card (OrdinaryRelationTag n)=2*n := by
  induction n with
  | zero => simp [OrdinaryRelationTag]
  | succ n ih =>
      change Fintype.card ((Fin 1 ⊕ Fin 1) ⊕ OrdinaryRelationTag n)=_
      rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,ih]
      omega

end SumsetRanges
