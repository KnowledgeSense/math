import MainTheorems.PreorderGamma.Macaulay.MatchingExchange
import Mathlib.Data.Finset.Max

namespace ResearchMain.PreorderGamma.Macaulay

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def IsCanonicalMatching (M : Finset (E × E)) : Prop :=
  IsOrderMatching M ∧ ∀ N, IsOrderMatching N →
    leftSupport N = leftSupport M → rightSupport N = rightSupport M →
      binaryCode M ≤ binaryCode N

theorem canonical_matching_unique {M N : Finset (E × E)}
    (hM : IsCanonicalMatching M) (hN : IsCanonicalMatching N)
    (hl : leftSupport M = leftSupport N) (hr : rightSupport M = rightSupport N) : M = N := by
  apply binaryCode_injective
  exact Nat.le_antisymm (hM.2 N hN.1 hl.symm hr.symm) (hN.2 M hM.1 hl hr)

theorem exists_canonical_matching {S T : Finset E} (h : IsMatchedPair S T) :
    ∃ M : Finset (E × E), IsCanonicalMatching M ∧ leftSupport M = S ∧ rightSupport M = T := by
  classical
  let candidates : Finset (Finset (E × E)) := Finset.univ.filter fun M =>
    IsOrderMatching M ∧ leftSupport M = S ∧ rightSupport M = T
  have hc : candidates.Nonempty := by
    obtain ⟨M, hM, hl, hr⟩ := exists_orderMatching h
    exact ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM, hl, hr⟩⟩
  obtain ⟨M, hm, hmin⟩ := Finset.exists_min_image candidates binaryCode hc
  have hM : IsOrderMatching M ∧ leftSupport M = S ∧ rightSupport M = T :=
    (Finset.mem_filter.mp hm).2
  refine ⟨M, ⟨hM.1, ?_⟩, hM.2.1, hM.2.2⟩
  intro N hN hl hr
  apply hmin N
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hN, hl.trans hM.2.1, hr.trans hM.2.2⟩

theorem canonical_matching_subset {M N : Finset (E × E)}
    (hM : IsCanonicalMatching M) (hNM : N ⊆ M) : IsCanonicalMatching N := by
  refine ⟨hM.1.subset hNM, ?_⟩
  intro T hT hl hr
  let R := M \ N
  have hu : IsOrderMatching (T ∪ R) := hM.1.replace hNM hT hl hr
  have hs := replacement_supports hM.1 hNM hl hr
  have hmin := hM.2 (T ∪ R) hu hs.1 hs.2
  have hd : Disjoint T R := by
    apply disjoint_of_leftSupport
    rw [hl, hM.1.leftSupport_sdiff hNM]
    exact disjoint_sdiff_self_right
  have hc := binaryCode_sdiff_add hNM
  rw [binaryCode_union T R hd] at hmin
  change binaryCode R + binaryCode N = binaryCode M at hc
  omega

theorem canonical_matching_empty : IsCanonicalMatching (∅ : Finset (E × E)) := by
  refine ⟨⟨by simp, by simp [Set.InjOn], by simp [Set.InjOn], ?_⟩, ?_⟩
  · simp [leftSupport, rightSupport]
  · intro N _ _ _
    simp [binaryCode]

noncomputable def canonicalMatchings (k : ℕ) : Finset (Finset (E × E)) := by
  classical
  exact Finset.univ.filter fun M => IsCanonicalMatching M ∧ M.card = k

@[simp] theorem mem_canonicalMatchings {k : ℕ} {M : Finset (E × E)} :
    M ∈ canonicalMatchings k ↔ IsCanonicalMatching M ∧ M.card = k := by
  classical
  simp [canonicalMatchings]

theorem canonicalMatchings_card (k : ℕ) :
    (canonicalMatchings (E := E) k).card = gammaCoefficient (E := E) k := by
  classical
  unfold gammaCoefficient
  apply Finset.card_bij (fun M _ => (leftSupport M, rightSupport M))
  · intro M hm
    obtain ⟨hM, hk⟩ := mem_canonicalMatchings.mp hm
    exact mem_matchedPairs.mpr
      ⟨hM.1.card_leftSupport.trans hk, hM.1.card_rightSupport.trans hk, hM.1.matchedPair⟩
  · intro M hm N hn he
    exact canonical_matching_unique (mem_canonicalMatchings.mp hm).1
      (mem_canonicalMatchings.mp hn).1 (congrArg Prod.fst he) (congrArg Prod.snd he)
  · intro p hp
    obtain ⟨hs, _, hpair⟩ := mem_matchedPairs.mp hp
    obtain ⟨M, hM, hl, hr⟩ := exists_canonical_matching hpair
    refine ⟨M, mem_canonicalMatchings.mpr ⟨hM, ?_⟩, Prod.ext hl hr⟩
    rw [← hM.1.card_leftSupport, hl, hs]

end ResearchMain.PreorderGamma.Macaulay
