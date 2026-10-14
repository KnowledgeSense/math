import FourGeneratedSemigroups.SingleBinomialReduction
import FourGeneratedSemigroups.StaircaseFiniteness
import FourGeneratedSemigroups.FinitePresentation

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

/-- The boundary relations and one critical relation normalize factorizations
either into the Apéry staircase or into a factorization using generator zero. -/
theorem boundary_congruence_normalize (C : AddCon Factorization)
    (p : Factorization) (hp3 : p 3=0) (htop : C (topPower G) p)
    (hboundary : ∀ h∈staircaseBoundary G,h 0=0 → h≠topPower G →
      ∃ c,C h c ∧ 0<c 0) (a : Factorization) :
    ∃ b,C a b ∧ (b∈staircase G ∨ 0<b 0) := by
  have hall : ∀ n,∀ a : Factorization,a 3=n →
      ∃ b,C a b ∧ (b∈staircase G ∨ 0<b 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha3
      by_cases ha0 : 0<a 0
      · exact ⟨a,C.refl a,Or.inr ha0⟩
      by_cases haT : a∈staircase G
      · exact ⟨a,C.refl a,Or.inl haT⟩
      by_cases hcut : a 3<criticalExponent G.generators G.positive 3
      · obtain ⟨h,hh,hha⟩ := exists_boundary_le G a haT
        have hh0 : h 0=0 := by have := hha 0; omega
        have hne : h≠topPower G := by
          intro he
          have hx := hha 3
          simp [he,topPower] at hx
          omega
        obtain ⟨c,hc,hc0⟩ := hboundary h hh hh0 hne
        obtain ⟨r,hr⟩ := le_iff_exists_add.mp hha
        refine ⟨c+r,?_,Or.inr ?_⟩
        · rw [hr]; exact C.add hc (C.refl r)
        · simp only [Finsupp.add_apply]; omega
      · have hle : topPower G≤a := Finsupp.single_le_iff.mpr (Nat.le_of_not_gt hcut)
        obtain ⟨r,hr⟩ := le_iff_exists_add.mp hle
        have hsmall : (p+r) 3<n := by
          have hh : a 3=criticalExponent G.generators G.positive 3+r 3 := by simp [hr,topPower]
          have hpos := (criticalExponent_spec G.generators G.positive 3).1
          simp only [Finsupp.add_apply,hp3,zero_add]
          omega
        obtain ⟨b,hb,hbT⟩ := ih ((p+r) 3) hsmall (p+r) rfl
        refine ⟨b,?_,hbT⟩
        have hc : C a (p+r) := by rw [hr]; exact C.add htop (C.refl r)
        exact C.trans hc hb
  exact hall (a 3) a rfl

/-- The normalization relations generate the entire genuine factorization congruence. -/
theorem boundary_congruence_eq_factorization (C : AddCon Factorization)
    (hC : C≤factorizationCongruence G.generators)
    (p : Factorization) (hp3 : p 3=0) (htop : C (topPower G) p)
    (hboundary : ∀ h∈staircaseBoundary G,h 0=0 → h≠topPower G →
      ∃ c,C h c ∧ 0<c 0)
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) :
    C=factorizationCongruence G.generators := by
  apply le_antisymm hC
  have hall : ∀ n,∀ a b : Factorization,factorizationMap G.generators a=n →
      factorizationMap G.generators b=n → C a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b ha hb
      obtain ⟨a',haa',ha'T⟩ := boundary_congruence_normalize G C p hp3 htop hboundary a
      obtain ⟨b',hbb',hb'T⟩ := boundary_congruence_normalize G C p hp3 htop hboundary b
      have hwa : factorizationMap G.generators a'=n := (hC haa').symm.trans ha
      have hwb : factorizationMap G.generators b'=n := (hC hbb').symm.trans hb
      suffices C a' b' from C.trans haa' (C.trans this (C.symm hbb'))
      by_cases hnA : (n : ℤ)∈S.apery (G.generators 0)
      · have ha'T' : a'∈staircase G := by
          rcases ha'T with ht|hpos
          · exact ht
          · have hz := G.factorization_coordinate_zero_of_apery 0 a' (by simpa [hwa] using hnA)
            omega
        have hb'T' : b'∈staircase G := by
          rcases hb'T with ht|hpos
          · exact ht
          · have hz := G.factorization_coordinate_zero_of_apery 0 b' (by simpa [hwb] using hnA)
            omega
        have he := hinj ha'T' hb'T' (by simp [hwa,hwb])
        rw [he]
        exact C.refl b'
      · have hpa : 0<a' 0 := ha'T.resolve_left (fun ht => hnA (hwa ▸ ht.2.2))
        have hpb : 0<b' 0 := hb'T.resolve_left (fun ht => hnA (hwb ▸ ht.2.2))
        have hlea : Finsupp.single 0 1≤a' := Finsupp.single_le_iff.mpr hpa
        have hleb : Finsupp.single 0 1≤b' := Finsupp.single_le_iff.mpr hpb
        obtain ⟨ar,har⟩ := le_iff_exists_add.mp hlea
        obtain ⟨br,hbr⟩ := le_iff_exists_add.mp hleb
        have hwar : G.generators 0+factorizationMap G.generators ar=n := by simpa [har] using hwa
        have hwbr : G.generators 0+factorizationMap G.generators br=n := by simpa [hbr] using hwb
        have hsmall : factorizationMap G.generators ar<n := by have := G.positive 0; omega
        have hrest := ih (factorizationMap G.generators ar) hsmall ar br rfl (by omega)
        rw [har,hbr]
        exact C.add (C.refl (Finsupp.single 0 1)) hrest
  intro a b hab
  exact hall (factorizationMap G.generators a) a b rfl hab.symm

end FourGeneratedSemigroups
