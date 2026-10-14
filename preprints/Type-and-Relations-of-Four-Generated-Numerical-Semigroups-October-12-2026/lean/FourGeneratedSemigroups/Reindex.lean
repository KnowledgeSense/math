import FourGeneratedSemigroups.BoundaryPresentation

noncomputable section
namespace FourGeneratedSemigroups

@[simp] lemma domCongr_inverse (e : Equiv.Perm (Fin 4)) (a : Factorization) :
    Finsupp.domCongr e (Finsupp.domCongr e.symm a)=a := by
  ext i; simp [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply]

@[simp] lemma domCongr_inverse_left (e : Equiv.Perm (Fin 4)) (a : Factorization) :
    Finsupp.domCongr e.symm (Finsupp.domCongr e a)=a := by
  ext i; simp [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply]

lemma factorizationMap_reindex (d : Fin 4 → ℕ) (e : Equiv.Perm (Fin 4)) (a : Factorization) :
    factorizationMap d (Finsupp.domCongr e a)=factorizationMap (d ∘ e) a := by
  simpa [factorizationMap,Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply,Function.comp_def] using
    (Equiv.sum_comp e (fun j => (Finsupp.domCongr e a) j*d j)).symm

namespace FourGenerated
variable {S : NumericalSemigroup} (G : FourGenerated S)

/-- Relabel the specified four minimal generators by a permutation. -/
def reindex (e : Equiv.Perm (Fin 4)) : FourGenerated S where
  generators := G.generators ∘ e
  positive i := G.positive (e i)
  generates n := by
    constructor
    · intro hn
      obtain ⟨a,ha⟩ := (G.generates n).mp hn
      refine ⟨Finsupp.domCongr e.symm a,?_⟩
      rw [←factorizationMap_reindex]
      simpa only [domCongr_inverse] using ha
    · rintro ⟨a,ha⟩
      exact (G.generates n).mpr ⟨Finsupp.domCongr e a,by rwa [factorizationMap_reindex]⟩
  minimal i := by
    rintro ⟨a,hai,ha⟩
    apply G.minimal (e i)
    refine ⟨Finsupp.domCongr e a,?_,?_⟩
    · simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using hai
    · rwa [factorizationMap_reindex]

end FourGenerated

lemma criticalRelation_reindex (d : Fin 4 → ℕ) (e : Equiv.Perm (Fin 4))
    (i : Fin 4) (q : ℕ) :
    CriticalRelation (d ∘ e) i q ↔ CriticalRelation d (e i) q := by
  constructor
  · rintro ⟨hq,a,hai,ha⟩
    refine ⟨hq,Finsupp.domCongr e a,?_,?_⟩
    · simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using hai
    · rwa [factorizationMap_reindex]
  · rintro ⟨hq,a,hai,ha⟩
    refine ⟨hq,Finsupp.domCongr e.symm a,?_,?_⟩
    · simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using hai
    · have hh := factorizationMap_reindex d e (Finsupp.domCongr e.symm a)
      rw [domCongr_inverse] at hh
      exact hh.symm.trans ha

theorem criticalExponent_reindex (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    criticalExponent (d ∘ e) (fun i => hd (e i)) i=criticalExponent d hd (e i) := by
  apply le_antisymm
  · apply criticalExponent_le
    exact (criticalRelation_reindex d e i _).mpr (criticalExponent_spec d hd (e i))
  · apply criticalExponent_le
    exact (criticalRelation_reindex d e i _).mp (criticalExponent_spec (d ∘ e) _ i)

theorem criticalArc_reindex (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    CriticalArc (d ∘ e) (fun i => hd (e i)) i j ↔ CriticalArc d hd (e i) (e j) := by
  constructor
  · rintro ⟨hij,a,hai,haj,ha⟩
    refine ⟨fun he => hij (e.injective he),Finsupp.domCongr e a,?_,?_,?_⟩
    · simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using hai
    · simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using haj
    · rw [factorizationMap_reindex]
      simpa only [criticalExponent_reindex,Function.comp_apply] using ha
  · rintro ⟨hij,a,hai,haj,ha⟩
    refine ⟨fun he => hij (congrArg e he),Finsupp.domCongr e.symm a,?_,?_,?_⟩
    · simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using hai
    · simpa [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using haj
    · have hh := factorizationMap_reindex d e (Finsupp.domCongr e.symm a)
      rw [domCongr_inverse] at hh
      rw [criticalExponent_reindex]
      exact hh.symm.trans ha


noncomputable def reindexRelations (e : Equiv.Perm (Fin 4))
    (R : Finset (Factorization × Factorization)) : Finset (Factorization × Factorization) := by
  classical
  exact R.image (fun ab => (Finsupp.domCongr e.symm ab.1,Finsupp.domCongr e.symm ab.2))

lemma generatedRelation_reindex (e : Equiv.Perm (Fin 4))
    (R : Finset (Factorization × Factorization)) {a b : Factorization}
    (h : addConGen (fun a b => (a,b)∈R) a b) :
    addConGen (fun a b => (a,b)∈reindexRelations e R)
      (Finsupp.domCongr e.symm a) (Finsupp.domCongr e.symm b) := by
  classical
  change AddConGen.Rel _ a b at h
  change AddConGen.Rel _ _ _
  induction h with
  | of a b hab => exact AddConGen.Rel.of _ _ (Finset.mem_image.mpr ⟨(a,b),hab,rfl⟩)
  | refl a => exact AddConGen.Rel.refl _
  | symm h ih => exact AddConGen.Rel.symm ih
  | trans h1 h2 ih1 ih2 => exact AddConGen.Rel.trans ih1 ih2
  | add h1 h2 ih1 ih2 => simpa only [map_add] using AddConGen.Rel.add ih1 ih2

theorem isPresentation_reindex (d : Fin 4 → ℕ) (e : Equiv.Perm (Fin 4))
    (R : Finset (Factorization × Factorization)) (hR : IsPresentation d R) :
    IsPresentation (d ∘ e) (reindexRelations e R) := by
  classical
  apply le_antisymm
  · apply AddCon.addConGen_le.mpr
    intro a b hab
    obtain ⟨⟨u,v⟩,huv,he⟩ := Finset.mem_image.mp hab
    cases he
    have hh : addConGen (fun a b => (a,b)∈R) u v := AddConGen.Rel.of _ _ huv
    rw [hR] at hh
    change factorizationMap d u=factorizationMap d v at hh
    change factorizationMap (d ∘ e) (Finsupp.domCongr e.symm u)=
      factorizationMap (d ∘ e) (Finsupp.domCongr e.symm v)
    simpa only [←factorizationMap_reindex,domCongr_inverse] using hh
  · intro a b hab
    change factorizationMap (d ∘ e) a=factorizationMap (d ∘ e) b at hab
    have hh : factorizationMap d (Finsupp.domCongr e a)=factorizationMap d (Finsupp.domCongr e b) := by
      simpa only [factorizationMap_reindex] using hab
    have hgen : addConGen (fun a b => (a,b)∈R) (Finsupp.domCongr e a) (Finsupp.domCongr e b) := by
      rw [hR]; exact hh
    simpa only [domCongr_inverse_left] using generatedRelation_reindex e R hgen

lemma presentationNumber_reindex_le (d : Fin 4 → ℕ) (e : Equiv.Perm (Fin 4)) :
    presentationNumber (d ∘ e)≤presentationNumber d := by
  obtain ⟨R,hR,hcard⟩ := exists_minimalPresentation_card d
  calc
    _ ≤ (reindexRelations e R).card :=
      presentationNumber_le _ _ (isPresentation_reindex d e R hR.1)
    _ ≤ R.card := Finset.card_image_le
    _ = _ := hcard

/-- The genuine minimum presentation cardinality does not depend on generator labels. -/
theorem presentationNumber_reindex (d : Fin 4 → ℕ) (e : Equiv.Perm (Fin 4)) :
    presentationNumber (d ∘ e)=presentationNumber d := by
  apply le_antisymm (presentationNumber_reindex_le d e)
  have hh := presentationNumber_reindex_le (d ∘ e) e.symm
  simpa [Function.comp_def] using hh

end FourGeneratedSemigroups
