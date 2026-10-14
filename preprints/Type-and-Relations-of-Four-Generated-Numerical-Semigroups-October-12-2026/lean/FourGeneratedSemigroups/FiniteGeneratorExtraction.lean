import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Fintype.Card

noncomputable section
namespace FourGeneratedSemigroups

/-- A finite family of ideal generators contains an irredundant generating
subfamily; every omitted member was already redundant in the full family. -/
theorem exists_irredundant_generator_subfamily {R ι : Type*} [CommRing R] [Fintype ι]
    (f : ι→R) : ∃T : Finset ι,
    Ideal.span (f '' (T : Set ι))=Ideal.span (Set.range f) ∧
    (∀i∈T, f i∉Ideal.span (f '' ((↑T : Set ι) \ {i}))) ∧
    (∀i∉T, f i∈Ideal.span (f '' {j | j≠i})) := by
  classical
  have hex : ∃n : ℕ, ∃T : Finset ι,
      Ideal.span (f '' (T : Set ι))=Ideal.span (Set.range f) ∧ T.card=n := by
    exact ⟨Finset.univ.card,Finset.univ,by simp,rfl⟩
  obtain ⟨T,hT,hcard⟩ := Nat.find_spec hex
  refine ⟨T,hT,?_,?_⟩
  · intro i hi hred
    have he : Ideal.span (f '' (↑(T.erase i) : Set ι))=Ideal.span (Set.range f) := by
      apply le_antisymm
      · apply Ideal.span_mono
        rintro x ⟨j,hj,rfl⟩
        exact ⟨j,rfl⟩
      · rw [← hT,Ideal.span_le]
        rintro x ⟨j,hj,rfl⟩
        by_cases hji : j=i
        · subst j
          simpa [Finset.coe_erase] using hred
        · exact Ideal.subset_span ⟨j,Finset.mem_erase.mpr ⟨hji,hj⟩,rfl⟩
    have hmin := Nat.find_min' hex ⟨T.erase i,he,rfl⟩
    have hlt := Finset.card_erase_lt_of_mem hi
    omega
  · intro i hi
    have hmem : f i∈Ideal.span (f '' (↑T : Set ι)) := by
      rw [hT]
      exact Ideal.subset_span ⟨i,rfl⟩
    apply (Ideal.span_mono (show f '' (↑T : Set ι)⊆f '' {j | j≠i} from ?_)) hmem
    rintro x ⟨j,hj,rfl⟩
    exact ⟨j,fun he => hi (he ▸ hj),rfl⟩

/-- If at most one member of the original family is redundant, an irredundant
subfamily loses at most one generator. -/
theorem exists_large_irredundant_generator_subfamily {R ι : Type*} [CommRing R] [Fintype ι]
    (f : ι→R)
    (hunique : ∀i j, f i∈Ideal.span (f '' {k | k≠i}) →
      f j∈Ideal.span (f '' {k | k≠j}) → i=j) :
    ∃T : Finset ι, Ideal.span (f '' (T : Set ι))=Ideal.span (Set.range f) ∧
    (∀i∈T, f i∉Ideal.span (f '' ((↑T : Set ι) \ {i}))) ∧
    Fintype.card ι≤T.card+1 := by
  classical
  obtain ⟨T,hT,hirred,homitted⟩ := exists_irredundant_generator_subfamily f
  refine ⟨T,hT,hirred,?_⟩
  have hcard : (Finset.univ\T).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hunique i j (homitted i (Finset.mem_sdiff.mp hi).2)
      (homitted j (Finset.mem_sdiff.mp hj).2)
  have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  simp only [Finset.card_univ] at he
  omega

lemma span_subfamily_range {R ι : Type*} [CommRing R] (f : ι→R) (T : Finset ι) :
    Ideal.span (Set.range (fun i : T => f i.val))=Ideal.span (f '' (T : Set ι)) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,i.property,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,rfl⟩

lemma irredundant_subfamily {R ι : Type*} [CommRing R] (f : ι→R) (T : Finset ι)
    (h : ∀i∈T, f i∉Ideal.span (f '' ((↑T : Set ι) \ {i}))) (i : T) :
    f i.val∉Ideal.span ((fun j : T => f j.val) '' {j | j≠i}) := by
  intro hi
  apply h i.val i.property
  apply (Ideal.span_mono (show (fun j : T => f j.val) '' {j | j≠i} ⊆
      f '' ((↑T : Set ι) \ {i.val}) from ?_)) hi
  rintro x ⟨j,hj,rfl⟩
  exact ⟨j.val,⟨j.property,fun he => hj (Subtype.ext he)⟩,rfl⟩

end FourGeneratedSemigroups
