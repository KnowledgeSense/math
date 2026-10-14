import MainTheorems.Hypercomb.RootedSets

namespace ResearchMain.Hypercomb

open Classical Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem strongIndependent_singleEdge (S : Finset (Option V)) :
    StrongIndependent {Finset.univ} S ↔ S.card ≤ 1 := by
  simp [StrongIndependent]

def excludedInitial (S : SmallSet V) : Excluded {Finset.univ} (none : Option V) :=
  ⟨S.val.map Function.Embedding.some, by
    constructor
    · exact strongIndependent_singleEdge _ |>.mpr (by simpa using S.property)
    · simp⟩

theorem excludedInitial_injective : Function.Injective (excludedInitial (V := V)) := by
  intro S U he
  have h := congrArg (fun S => S.val.eraseNone) he
  exact Subtype.ext (by simpa only [excludedInitial, Finset.eraseNone_map_some] using h)

theorem excludedInitial_surjective : Function.Surjective (excludedInitial (V := V)) := by
  intro S
  have hcard := (strongIndependent_singleEdge S.val).mp S.property.1
  refine ⟨⟨S.val.eraseNone, (Finset.card_eraseNone_le _).trans hcard⟩, Subtype.ext ?_⟩
  change S.val.eraseNone.map Function.Embedding.some = S.val
  rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem S.property.2]

noncomputable def excludedInitialEquiv : SmallSet V ≃ Excluded {Finset.univ} (none : Option V) :=
  Equiv.ofBijective excludedInitial ⟨excludedInitial_injective, excludedInitial_surjective⟩

theorem excludedPolynomial_initial : excludedPolynomial {Finset.univ} (none : Option V) =
    1 + C (Fintype.card V : ℝ) * X := by
  rw [excludedPolynomial, ← Equiv.sum_comp (excludedInitialEquiv (V := V))]
  change (∑ S : SmallSet V, X ^ (excludedInitial S).val.card) = _
  simp only [excludedInitial, Finset.card_map]
  exact smallSet_polynomial

def includedInitial (_ : Unit) : Included {Finset.univ} (none : Option V) :=
  ⟨{none}, by constructor; exact (strongIndependent_singleEdge _).mpr (by simp); simp⟩

theorem includedInitial_bijective : Function.Bijective (includedInitial (V := V)) := by
  constructor
  · intro S U _
    exact Subsingleton.elim _ _
  · intro S
    have hcard := (strongIndependent_singleEdge S.val).mp S.property.1
    have he : S.val = {none} := by
      ext x
      constructor
      · intro hx
        exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hcard x hx none S.property.2)
      · intro hx
        rw [Finset.mem_singleton.mp hx]
        exact S.property.2
    exact ⟨(), Subtype.ext he.symm⟩

noncomputable def includedInitialEquiv : Unit ≃ Included {Finset.univ} (none : Option V) :=
  Equiv.ofBijective includedInitial includedInitial_bijective

theorem includedPolynomial_initial : includedPolynomial {Finset.univ} (none : Option V) = X := by
  rw [includedPolynomial, ← Equiv.sum_comp (includedInitialEquiv (V := V))]
  change (∑ S : Unit, X ^ (includedInitial (V := V) S).val.card) = _
  simp [includedInitial]

end ResearchMain.Hypercomb
