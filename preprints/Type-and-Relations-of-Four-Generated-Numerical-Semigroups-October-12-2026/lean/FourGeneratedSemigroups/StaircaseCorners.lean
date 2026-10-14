import FourGeneratedSemigroups.SecondaryStaircase

noncomputable section
namespace FourGeneratedSemigroups

/-- The coordinate-maximal monomials of the actual three-dimensional staircase. -/
def staircaseCorners {S : NumericalSemigroup} (G : FourGenerated S) : Set Factorization :=
  {c | c∈staircase G ∧ ∀ i : Fin 4, i≠0 → c+Finsupp.single i 1∉staircase G}

/-- The staircase is a lower set for coordinatewise divisibility. -/
theorem staircase_lower {S : NumericalSemigroup} (G : FourGenerated S)
    {a b : Factorization} (hb : b∈staircase G) (hab : a≤b) : a∈staircase G := by
  obtain ⟨r,hr⟩ := le_iff_exists_add.mp hab
  refine ⟨by have := hab 0; have := hb.1; omega,lt_of_le_of_lt (hab 3) hb.2.1,?_⟩
  apply NumericalSemigroup.apery_add_left
    ((NumericalSemigroup.memInt_natCast S _).mpr (G.factorization_mem a))
    ((NumericalSemigroup.memInt_natCast S _).mpr (G.factorization_mem r))
  simpa [hr,map_add,Nat.cast_add] using hb.2.2

lemma corner_of_maximalApery {S : NumericalSemigroup} (G : FourGenerated S)
    (c : Factorization) (hc : c∈staircase G)
    (hw : (factorizationMap G.generators c : ℤ) ∈ S.maximalApery (G.generators 0)) :
    c∈staircaseCorners G := by
  refine ⟨hc,?_⟩
  intro i hi hci
  apply hw.2 (G.generators i) (G.generator_mem i) (Nat.ne_of_gt (G.positive i))
  simpa using hci.2.2

/-- Pseudo-Frobenius elements inject into actual staircase corners. -/
theorem type_le_staircaseCorners {S : NumericalSemigroup} (G : FourGenerated S)
    (hfinite : (staircase G).Finite) : S.type≤Nat.card (staircaseCorners G) := by
  classical
  have hex : ∀ w : S.maximalApery (G.generators 0),
      ∃ c : staircaseCorners G, (factorizationMap G.generators c.val : ℤ)=w.val := by
    intro w
    obtain ⟨c,hc,hc0,hc3⟩ := apery_has_bounded_factorization G w.val w.property.1
    have hcs : c∈staircase G := ⟨hc0,hc3,by simpa [hc] using w.property.1⟩
    exact ⟨⟨c,corner_of_maximalApery G c hcs (by simp [hc,w.property])⟩,hc⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rw [←hf a,←hf b,hab]
  let : Finite (staircaseCorners G) := (hfinite.subset (fun _ h => h.1)).to_subtype
  rw [S.type_eq_card_maximalApery _ (G.generator_mem 0) (Nat.ne_of_gt (G.positive 0))]
  exact Nat.card_le_card_of_injective f hinj

end FourGeneratedSemigroups
