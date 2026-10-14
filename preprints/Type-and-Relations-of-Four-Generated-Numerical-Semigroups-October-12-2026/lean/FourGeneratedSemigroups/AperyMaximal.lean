import FourGeneratedSemigroups.AperyFactorizations

noncomputable section
namespace FourGeneratedSemigroups

/-- Maximality in the semigroup order can be tested against the four generators. -/
theorem maximalApery_iff_generator_tests {S : NumericalSemigroup} (G : FourGenerated S)
    (w : ℤ) :
    w∈S.maximalApery (G.generators 0) ↔
      w∈S.apery (G.generators 0) ∧
        ∀ i : Fin 4,w+(G.generators i : ℤ)∉S.apery (G.generators 0) := by
  constructor
  · intro h
    exact ⟨h.1,fun i => h.2 _ (G.generator_mem i) (Nat.ne_of_gt (G.positive i))⟩
  · rintro ⟨hw,hgen⟩
    refine ⟨hw,?_⟩
    intro n hn hn0 hsum
    obtain ⟨c,hc⟩ := (G.generates n).mp hn
    have hnz : c≠0 := by intro he; apply hn0; simpa [he] using hc.symm
    have hex : ∃ i,c i≠0 := by
      by_contra hh
      push Not at hh
      exact hnz (Finsupp.ext hh)
    obtain ⟨i,hi⟩ := hex
    have hle : Finsupp.single i 1≤c := Finsupp.single_le_iff.mpr (by omega)
    obtain ⟨r,hr⟩ := le_iff_exists_add.mp hle
    have hnexpr : n=G.generators i+factorizationMap G.generators r := by
      simpa [hr] using hc.symm
    apply hgen i
    apply NumericalSemigroup.apery_add_left
      (NumericalSemigroup.memInt_add hw.1
        ((NumericalSemigroup.memInt_natCast S _).mpr (G.generator_mem i)))
      ((NumericalSemigroup.memInt_natCast S _).mpr (G.factorization_mem r))
    simpa [hnexpr,Nat.cast_add,add_assoc] using hsum

end FourGeneratedSemigroups
