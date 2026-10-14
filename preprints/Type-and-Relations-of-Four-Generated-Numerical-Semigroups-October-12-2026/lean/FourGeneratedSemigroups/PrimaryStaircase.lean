import FourGeneratedSemigroups.CriticalBox

noncomputable section
namespace FourGeneratedSemigroups

/-- A directed critical-relation arc, defined from actual factorizations. -/
def CriticalArc (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i j : Fin 4) : Prop :=
  i≠j ∧ ∃ c : Factorization, c i=0 ∧ 0<c j ∧
    factorizationMap d c=criticalExponent d hd i*d i

/-- A primary ordering has critical relations from generators 1 and 2 that
involve the distinguished generator 0. -/
def PrimaryOrdering {S : NumericalSemigroup} (G : FourGenerated S) : Prop :=
  CriticalArc G.generators G.positive 1 0 ∧ CriticalArc G.generators G.positive 2 0

/-- The paper's staircase, represented by four coordinates with coordinate zero fixed to zero. -/
def staircase {S : NumericalSemigroup} (G : FourGenerated S) : Set Factorization :=
  {c | c 0=0 ∧ c 3<criticalExponent G.generators G.positive 3 ∧
    (factorizationMap G.generators c : ℤ) ∈ S.apery (G.generators 0)}

lemma apery_coordinate_lt_of_criticalArc {S : NumericalSemigroup} (G : FourGenerated S)
    (i : Fin 4) (hi : CriticalArc G.generators G.positive i 0)
    (c : Factorization)
    (hc : (factorizationMap G.generators c : ℤ) ∈ S.apery (G.generators 0)) :
    c i<criticalExponent G.generators G.positive i := by
  by_contra hbound
  have hle : Finsupp.single i (criticalExponent G.generators G.positive i) ≤ c :=
    Finsupp.single_le_iff.mpr (by omega)
  obtain ⟨rest,hrest⟩ := le_iff_exists_add.mp hle
  obtain ⟨u,hui,hu0,hu⟩ := hi.2
  have heq : factorizationMap G.generators (u+rest)=factorizationMap G.generators c := by
    rw [hrest,map_add,map_add,hu,factorizationMap_single]
  have hz := G.factorization_coordinate_zero_of_apery 0 (u+rest) (by simpa [heq] using hc)
  simp only [Finsupp.add_apply] at hz
  omega

/-- For a primary ordering, the bounded staircase has no repeated semigroup degrees. -/
theorem primary_staircase_weight_injective {S : NumericalSemigroup}
    (G : FourGenerated S) (hG : PrimaryOrdering G) :
    Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ)) (staircase G) := by
  intro a ha b hb hab
  apply criticalBox_weight_injective G.generators G.positive a b ha.1 hb.1
  · intro i hi
    fin_cases i
    · contradiction
    · exact apery_coordinate_lt_of_criticalArc G 1 hG.1 a ha.2.2
    · exact apery_coordinate_lt_of_criticalArc G 2 hG.2 a ha.2.2
    · exact ha.2.1
  · intro i hi
    fin_cases i
    · contradiction
    · exact apery_coordinate_lt_of_criticalArc G 1 hG.1 b hb.2.2
    · exact apery_coordinate_lt_of_criticalArc G 2 hG.2 b hb.2.2
    · exact hb.2.1
  · exact Int.ofNat_inj.mp hab

/-- The actual primary staircase maps bijectively to the actual Apéry set. -/
theorem primary_staircase_bijOn {S : NumericalSemigroup}
    (G : FourGenerated S) (hG : PrimaryOrdering G) :
    Set.BijOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G) (S.apery (G.generators 0)) := by
  refine ⟨fun _ h => h.2.2,primary_staircase_weight_injective G hG,?_⟩
  intro w hw
  obtain ⟨c,hc,hc0,hc3⟩ := apery_has_bounded_factorization G w hw
  exact ⟨c,⟨hc0,hc3,by simpa [hc] using hw⟩,hc⟩

 theorem finite_primary_staircase {S : NumericalSemigroup}
    (G : FourGenerated S) (hG : PrimaryOrdering G) : (staircase G).Finite :=
  (primary_staircase_bijOn G hG).finite_iff_finite.mpr (S.finite_apery _)

end FourGeneratedSemigroups
