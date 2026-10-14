import FourGeneratedSemigroups.CriticalArcStructure
import FourGeneratedSemigroups.PrimaryOrderingGraph

noncomputable section
namespace FourGeneratedSemigroups

lemma criticalArc_outgoing_positive (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4) :
    1≤outgoingDegree (CriticalArc d hd) i := by
  classical
  obtain ⟨j,hj⟩ := criticalArc_exists d hd i
  have hh := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 4))) =>
    Nat.zero_le (if CriticalArc d hd i k then 1 else 0)) (Finset.mem_univ j)
  simpa [outgoingDegree,hj] using hh

/-- In the secondary case every critical vertex has a unique outgoing neighbor. -/
theorem criticalArc_unique_of_secondary (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (hsecondary : ∀ v,incomingDegree (CriticalArc d hd) v≤1) :
    ∀ i j k,CriticalArc d hd i j → CriticalArc d hd i k → j=k := by
  intro i j k hij hik
  obtain ⟨v,hv,hunique⟩ := existsUnique_outgoing_of_degrees (CriticalArc d hd)
    (criticalArc_outgoing_positive d hd) hsecondary i
  exact (hunique j hij).trans (hunique k hik).symm

/-- Once one secondary pair is labeled 0,1, the other two generators necessarily
form the second pair required by the staircase construction. -/
theorem secondaryCriticalOrdering_of_pair {S : NumericalSemigroup} (G : FourGenerated S)
    (hsecondary : ∀ v,incomingDegree (CriticalArc G.generators G.positive) v≤1)
    (h10 : CriticalArc G.generators G.positive 1 0) : SecondaryCriticalOrdering G := by
  have hu := criticalArc_unique_of_secondary G.generators G.positive hsecondary
  have h01 := criticalArc_reverse_of_unique G.generators G.positive hu h10
  obtain ⟨k,h2k⟩ := criticalArc_exists G.generators G.positive 2
  have h23 : CriticalArc G.generators G.positive 2 3 := by
    fin_cases k
    · have h02 := criticalArc_reverse_of_unique G.generators G.positive hu h2k
      have hh := hu 0 1 2 h01 h02
      exact False.elim (by cases hh)
    · have h12 := criticalArc_reverse_of_unique G.generators G.positive hu h2k
      have hh := hu 1 0 2 h10 h12
      exact False.elim (by cases hh)
    · exact False.elim (h2k.1 rfl)
    · exact h2k
  exact ⟨h10,criticalDegree_eq_of_unique G.generators G.positive hu h23⟩

end FourGeneratedSemigroups
