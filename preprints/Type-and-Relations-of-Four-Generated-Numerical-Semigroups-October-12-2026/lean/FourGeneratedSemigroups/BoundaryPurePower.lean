import FourGeneratedSemigroups.StaircaseBoundary
import FourGeneratedSemigroups.CriticalApery

noncomputable section
namespace FourGeneratedSemigroups

lemma factorization_below_critical_unique (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (i : Fin 4) (q : ℕ) (hq : q<criticalExponent d hd i) (c : Factorization)
    (hc : factorizationMap d c=q*d i) : c=Finsupp.single i q := by
  have hw : factorizationMap d (Finsupp.single i q)=factorizationMap d c := by simpa using hc.symm
  by_cases hi : q≤c i
  · exact (equal_weight_of_le d hd _ _ hw (Finsupp.single_le_iff.mpr hi)).symm
  · exact False.elim (impossible_single_positive_difference d hd (Finsupp.single i q) c hw i
      (by simpa using Nat.lt_of_not_ge hi) (by simpa using hq)
      (by intro j hj; simp [hj]))

lemma below_critical_pure_degree_apery {S : NumericalSemigroup} (G : FourGenerated S)
    (i : Fin 4) (hi : i≠0) (q : ℕ) (hq : q<criticalExponent G.generators G.positive i) :
    ((q*G.generators i : ℕ) : ℤ)∈S.apery (G.generators 0) := by
  refine ⟨?_,?_⟩
  · apply (NumericalSemigroup.memInt_natCast S _).mpr
    simpa using G.factorization_mem (Finsupp.single i q)
  · rintro ⟨n,hn,hnS⟩
    obtain ⟨c,hc⟩ := (G.generates n).mp hnS
    have he : factorizationMap G.generators (Finsupp.single 0 1+c)=q*G.generators i := by
      simp only [map_add,factorizationMap_single,one_mul,hc]
      omega
    have hh := factorization_below_critical_unique G.generators G.positive i q hq _ he
    have hz := congrArg (fun a : Factorization => a 0) hh
    simp [Ne.symm hi] at hz

/-- The cutoff pure power is a genuine minimal boundary generator. -/
theorem top_power_mem_boundary {S : NumericalSemigroup} (G : FourGenerated S) :
    Finsupp.single 3 (criticalExponent G.generators G.positive 3)∈staircaseBoundary G := by
  refine ⟨?_,?_⟩
  · intro h
    have hh := h.2.1
    simp at hh
  · intro b hb
    have hshape : b=Finsupp.single 3 (b 3) := by
      ext i
      by_cases hi : i=3
      · subst i; simp
      · have hh := hb.le i
        simp [hi] at hh
        simp [hi,hh]
    have hsmall : b 3<criticalExponent G.generators G.positive 3 := by
      have hh := hb.le 3
      simp only [Finsupp.single_eq_same] at hh
      by_contra hn
      have heq : b 3=criticalExponent G.generators G.positive 3 := by omega
      exact hb.ne (by simpa [heq] using hshape)
    have hb0 : b 0=0 := by
      have hh := congrArg (fun a : Factorization => a 0) hshape
      simpa using hh
    refine ⟨hb0,hsmall,?_⟩
    have hw : factorizationMap G.generators b=b 3*G.generators 3 := by
      calc
        _ = factorizationMap G.generators (Finsupp.single 3 (b 3)) := congrArg _ hshape
        _ = _ := factorizationMap_single _ _ _
    simpa only [hw] using below_critical_pure_degree_apery G 3 (by decide) (b 3) hsmall

/-- All other boundary generators have third coordinate strictly below the cutoff. -/
theorem boundary_below_top_unless_pure {S : NumericalSemigroup} (G : FourGenerated S)
    (a : Factorization) (ha : a∈staircaseBoundary G)
    (hne : a≠Finsupp.single 3 (criticalExponent G.generators G.positive 3)) :
    a 3<criticalExponent G.generators G.positive 3 := by
  by_contra hn
  have hh := boundary_divides_eq G ha (top_power_mem_boundary G)
    (Finsupp.single_le_iff.mpr (Nat.le_of_not_gt hn))
  exact hne hh.symm

end FourGeneratedSemigroups
