import FourGeneratedSemigroups.Apery
import FourGeneratedSemigroups.CriticalRelations
import Mathlib.Data.Finsupp.Order

noncomputable section
namespace FourGeneratedSemigroups

namespace FourGenerated
variable {S : NumericalSemigroup} (G : FourGenerated S)

 theorem factorization_mem (c : Factorization) : factorizationMap G.generators c ∈ S.monoid :=
  (G.generates _).mpr ⟨c,rfl⟩

 theorem generator_mem (i : Fin 4) : G.generators i ∈ S.monoid := by
  simpa using G.factorization_mem (Finsupp.single i 1)

 theorem generators_injective : Function.Injective G.generators := by
  intro i j hij
  by_contra h
  apply G.minimal i
  exact ⟨Finsupp.single j 1,by simp [Ne.symm h],by simpa using hij.symm⟩

 theorem factorization_coordinate_zero_of_apery (i : Fin 4) (c : Factorization)
    (hc : (factorizationMap G.generators c : ℤ) ∈ S.apery (G.generators i)) : c i=0 := by
  by_contra hci
  have hle : Finsupp.single i 1 ≤ c := Finsupp.single_le_iff.mpr (by omega)
  obtain ⟨rest,rfl⟩ := le_iff_exists_add.mp hle
  apply hc.2
  refine ⟨factorizationMap G.generators rest,?_,G.factorization_mem rest⟩
  simp

end FourGenerated

namespace NumericalSemigroup

/-- Apéry sets are closed under taking semigroup summands. -/
theorem apery_add_left {S : NumericalSemigroup} {d : ℕ} {x y : ℤ}
    (hx : S.memInt x) (hy : S.memInt y) (hxy : x+y ∈ S.apery d) : x ∈ S.apery d := by
  refine ⟨hx,?_⟩
  intro hgap
  apply hxy.2
  have hh := memInt_add hgap hy
  have he : x+y-(d : ℤ)=(x-(d : ℤ))+y := by omega
  rwa [he]

end NumericalSemigroup

/-- Every occurring degree has a factorization whose chosen coordinate is less
than its critical exponent. -/
theorem exists_factorization_below_critical (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (i : Fin 4) (n : ℕ) (hn : ∃ c, factorizationMap d c=n) :
    ∃ c : Factorization, factorizationMap d c=n ∧ c i<criticalExponent d hd i := by
  classical
  have hex : ∃ k : ℕ, ∃ c : Factorization, factorizationMap d c=n ∧ c i=k := by
    obtain ⟨c,hc⟩ := hn
    exact ⟨c i,c,hc,rfl⟩
  let k := Nat.find hex
  obtain ⟨c,hc,hci⟩ := Nat.find_spec hex
  refine ⟨c,hc,?_⟩
  by_contra hbound
  have hle : Finsupp.single i (criticalExponent d hd i) ≤ c :=
    Finsupp.single_le_iff.mpr (by omega)
  obtain ⟨rest,hrest⟩ := le_iff_exists_add.mp hle
  obtain ⟨u,hui,hu⟩ := (criticalExponent_spec d hd i).2
  have hnew : factorizationMap d (u+rest)=n := by
    rw [hrest,map_add,factorizationMap_single] at hc
    simpa [map_add,hu] using hc
  have hnewi : (u+rest) i=rest i := by simp [hui]
  have hmin : k ≤ rest i := Nat.find_min' hex ⟨u+rest,hnew,hnewi⟩
  have hpos := (criticalExponent_spec d hd i).1
  have hcoord : c i=criticalExponent d hd i+rest i := by simp [hrest]
  change c i=k at hci
  omega

/-- Cutting the third coordinate at its critical exponent does not remove any
Apéry degree. This is the surjectivity part of the staircase construction. -/
theorem apery_has_bounded_factorization {S : NumericalSemigroup} (G : FourGenerated S)
    (w : ℤ) (hw : w ∈ S.apery (G.generators 0)) :
    ∃ c : Factorization, (factorizationMap G.generators c : ℤ)=w ∧ c 0=0 ∧
      c 3<criticalExponent G.generators G.positive 3 := by
  obtain ⟨n,rfl,hn⟩ := hw.1
  obtain ⟨c,hc,hbound⟩ := exists_factorization_below_critical G.generators G.positive 3 n
    ((G.generates n).mp hn)
  refine ⟨c,by omega,?_,hbound⟩
  apply G.factorization_coordinate_zero_of_apery 0 c
  simpa [hc] using hw

end FourGeneratedSemigroups
