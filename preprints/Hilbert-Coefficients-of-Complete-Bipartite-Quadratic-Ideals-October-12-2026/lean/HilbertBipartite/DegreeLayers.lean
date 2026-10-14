import HilbertBipartite.Definitions
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace HilbertBipartite

noncomputable def degreeAtMost (α : Type*) [Fintype α] [DecidableEq α] (d : Nat) :
    Finset (α →₀ Nat) :=
  (Finset.range (d+1)).biUnion (fun r => (Finset.univ : Finset α).finsuppAntidiag r)

@[simp] theorem mem_degreeAtMost {α : Type*} [Fintype α] [DecidableEq α]
    {d : Nat} {a : α →₀ Nat} : a ∈ degreeAtMost α d ↔ (∑ i, a i) ≤ d := by
  classical
  simp only [degreeAtMost, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  constructor
  · rintro ⟨r, hr, he⟩
    have : (∑ i, a i) = r := he
    omega
  · intro h
    refine ⟨Finset.univ.sum a, ?_, rfl⟩
    exact Nat.lt_succ_of_le h

/-- Stars and bars for all exponents of bounded total degree. -/
theorem card_degreeAtMost (α : Type*) [Fintype α] [DecidableEq α] (d : Nat) :
    (degreeAtMost α d).card = (d + Fintype.card α).choose (Fintype.card α) := by
  classical
  unfold degreeAtMost
  rw [Finset.card_biUnion]
  · simp_rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ]
    exact Nat.sum_range_multichoose d (Fintype.card α)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have ha' := (Finset.mem_finsuppAntidiag.mp ha).1
    have hb' := (Finset.mem_finsuppAntidiag.mp hb).1
    exact hij (ha'.symm.trans hb')

noncomputable def lowDegreePairs (p q s : Nat) : Finset (ExponentPair p q) :=
  (degreeAtMost (Fin p ⊕ Fin q) (2*s-1)).image Finsupp.sumFinsuppEquivProdFinsupp

theorem card_lowDegreePairs (p q s : Nat) (hs : 1 ≤ s) :
    (lowDegreePairs p q s).card = (2*s+p+q-1).choose (p+q) := by
  classical
  rw [lowDegreePairs, Finset.card_image_of_injective _ Finsupp.sumFinsuppEquivProdFinsupp.injective,
    card_degreeAtMost]
  simp only [Fintype.card_sum, Fintype.card_fin]
  congr 1
  omega

end HilbertBipartite
