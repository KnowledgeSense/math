import SumsetRanges.IndependentCopies

open Finset Polynomial
namespace SumsetRanges

def linearDegree (m : ℕ) : LinearLattice m →+ ℤ where
  toFun v := ∑ a, v a
  map_zero' := by simp
  map_add' v w := by simp [Finset.sum_add_distrib]

theorem linearDegree_point (m : ℕ) (hm : 1 ≤ m) (a : LinearIndex m) :
    linearDegree m (linearPoint a)=1 := by
  rcases a with i | (_ | j)
  · simp [linearDegree,linearPoint]
  · simp [linearDegree,linearPoint,Fintype.sum_sum_type]
    omega
  · simp [linearDegree,linearPoint]

theorem linearDegree_block (m : ℕ) (hm : 1 ≤ m) :
    ∀ a∈linearBlock m,linearDegree m a=1 := by
  intro a ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  exact linearDegree_point m hm i

theorem restrictedPolynomial_linearBlock (m : ℕ) (hm : 2 ≤ m) :
    restrictedPolynomial (linearBlock m) = (1+X)^(2*m)-X^m := by
  ext q
  rw [coeff_restrictedPolynomial,card_restrictedSums_linearBlock m q hm]
  simp only [coeff_sub,coeff_one_add_X_pow,coeff_X_pow]
  by_cases hq : q=m
  · subst q
    have hc : 1 ≤ (2*m).choose m := Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.choose_pos (by omega)))
    simp only [ite_true]
    rw [Nat.cast_sub hc]
    simp
  · simp only [ite_eq_right hq,Nat.sub_zero,sub_zero]

/-- r independent copies of the actual linear relation block. -/
def linearBlocks (m r : ℕ) : Finset (Fin r → LinearLattice m) :=
  independentCopies (linearBlock m) r

theorem card_linearBlocks (m r : ℕ) (hm : 2 ≤ m) : (linearBlocks m r).card=2*m*r := by
  rw [linearBlocks,card_independentCopies _ (linearDegree m) (linearDegree_block m (by omega)),
    card_linearBlock m hm]
  ring

/-- Lemma 4.1 for all numbers of blocks, using actual finite lattice sets. -/
theorem restrictedPolynomial_linearBlocks (m r : ℕ) (hm : 2 ≤ m) :
    restrictedPolynomial (linearBlocks m r) = ((1+X)^(2*m)-X^m)^r := by
  rw [linearBlocks,restrictedPolynomial_independentCopies _ (linearDegree m)
    (linearDegree_block m (by omega)),restrictedPolynomial_linearBlock m hm]

end SumsetRanges
