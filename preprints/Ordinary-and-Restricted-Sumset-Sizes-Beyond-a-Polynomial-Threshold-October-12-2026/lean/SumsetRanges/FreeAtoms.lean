import SumsetRanges.BlockNorms

open Finset Polynomial
namespace SumsetRanges

def freeAtoms (n : ℕ) : Finset (Fin n→ℤ) := independentCopies ({1} : Finset ℤ) n

def freeDegree (n : ℕ) : (Fin n→ℤ) →+ ℤ := copiedDegree (AddMonoidHom.id ℤ) n

theorem freeDegree_points (n : ℕ) : ∀v∈freeAtoms n,freeDegree n v=1 :=
  copiedDegree_points {1} (AddMonoidHom.id ℤ) (by simp) n

theorem card_freeAtoms (n : ℕ) : (freeAtoms n).card=n := by
  rw [freeAtoms,card_independentCopies {1} (AddMonoidHom.id ℤ) (by simp)]
  simp

theorem freeAtoms_norm (n : ℕ) : ∀v∈freeAtoms n,coordinateNorm v≤1 :=
  copied_size_bound {1} Int.natAbs rfl 1 n (by simp)

theorem restrictedPolynomial_singleton {α : Type*} [AddCommMonoid α] [DecidableEq α] (a : α) :
    restrictedPolynomial ({a} : Finset α)=1+X := by
  simp [restrictedPolynomial,Finset.sum_range_succ,restrictedSums_one,monomial_one_one_eq_X]

theorem restrictedPolynomial_freeAtoms (n : ℕ) :
    restrictedPolynomial (freeAtoms n)=(1+X)^n := by
  rw [freeAtoms,restrictedPolynomial_independentCopies {1} (AddMonoidHom.id ℤ) (by simp),
    restrictedPolynomial_singleton]

end SumsetRanges
