import SumsetRanges.RestrictedBounds
import Mathlib.LinearAlgebra.Vandermonde

open Finset
namespace SumsetRanges

/-- The first L+1 integer moments, indexed from degree zero. -/
def momentMap (n L : ℕ) : (Fin n → ℤ) →+ (Fin (L+1) → ℤ) where
  toFun v j := ∑ i : Fin n, v i * (i.val : ℤ)^j.val
  map_zero' := by funext j; simp
  map_add' v w := by funext j; simp [add_mul,Finset.sum_add_distrib]

def coordinateSupport {n : ℕ} (v : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i≠0)

/-- Sparse injectivity of the moment map, by the integer Vandermonde theorem. -/
theorem momentMap_sparse_zero (n L : ℕ) (v : Fin n → ℤ)
    (hs : (coordinateSupport v).card≤L+1) (hv : momentMap n L v=0) : v=0 := by
  classical
  let S := coordinateSupport v
  let e : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  have hf : Function.Injective (fun j : Fin S.card => ((e j).val : ℤ)) := by
    intro i j he
    apply e.injective
    apply Fin.ext
    change ((e i).val : ℤ)=((e j).val : ℤ) at he
    exact Int.ofNat_inj.mp he
  have hm : ∀ j : Fin S.card,
      (∑ i : Fin S.card, v (e i) * ((e i).val : ℤ)^j.val)=0 := by
    intro j
    have hj : j.val<L+1 := lt_of_lt_of_le j.isLt hs
    have hh := congrFun hv ⟨j.val,hj⟩
    change (∑ i : Fin n,v i*(i.val : ℤ)^j.val)=0 at hh
    calc
      _ = ∑ i∈S,v i*(i.val : ℤ)^j.val := by
        calc
          _ = ∑ i∈Finset.univ.image e,v i*(i.val : ℤ)^j.val :=
            (Finset.sum_image e.injective.injOn).symm
          _ = _ := by rw [show Finset.univ.image e=S from S.image_orderEmbOfFin_univ rfl]
      _ = ∑ i : Fin n,v i*(i.val : ℤ)^j.val := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        have hz : v i=0 := by
          simp only [S,coordinateSupport,Finset.mem_filter,Finset.mem_univ,true_and,not_not] at hi
          exact hi
        rw [hz,zero_mul]
      _ = 0 := hh
  have hz := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hm
  funext i
  by_cases hi : v i=0
  · exact hi
  · have hiS : i∈S := by simp [S,coordinateSupport,hi]
    have hmem : i∈Set.range e := by
      rw [show Set.range e=(S:Set (Fin n)) from S.range_orderEmbOfFin rfl]
      exact hiS
    obtain ⟨j,rfl⟩ := hmem
    exact congrFun hz j

end SumsetRanges
