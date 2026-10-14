import SumsetRanges.FiniteNewtonSeparation
import SumsetRanges.MomentMap

open Finset
namespace SumsetRanges

abbrev WeightedIndex {n : ℕ} (v : Fin n → ℕ) := Σi : Fin n,Fin (v i)

theorem weightedIndex_power_sum {n : ℕ} (v : Fin n → ℕ) (j : ℕ) :
    (∑a : WeightedIndex v,(a.1.val : ℤ)^j)=∑i : Fin n,(v i : ℤ)*(i.val : ℤ)^j := by
  simp [Fintype.sum_sigma]

theorem weightedIndex_card {n : ℕ} (v : Fin n → ℕ) :
    Fintype.card (WeightedIndex v)=∑i,v i := by simp [WeightedIndex,Fintype.card_sigma]

/-- Nonnegative bounded mass is separated by moments through its mass bound. -/
theorem momentMap_nonnegative_injective (n L : ℕ) (v w : Fin n → ℕ)
    (_hv : (∑i,v i)≤L) (_hw : (∑i,w i)≤L)
    (he : momentMap n L (fun i => (v i : ℤ))=momentMap n L (fun i => (w i : ℤ))) : v=w := by
  have hmass : (∑i,v i)=(∑i,w i) := by
    have h0 := congrFun he ⟨0,by omega⟩
    simp only [momentMap,AddMonoidHom.coe_mk,ZeroHom.coe_mk,pow_zero,mul_one] at h0
    exact_mod_cast h0
  have hp : ∀j≤∑i,v i,(∑a : WeightedIndex v,(a.1.val : ℤ)^j)=
      ∑a : WeightedIndex w,(a.1.val : ℤ)^j := by
    intro j hj
    rw [weightedIndex_power_sum,weightedIndex_power_sum]
    exact congrFun he ⟨j,by omega⟩
  have hm := finite_multiset_eq_of_power_sums (∑i,v i)
    (fun a : WeightedIndex v => (a.1.val : ℤ)) (fun a : WeightedIndex w => (a.1.val : ℤ))
    (weightedIndex_card v) (by rw [weightedIndex_card,hmass]) hp
  funext i
  have hs := congrArg (fun s : Multiset ℤ => (s.map (fun x => if x=(i.val:ℤ) then (1:ℕ) else 0)).sum) hm
  simp only [Multiset.map_map] at hs
  change (∑a : WeightedIndex v,if (a.1.val:ℤ)=(i.val:ℤ) then (1:ℕ) else 0)=
    (∑a : WeightedIndex w,if (a.1.val:ℤ)=(i.val:ℤ) then (1:ℕ) else 0) at hs
  have count (a : Fin n → ℕ) :
      (∑ x : WeightedIndex a, if (x.1.val : ℤ) = (i.val : ℤ) then (1:ℕ) else 0) = a i := by
    change (∑ x : (Σ j : Fin n, Fin (a j)), _) = _
    rw [Fintype.sum_sigma]
    simp only [Int.natCast_inj, ← Fin.ext_iff]
    simp
  rw [count v, count w] at hs
  exact hs

end SumsetRanges
