import SumsetRanges.MomentMap
import SumsetRanges.FreimanImages

open Finset
namespace SumsetRanges

def latticeNorm {n : ℕ} (v : Fin n → ℤ) : ℕ := ∑ i, (v i).natAbs

theorem support_card_le_latticeNorm {n : ℕ} (v : Fin n → ℤ) :
    (coordinateSupport v).card ≤ latticeNorm v := by
  calc
    _ = ∑ _i∈coordinateSupport v,1 := by simp
    _ ≤ ∑ i∈coordinateSupport v,(v i).natAbs := by
      apply Finset.sum_le_sum
      intro i hi
      have hv : v i≠0 := (Finset.mem_filter.mp hi).2
      have hn : (v i).natAbs≠0 := by simpa using hv
      omega
    _ ≤ ∑ i : Fin n,(v i).natAbs := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem latticeNorm_add {n : ℕ} (v w : Fin n → ℤ) :
    latticeNorm (v+w) ≤ latticeNorm v+latticeNorm w := by
  unfold latticeNorm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => Int.natAbs_add_le (v i) (w i))

@[simp] theorem latticeNorm_neg {n : ℕ} (v : Fin n → ℤ) : latticeNorm (-v)=latticeNorm v := by
  simp [latticeNorm]

theorem latticeNorm_sub {n : ℕ} (v w : Fin n → ℤ) :
    latticeNorm (v-w) ≤ latticeNorm v+latticeNorm w := by
  simpa only [sub_eq_add_neg,latticeNorm_neg] using latticeNorm_add v (-w)

theorem latticeNorm_sum {ι : Type*} {n : ℕ} (S : Finset ι) (f : ι → Fin n → ℤ) :
    latticeNorm (∑ a∈S,f a) ≤ ∑ a∈S,latticeNorm (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [latticeNorm]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (latticeNorm_add _ _).trans (Nat.add_le_add_left ih _)

theorem latticeNorm_restricted_sum {n : ℕ} (A : Finset (Fin n → ℤ)) (M q : ℕ)
    (hA : ∀ a∈A,latticeNorm a≤M) (x : Fin n → ℤ) (hx : x∈restrictedSums A q) :
    latticeNorm x≤q*M := by
  obtain ⟨S,hS,hSc,rfl⟩ := mem_restrictedSums.mp hx
  calc
    _ ≤ ∑ a∈S,latticeNorm a := latticeNorm_sum S id
    _ ≤ ∑ _a∈S,M := Finset.sum_le_sum (fun a ha => hA a (hS ha))
    _ = q*M := by simp [hSc]

/-- The sparse moment map is injective on each actual restricted sumset whenever
 the total possible difference norm fits the number of moments. -/
theorem momentMap_injOn_restrictedSums (n L M q : ℕ) (A : Finset (Fin n → ℤ))
    (hA : ∀ a∈A,latticeNorm a≤M) (hL : 2*q*M≤L+1) :
    Set.InjOn (momentMap n L) (restrictedSums A q) := by
  intro x hx y hy he
  have hnx := latticeNorm_restricted_sum A M q hA x hx
  have hny := latticeNorm_restricted_sum A M q hA y hy
  have hns := latticeNorm_sub x y
  have hsupport := support_card_le_latticeNorm (x-y)
  have hs : (coordinateSupport (x-y)).card≤L+1 := by nlinarith
  have hm : momentMap n L (x-y)=0 := by rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp (momentMap_sparse_zero n L (x-y) hs hm)

theorem moment_coordinate_bound (n L M : ℕ) (hn : 1≤n) (v : Fin n → ℤ)
    (hv : latticeNorm v≤M) (j : Fin (L+1)) :
    ((momentMap n L v) j).natAbs≤M*n^L := by
  change (∑ i : Fin n,v i*(i.val:ℤ)^j.val).natAbs≤_
  calc
    _ ≤ ∑ i : Fin n,(v i*(i.val:ℤ)^j.val).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ i : Fin n,(v i).natAbs*n^L := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
      apply Nat.mul_le_mul_left
      calc
        i.val^j.val ≤ n^j.val := Nat.pow_le_pow_left (Nat.le_of_lt i.isLt) j.val
        _ ≤ n^L := Nat.pow_le_pow_right hn (Nat.le_of_lt_succ j.isLt)
    _ = latticeNorm v*n^L := by rw [← Finset.sum_mul]; rfl
    _ ≤ M*n^L := Nat.mul_le_mul_right _ hv

end SumsetRanges
