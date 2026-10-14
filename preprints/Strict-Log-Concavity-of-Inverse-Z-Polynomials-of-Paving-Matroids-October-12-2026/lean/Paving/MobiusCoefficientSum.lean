import Paving.MobiusSubtraction
import Paving.RankSubsetEnumeration

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α] {M : Matroid α}

/-- The binomial row written with the rank-complement lower argument. -/
def uniformEntry (r n k : ℕ) : ℤ := (n.choose k:ℤ)*(n-k-1).choose (r-1-k)

/-- Exact rank-k upper Möbius aggregate on the actual paving flat lattice. -/
theorem IsPaving.signed_mobius_rank_sum (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (k : ℕ) (hk : k≤d) :
    (∑ F ∈ (univ : Finset (MatroidInverseZ.Flat M)).filter
      (fun F => MatroidInverseZ.flatRank M F=k),
        (-1 : ℤ)^(rank M-k)*IncidenceAlgebra.mu ℤ F ⊤) =
      uniformEntry (rank M) M.E.ncard k -
        ∑ H ∈ hyperplanes M, uniformEntry (rank M) H.ncard k := by
  let w := fun S : Set α => ((M.E.ncard-k-1).choose (d-k+1):ℤ) -
    ∑ H ∈ (hyperplanes M).filter (fun H => S ⊆ H), ((H.ncard-k-1).choose (d-k+1):ℤ)
  have hs : (∑ F ∈ (univ : Finset (MatroidInverseZ.Flat M)).filter
      (fun F => MatroidInverseZ.flatRank M F=k),
        (-1 : ℤ)^(rank M-k)*IncidenceAlgebra.mu ℤ F ⊤) =
      ∑ F ∈ (univ : Finset (MatroidInverseZ.Flat M)).filter
        (fun F => MatroidInverseZ.flatRank M F=k), w F.1 := by
    apply sum_congr rfl
    intro F hF
    have hfk := (mem_filter.mp hF).2
    have hi := hM.flat_indep_of_rank F.2 (by change subsetRank M F.1=k at hfk; omega)
    have hc : F.1.ncard=k := by
      have he : MatroidInverseZ.flatRank M F=F.1.ncard := congrArg ENat.toNat hi.eRk_eq_encard
      omega
    rw [hM.upper_mu_subtraction d hr F (by omega), hc, hr, ← mul_assoc, ← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow, one_mul]
    rfl
  rw [hs, hM.sum_rank_flats k (by omega) w]
  simp only [w, sum_sub_distrib, sum_const, nsmul_eq_mul, card_powersetCard,
    ← Set.ncard_eq_toFinset_card']
  have hswap : (∑ S ∈ M.E.toFinset.powersetCard k,
      ∑ H ∈ (hyperplanes M).filter (fun H => (S:Set α) ⊆ H),
        ((H.ncard-k-1).choose (d-k+1):ℤ)) =
      ∑ H ∈ hyperplanes M, (H.ncard.choose k:ℤ)*((H.ncard-k-1).choose (d-k+1):ℤ) := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro H hH
    exact subset_hyperplane_sum H M.E ((mem_hyperplanes M H).mp hH).1.subset_ground k _
  rw [hswap]
  simp only [uniformEntry, hr, show d+2-1-k=d-k+1 by omega]

/-- Noncentral lower-half coefficients of the original matroid invariant. -/
theorem IsPaving.actual_inverseZ_noncentral_formula (hM : IsPaving M) (hr : 3≤rank M)
    (k : ℕ) (hk : 2*k<rank M) :
    (matroidInverseZ M).coeff k = uniformEntry (rank M) M.E.ncard k -
      ∑ H ∈ hyperplanes M, uniformEntry (rank M) H.ncard k := by
  rw [hM.actual_inverseZ_lower_mu hr k hk, ← sum_filter]
  exact hM.signed_mobius_rank_sum (rank M-2) (by omega) k (by omega)

end Paving
