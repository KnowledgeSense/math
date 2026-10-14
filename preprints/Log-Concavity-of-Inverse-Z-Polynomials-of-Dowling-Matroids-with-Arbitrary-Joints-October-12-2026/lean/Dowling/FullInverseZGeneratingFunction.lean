import Dowling.FullInverseZColumns
import Dowling.ZeroSubstitutionCoefficients

noncomputable section
namespace Dowling
open scoped Classical BigOperators
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

/-- The genuine full-Dowling inverse-Z EGF is determined by its actual flat
convolution. Labelled block counting, rather than a formal candidate premise,
supplies the exact primitive substitution. -/
theorem fullYSeries_flat_relation :
    fullZSeries G*(fullYSeries G).subst (-dowlingBlockCoordinate (Fintype.card G))=1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_subst_zero _ _ _ (by simp)]
  have he : (∑ k ∈ Finset.range (n+1), coeff k (fullYSeries G)*
      coeff n (fullZSeries G*(-dowlingBlockCoordinate (Fintype.card G))^k)) =
      Polynomial.C ((n.factorial : ℝ)⁻¹)*
        ∑ k ∈ Finset.range (n+1), partitionColumn G n k *
          (Polynomial.C ((-1:ℝ)^k)*(fullY G k).map (Int.castRingHom ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_mul_neg_pow,partitionColumn_coeff]
    change (coeff k (invariantEGF (fullY G)))*_=_
    rw [invariantEGF_coeff]
    have hk : (k.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hc : Polynomial.C ((k.factorial : ℝ)⁻¹)*
        Polynomial.C ((k.factorial : ℝ)/(n.factorial : ℝ)) =
        Polynomial.C ((n.factorial : ℝ)⁻¹) := by
      rw [← Polynomial.C_mul]
      congr 1
      field_simp
    simp only [map_pow,map_neg,map_one]
    calc
      _ = (Polynomial.C ((k.factorial : ℝ)⁻¹)*
          Polynomial.C ((k.factorial : ℝ)/(n.factorial : ℝ)))*
          (partitionColumn G n k*((-1)^k*(fullY G k).map (Int.castRingHom ℝ))) := by ring
      _ = _ := by rw [hc]
  rw [he,partitionColumn_convolution]
  by_cases hn : n=0
  · subst n
    norm_num
  · simp [hn]

end Dowling
