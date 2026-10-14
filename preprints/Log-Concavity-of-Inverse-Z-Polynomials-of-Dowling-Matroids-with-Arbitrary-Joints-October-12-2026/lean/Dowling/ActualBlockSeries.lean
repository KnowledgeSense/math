import Dowling.FlatColorWeights
import Dowling.DowlingInverseZCandidateDefinitions

noncomputable section
namespace Dowling
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

theorem actual_braidZ_series : fullZSeries Unit=dowlingBraidZ := by
  rw [fullZSeries_eq_candidate,dowlingBraidZ_eq_candidate_one]
  congr 1
  norm_num

theorem dowlingBlockCoordinate_coeff_succ_actual (n : ℕ) :
    coeff (n+1) (dowlingBlockCoordinate (Fintype.card G)) =
      Polynomial.C ((Fintype.card G : ℝ)^n/((n+1).factorial : ℝ))*zeroBlockWeight Unit n := by
  rw [dowlingBlockCoordinate,coeff_C_mul,← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale]
  have hz : coeff n dowlingBraidZ=Polynomial.C ((n.factorial : ℝ)⁻¹)*zeroBlockWeight Unit n := by
    rw [← actual_braidZ_series]
    exact invariantEGF_coeff (fullZ Unit) n
  rw [dowlingBraidPrimitive,candidatePrimitive,coeff_mk,Nat.add_sub_cancel,hz]
  simp only [← Polynomial.C_pow]
  have hm : (Fintype.card G : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero (α := G)
  have hc : (Fintype.card G : ℝ)⁻¹*(Fintype.card G : ℝ)^(n+1)*
      ((n+1 : ℕ) : ℝ)⁻¹*(n.factorial : ℝ)⁻¹ =
      (Fintype.card G : ℝ)^n/((n+1).factorial : ℝ) := by
    rw [pow_succ,Nat.factorial_succ,Nat.cast_mul]
    field_simp
  calc
    _ = Polynomial.C ((Fintype.card G : ℝ)⁻¹*(Fintype.card G : ℝ)^(n+1)*
      ((n+1 : ℕ) : ℝ)⁻¹*(n.factorial : ℝ)⁻¹)*zeroBlockWeight Unit n := by
        simp only [Polynomial.C_mul]
        ring
    _ = _ := by rw [hc]

theorem labeledColorSeries_zeroBlock : labeledColorSeries (zeroBlockWeight G)=fullZSeries G := rfl

theorem labeledColorSeries_balancedBlock :
    labeledColorSeries (balancedBlockWeight G)=dowlingBlockCoordinate (Fintype.card G) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    rw [labeledColorSeries_coeff,balancedBlockWeight_zero,mul_zero,coeff_zero_eq_constantCoeff_apply]
    exact (dowlingBlockCoordinate_constantCoeff _).symm
  | succ n =>
    rw [labeledColorSeries_coeff,dowlingBlockCoordinate_coeff_succ_actual]
    simp only [balancedBlockWeight,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
    rw [← mul_assoc,← Polynomial.C_mul]
    congr 1
    congr 1
    rw [div_eq_mul_inv,mul_comm]

theorem labeledColorProduct_flat (k : ℕ) :
    labeledColorProduct (flatColorWeight (k := k) G)=
      fullZSeries G*dowlingBlockCoordinate (Fintype.card G)^k := by
  rw [labeledColorProduct,Fintype.prod_option]
  simp only [flatColorWeight,labeledColorSeries_zeroBlock,labeledColorSeries_balancedBlock,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end Dowling
