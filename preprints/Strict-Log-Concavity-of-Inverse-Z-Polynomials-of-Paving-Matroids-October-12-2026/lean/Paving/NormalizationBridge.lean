import Paving.SourceCoefficientFormulas
import Paving.ActualEvenRows
import Paving.UniformNormalization

namespace Paving
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α]

theorem uniformEntry_cast_normalized (r n k : ℕ) (hr : r≤n) (hk : k<r) :
    (uniformEntry r n k:ℝ) = (n.choose (r-1):ℝ)*uniformComponent r n k := by
  rw [uniformEntry_source r n k hr hk]
  push_cast
  exact uniform_coefficient_normalized hk hr

theorem actualLowerMixture_expansion (M : Matroid α) (k : ℕ) (hk : k<rank M) :
    actualLowerMixture M k = uniformComponent (rank M) M.E.ncard k -
      ∑ H : StressedIndex M, hyperplaneWeight M H*uniformComponent (rank M) H.1.ncard k := by
  classical
  simp only [actualLowerMixture,Fintype.sum_option,actualWeight,actualParameter,lowerComponent]
  have he (H : StressedIndex M) : hyperplaneComponent (rank M) M.E.ncard H.1.ncard k =
      uniformComponent (rank M) M.E.ncard k-uniformComponent (rank M) H.1.ncard k := by
    have hh := (mem_stressedHyperplanes M H.1).mp H.2
    exact hyperplaneComponent_difference hk hh.2 (hyperplane_card_lt hh.1).le
  simp_rw [he,mul_sub]
  rw [sum_sub_distrib,← sum_mul]
  ring

/-- Normalization of the exact stressed-hyperplane subtraction as the actual
nonnegative matroid mixture. -/
theorem actualLowerMixture_normalized (M : Matroid α) (k : ℕ) (hk : k<rank M) :
    ((uniformEntry (rank M) M.E.ncard k-
      ∑ H ∈ stressedHyperplanes M,uniformEntry (rank M) H.ncard k : ℤ):ℝ) =
      normalization M*actualLowerMixture M k := by
  classical
  rw [actualLowerMixture_expansion M k hk,mul_sub,mul_sum]
  have hsum : (∑ H : StressedIndex M, (uniformEntry (rank M) H.1.ncard k:ℝ)) =
      ((∑ H ∈ stressedHyperplanes M,uniformEntry (rank M) H.ncard k:ℤ):ℝ) := by
    push_cast
    exact sum_attach (stressedHyperplanes M) (fun H => (uniformEntry (rank M) H.ncard k:ℝ))
  rw [Int.cast_sub,← hsum,uniformEntry_cast_normalized _ _ _ (rank_le_ground_card M) hk]
  congr 1
  apply sum_congr rfl
  intro H _
  have hh := (mem_stressedHyperplanes M H.1).mp H.2
  rw [uniformEntry_cast_normalized _ _ _ hh.2 hk,hyperplaneWeight]
  have hb : normalization M≠0 := ne_of_gt (normalization_positive M)
  field_simp

/-- The actual original coefficient equals the positive scalar normalization,
with no coefficient bridge among the hypotheses. -/
theorem IsPaving.actual_coefficient_lower {M : Matroid α} (hM : IsPaving M)
    (hr : 3≤rank M) (k : ℕ) (hk : 2*k<rank M) :
    ((matroidInverseZ M).coeff k:ℝ)=normalization M*actualLowerMixture M k := by
  rw [hM.source_noncentral_coefficient hr k hk,actualLowerMixture_normalized M k (by omega)]

theorem uniform_middle_difference (m n : ℕ) (hm : 1≤m) (hn : 2*m≤n) :
    uniformComponent (2*m) n m-uniformComponent (2*m) n (m-1) =
      middleIncrement (middleBinomial m) ((n:ℝ)-m) m := by
  have hc : (2*m-1).choose m=(2*m-1).choose (m-1) := by
    rw [← Nat.choose_symm (show m≤2*m-1 by omega)]
    congr 1
    omega
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hnR : (2:ℝ)*m≤n := by exact_mod_cast hn
  unfold uniformComponent middleIncrement middleBinomial
  rw [hc,Nat.cast_sub hm]
  push_cast
  field_simp (disch := first | positivity | linarith)
  ring

end Paving
