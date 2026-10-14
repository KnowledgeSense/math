import Dowling.MainBoundaries
import Dowling.DowlingApexStrict

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] [Subsingleton G] {n : ℕ}

theorem apex_actual_coeff (hn : 2≤n) (X : Set (Fin n)) (hX : X.Nonempty) (k : ℕ) :
    ((configurationY (G := G) X).coeff k : ℝ)=
      (n.factorial : ℝ)*apexScalar n X.toFinset.card k :=
  apex_actual_coeff_raised hn X hX k

theorem apex_retained_positive (hn : 2≤n) (X : Set (Fin n)) (hX : X.Nonempty)
    (k : ℕ) (hk : k≤n) : 0<(configurationY (G := G) X).coeff k := by
  have hcard : 1≤X.toFinset.card := Finset.card_pos.mpr (by simpa using hX : X.toFinset.Nonempty)
  have hle : X.toFinset.card≤n := by simpa using Finset.card_le_univ X.toFinset
  have hs := apexScalar_pos n X.toFinset.card k hn hcard hle hk
  have hc : (0 : ℝ)<((configurationY (G := G) X).coeff k : ℝ) := by
    rw [apex_actual_coeff hn X hX k]
    exact mul_pos (by positivity) hs
  exact_mod_cast hc

theorem apex_retained_strict (hn : 2≤n) (X : Set (Fin n)) (hX : X.Nonempty)
    (k : ℕ) (hk : 1≤k) (hkn : k<n) :
    (configurationY (G := G) X).coeff (k-1)*(configurationY (G := G) X).coeff (k+1)<
      ((configurationY (G := G) X).coeff k)^2 := by
  have hcard : 1≤X.toFinset.card := Finset.card_pos.mpr (by simpa using hX : X.toFinset.Nonempty)
  have hle : X.toFinset.card≤n := by simpa using Finset.card_le_univ X.toFinset
  have hs := apexScalar_strict_log_concave n X.toFinset.card k hn hcard hle hk hkn
  have ht := mul_lt_mul_of_pos_left hs (sq_pos_of_pos (by positivity : (0 : ℝ)<n.factorial))
  have he : ((configurationY (G := G) X).coeff (k-1) : ℝ)*
      ((configurationY (G := G) X).coeff (k+1) : ℝ)<((configurationY (G := G) X).coeff k : ℝ)^2 := by
    rw [apex_actual_coeff hn X hX (k-1),apex_actual_coeff hn X hX (k+1),apex_actual_coeff hn X hX k]
    nlinarith only [ht]
  exact_mod_cast he

theorem apex_retained_main (hn : 2≤n) (X : Set (Fin n)) (hX : X.Nonempty) :
    StrictInverseZRow (matroid G n X).eRank.toNat (configurationY (G := G) X) := by
  rw [matroid_eRank_marked X hX]
  exact ⟨retained_natDegree hn X (Or.inr hX),apex_retained_positive hn X hX,
    retained_coeff_symm hn X (Or.inr hX),apex_retained_strict hn X hX⟩

end Dowling
