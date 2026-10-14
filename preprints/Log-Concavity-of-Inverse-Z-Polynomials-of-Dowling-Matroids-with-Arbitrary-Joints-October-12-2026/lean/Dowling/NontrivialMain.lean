import Dowling.RetainedActualCoefficients
import Dowling.RetainedDegree
import Dowling.DowlingJointlessClosed
import Dowling.DowlingRetainedLinearity

noncomputable section
namespace Dowling
open Finset Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] [Nontrivial G] {n : ℕ}

theorem retained_actual_coeff_closed (hn : 2≤n) (X : Set (Fin n)) (k : ℕ) :
    ((configurationY (G := G) X).coeff k : ℝ)=
      (n.factorial : ℝ)*(Fintype.card G : ℝ)^n*
        retainedNontrivialScalar (Fintype.card G : ℝ)⁻¹ (((n-X.toFinset.card : ℕ) : ℝ)/n) n k := by
  rw [retained_actual_coeff_raised G hn X k]
  congr 1
  by_cases hk : k≤n
  · simp only [quadraticWeightedRow,retainedNontrivialScalar,weightedMixtureCoefficient,ite_eq_left hk]
    apply sum_congr rfl
    intro j hj
    have hjn : 2*j≤n := by have := mem_range.mp hj; omega
    have ha : (0 : ℝ)<(Fintype.card G : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos (α := G))
    rw [jointlessRaisedWeight_eq ha n j hn hjn,retainedNontrivialWeight_linear]
  · simp [quadraticWeightedRow,retainedNontrivialScalar,weightedMixtureCoefficient,hk]

omit [Group G] in
theorem group_inverse_card_cases : (Fintype.card G : ℝ)⁻¹≤1/3 ∨ (Fintype.card G : ℝ)⁻¹=1/2 := by
  have hm : 2≤Fintype.card G := Fintype.one_lt_card
  by_cases h2 : Fintype.card G=2
  · right
    norm_num [h2]
  · left
    have h3 : (3 : ℝ)≤Fintype.card G := by exact_mod_cast (show 3≤Fintype.card G by omega)
    exact (inv_le_comm₀ (by positivity) (by positivity)).mpr (by norm_num; exact_mod_cast h3)

theorem retained_missing_fraction_bounds (hn : 2≤n) (X : Set (Fin n)) :
    0≤(((n-X.toFinset.card : ℕ) : ℝ)/n) ∧ (((n-X.toFinset.card : ℕ) : ℝ)/n)≤1 := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  exact ⟨by positivity,(div_le_one hn0).mpr (by exact_mod_cast Nat.sub_le n X.toFinset.card)⟩

theorem retained_nontrivial_positive (hn : 2≤n) (X : Set (Fin n)) (k : ℕ) (hk : k≤n) :
    0<(configurationY (G := G) X).coeff k := by
  have hm : (0 : ℝ)<Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have ha := inv_pos.mpr hm
  have ha2 : (Fintype.card G : ℝ)⁻¹≤1/2 := by
    rcases group_inverse_card_cases (G := G) with h | h <;> linarith
  obtain ⟨hθ,hθ1⟩ := retained_missing_fraction_bounds hn X
  have hs := retainedNontrivialScalar_pos ha ha2 hθ hθ1 n k hn hk
  have hc : (0 : ℝ)<((configurationY (G := G) X).coeff k : ℝ) := by
    rw [retained_actual_coeff_closed hn X k]
    exact mul_pos (by positivity) hs
  exact_mod_cast hc

theorem retained_nontrivial_strict (hn : 2≤n) (X : Set (Fin n)) (k : ℕ) (hk : 1≤k) (hkn : k<n) :
    (configurationY (G := G) X).coeff (k-1)*(configurationY (G := G) X).coeff (k+1)<
      ((configurationY (G := G) X).coeff k)^2 := by
  have hm : (0 : ℝ)<Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  obtain ⟨hθ,hθ1⟩ := retained_missing_fraction_bounds hn X
  have hs := retainedNontrivialScalar_strict_log_concave (inv_pos.mpr hm)
    (group_inverse_card_cases (G := G)) hθ hθ1 n k hn hk hkn
  have hc : (0 : ℝ)<(n.factorial : ℝ)*(Fintype.card G : ℝ)^n := by positivity
  have ht := mul_lt_mul_of_pos_left hs (sq_pos_of_pos hc)
  have he : ((configurationY (G := G) X).coeff (k-1) : ℝ)*
      ((configurationY (G := G) X).coeff (k+1) : ℝ)<((configurationY (G := G) X).coeff k : ℝ)^2 := by
    rw [retained_actual_coeff_closed hn X (k-1),retained_actual_coeff_closed hn X (k+1),
      retained_actual_coeff_closed hn X k]
    nlinarith only [ht]
  exact_mod_cast he

end Dowling
