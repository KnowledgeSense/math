import Dowling.JointlessActualSeriesEGF
import Dowling.FullInverseZIdentification

noncomputable section
namespace Dowling
open PowerSeries Finset

/-- Source auxiliary EGF: its linear coefficient is zero. Its identification
with the jointless matroid is explicitly restricted to n≥2. -/
def jointlessSeries (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  dowlingInverseZCandidate m*(1-C (1+Polynomial.X)*X+X*jointTauSeries m)

variable (G : Type*) [Group G] [Fintype G]

theorem fullYSeries_scaled_coeff (n : ℕ) :
    Polynomial.C (n.factorial : ℝ)*coeff n (fullYSeries G)=(fullY G n).map (Int.castRingHom ℝ) := by
  rw [fullYSeries,invariantEGF_coeff,← mul_assoc,← map_mul,mul_inv_cancel₀ (by positivity),map_one,one_mul]

theorem fullYSeries_shift_scaled_coeff (n : ℕ) :
    Polynomial.C ((n+1).factorial : ℝ)*coeff (n+1) (X*fullYSeries G)=
      Polynomial.C (n+1 : ℝ)*(fullY G n).map (Int.castRingHom ℝ) := by
  rw [coeff_succ_X_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,map_mul,
    mul_assoc,fullYSeries_scaled_coeff]

theorem jointTauSeries_product_coeff (n : ℕ) :
    Polynomial.C ((n+1).factorial : ℝ)*coeff (n+1) (X*(jointTauSeries (Fintype.card G)*fullYSeries G))=
      Polynomial.C (n+1 : ℝ)*
        (∑ r∈range (n+2),Polynomial.C ((n.choose (r-1) : ℕ) : ℤ)*
          jointRankCorrection G (n+1) r).map (Int.castRingHom ℝ) := by
  rw [jointTauSeries_eq_EGF]
  change Polynomial.C ((n+1).factorial : ℝ)*
    coeff (n+1) (X*(invariantEGF (jointTauPolynomial G)*invariantEGF (fullY G)))=_
  rw [invariantEGF_shift_product_coeff]
  congr 1
  conv_rhs => rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ']
  have hz : jointRankCorrection G (n+1) 0=0 := by simp [jointRankCorrection]
  simp only [hz,mul_zero,add_zero]
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.map_mul,Polynomial.map_C]
  have he := jointTauPolynomial_correction G (n+1) d
  rw [show n+1-(d+1)=n-d by omega] at he
  rw [← he,Polynomial.map_mul]
  simp only [Nat.add_sub_cancel_right,map_natCast]
  ring

/-- Exact factorial-normalized coefficient identity obtained from the actual
one-joint deletion polynomial and its actual KL primitive. -/
theorem jointlessSeries_coeff_deletion (n : ℕ) :
    Polynomial.C ((n+1).factorial : ℝ)*coeff (n+1) (jointlessSeries (Fintype.card G))=
      (fullY G (n+1)-Polynomial.C (n+1 : ℤ)*jointDelta G (n+1)).map (Int.castRingHom ℝ) := by
  have he : jointlessSeries (Fintype.card G)=fullYSeries G-
      C (1+Polynomial.X)*(X*fullYSeries G)+X*(jointTauSeries (Fintype.card G)*fullYSeries G) := by
    rw [jointlessSeries,← fullYSeries_eq_candidate]
    ring
  rw [he,map_add,map_sub,coeff_C_mul,mul_add,mul_sub]
  rw [fullYSeries_scaled_coeff]
  have hc : Polynomial.C ((n+1).factorial : ℝ)*((1+Polynomial.X)*coeff (n+1) (X*fullYSeries G))=
      (1+Polynomial.X)*(Polynomial.C ((n+1).factorial : ℝ)*coeff (n+1) (X*fullYSeries G)) := by ring
  rw [hc,fullYSeries_shift_scaled_coeff,jointTauSeries_product_coeff]
  rw [jointDelta,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C]
  simp only [Nat.add_sub_cancel_right,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_add,Polynomial.map_one,Polynomial.map_X,map_add,map_one,map_natCast]
  ring

theorem jointlessSeries_actual (n : ℕ) [Nontrivial G] (hn : 2≤n) :
    Polynomial.C (n.factorial : ℝ)*coeff n (jointlessSeries (Fintype.card G))=
      (configurationY (G := G) (∅ : Set (Fin n))).map (Int.castRingHom ℝ) := by
  rw [jointless_nontrivial_identity hn]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using jointlessSeries_coeff_deletion G k

end Dowling
