import Dowling.FullInvariantReal
import Dowling.FlatTransformUniqueness

noncomputable section
namespace Dowling
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

@[simp] theorem flatCoordinateTail_constant (m : ℝ) : (flatCoordinateTail m).constantCoeff = 1 := by
  have h := dowlingFlatCoordinate_coeff_one m
  rw [dowlingFlatCoordinate_eq_X_mul,show 1=0+1 from rfl,coeff_succ_X_mul,
    coeff_zero_eq_constantCoeff_apply] at h
  exact h

/-- Actual full-Dowling invariants are characterized by the proved flat
transform, strict-half KL support and ordinary Z reciprocity. -/
theorem full_invariants_unique (P Z : PowerSeries (Polynomial ℝ))
    (h0 : coeff 0 P=1)
    (hP : ∀ n, 0<n → ∀ k, n≤2*k → (coeff n P).coeff k=0)
    (hZ : ∀ n t, t≠0 → t^n*(coeff n Z).eval t⁻¹=(coeff n Z).eval t)
    (he : Z=candidateExp (C Polynomial.X*X)*P.subst (dowlingFlatCoordinate (Fintype.card G))) :
    fullPSeries G=P ∧ fullZSeries G=Z := by
  apply flat_transform_unique (candidateExp (C Polynomial.X*X)) (flatCoordinateTail (Fintype.card G))
  · exact candidateExp_constantCoeff (by simp)
  · exact flatCoordinateTail_constant _
  · rw [fullPSeries_constant,h0]
  · exact fun n hn k hk => fullPSeries_high_coeff n k hn hk
  · exact hP
  · exact fullZSeries_coeff_reciprocal
  · exact hZ
  · rw [← dowlingFlatCoordinate_eq_X_mul]
    exact fullZSeries_flat_relation
  · rw [← dowlingFlatCoordinate_eq_X_mul]
    exact he

end Dowling
