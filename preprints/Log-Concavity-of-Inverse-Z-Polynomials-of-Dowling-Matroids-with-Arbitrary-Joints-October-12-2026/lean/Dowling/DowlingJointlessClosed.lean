import Dowling.DowlingJointlessClosedDifference
import Dowling.DowlingJointlessInitial

noncomputable section
namespace Dowling

theorem jointlessWeight_closed {a : ℝ} (n j : ℕ)
    (hm : (n+a-1)/2≠0) (hl : (n+a)/2≠0) (hr : (n+a)/2-j≠0) :
    jointlessWeight a n j=
      a/2*(((n+a)/2)^j/(j.factorial:ℝ)*(((n+a)/2-j)/((n+a)/2)^2)-
      ((n+a-1)/2)^j/(j.factorial:ℝ)*
        (jointlessCorrection a ((n+a-1)/2) ((n+a)/2-j)/((n+a-1)/2)^4)) := by
  unfold jointlessWeight dowlingBaseWeight jointlessNormalizedWeight jointlessRatioFunction
  rw [dowlingQuadraticWeight_factor hl]
  have hLam : ((n:ℝ)+a-1)/2+1/2=((n:ℝ)+a)/2 := by ring
  rw [hLam]
  have hpref : a/((n:ℝ)+a)=a/(2*(((n:ℝ)+a)/2)) := by ring
  rw [hpref]
  generalize ((n:ℝ)+a)/2=l at *
  generalize ((n:ℝ)+a-1)/2=m at *
  rw [div_pow]
  field_simp

theorem jointlessRaisedWeight_eq_zero_index {a : ℝ} (ha : 0<a) (n : ℕ) (hn : 2≤n) :
    jointlessRaisedWeight a n 0=jointlessWeight a n 0 := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hm : 0<((n:ℝ)+a-1)/2 := by linarith
  rw [jointlessWeight,dowlingBaseWeight,jointlessNormalizedWeight_zero a _ hm]
  unfold jointlessRaisedWeight jointlessUnraisedWeight
  simp only [Nat.cast_zero,sub_zero,show (0:ℕ)<2 by omega,
    ite_eq_left,dowlingQuadraticWeight_zero,mul_one,sub_zero]
  have hnp : (n:ℝ)+a≠0 := by linarith
  have hnm : (n:ℝ)+a-1≠0 := by linarith
  field_simp
  ring

/-- The literal signed-kernel raising weights equal the closed positive weights on all support. -/
theorem jointlessRaisedWeight_eq {a : ℝ} (ha : 0<a) (n j : ℕ) (hn : 2≤n) (hj : 2*j≤n) :
    jointlessRaisedWeight a n j=jointlessWeight a n j := by
  by_cases hj0 : j=0
  · subst j
    exact jointlessRaisedWeight_eq_zero_index ha n hn
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hjR : 2*(j:ℝ)≤n := by exact_mod_cast hj
  have hm : (n+a-1)/2≠0 := by linarith
  have hl : (n+a)/2≠0 := by linarith
  have hr : (n+a)/2-j≠0 := by linarith
  have hr1 : (n+a)/2-j+1≠0 := by linarith
  rw [jointlessRaisedWeight_closed_positive n j (by omega) hm hl hr hr1,
    jointlessWeight_closed n j hm hl hr]

end Dowling
