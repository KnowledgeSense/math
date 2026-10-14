import Dowling.DowlingJointlessClosedAlgebra

noncomputable section
namespace Dowling

theorem jointlessRemovedFactor_difference (a μ j : ℝ) (hm : μ≠0)
    (hr : μ+1/2-j≠0) (hr1 : μ+1/2-j+1≠0) :
    jointlessRemovedFactor a μ j/(μ+1/2-j)-
      (j/μ)*jointlessRemovedFactor a μ (j-1)/(μ+1/2-j+1)=
        jointlessCorrection a μ (μ+1/2-j)/μ^4 := by
  let r := μ+1/2-j
  have hj : j=μ+1/2-r := by dsimp [r]; ring
  change r≠0 at hr
  change r+1≠0 at hr1
  change _ = jointlessCorrection a μ r/μ^4
  rw [hj]
  have h1 : μ+1/2-(μ+1/2-r)=r := by ring
  rw [h1]
  unfold jointlessRemovedFactor jointlessCorrection
  field_simp
  ring

theorem jointless_factorial_power_previous {c : ℝ} (hc : c≠0) (j : ℕ) (hj : 1≤j) :
    c^(j-1)/((j-1).factorial:ℝ)=c^j/(j.factorial:ℝ)*(j/c) := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  simp only [Nat.succ_sub_one,Nat.factorial_succ,pow_succ,Nat.cast_mul,Nat.cast_succ]
  field_simp

theorem jointlessRaisedWeight_closed_positive {a : ℝ} (n j : ℕ) (hj : 1≤j)
    (hm : (n+a-1)/2≠0) (hl : (n+a)/2≠0)
    (hr : (n+a)/2-j≠0) (hr1 : (n+a)/2-j+1≠0) :
    jointlessRaisedWeight a n j=
      a/2*(((n+a)/2)^j/(j.factorial:ℝ)*(((n+a)/2-j)/((n+a)/2)^2)-
      ((n+a-1)/2)^j/(j.factorial:ℝ)*
        (jointlessCorrection a ((n+a-1)/2) ((n+a)/2-j)/((n+a-1)/2)^4)) := by
  have hj0 : j≠0 := by omega
  have hjcast : ((j-1:ℕ):ℝ)=(j:ℝ)-1 := by simp only [Nat.cast_sub hj,Nat.cast_one]
  rw [jointlessRaisedWeight,ite_eq_right hj0,
    jointlessUnraisedWeight_factor n j hm hl,jointlessUnraisedWeight_factor n (j-1) hm hl,
    jointless_factorial_power_previous hl j hj,jointless_factorial_power_previous hm j hj,hjcast]
  have hdiff := jointlessRemovedFactor_difference a ((n+a-1)/2) j hm
    (by convert hr using 1; ring) (by convert hr1 using 1; ring)
  have hLam : ((n:ℝ)+a-1)/2+1/2=((n:ℝ)+a)/2 := by ring
  rw [hLam] at hdiff
  rw [← hdiff]
  generalize ((n:ℝ)+a)/2=l at *
  generalize ((n:ℝ)+a-1)/2=m at *
  field_simp
  ring

end Dowling
