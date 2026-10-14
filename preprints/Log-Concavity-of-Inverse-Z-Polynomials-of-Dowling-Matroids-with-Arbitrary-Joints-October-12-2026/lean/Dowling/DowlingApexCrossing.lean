import Dowling.DowlingApexComponentRatios

noncomputable section
namespace Dowling

theorem apexCurvatureRatio_positive_monotone (L j i h : ℝ) (hj : 0<j) (hL : j<L)
    (hi : 0 < i) (hih : i≤h) (hh : h≤j) (hpos : 0<apexCurvatureRatio L j i) :
    apexCurvatureRatio L j i≤apexCurvatureRatio L j h := by
  have hL0 : 0<L := by linarith
  have hLi : 0<L-i := by linarith
  have hLh : 0<L-h := by linarith
  have hji : 0<j+1-i := by linarith
  have hjh : 0<j+1-h := by linarith
  have hC : 0<j+(L-j)^2 := by positivity
  have hdi : 0<L*j*(L-i)*(j+1-i) := by positivity
  have hdh : 0<L*j*(L-h)*(j+1-h) := by positivity
  unfold apexCurvatureRatio at *
  have hnum : 0 < i*(i*(j+(L-j)^2)-L^2) := by
    have hz := (lt_div_iff₀ hdi).mp hpos
    simpa using hz
  have hinner : 0 < i*(j+(L-j)^2)-L^2 := by nlinarith
  have hinnerle : i*(j+(L-j)^2)-L^2≤h*(j+(L-j)^2)-L^2 := by nlinarith
  have hn : i*(i*(j+(L-j)^2)-L^2)≤h*(h*(j+(L-j)^2)-L^2) :=
    mul_le_mul hih hinnerle hinner.le (by linarith)
  have hd : L*j*(L-h)*(j+1-h)≤L*j*(L-i)*(j+1-i) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · linarith
    · exact hjh.le
    · positivity
  apply (div_le_div_iff₀ hdi hdh).mpr
  calc
    _ ≤ (h*(h*(j+(L-j)^2)-L^2))*(L*j*(L-h)*(j+1-h)) :=
      mul_le_mul_of_nonneg_right hn hdh.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by linarith)

end Dowling
