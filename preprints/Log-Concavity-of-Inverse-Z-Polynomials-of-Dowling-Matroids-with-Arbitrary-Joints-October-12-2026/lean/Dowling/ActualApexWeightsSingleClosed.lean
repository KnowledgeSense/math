import Dowling.ActualApexWeightsSingleAlgebra

noncomputable section
namespace Dowling

theorem apexClosedRatio_algebra (μ r : ℝ) (hμ : μ≠0) (hr : r≠0) (hr1 : r+1≠0) :
    (1-(μ+1/2-r)*(μ-1/2-r)/μ^2)/r-
      (μ+1/2-r)/μ*(1-(μ-1/2-r)*(μ-3/2-r)/μ^2)/(r+1)=
      r/μ^2*apexClosedRatio μ r := by
  rw [apexClosedRatio]
  field_simp
  ring

theorem apexSingleRaised_closed (n j : ℕ) (hn : 2≤n) (hj : 2*j≤n) :
    apexSingleRaised n j=dowlingBaseWeight 1 n j*
      (((n : ℝ)/(n+1))^j*(((n : ℝ)+1)/2)^2/((n : ℝ)/2)^2*
        apexClosedRatio ((n : ℝ)/2) (((n : ℝ)+1)/2-j)/n) := by
  let μ : ℝ := (n : ℝ)/2
  let L : ℝ := ((n : ℝ)+1)/2
  let r : ℝ := L-j
  have hμ : 0<μ := by dsimp [μ]; positivity
  have hL : 0<L := by dsimp [L]; positivity
  have hr : 0<r := by
    have hj' : (2*j : ℝ)≤n := by exact_mod_cast hj
    dsimp [r,L]
    linarith
  have hn0 : (n : ℝ)≠0 := by positivity
  have hf : (j.factorial : ℝ)≠0 := by positivity
  have hJ : (j : ℝ)=μ+1/2-r := by dsimp [r,L,μ]; ring
  have hden : (n : ℝ)+1-2*j=2*r := by dsimp [r,L]; ring
  have hden1 : (n : ℝ)+1-2*((j : ℝ)-1)=2*(r+1) := by dsimp [r,L]; ring
  have hs : (if j=0 then 0 else apexSingleUnraised n (j-1)/((n : ℝ)+1-2*((j : ℝ)-1)))=
      (if j=0 then 0 else apexSingleUnraised n (j-1))/((n : ℝ)+1-2*((j : ℝ)-1)) := by
    split <;> simp_all only [zero_div]
  rw [apexSingleRaised,hs,apexSingleUnraised_formula n j (by omega),
    apexSingleUnraised_shift_formula n j (by omega),hden,hden1,dowlingBaseWeight_one_formula]
  change (1/(n : ℝ))*((1-(j : ℝ)*(j-1)/μ^2)*(μ^j/(j.factorial : ℝ))/(2*r)-
    ((j : ℝ)/μ*(1-(j-1)*(j-2)/μ^2)*(μ^j/(j.factorial : ℝ)))/(2*(r+1)))=
    (r*L^j)/(2*(j.factorial : ℝ)*L^2)*
      (((n : ℝ)/(n+1))^j*L^2/μ^2*apexClosedRatio μ r/n)
  have hratio : (n : ℝ)/(n+1)=μ/L := by dsimp [μ,L]; field_simp
  rw [hratio,div_pow]
  have ha := apexClosedRatio_algebra μ r hμ.ne' hr.ne' (by linarith)
  have hx : (1-(j : ℝ)*(j-1)/μ^2)/r-
      (j : ℝ)/μ*(1-(j-1)*(j-2)/μ^2)/(r+1)=r/μ^2*apexClosedRatio μ r := by
    rw [hJ]
    convert ha using 1; ring
  calc
    _ = μ^j/(2*n*(j.factorial : ℝ))*
        ((1-(j : ℝ)*(j-1)/μ^2)/r-(j : ℝ)/μ*(1-(j-1)*(j-2)/μ^2)/(r+1)) := by field_simp; ring
    _ = _ := by
      rw [hx]
      simp only [div_pow]
      field_simp [hL.ne',hμ.ne']
      dsimp [μ]
      ring

theorem apexNormalizedWeight_one_closed (n j : ℕ) (hn : 2≤n) (hj : 2*j≤n) :
    apexNormalizedWeight n 1 j=
      ((n : ℝ)/(n+1))^j*(((n : ℝ)+1)/2)^2/((n : ℝ)/2)^2*
        apexClosedRatio ((n : ℝ)/2) (((n : ℝ)+1)/2-j)/n := by
  have h := apexRaisedWeight_one n j hn hj
  rw [apexSingleRaised_closed n j hn hj,apexRaisedWeight] at h
  apply mul_left_cancel₀ _ h
  rw [dowlingBaseWeight_one_formula]
  have hr : 0<((n : ℝ)+1)/2-j := by
    have hj' : (2*j : ℝ)≤n := by exact_mod_cast hj
    linarith
  positivity

end Dowling
