import Dowling.ActualApexWeightsPolynomial

noncomputable section
namespace Dowling

/-- A boundary-safe natural-power form of the rank-one-parameter raised weight. -/
theorem dowlingBaseWeight_one_formula (n j : ℕ) :
    dowlingBaseWeight 1 n j=
      ((((n : ℝ)+1)/2-j)*(((n : ℝ)+1)/2)^j)/
        (2*(j.factorial : ℝ)*(((n : ℝ)+1)/2)^2) := by
  have hL0 : ((n : ℝ)+1)/2≠0 := by positivity
  have hn : (n : ℝ)+1≠0 := by positivity
  cases j with
  | zero =>
    simp only [dowlingBaseWeight,dowlingQuadraticWeight_zero,mul_one,Nat.cast_zero,sub_zero,pow_zero,
      Nat.factorial_zero,Nat.cast_one,mul_one]
    field_simp
  | succ j =>
    rw [dowlingBaseWeight,dowlingQuadraticWeight_succ]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [pow_succ]
    have hf : ((j+1).factorial : ℝ)≠0 := by positivity
    field_simp

/-- The exact source f_h ratio, including the terminal B_0 shift. -/
theorem apexF_base_ratio (n h j : ℕ) (hhj : h≤j) (hjn : 2*j≤n) :
    dowlingBaseWeight 1 n j*apexF n h j=dowlingBaseWeight 1 (n-2*h) (j-h) := by
  let L : ℝ := ((n : ℝ)+1)/2
  have hL : 0<L := by dsimp [L]; positivity
  have hLH : 0<L-h := by
    have hh : (2*h : ℝ)≤n := by exact_mod_cast (show 2*h≤n by omega)
    dsimp [L]
    linarith
  have hN : ((n-2*h : ℕ) : ℝ)=(n : ℝ)-2*h := by
    rw [Nat.cast_sub (by omega : 2*h≤n),Nat.cast_mul,Nat.cast_ofNat]
  have hJ : ((j-h : ℕ) : ℝ)=(j : ℝ)-h := Nat.cast_sub hhj
  have hf : ((j-h).factorial : ℝ)*(j.descFactorial h : ℝ)=(j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hhj
  have hf0 : (j.factorial : ℝ)≠0 := by positivity
  have hf1 : ((j-h).factorial : ℝ)≠0 := by positivity
  have hd : (j.descFactorial h : ℝ)/(j.factorial : ℝ)=1/((j-h).factorial : ℝ) := by
    field_simp
    nlinarith only [hf]
  rw [dowlingBaseWeight_one_formula,dowlingBaseWeight_one_formula,apexF,ite_eq_left hhj,hN,hJ]
  have hshift : ((n : ℝ)-2*h+1)/2=L-h := by dsimp [L]; ring
  rw [hshift]
  change ((L-j)*L^j)/(2*(j.factorial : ℝ)*L^2)*
    ((j.descFactorial h : ℝ)*(L-h)^(j-h)/L^j*L^2/(L-h)^2)=_
  calc
    _ = ((j.descFactorial h : ℝ)/(j.factorial : ℝ))*(L-j)*(L-h)^(j-h)/(2*(L-h)^2) := by
      field_simp [ne_of_gt hL,ne_of_gt hLH]
    _ = _ := by
      rw [hd]
      field_simp
      ring

end Dowling
