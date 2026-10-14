import Dowling.WhitneySeriesDefinitions

noncomputable section
namespace Dowling
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

theorem derivative_whitneySeries_succ (k : ℕ) :
    derivative (whitneySeries G (k+1)) = whitneySeries G k +
      C (Polynomial.C (1+(Fintype.card G : ℝ)*(k+1))*Polynomial.X)*whitneySeries G (k+1) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_derivative,map_add,coeff_C_mul,whitneySeries_coeff]
  simpa only [map_add] using whitneyTerm_derivative_step (G := G) n k

theorem factorial_scale (n : ℕ) : ((n+1).factorial : ℝ)⁻¹*(n+1) = (n.factorial : ℝ)⁻¹ := by
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  field_simp

theorem derivative_whitneySeries_zero :
    derivative (whitneySeries G 0) = whitneySeries G 0*C Polynomial.X := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_derivative,coeff_mul_C,whitneySeries_coeff,whitneyTerm_zero_column,
    pow_succ]
  have h := congrArg Polynomial.C (factorial_scale n)
  simp only [map_mul,map_add,map_natCast,map_one] at h
  calc
    _ = (Polynomial.C (((n+1).factorial:ℝ)⁻¹)*((n:Polynomial ℝ)+1))*Polynomial.X^n*Polynomial.X := by ring
    _ = _ := by rw [h]

theorem whitneySeries_zero_eq_exp :
    whitneySeries G 0 = candidateExp (C Polynomial.X*X) := by
  apply candidate_ode_unique _ _ (C Polynomial.X)
  · rw [whitneySeries_constant,candidateExp_constantCoeff (by simp)]
    simp
  · exact derivative_whitneySeries_zero
  · rw [derivative_candidateExp (by simp)]
    simp

/-- The flat coordinate obeys the exact labelled-block differential equation. -/
theorem derivative_dowlingFlatCoordinate (m : ℝ) :
    derivative (dowlingFlatCoordinate m) = 1+C (Polynomial.C m*Polynomial.X)*dowlingFlatCoordinate m := by
  apply PowerSeries.ext
  intro n
  rw [coeff_derivative,map_add,coeff_C_mul]
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [dowlingFlatCoordinate_coeff_succ,dowlingFlatCoordinate_coeff_succ]
    simp only [coeff_one,ite_eq_right (Nat.succ_ne_zero n),zero_add]
    have h : m^(n+1)/(n+2).factorial*((n:ℝ)+2) = m*(m^n/(n+1).factorial) := by
      rw [show n+2=(n+1)+1 by omega,Nat.factorial_succ,pow_succ]
      push_cast
      have hn : (n:ℝ)+1+1 ≠ 0 := by positivity
      have hf : ((n+1).factorial:ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have hc := congrArg Polynomial.C h
    simp only [map_mul,map_add,map_natCast,map_ofNat] at hc
    rw [pow_succ]
    calc
      _ = (Polynomial.C (m^(n+1)/(n+1+1).factorial)*((n:Polynomial ℝ)+2))*Polynomial.X^n*Polynomial.X := by push_cast; ring
      _ = _ := by rw [hc]; ring

end Dowling
