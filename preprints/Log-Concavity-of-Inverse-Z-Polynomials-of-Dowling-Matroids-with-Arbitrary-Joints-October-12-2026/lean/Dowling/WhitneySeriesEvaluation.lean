import Dowling.WhitneySeriesODE

noncomputable section
namespace Dowling
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

def whitneyBasis (m : ℝ) (k : ℕ) : PowerSeries (Polynomial ℝ) :=
  C (Polynomial.C ((k.factorial : ℝ)⁻¹))*candidateExp (C Polynomial.X*X)*(dowlingFlatCoordinate m)^k

@[simp] theorem whitneyBasis_constant (m : ℝ) (k : ℕ) :
    (whitneyBasis m k).constantCoeff = if k=0 then 1 else 0 := by
  have he : constantCoeff (candidateExp (C Polynomial.X*X : PowerSeries (Polynomial ℝ))) = 1 :=
    candidateExp_constantCoeff (by simp)
  simp only [whitneyBasis,map_mul,map_pow,constantCoeff_C,he,
    dowlingFlatCoordinate_constantCoeff,mul_one]
  cases k <;> simp

@[simp] theorem whitneyBasis_zero (m : ℝ) : whitneyBasis m 0 = candidateExp (C Polynomial.X*X) := by
  simp [whitneyBasis]

theorem derivative_whitneyBasis_succ (m : ℝ) (k : ℕ) :
    derivative (whitneyBasis m (k+1)) = whitneyBasis m k +
      C (Polynomial.C (1+m*(k+1))*Polynomial.X)*whitneyBasis m (k+1) := by
  have h := congrArg (fun x : ℝ => (C (Polynomial.C x) : PowerSeries (Polynomial ℝ))) (factorial_scale k)
  simp only [map_mul,map_add,map_natCast,map_one] at h
  unfold whitneyBasis
  simp only [Derivation.leibniz,smul_eq_mul,derivative_C,mul_zero,add_zero,derivative_pow]
  rw [derivative_candidateExp (by simp),derivative_dowlingFlatCoordinate]
  simp only [Derivation.leibniz,smul_eq_mul,derivative_C,mul_zero,derivative_X,mul_one,
    map_mul,map_add,map_one,map_natCast,pow_succ,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  linear_combination h * candidateExp (C Polynomial.X*X) * (dowlingFlatCoordinate m)^k

theorem candidate_ode_unique_inhomogeneous (f g a h : PowerSeries (Polynomial ℝ))
    (h0 : f.constantCoeff=g.constantCoeff)
    (hf : derivative f=a+h*f) (hg : derivative g=a+h*g) : f=g := by
  apply sub_eq_zero.mp
  apply candidate_ode_zero (f-g) h
  · simpa only [map_sub,sub_eq_zero] using h0
  · rw [map_sub,hf,hg]
    ring

/-- Exact EGF of actual full-Dowling flats with a fixed number of free blocks. -/
theorem whitneySeries_eq_basis (k : ℕ) : whitneySeries G k = whitneyBasis (Fintype.card G) k := by
  induction k with
  | zero => rw [whitneyBasis_zero,whitneySeries_zero_eq_exp]
  | succ k ih =>
    apply candidate_ode_unique_inhomogeneous _ _ (whitneySeries G k)
      (C (Polynomial.C (1+(Fintype.card G : ℝ)*(k+1))*Polynomial.X))
    · rw [whitneySeries_constant,whitneyBasis_constant]
    · exact derivative_whitneySeries_succ k
    · rw [derivative_whitneyBasis_succ,ih]

end Dowling
