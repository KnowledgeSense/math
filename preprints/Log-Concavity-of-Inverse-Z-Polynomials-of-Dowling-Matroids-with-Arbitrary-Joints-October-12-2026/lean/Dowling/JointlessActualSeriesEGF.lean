import Dowling.JointlessActualSeriesTauCoefficients

noncomputable section
namespace Dowling
open PowerSeries Finset

/-- Literal factorial cancellation in an ordinary exponential generating
series product. This does not assume a labelled combinatorial formula. -/
theorem invariantEGF_product_coeff (A B : ℕ→Polynomial ℤ) (n : ℕ) :
    Polynomial.C (n.factorial : ℝ)*coeff n (invariantEGF A*invariantEGF B)=
      ∑ d∈range (n+1),Polynomial.C (n.choose d : ℝ)*
        (A d).map (Int.castRingHom ℝ)*(B (n-d)).map (Int.castRingHom ℝ) := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.mul_sum]
  apply sum_congr rfl
  intro d hd
  have hdn : d≤n := by have := mem_range.mp hd; omega
  have hf : (n.factorial : ℝ)*(d.factorial : ℝ)⁻¹*((n-d).factorial : ℝ)⁻¹=(n.choose d : ℝ) := by
    have hd0 : (d.factorial : ℝ)≠0 := by positivity
    have hn0 : ((n-d).factorial : ℝ)≠0 := by positivity
    have hh : (n.choose d : ℝ)*d.factorial*(n-d).factorial=n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hdn
    field_simp
    nlinarith only [hh]
  rw [invariantEGF_coeff,invariantEGF_coeff]
  calc
    _ = Polynomial.C ((n.factorial : ℝ)*(d.factorial : ℝ)⁻¹*((n-d).factorial : ℝ)⁻¹)*
        (A d).map (Int.castRingHom ℝ)*(B (n-d)).map (Int.castRingHom ℝ) := by
      simp only [map_mul]
      ring
    _ = _ := by rw [hf]

theorem invariantEGF_shift_product_coeff (A B : ℕ→Polynomial ℤ) (n : ℕ) :
    Polynomial.C ((n+1).factorial : ℝ)*coeff (n+1) (X*(invariantEGF A*invariantEGF B))=
      Polynomial.C (n+1 : ℝ)*∑ d∈range (n+1),Polynomial.C (n.choose d : ℝ)*
        (A d).map (Int.castRingHom ℝ)*(B (n-d)).map (Int.castRingHom ℝ) := by
  rw [coeff_succ_X_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,map_mul,
    mul_assoc,invariantEGF_product_coeff]

def jointTauPolynomial (G : Type*) [Group G] [Fintype G] (d : ℕ) : Polynomial ℤ :=
  if d%2=1 then Polynomial.C ((fullP G d).coeff (d/2))*Polynomial.X^((d+1)/2) else 0

variable (G : Type*) [Group G] [Fintype G]

theorem jointTauSeries_eq_EGF : jointTauSeries (Fintype.card G)=invariantEGF (jointTauPolynomial G) := by
  apply PowerSeries.ext
  intro d
  by_cases he : d%2=0
  · have hd : d=2*(d/2) := by omega
    rw [hd,jointTauSeries_coeff_even,invariantEGF_coeff]
    simp [jointTauPolynomial]
  · have hd : d=2*(d/2)+1 := by omega
    rw [hd,jointTauSeries_coeff_odd,invariantEGF_coeff]
    have hdiv : (2*(d/2)+1)/2=d/2 := by omega
    have hdiv' : (2*(d/2)+1+1)/2=d/2+1 := by omega
    simp only [jointTauPolynomial,show (2*(d/2)+1)%2=1 by omega,ite_true,hdiv,hdiv',
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,← mul_assoc,← map_mul]
    rfl

/-- The local odd-rank tau polynomial is exactly the positive-rank correction
factor used in the actual deletion formula. -/
theorem jointTauPolynomial_correction (n d : ℕ) :
    jointTauPolynomial G d*fullY G (n-(d+1))=jointRankCorrection G n (d+1) := by
  have hp : d%2=1 ↔ (d+1)%2=0 ∧ 2≤d+1 := by omega
  simp only [jointTauPolynomial,jointRankCorrection,Nat.add_sub_cancel_right,hp]
  split <;> simp

end Dowling
