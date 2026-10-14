import Dowling.FullZFlatSum
import Dowling.WhitneySeriesEvaluation
import Fan.CoefficientChangeVariable

noncomputable section
namespace Dowling
open scoped Classical BigOperators
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

def flatCoordinateTail (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  (PowerSeries.map Polynomial.C candidateExpTailReal).subst
    (C (Polynomial.C m)*C Polynomial.X*X)

theorem dowlingFlatCoordinate_eq_X_mul (m : ℝ) :
    dowlingFlatCoordinate m = X*flatCoordinateTail m := rfl

theorem whitneyTerm_eq_tail_coeff (n k : ℕ) (hk : k ≤ n) :
    whitneyTerm G n k = Polynomial.C ((k.factorial : ℝ)⁻¹)*
      coeff (n-k) ((flatCoordinateTail (Fintype.card G))^k*candidateExp (C Polynomial.X*X)) := by
  have he : whitneyBasis (Fintype.card G) k = C (Polynomial.C ((k.factorial : ℝ)⁻¹))*
      (X^k*((flatCoordinateTail (Fintype.card G))^k*candidateExp (C Polynomial.X*X))) := by
    unfold whitneyBasis
    rw [dowlingFlatCoordinate_eq_X_mul,mul_pow]
    ring
  have h := congrArg (coeff n) (whitneySeries_eq_basis (G := G) k)
  rw [whitneySeries_coeff,he,coeff_C_mul,coeff_X_pow_mul',ite_eq_left hk] at h
  exact h

theorem fullZSeries_coeff_whitney (n : ℕ) :
    coeff n (fullZSeries G) = ∑ k ∈ Finset.range (n+1),
      whitneyTerm G n k * (fullP G k).map (Int.castRingHom ℝ) := by
  rw [fullZSeries,invariantEGF_coeff,fullZ_whitney_transform]
  simp only [Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,
    Polynomial.map_X,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold whitneyTerm
  rw [div_eq_mul_inv,map_mul]
  simp only [map_natCast]
  ring

/-- Exact full-Dowling flat exponential generating identity, derived from the
actual interval contraction and literal labelled partition enumeration. -/
theorem fullZSeries_flat_relation :
    fullZSeries G = candidateExp (C Polynomial.X*X)*
      (fullPSeries G).subst (dowlingFlatCoordinate (Fintype.card G)) := by
  apply PowerSeries.ext
  intro n
  rw [fullZSeries_coeff_whitney,mul_comm,dowlingFlatCoordinate_eq_X_mul,
    Fan.coeff_subst_X_mul_product]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [whitneyTerm_eq_tail_coeff n k hkn]
  change _ = (coeff k (invariantEGF (fullP G))) * _
  rw [invariantEGF_coeff]
  ring

end Dowling
