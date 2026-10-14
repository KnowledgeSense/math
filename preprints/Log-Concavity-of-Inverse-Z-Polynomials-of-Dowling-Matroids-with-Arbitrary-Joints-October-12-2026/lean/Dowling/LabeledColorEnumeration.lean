import Dowling.LabeledColorSeries

noncomputable section
namespace Dowling
open scoped Classical
open Finset PowerSeries
variable {I : Type*} [Fintype I]

/-- The labelled-color exponential formula is proved by adding the first label
and by the formal product rule, with no assumed multinomial enumeration. -/
theorem labeledColorSum_eq_factorial_coeff (f : I → ℕ → Polynomial ℝ) (n : ℕ) :
    labeledColorSum f n=(n.factorial : Polynomial ℝ)*coeff n (labeledColorProduct f) := by
  induction n generalizing f with
  | zero => rw [labeledColorSum_zero,labeledColorProduct_constant]; norm_num
  | succ n ih =>
    rw [labeledColorSum_succ]
    simp_rw [ih]
    rw [← mul_sum,← map_sum,← derivative_labeledColorProduct,coeff_derivative,Nat.factorial_succ]
    push_cast
    ring

/-- Exact finite EGF product identity, retaining every empty color fiber and
valid for arbitrary polynomial weights, including zero and negative weights. -/
theorem labeled_color_enumeration (f : I → ℕ → Polynomial ℝ) (n : ℕ) :
    (∑ w : Fin n → I, ∏ c : I, f c (Finset.univ.filter (fun i => w i=c)).card)=
      (n.factorial : Polynomial ℝ)*PowerSeries.coeff n
        (∏ c : I, PowerSeries.mk (fun j => Polynomial.C (1/(j.factorial : ℝ))*f c j)) := by
  simpa only [labeledColorSum,labeledColorCount,labeledColorProduct,labeledColorSeries,one_div]
    using labeledColorSum_eq_factorial_coeff f n

end Dowling
