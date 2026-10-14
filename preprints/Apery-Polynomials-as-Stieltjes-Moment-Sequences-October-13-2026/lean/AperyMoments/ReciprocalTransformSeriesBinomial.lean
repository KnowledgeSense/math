import AperyMoments.ReciprocalTransformSeriesDouble

noncomputable section
namespace AperyMoments
open Complex Finset
open scoped Topology

def reciprocalEvenTerm (α R : ℝ) (m : ℕ) : ℂ :=
  (spectralMomentCoefficient m α:ℂ)/(R:ℂ)^(m+1)/
    (1+(α:ℂ)/(R:ℂ))^(2*m+1)

theorem reciprocalDoubleTerm_hasSum {α R : ℝ} (hα : 0≤α) (hα1 : α≤1)
    (hR : 256<R) (m : ℕ) :
    HasSum (reciprocalDoubleTerm α R m) (reciprocalEvenTerm α R m) := by
  have hR0 : 0<R := by linarith
  have hn : ‖(-(α:ℂ))/(R:ℂ)‖<1 := by
    simp only [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hα,
      abs_of_pos hR0]
    exact (div_lt_one hR0).mpr (by linarith)
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (2*m) hn).mul_left
    ((spectralMomentCoefficient m α:ℂ)/(R:ℂ)^(m+1))
  convert hs using 1
  · funext k
    rw [show (k+2*m).choose (2*m)=(2*m+k).choose k by
      rw [Nat.add_comm]; exact Nat.choose_symm_of_eq_add (by omega)]
    simp only [reciprocalDoubleTerm,div_pow,pow_add,pow_one]
    ring
  · simp only [reciprocalEvenTerm,neg_div,sub_neg_eq_add]
    ring

end AperyMoments
