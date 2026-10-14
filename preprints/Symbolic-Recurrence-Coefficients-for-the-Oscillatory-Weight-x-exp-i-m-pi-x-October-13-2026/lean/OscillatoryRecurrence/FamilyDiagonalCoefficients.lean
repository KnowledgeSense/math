import OscillatoryRecurrence.NumeratorLeading
import OscillatoryRecurrence.FamilyLowerCoefficients

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

theorem evaluatedBorder_as_family (η : ℝ) {n : ℕ} (hn : 4≤n) :
    evaluatedBorder η n = (n:ℂ)*(n+1)*evaluatedHankel η n-
      (numeratorLeadingFactor n:ℂ)*((polynomialHankel n).leadingCoeff:ℂ)*
        (η:ℂ)^2*evaluatedFamily η (hankelDegree n-1) := by
  have h := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℂ) ((η:ℂ)^2))
    (recurrenceFamily_numerator_identity hn)
  simp only [polynomialNumerator,eval₂_sub,eval₂_mul,eval₂_C,eval₂_X,
    Rat.coe_castHom,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one] at h
  change _ = _ - _ at h
  unfold evaluatedBorder evaluatedHankel evaluatedFamily
  linear_combination h

theorem evaluatedBorder_ratio_family (m : ℤ) (hm : m≠0) {n : ℕ} (hn : 4≤n) :
    evaluatedBorder ((m:ℝ)*Real.pi) n/evaluatedHankel ((m:ℝ)*Real.pi) n =
      (n:ℂ)*(n+1)-(numeratorLeadingFactor n:ℂ)*((((m:ℝ)*Real.pi):ℂ)^2)*
        evaluatedFamily ((m:ℝ)*Real.pi) (hankelDegree n-1)/
          evaluatedFamily ((m:ℝ)*Real.pi) (hankelDegree n) := by
  rw [evaluatedBorder_as_family _ hn,evaluatedHankel_as_family _ (by omega : 1≤n)]
  have hf := evaluatedFamily_hankel_ne_zero m hm (by omega : 1≤n)
  have hc : ((polynomialHankel n).leadingCoeff:ℂ)≠0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr (polynomialHankel_ne_zero n)
  field_simp
  push_cast
  ring

theorem recurrenceDiagonal_family (m : ℤ) (hm : m≠0) (n : ℕ) (hn : 3≤n) :
    recurrenceDiagonal ((m:ℝ)*Real.pi) n = Complex.I *
      (2*(n+2:ℂ)/(((m:ℝ)*Real.pi):ℂ)+(((m:ℝ)*Real.pi):ℂ)*
        ((numeratorLeadingFactor (n+1):ℂ)*
          evaluatedFamily ((m:ℝ)*Real.pi) (hankelDegree (n+1)-1)/
            evaluatedFamily ((m:ℝ)*Real.pi) (hankelDegree (n+1))-
         (numeratorLeadingFactor (n+2):ℂ)*
          evaluatedFamily ((m:ℝ)*Real.pi) (hankelDegree (n+2)-1)/
            evaluatedFamily ((m:ℝ)*Real.pi) (hankelDegree (n+2)))) := by
  rw [recurrenceDiagonal_determinants m hm,
    border_ratio_normalization m hm _ (by omega),
    border_ratio_normalization m hm _ (by omega)]
  have hq (r : ℕ) : -evaluatedBorder ((m:ℝ)*Real.pi) r/
      ((Complex.I*((m:ℝ)*Real.pi))*evaluatedHankel ((m:ℝ)*Real.pi) r) =
      -(evaluatedBorder ((m:ℝ)*Real.pi) r/evaluatedHankel ((m:ℝ)*Real.pi) r)/
        (Complex.I*((m:ℝ)*Real.pi)) := by ring
  rw [hq,hq,evaluatedBorder_ratio_family m hm (by omega : 4≤n+2),
    evaluatedBorder_ratio_family m hm (by omega : 4≤n+1)]
  have ht : ((((m:ℝ)*Real.pi):ℂ))≠0 := by
    exact_mod_cast mul_ne_zero (Int.cast_ne_zero.mpr hm) Real.pi_ne_zero
  have h1 := evaluatedFamily_hankel_ne_zero m hm (by omega : 1≤n+1)
  have h2 := evaluatedFamily_hankel_ne_zero m hm (by omega : 1≤n+2)
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

theorem recurrenceDiagonal_even_family (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 2≤k) :
    recurrenceDiagonal ((m:ℝ)*Real.pi) (2*k-1) = Complex.I *
      (2*(2*k+1:ℂ)/(((m:ℝ)*Real.pi):ℂ)+(k:ℂ)*(k+1)*(((m:ℝ)*Real.pi):ℂ)*
        (2*evaluatedFamily ((m:ℝ)*Real.pi) (k^2-1)/
            evaluatedFamily ((m:ℝ)*Real.pi) (k^2)-
          evaluatedFamily ((m:ℝ)*Real.pi) (k*(k+1)-1)/
            evaluatedFamily ((m:ℝ)*Real.pi) (k*(k+1)))) := by
  rw [recurrenceDiagonal_family m hm _ (by omega),
    show 2*k-1+1=2*k by omega,show 2*k-1+2=2*k+1 by omega,
    numeratorLeadingFactor_even,numeratorLeadingFactor_odd,
    hankelDegree_even,hankelDegree_odd]
  have he : ((2*k-1:ℕ):ℂ)+2=2*(k:ℂ)+1 := by
    have := congrArg (fun r : ℕ => (r:ℂ)) (show 2*k-1+2=2*k+1 by omega)
    push_cast at this
    exact this
  rw [he]
  push_cast
  ring

theorem recurrenceDiagonal_odd_family (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 2≤k) :
    recurrenceDiagonal ((m:ℝ)*Real.pi) (2*k) = Complex.I *
      (2*(2*k+2:ℂ)/(((m:ℝ)*Real.pi):ℂ)+(((m:ℝ)*Real.pi):ℂ)*
        ((k:ℂ)*(k+1)*evaluatedFamily ((m:ℝ)*Real.pi) (k*(k+1)-1)/
            evaluatedFamily ((m:ℝ)*Real.pi) (k*(k+1))-
          2*(k+1:ℂ)*(k+2)*evaluatedFamily ((m:ℝ)*Real.pi) (k*(k+2))/
            evaluatedFamily ((m:ℝ)*Real.pi) ((k+1)^2))) := by
  rw [recurrenceDiagonal_family m hm _ (by omega),
    show 2*k+2=2*(k+1) by omega,numeratorLeadingFactor_odd,
    numeratorLeadingFactor_even,hankelDegree_odd,hankelDegree_even]
  have he : (k+1)^2-1=k*(k+2) := by
    have hp : (k+1)^2=k*(k+2)+1 := by ring
    omega
  rw [he]
  push_cast
  ring

end OscillatoryRecurrence
