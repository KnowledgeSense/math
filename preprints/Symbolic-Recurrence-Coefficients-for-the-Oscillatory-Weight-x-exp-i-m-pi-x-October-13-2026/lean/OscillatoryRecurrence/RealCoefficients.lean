import OscillatoryRecurrence.FamilyDiagonalCoefficients

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

/-- Real evaluation of the single monic rational family. -/
def realFamily (η : ℝ) (j : ℕ) : ℝ :=
  (recurrenceFamily j).eval₂ (Rat.castHom ℝ) (η^2)

def realHankel (η : ℝ) (n : ℕ) : ℝ :=
  (polynomialHankel n).eval₂ (Rat.castHom ℝ) (η^2)

def realBorder (η : ℝ) (n : ℕ) : ℝ :=
  (polynomialBorder n).eval₂ (Rat.castHom ℝ) (η^2)

/-- The real diagonal coefficient in the source's one-based recurrence indexing. -/
def alpha (η : ℝ) (n : ℕ) : ℝ :=
  (realBorder η (n+1)/realHankel η (n+1)-realBorder η n/realHankel η n)/η

/-- The real lower coefficient in the source's one-based recurrence indexing. -/
def beta (η : ℝ) (n : ℕ) : ℝ :=
  -realHankel η (n+1)*realHankel η (n-1)/(η^2*realHankel η n^2)

theorem eval₂_real_cast (p : ℚ[X]) (x : ℝ) :
    ((p.eval₂ (Rat.castHom ℝ) x:ℝ):ℂ)=p.eval₂ (Rat.castHom ℂ) (x:ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add,Complex.ofReal_add,hp,hq]
  | monomial n r => simp

theorem realFamily_cast (η : ℝ) (j : ℕ) :
    (realFamily η j:ℂ)=evaluatedFamily η j := by
  simp only [realFamily,evaluatedFamily,eval₂_real_cast,Complex.ofReal_pow]

theorem realHankel_cast (η : ℝ) (n : ℕ) :
    (realHankel η n:ℂ)=evaluatedHankel η n := by
  simp only [realHankel,evaluatedHankel,eval₂_real_cast,Complex.ofReal_pow]

theorem realBorder_cast (η : ℝ) (n : ℕ) :
    (realBorder η n:ℂ)=evaluatedBorder η n := by
  simp only [realBorder,evaluatedBorder,eval₂_real_cast,Complex.ofReal_pow]

theorem recurrenceDiagonal_alpha (m : ℤ) (hm : m≠0) (n : ℕ) :
    recurrenceDiagonal ((m:ℝ)*Real.pi) n =
      Complex.I*(alpha ((m:ℝ)*Real.pi) (n+1):ℂ) := by
  rw [recurrenceDiagonal_determinants m hm,
    border_ratio_normalization m hm _ (by omega),
    border_ratio_normalization m hm _ (by omega)]
  simp only [alpha,Complex.ofReal_div,Complex.ofReal_sub,realBorder_cast,realHankel_cast]
  have ht : ((((m:ℝ)*Real.pi):ℂ))≠0 := by
    exact_mod_cast mul_ne_zero (Int.cast_ne_zero.mpr hm) Real.pi_ne_zero
  have h1 := evaluatedHankel_ne_zero m hm (n+1)
  have h2 := evaluatedHankel_ne_zero m hm (n+2)
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

theorem recurrenceLower_beta (m : ℤ) (hm : m≠0) (n : ℕ) :
    recurrenceLower ((m:ℝ)*Real.pi) n = (beta ((m:ℝ)*Real.pi) (n+1):ℂ) := by
  rw [recurrenceLower_polynomials m hm]
  simp only [beta,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,
    Complex.ofReal_pow,realHankel_cast,Nat.add_sub_cancel]

theorem alpha_even (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 2≤k) :
    alpha ((m:ℝ)*Real.pi) (2*k) =
      2*(2*k+1:ℝ)/((m:ℝ)*Real.pi)+(k:ℝ)*(k+1)*((m:ℝ)*Real.pi)*
        (2*realFamily ((m:ℝ)*Real.pi) (k^2-1)/realFamily ((m:ℝ)*Real.pi) (k^2)-
          realFamily ((m:ℝ)*Real.pi) (k*(k+1)-1)/realFamily ((m:ℝ)*Real.pi) (k*(k+1))) := by
  apply Complex.ofReal_injective
  apply mul_left_cancel₀ Complex.I_ne_zero
  have h := recurrenceDiagonal_even_family m hm k hk
  rw [recurrenceDiagonal_alpha m hm,show 2*k-1+1=2*k by omega] at h
  simpa only [Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_ofNat,Complex.ofReal_one,realFamily_cast] using h

theorem alpha_odd (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 2≤k) :
    alpha ((m:ℝ)*Real.pi) (2*k+1) =
      2*(2*k+2:ℝ)/((m:ℝ)*Real.pi)+((m:ℝ)*Real.pi)*
        ((k:ℝ)*(k+1)*realFamily ((m:ℝ)*Real.pi) (k*(k+1)-1)/
            realFamily ((m:ℝ)*Real.pi) (k*(k+1))-
          2*(k+1:ℝ)*(k+2)*realFamily ((m:ℝ)*Real.pi) (k*(k+2))/
            realFamily ((m:ℝ)*Real.pi) ((k+1)^2)) := by
  apply Complex.ofReal_injective
  apply mul_left_cancel₀ Complex.I_ne_zero
  have h := recurrenceDiagonal_odd_family m hm k hk
  rw [recurrenceDiagonal_alpha m hm] at h
  simpa only [Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_ofNat,Complex.ofReal_one,realFamily_cast] using h

theorem beta_odd (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 1≤k) :
    beta ((m:ℝ)*Real.pi) (2*k+1) =
      realFamily ((m:ℝ)*Real.pi) (k^2)*realFamily ((m:ℝ)*Real.pi) ((k+1)^2)/
        (((m:ℝ)*Real.pi)^2*realFamily ((m:ℝ)*Real.pi) (k*(k+1))^2) := by
  apply Complex.ofReal_injective
  have h := recurrenceLower_odd_family m hm k hk
  rw [recurrenceLower_beta m hm] at h
  simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,realFamily_cast] using h

theorem beta_even (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 1≤k) :
    beta ((m:ℝ)*Real.pi) (2*k) =
      -(2*k:ℝ)^2*realFamily ((m:ℝ)*Real.pi) (k*(k-1))*
        realFamily ((m:ℝ)*Real.pi) (k*(k+1))/
        (((m:ℝ)*Real.pi)^2*realFamily ((m:ℝ)*Real.pi) (k^2)^2) := by
  apply Complex.ofReal_injective
  have h := recurrenceLower_even_family m hm (k-1)
  rw [recurrenceLower_beta m hm,show 2*(k-1)+1+1=2*k by omega,
    show k-1+1=k by omega,show k-1+2=k+1 by omega,
    Nat.mul_comm (k-1) k] at h
  have he : ((k-1:ℕ):ℂ)+1=(k:ℂ) := by
    exact_mod_cast (show k-1+1=k by omega)
  rw [he] at h
  simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_neg,
    Complex.ofReal_natCast,Complex.ofReal_ofNat,Complex.ofReal_one,realFamily_cast] using h

end OscillatoryRecurrence
