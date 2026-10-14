import OscillatoryRecurrence.GramDeterminant
import OscillatoryRecurrence.BorderCoefficient
import OscillatoryRecurrence.Recurrence

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

 theorem recurrenceDiagonal_determinants (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    recurrenceDiagonal ((m:ℝ)*Real.pi) n =
      borderedHankel ((m:ℝ)*Real.pi) (n+2)/hankel ((m:ℝ)*Real.pi) (n+2) -
      borderedHankel ((m:ℝ)*Real.pi) (n+1)/hankel ((m:ℝ)*Real.pi) (n+1) := by
  unfold recurrenceDiagonal
  rw [subleading_border_ratio m hm n, subleading_border_ratio m hm (n+1)]
  ring

 theorem recurrenceLower_determinants (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    recurrenceLower ((m:ℝ)*Real.pi) n =
      hankel ((m:ℝ)*Real.pi) (n+2)*hankel ((m:ℝ)*Real.pi) n /
        hankel ((m:ℝ)*Real.pi) (n+1)^2 := by
  unfold recurrenceLower
  rw [squaredNorm_hankel_ratio m hm (n+1), squaredNorm_hankel_ratio m hm n]
  field_simp [hankel_ne_zero m hm n, hankel_ne_zero m hm (n+1)]

 def evaluatedHankel (η : ℝ) (n : ℕ) : ℂ :=
  (polynomialHankel n).eval₂ (Rat.castHom ℂ) ((η:ℂ)^2)

 def evaluatedBorder (η : ℝ) (n : ℕ) : ℂ :=
  (polynomialBorder n).eval₂ (Rat.castHom ℂ) ((η:ℂ)^2)

 theorem hankel_normalization (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    (Complex.I*((m:ℝ)*Real.pi))^(n^2)*hankel ((m:ℝ)*Real.pi) n =
      ((-1:ℂ)^m)^n*evaluatedHankel ((m:ℝ)*Real.pi) n := by
  have h := exponential_hankel_normalization _ _ (integral_frequency_ne_zero m hm)
    (integral_frequency_exp m) (integral_frequency_exp_neg m) n
  have hz : -(Complex.I*((m:ℝ)*Real.pi))^2 = (((m:ℝ)*Real.pi):ℂ)^2 := by
    rw [mul_pow,Complex.I_sq]; ring
  rw [hz] at h
  simpa only [hankel,moment,evaluatedHankel,Complex.ofReal_mul] using h

 theorem border_normalization (m : ℤ) (hm : m ≠ 0) (n : ℕ) (hn : 0<n) :
    (Complex.I*((m:ℝ)*Real.pi))^(n^2+1)*borderedHankel ((m:ℝ)*Real.pi) n =
      -(((-1:ℂ)^m)^n)*evaluatedBorder ((m:ℝ)*Real.pi) n := by
  have h := exponential_border_normalization _ _ (integral_frequency_ne_zero m hm)
    (integral_frequency_exp m) (integral_frequency_exp_neg m) n hn
  have hz : -(Complex.I*((m:ℝ)*Real.pi))^2 = (((m:ℝ)*Real.pi):ℂ)^2 := by
    rw [mul_pow,Complex.I_sq]; ring
  rw [hz] at h
  simpa only [borderedHankel,ite_eq_right (Nat.ne_of_gt hn),moment,evaluatedBorder,
    Complex.ofReal_mul] using h

 theorem evaluatedHankel_ne_zero (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    evaluatedHankel ((m:ℝ)*Real.pi) n ≠ 0 := by
  simpa only [evaluatedHankel,Complex.ofReal_pow] using
    polynomialHankel_frequency_ne_zero m hm n

 theorem border_ratio_normalization (m : ℤ) (hm : m ≠ 0) (n : ℕ) (hn : 0<n) :
    borderedHankel ((m:ℝ)*Real.pi) n / hankel ((m:ℝ)*Real.pi) n =
      -evaluatedBorder ((m:ℝ)*Real.pi) n /
        ((Complex.I*((m:ℝ)*Real.pi))*evaluatedHankel ((m:ℝ)*Real.pi) n) := by
  have hd := hankel_normalization m hm n
  have he := border_normalization m hm n hn
  have ht := integral_frequency_ne_zero m hm
  have hD := hankel_ne_zero m hm n
  have hH := evaluatedHankel_ne_zero m hm n
  rw [pow_add,pow_one] at he
  apply (div_eq_div_iff hD (mul_ne_zero ht hH)).mpr
  apply (mul_left_cancel₀ (pow_ne_zero (n^2) ht))
  linear_combination evaluatedHankel ((m:ℝ)*Real.pi) n * he +
    evaluatedBorder ((m:ℝ)*Real.pi) n * hd

theorem recurrenceLower_polynomials (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    recurrenceLower ((m:ℝ)*Real.pi) n =
      -evaluatedHankel ((m:ℝ)*Real.pi) (n+2)*evaluatedHankel ((m:ℝ)*Real.pi) n /
        (((((m:ℝ)*Real.pi):ℂ)^2)*evaluatedHankel ((m:ℝ)*Real.pi) (n+1)^2) := by
  let η : ℝ := (m:ℝ)*Real.pi
  let t : ℂ := Complex.I*η
  let s : ℂ := (-1)^m
  have ht : t ≠ 0 := by simpa only [t,η,Complex.ofReal_mul] using integral_frequency_ne_zero m hm
  have hd0 : t^(n^2)*hankel η n = s^n*evaluatedHankel η n := by
    simpa only [t,η,s,Complex.ofReal_mul] using hankel_normalization m hm n
  have hd1 : t^((n+1)^2)*hankel η (n+1) = s^(n+1)*evaluatedHankel η (n+1) := by
    simpa only [t,η,s,Complex.ofReal_mul] using hankel_normalization m hm (n+1)
  have hd2 : t^((n+2)^2)*hankel η (n+2) = s^(n+2)*evaluatedHankel η (n+2) := by
    simpa only [t,η,s,Complex.ofReal_mul] using hankel_normalization m hm (n+2)
  have hp : t^2*hankel η (n+2)*hankel η n*evaluatedHankel η (n+1)^2 =
      hankel η (n+1)^2*evaluatedHankel η (n+2)*evaluatedHankel η n := by
    apply mul_left_cancel₀ (pow_ne_zero (2*(n+1)^2) ht)
    calc
      _ = (t^((n+2)^2)*hankel η (n+2))*(t^(n^2)*hankel η n)*
          evaluatedHankel η (n+1)^2 := by
        have he : 2*(n+1)^2+2=(n+2)^2+n^2 := by ring
        have hpow := congrArg (fun a : ℕ => t^a) he
        simp only [pow_add,pow_mul] at hpow
        linear_combination hankel η (n+2)*hankel η n*evaluatedHankel η (n+1)^2*hpow
      _ = (t^((n+1)^2)*hankel η (n+1))^2*
          evaluatedHankel η (n+2)*evaluatedHankel η n := by
        rw [hd0,hd2,hd1]
        simp only [pow_add,pow_one,pow_two]
        ring
      _ = _ := by rw [pow_mul]; ring
  have hz : t^2 = -(η:ℂ)^2 := by dsimp [t]; rw [mul_pow,Complex.I_sq]; ring
  rw [hz] at hp
  rw [recurrenceLower_determinants m hm n]
  change hankel η (n+2)*hankel η n/hankel η (n+1)^2 = _
  apply (div_eq_div_iff (pow_ne_zero 2 (hankel_ne_zero m hm (n+1)))
    (mul_ne_zero (pow_ne_zero 2 (by
      exact_mod_cast mul_ne_zero (Int.cast_ne_zero.mpr hm) Real.pi_ne_zero))
      (pow_ne_zero 2 (evaluatedHankel_ne_zero m hm (n+1))))).mpr
  have hf : (hankel η (n+2)*hankel η n)*((η:ℂ)^2*evaluatedHankel η (n+1)^2) =
      (-evaluatedHankel η (n+2)*evaluatedHankel η n)*hankel η (n+1)^2 := by
    linear_combination -hp
  simpa only [η,Complex.ofReal_mul] using hf

end OscillatoryRecurrence
