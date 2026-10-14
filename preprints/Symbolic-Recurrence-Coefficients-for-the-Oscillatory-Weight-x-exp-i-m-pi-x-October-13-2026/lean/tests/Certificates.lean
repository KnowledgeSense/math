import OscillatoryRecurrence

open Polynomial OscillatoryRecurrence

example (j : ℕ) : (recurrenceFamily j).Monic ∧ (recurrenceFamily j).natDegree=j :=
  uniform_monic_family.1 j

example : recurrenceFamily 0=1 ∧ recurrenceFamily 1=X-C 2 :=
  uniform_monic_family.2

example (m : ℤ) (hm : m≠0) (n : ℕ) :
    hankel ((m:ℝ)*Real.pi) n≠0 := hankel_ne_zero m hm n

example (m : ℤ) (hm : m≠0) (n : ℕ) (hn : 1≤n) :
    realFamily ((m:ℝ)*Real.pi) (hankelDegree n)≠0 :=
  realFamily_denominator_ne_zero m hm hn

example (m : ℤ) (hm : m≠0) (n : ℕ) (hn : 1≤n) :
    X*orthogonalPolynomial ((m:ℝ)*Real.pi) n =
      orthogonalPolynomial ((m:ℝ)*Real.pi) (n+1)+
      C (Complex.I*(alpha ((m:ℝ)*Real.pi) n:ℂ))*orthogonalPolynomial ((m:ℝ)*Real.pi) n+
      C (beta ((m:ℝ)*Real.pi) n:ℂ)*orthogonalPolynomial ((m:ℝ)*Real.pi) (n-1) :=
  original_three_term_recurrence m hm n hn

example (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 2≤k) :
    alpha ((m:ℝ)*Real.pi) (2*k) =
      2*(2*k+1:ℝ)/((m:ℝ)*Real.pi)+(k:ℝ)*(k+1)*((m:ℝ)*Real.pi)*
        (2*realFamily ((m:ℝ)*Real.pi) (k^2-1)/realFamily ((m:ℝ)*Real.pi) (k^2)-
          realFamily ((m:ℝ)*Real.pi) (k*(k+1)-1)/realFamily ((m:ℝ)*Real.pi) (k*(k+1))) :=
  alpha_even m hm k hk

example (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 2≤k) :
    alpha ((m:ℝ)*Real.pi) (2*k+1) =
      2*(2*k+2:ℝ)/((m:ℝ)*Real.pi)+((m:ℝ)*Real.pi)*
        ((k:ℝ)*(k+1)*realFamily ((m:ℝ)*Real.pi) (k*(k+1)-1)/
            realFamily ((m:ℝ)*Real.pi) (k*(k+1))-
          2*(k+1:ℝ)*(k+2)*realFamily ((m:ℝ)*Real.pi) (k*(k+2))/
            realFamily ((m:ℝ)*Real.pi) ((k+1)^2)) :=
  alpha_odd m hm k hk

example (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 1≤k) :
    beta ((m:ℝ)*Real.pi) (2*k) =
      -(2*k:ℝ)^2*realFamily ((m:ℝ)*Real.pi) (k*(k-1))*
        realFamily ((m:ℝ)*Real.pi) (k*(k+1))/
        (((m:ℝ)*Real.pi)^2*realFamily ((m:ℝ)*Real.pi) (k^2)^2) :=
  beta_even m hm k hk

example (m : ℤ) (hm : m≠0) (k : ℕ) (hk : 1≤k) :
    beta ((m:ℝ)*Real.pi) (2*k+1) =
      realFamily ((m:ℝ)*Real.pi) (k^2)*realFamily ((m:ℝ)*Real.pi) ((k+1)^2)/
        (((m:ℝ)*Real.pi)^2*realFamily ((m:ℝ)*Real.pi) (k*(k+1))^2) :=
  beta_odd m hm k hk

example : recurrenceFamily 2=X^2-C 13*X+C 6 := by
  rw [recurrenceFamily_appendix_2]
  unfold appendixG2
  norm_num only [map_one,map_neg]
  ring

example : recurrenceFamily 16=appendixG16 := recurrenceFamily_appendix_16
example : recurrenceFamily 15=appendixG15 := recurrenceFamily_appendix_15
example : recurrenceFamily 12=appendixG12 := recurrenceFamily_appendix_12
example : recurrenceFamily 11=appendixG11 := recurrenceFamily_appendix_11
example : recurrenceFamily 9=appendixG9 := recurrenceFamily_appendix_9
example : recurrenceFamily 8=appendixG8 := recurrenceFamily_appendix_8
example : recurrenceFamily 6=appendixG6 := recurrenceFamily_appendix_6
example : recurrenceFamily 5=appendixG5 := recurrenceFamily_appendix_5
example : recurrenceFamily 4=appendixG4 := recurrenceFamily_appendix_4
example : recurrenceFamily 3=appendixG3 := recurrenceFamily_appendix_3
