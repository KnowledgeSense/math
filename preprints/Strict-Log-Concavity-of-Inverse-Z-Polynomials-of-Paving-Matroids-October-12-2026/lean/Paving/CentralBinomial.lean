import Paving.UniformCoefficients
import Paving.MobiusCoefficientSum

namespace Paving

theorem choose_two_stage_comm (n a b : ℕ) :
    n.choose a*(n-a).choose b = n.choose b*(n-b).choose a := by
  have h1 := Nat.choose_mul (n:=n) (k:=a+b) (s:=a) (by omega)
  have h2 := Nat.choose_mul (n:=n) (k:=a+b) (s:=b) (by omega)
  have hs : (a+b).choose a=(a+b).choose b := by
    rw [← Nat.choose_symm (show a≤a+b by omega)]
    congr 1
    omega
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.add_sub_cancel_right,← hs] at h2
  exact h1.symm.trans h2

/-- Exact cancellation of the uniform odd-rank top inverse-Q correction. -/
theorem central_binomial_payment (m h : ℕ) (hm : 2≤m) (hh : 2*m-1≤h) :
    uniformEntry (2*m) h m -
      ((h.choose (m-1):ℤ)*(h-m).choose (m-1) -
        (h.choose m:ℤ)*(h-m-1).choose (m-2)) =
      uniformEntry (2*m) h (m-1) := by
  have hp1 := Nat.choose_succ_succ (h-m-1) (m-2)
  simp only [Nat.succ_eq_add_one] at hp1
  rw [show h-m-1+1=h-m by omega,show m-2+1=m-1 by omega] at hp1
  have hp2 := Nat.choose_succ_succ (h-m) (m-1)
  simp only [Nat.succ_eq_add_one] at hp2
  rw [show m-1+1=m by omega] at hp2
  have hc := choose_two_stage_comm h m (m-1)
  rw [show h-(m-1)=h-m+1 by omega] at hc
  have h1 : ((h-m).choose (m-1):ℤ)=((h-m-1).choose (m-2):ℤ)+((h-m-1).choose (m-1):ℤ) := by exact_mod_cast hp1
  have h2 : ((h-m+1).choose m:ℤ)=((h-m).choose (m-1):ℤ)+((h-m).choose m:ℤ) := by exact_mod_cast hp2
  have h3 : (h.choose m:ℤ)*((h-m).choose (m-1):ℤ)=
      (h.choose (m-1):ℤ)*((h-m+1).choose m:ℤ) := by exact_mod_cast hc
  unfold uniformEntry
  rw [show 2*m-1-m=m-1 by omega,show h-(m-1)-1=h-m by omega,
    show 2*m-1-(m-1)=m by omega]
  rw [h1] at h3
  rw [h2] at h3
  linear_combination h3

/-- The even correction in the source is supplied by the actual uniform
hyperplane inverse-KL polynomial. -/
theorem uniform_central_correction {α : Type*} [Fintype α] (m : ℕ) (hm : 2≤m)
    (hh : 2*m-1≤Fintype.card α) :
    uniformEntry (2*m) (Fintype.card α) m -
      (uniformQ (α:=α) (2*m-2)).coeff (m-1) =
      uniformEntry (2*m) (Fintype.card α) (m-1) := by
  rw [uniformQ_coeff_lower (2*m-2) (m-1) (by omega) (by omega) (by omega)]
  rw [show Fintype.card α-(m-1)-1=Fintype.card α-m by omega,
    show 2*m-2-(m-1)=m-1 by omega,
    show 2*m-2+1-(m-1)=m by omega,
    show m-1-1=m-2 by omega]
  exact central_binomial_payment m (Fintype.card α) hm hh

end Paving
