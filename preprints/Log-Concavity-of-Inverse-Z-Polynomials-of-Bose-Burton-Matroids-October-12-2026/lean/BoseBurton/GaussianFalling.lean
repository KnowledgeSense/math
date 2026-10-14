import BoseBurton.FiniteProducts

noncomputable section
namespace BoseBurton

theorem fallingProduct_factorial_cleared (z : ℝ) (j k : ℕ) (hjk : j<k) :
    fallingProduct z j k*qFactorial z (k-1-j)=qFactorial z (k-1) := by
  induction j with
  | zero => simp [fallingProduct_zero]
  | succ j ih =>
    rw [fallingProduct_succ]
    have he : qFactorial z (k-1-j)=qFactorial z (k-1-(j+1))*(1-z^(k-(j+1))) := by
      conv_lhs => rw [show k-1-j=(k-1-(j+1))+1 by omega,qFactorial_succ]
      rw [show k-1-(j+1)+1=k-(j+1) by omega]
    rw [← ih (by omega),he]
    ring

theorem fallingProduct_factorial (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (j k : ℕ) (hjk : j<k) :
    fallingProduct z j k=qFactorial z (k-1)/qFactorial z (k-1-j) := by
  apply (eq_div_iff (qFactorial_pos z hz0 hz1 _).ne').mpr
  exact fallingProduct_factorial_cleared z j k hjk

theorem qFactorial_predecessor (z : ℝ) (n : ℕ) (hn : 1≤n) :
    qFactorial z n=qFactorial z (n-1)*(1-z^n) := by
  conv_lhs => rw [show n=(n-1)+1 by omega,qFactorial_succ]
  rw [show n-1+1=n by omega]

theorem gaussian_upper_falling (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r h k : ℕ) (hh : 1≤h) (hl : h≤k) (hr : h≤r-k) :
    gaussian z (r-h) k*gaussian z (k-1) h/gaussian z r k=
      qFactorial z (r-h)/(qFactorial z r*qFactorial z h)*
      pairedProduct z r (h-1) k*(1-z^(k-h))*(1-z^(r-k)) := by
  by_cases heq : h=k
  · subst h
    simp [gaussian,show ¬k≤k-1 by omega]
  · have hlt : h<k := by omega
    have hp (i : ℕ) := (qFactorial_pos z hz0 hz1 i).ne'
    rw [pairedProduct,fallingProduct_factorial z hz0 hz1 (h-1) k (by omega),
      fallingProduct_factorial z hz0 hz1 (h-1) (r-k) (by omega)]
    simp only [gaussian,show k≤r-h by omega,show h≤k-1 by omega,show k≤r by omega,
      ite_true,show r-h-k=r-k-h by omega,show k-1-(h-1)=k-h by omega,
      show r-k-1-(h-1)=r-k-h by omega]
    rw [qFactorial_predecessor z (k-h) (by omega),qFactorial_predecessor z (r-k) (by omega)]
    rw [show k-h-1=k-1-h by omega]
    have hzkh := (one_sub_pow_pos z hz0 hz1 (k-h) (by omega)).ne'
    field_simp [hp]

theorem gaussian_lower_falling (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r h k : ℕ) (hh : 1≤h) (hl : h≤k) (hr : h≤r-k) :
    gaussian z (r-h) (k-h)*gaussian z (r-k-1) (h-1)/gaussian z r k=
      qFactorial z (r-h)/(qFactorial z r*qFactorial z h)*
      pairedProduct z r (h-1) k*(1-z^h)*(1-z^k) := by
  have hp (i : ℕ) := (qFactorial_pos z hz0 hz1 i).ne'
  rw [pairedProduct,fallingProduct_factorial z hz0 hz1 (h-1) k (by omega),
    fallingProduct_factorial z hz0 hz1 (h-1) (r-k) (by omega)]
  simp only [gaussian,show k-h≤r-h by omega,show h-1≤r-k-1 by omega,show k≤r by omega,
    ite_true,show r-h-(k-h)=r-k by omega,show k-1-(h-1)=k-h by omega,
    show r-k-1-(h-1)=r-k-h by omega]
  rw [qFactorial_predecessor z h hh,qFactorial_predecessor z k (by omega)]
  have hzh := (one_sub_pow_pos z hz0 hz1 h hh).ne'
  field_simp [hp]

end BoseBurton
