import Paving.Components

noncomputable section
namespace Paving

theorem uniform_coefficient_cleared {k s i : ℕ} (hik : i < k) (hks : k ≤ s) :
    (s-i)*s.choose i*(s-i-1).choose (s-k)=
      s.choose (k-1)*(k-1).choose i*(s-k+1) := by
  have hsi : i < s := lt_of_lt_of_le hik hks
  have hc := Nat.choose_mul (n:=s) (show i ≤ k-1 by omega)
  have hs : (s-i).choose (k-1-i)=(s-i).choose (s-k+1) := by
    have he : s-i-(k-1-i)=s-k+1 := by omega
    rw [← he,Nat.choose_symm (show k-1-i ≤ s-i by omega)]
  rw [hc,hs]
  have hf := Nat.add_one_mul_choose_eq (s-i-1) (s-k)
  rw [show s-i-1+1=s-i by omega] at hf
  nlinarith [hf]

theorem uniform_coefficient_normalized {k s i : ℕ} (hik : i < k) (hks : k ≤ s) :
    (s.choose i:ℝ)*((s-i-1).choose (s-k):ℝ)=
      (s.choose (k-1):ℝ)*uniformComponent k s i := by
  have hsi : i < s := lt_of_lt_of_le hik hks
  have hsiR : (i:ℝ) < s := by exact_mod_cast hsi
  have he := congrArg (fun x:ℕ => (x:ℝ)) (uniform_coefficient_cleared hik hks)
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub (Nat.le_of_lt hsi),
    Nat.cast_sub hks] at he
  unfold uniformComponent
  rw [← mul_div_assoc]
  apply (eq_div_iff (show (s:ℝ)-i≠0 by linarith)).mpr
  linear_combination he

end Paving
