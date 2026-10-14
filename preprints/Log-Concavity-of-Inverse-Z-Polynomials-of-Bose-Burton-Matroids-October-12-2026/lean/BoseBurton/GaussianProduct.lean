import BoseBurton.GaussianAlternating

noncomputable section
namespace BoseBurton
open Finset

def gaussianTerm (z x : ℝ) (n k : ℕ) : ℝ :=
  (-1:ℝ)^k*z^(k.choose 2)*gaussian z n k*x^k

theorem gaussianTerm_zero (z x : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n : ℕ) :
    gaussianTerm z x n 0=1 := by simp [gaussianTerm,gaussian_zero_right z hz0 hz1]

theorem gaussianTerm_pascal (z x : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n k : ℕ) :
    gaussianTerm z x (n+1) (k+1)=gaussianTerm z (z*x) n (k+1)-x*gaussianTerm z (z*x) n k := by
  unfold gaussianTerm
  rw [gaussian_pascal_succ z hz0 hz1 n k]
  have he : (k+1).choose 2=k.choose 2+k := by rw [Nat.choose_succ_succ]; simp; omega
  simp only [he,pow_add,mul_pow,pow_one]
  ring

theorem gaussian_product (z x : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n : ℕ) :
    (∑ k∈range (n+1),(-1:ℝ)^k*z^(k.choose 2)*gaussian z n k*x^k)=
      ∏ i∈range n,(1-x*z^i) := by
  change (∑ k∈range (n+1),gaussianTerm z x n k)=_
  induction n generalizing x with
  | zero => simp [gaussianTerm,gaussian_zero_right z hz0 hz1]
  | succ n ih =>
    rw [sum_range_succ']
    simp_rw [gaussianTerm_pascal z x hz0 hz1 n]
    rw [sum_sub_distrib,← mul_sum,gaussianTerm_zero z x hz0 hz1]
    have hshift : (∑ k∈range (n+1),gaussianTerm z (z*x) n (k+1))+1=
        ∑ k∈range (n+1),gaussianTerm z (z*x) n k := by
      have h := sum_range_succ' (gaussianTerm z (z*x) n) (n+1)
      rw [sum_range_succ,gaussianTerm_zero z (z*x) hz0 hz1] at h
      have hz : gaussianTerm z (z*x) n (n+1)=0 := by
        simp [gaussianTerm,gaussian_outside z n (n+1) (by omega)]
      rw [hz,add_zero] at h
      exact h.symm
    rw [show (∏ i∈range (n+1),(1-x*z^i))=
        (∏ i∈range n,(1-x*z^(i+1)))*(1-x) by rw [prod_range_succ']; simp]
    have he : (∏ i∈range n,(1-x*z^(i+1)))=∏ i∈range n,(1-(z*x)*z^i) := by
      apply prod_congr rfl
      intro i _
      rw [pow_succ]
      ring
    rw [he,← ih (z*x)]
    nlinarith [hshift]

end BoseBurton
