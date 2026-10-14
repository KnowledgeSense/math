import BoseBurton.FiniteProducts

noncomputable section
namespace BoseBurton
open Finset

theorem positiveWeight_pos (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s j : ℕ) (hsr : s<r) (hj : j≤s) : 0<positiveWeight z r s j := by
  unfold positiveWeight
  exact div_pos
    (mul_pos (mul_pos (mul_pos (one_sub_pow_pos z hz0.le hz1 (r-s) (by omega))
      (pow_pos hz0 _)) (gaussian_pos z hz0.le hz1 s j hj)) (qFactorial_pos z hz0.le hz1 _))
    (mul_pos (qFactorial_pos z hz0.le hz1 r) (qFactorial_pos z hz0.le hz1 j))

theorem positiveWeight_nonneg (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s j : ℕ) (hsr : s<r) : 0≤positiveWeight z r s j := by
  by_cases hj : j≤s
  · exact (positiveWeight_pos z hz0 hz1 r s j hsr hj).le
  · simp only [positiveWeight,gaussian,ite_eq_right hj,mul_zero,zero_mul,zero_div,le_refl]

theorem positiveWeight_zero (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (r s : ℕ) (hr : 0<r) :
    positiveWeight z r s 0=(1-z^(r-s))/(1-z^r) := by
  rw [positiveWeight,gaussian_zero_right z hz0 hz1]
  simp only [Nat.zero_mul,pow_zero,mul_one,Nat.sub_zero,qFactorial_zero]
  have he : qFactorial z r=qFactorial z (r-1)*(1-z^r) := by
    conv_lhs => rw [show r=(r-1)+1 by omega,qFactorial_succ]
    rw [show r-1+1=r by omega]
  rw [he]
  have h1 := (qFactorial_pos z hz0 hz1 (r-1)).ne'
  have h2 := (one_sub_pow_pos z hz0 hz1 r hr).ne'
  field_simp

theorem endpointFactor_pos (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (r s : ℕ) (hsr : s<r) :
    0<endpointFactor z r s := by
  apply prod_pos
  intro i _
  exact one_sub_pow_pos z hz0 hz1 (r-s+i) (by omega)

theorem normalizedCoefficient_pos (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s k : ℕ) (hsr : s<r) : 0<normalizedCoefficient z r s k := by
  unfold normalizedCoefficient
  split_ifs
  · exact endpointFactor_pos z hz0.le hz1 r s hsr
  · apply sum_pos'
    · intro j _
      exact mul_nonneg (positiveWeight_nonneg z hz0 hz1 r s j hsr)
        (pairedProduct_nonneg z hz0.le hz1 r j k)
    · refine ⟨0,mem_range.mpr (by omega),?_⟩
      rw [pairedProduct_zero,mul_one]
      exact positiveWeight_pos z hz0 hz1 r s 0 hsr (Nat.zero_le _)

theorem normalizedCoefficient_symm (z : ℝ) (r s k : ℕ) (hk : k≤r) :
    normalizedCoefficient z r s (r-k)=normalizedCoefficient z r s k := by
  unfold normalizedCoefficient
  have he : (r-k=0 ∨ r-k=r) ↔ (k=0 ∨ k=r) := by omega
  simp only [he]
  split_ifs
  · rfl
  · apply sum_congr rfl
    intro j _
    rw [pairedProduct_symm z r j k hk]

theorem scalarCoefficient_pos (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s k : ℕ) (hsr : s<r) (hk : k≤r) : 0<scalarCoefficient z r s k :=
  mul_pos (gaussian_pos z hz0.le hz1 r k hk) (normalizedCoefficient_pos z hz0 hz1 r s k hsr)

theorem scalarCoefficient_symm (z : ℝ) (r s k : ℕ) (hk : k≤r) :
    scalarCoefficient z r s (r-k)=scalarCoefficient z r s k := by
  rw [scalarCoefficient,scalarCoefficient,gaussian_symm z r k hk,normalizedCoefficient_symm z r s k hk]

end BoseBurton
