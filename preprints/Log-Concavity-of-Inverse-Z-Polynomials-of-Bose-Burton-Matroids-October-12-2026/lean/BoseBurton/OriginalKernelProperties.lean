import BoseBurton.OriginalKernel

noncomputable section
namespace BoseBurton
open Polynomial

theorem originalSignedKernel_coeff_pos (q : ℝ) (hq : 1<q)
    (r s k : ℕ) (hsr : s<r) (hk : k≤r) : 0<(originalSignedKernel q r s).coeff k := by
  have hq0 : 0<q := by linarith
  rw [originalSignedKernel_coeff q hq r s k hsr]
  exact mul_pos (pow_pos hq0 _) (scalarCoefficient_pos q⁻¹ (inv_pos.mpr hq0)
    ((inv_lt_one₀ hq0).mpr hq) r s k hsr hk)

theorem originalSignedKernel_coeff_symm (q : ℝ) (hq : 1<q)
    (r s k : ℕ) (hsr : s<r) (hk : k≤r) :
    (originalSignedKernel q r s).coeff (r-k)=(originalSignedKernel q r s).coeff k := by
  rw [originalSignedKernel_coeff q hq,originalSignedKernel_coeff q hq,
    scalarCoefficient_symm q⁻¹ r s k hk]
  all_goals exact hsr

theorem originalSignedKernel_coeff_above (q : ℝ) (hq : 1<q)
    (r s k : ℕ) (hsr : s<r) (hk : r<k) : (originalSignedKernel q r s).coeff k=0 := by
  rw [originalSignedKernel_coeff q hq r s k hsr,scalarCoefficient,
    gaussian_outside q⁻¹ r k hk,zero_mul,mul_zero]

theorem originalSignedKernel_strict_log_concave (q : ℝ) (hq : 2≤q)
    (r s k : ℕ) (hsr : s<r) (hs : 1≤s) (hk : 1≤k) (hkr : k<r) :
    (originalSignedKernel q r s).coeff (k-1)*(originalSignedKernel q r s).coeff (k+1)<
      ((originalSignedKernel q r s).coeff k)^2 := by
  have hq1 : 1<q := by linarith
  have hq0 : 0<q := by linarith
  have hzhalf : q⁻¹≤1/2 := by
    calc q⁻¹ ≤ (2:ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
         _ = 1/2 := by norm_num
  simp only [originalSignedKernel_coeff q hq1 r s _ hsr]
  have h := scalarCoefficient_strict_log_concave q⁻¹ (inv_pos.mpr hq0) hzhalf r s k hsr hs hk hkr
  have hm := mul_lt_mul_of_pos_left h (pow_pos (pow_pos hq0 (r.choose 2)) 2)
  convert hm using 1 <;> ring

theorem originalSignedKernel_natDegree (q : ℝ) (hq : 1<q)
    (r s : ℕ) (hsr : s<r) : (originalSignedKernel q r s).natDegree=r := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr (fun k hk=>originalSignedKernel_coeff_above q hq r s k hsr hk)
  · exact (originalSignedKernel_coeff_pos q hq r s r hsr le_rfl).ne'

end BoseBurton
