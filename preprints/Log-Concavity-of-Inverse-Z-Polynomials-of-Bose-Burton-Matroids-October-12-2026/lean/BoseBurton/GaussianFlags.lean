import BoseBurton.FiniteProducts

noncomputable section
namespace BoseBurton

theorem gaussian_flag (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (n k l : ℕ) (hlk : l≤k) (hkn : k≤n) :
    gaussian z n l*gaussian z (n-l) (k-l)=gaussian z n k*gaussian z k l := by
  have hp (i : ℕ) := (qFactorial_pos z hz0 hz1 i).ne'
  simp only [gaussian,show l≤n by omega,hlk,hkn,show k-l≤n-l by omega,ite_true,
    show n-l-(k-l)=n-k by omega]
  field_simp [hp]

theorem gaussian_disjoint_flag (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (n k l : ℕ) (hkl : k+l≤n) :
    gaussian z n l*gaussian z (n-l) k=gaussian z n k*gaussian z (n-k) l := by
  have hp (i : ℕ) := (qFactorial_pos z hz0 hz1 i).ne'
  simp only [gaussian,show l≤n by omega,show k≤n-l by omega,show k≤n by omega,
    show l≤n-k by omega,ite_true,show n-l-k=n-k-l by omega]
  field_simp [hp]

theorem gaussian_disjoint_flag_all (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (n k l : ℕ) (hkn : k≤n) (hln : l≤n) :
    gaussian z n l*gaussian z (n-l) k=gaussian z n k*gaussian z (n-k) l := by
  by_cases h : k+l≤n
  · exact gaussian_disjoint_flag z hz0 hz1 n k l h
  · simp [gaussian,show ¬k≤n-l by omega,show ¬l≤n-k by omega]

end BoseBurton
