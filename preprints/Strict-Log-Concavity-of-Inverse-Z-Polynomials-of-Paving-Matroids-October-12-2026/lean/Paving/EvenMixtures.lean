import Paving.MiddleComponents

noncomputable section
open Finset
namespace Paving

/-- The penultimate inequality for any actual-weight mixture meeting the geometric bound. -/
theorem even_penultimate_mixture_strict {ι : Type*} (s : Finset ι) (w : ι→ℝ)
    (h : ι→Option ℕ) (m n : ℕ) (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (hw : ∀j∈s,0 ≤ w j) (hs : ∑j∈s,w j=1)
    (hv : ∀j∈s,ValidParameter (2*m) n (h j))
    (hfloor : penultimateFloor (middleBinomial m) ((n:ℝ)-m) m ≤
      ∑j∈s,w j*lowerComponent (2*m) n (h j) (m-1)) :
    (∑j∈s,w j*lowerComponent (2*m) n (h j) (m-2))*
      ((∑j∈s,w j*lowerComponent (2*m) n (h j) (m-1))+
        middleIncrement (middleBinomial m) ((n:ℝ)-m) m) <
      (∑j∈s,w j*lowerComponent (2*m) n (h j) (m-1))^2 := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (2:ℝ)*m ≤ n := by exact_mod_cast hn
  have hC := middleBinomial_positive (show 1 ≤ m by omega)
  apply penultimate_strict hC (by linarith) (by linarith) hfloor
  have hpoint : ∀j∈s,lowerComponent (2*m) n (h j) (m-2) <
      penultimateRatio ((n:ℝ)-m) m*lowerComponent (2*m) n (h j) (m-1) := by
    intro j hj
    rw [lowerComponent_previous hm hn (h j) (hv j hj),
      lowerComponent_penultimate (show 1 ≤ m by omega) hn (h j) (hv j hj)]
    have hu := componentPosition_bounds (show 1 ≤ m by omega) hn (h j) (hv j hj)
    have hratio := previousComponent_ratio (m:=(m:ℝ)) (N:=(n:ℝ)-m)
      (by linarith) hu.1 hu.2
    nlinarith [mul_lt_mul_of_pos_left hratio hC]
  have hsum := mixture_strict_bound s w _ _ hw hs hpoint
  calc
    _ < ∑j∈s,w j*(penultimateRatio ((n:ℝ)-m) m*lowerComponent (2*m) n (h j) (m-1)) := hsum
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro j _; ring

end Paving
