import Dowling.DiscreteMidpointAlgebra

noncomputable section
namespace Dowling
open Finset

theorem midpoint_sum_two_ends (F : ℕ→ℝ) (n : ℕ) :
    ∑ i ∈ range (n+3), F i = F 0+(∑ i ∈ range (n+1),F (i+1))+F (n+2) := by
  rw [sum_range_succ,sum_range_succ']
  ring

/-- Finite diagonal comparison proved by removing one or both extreme points. -/
theorem midpoint_diagonal_bound (F : ℕ→ℝ) (H : ℤ→ℝ) (z : ℤ)
    (hF : ∀ i,0≤F i) (hH : ∀ i,0≤H i)
    (hdiag : ∀ i,F i≤H (z/2))
    (hcross : ∀ i j,F i*F j≤H ((z+i-j)/2)*H ((z+j-i)/2)) (n : ℕ) :
    ∑ i ∈ range (n+1), F i≤midpointBand H z n := by
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    have hshift (i j : ℕ) : F (i+1)*F (j+1)≤H ((z+i-j)/2)*H ((z+j-i)/2) := by
      have h := hcross (i+1) (j+1)
      convert h using 1; congr 2 <;> omega
    cases n with
    | zero => simpa using hdiag 0
    | succ n =>
      have hprod : min (F 0) (F (n+1))*max (F 0) (F (n+1))≤
          H ((z-(n+1 : ℕ))/2)*H ((z+(n+1 : ℕ))/2) := by
        rw [min_mul_max]
        simpa using hcross 0 (n+1)
      have hmin : 0≤min (F 0) (F (n+1)) := le_min (hF _) (hF _)
      have hmax : 0≤max (F 0) (F (n+1)) := le_trans (hF _) (le_max_left _ _)
      by_cases hbig : max (H ((z-(n+1 : ℕ))/2)) (H ((z+(n+1 : ℕ))/2))<max (F 0) (F (n+1))
      · have hsmall := midpoint_small_endpoint hmin (hH _) (hH _) hprod hbig
        have hb := midpointBand_one_step H z n
        by_cases hend : F 0≤F (n+1)
        · rw [min_eq_left hend] at hsmall
          have hI := ih n (by omega) (fun i=>F (i+1)) (fun i=>hF _) (fun i=>hdiag _) hshift
          rw [sum_range_succ']
          linarith
        · rw [min_eq_right (le_of_not_ge hend)] at hsmall
          have hI := ih n (by omega) F hF hdiag hcross
          rw [sum_range_succ]
          linarith
      · have hends := midpoint_two_sum hmin hmax (hH _) (hH _)
          min_le_max hprod (le_of_not_gt hbig)
        rw [min_add_max] at hends
        cases n with
        | zero =>
          have hb : midpointBand H z 1=H ((z-1)/2)+H ((z+1)/2) := by
            simp only [midpointBand,sum_range_succ,sum_range_zero,zero_add,Nat.cast_zero,
              Nat.cast_one,add_zero]
            rw [show (z-1)/2+1=(z+1)/2 by omega]
          simpa [hb,sum_range_succ] using hends
        | succ n =>
          have hI := ih n (by omega) (fun i=>F (i+1)) (fun i=>hF _) (fun i=>hdiag _) hshift
          rw [show n+1+1+1=n+3 by omega,midpoint_sum_two_ends,
            show n+1+1=n+2 by omega,midpointBand_two_step]
          linarith

end Dowling
