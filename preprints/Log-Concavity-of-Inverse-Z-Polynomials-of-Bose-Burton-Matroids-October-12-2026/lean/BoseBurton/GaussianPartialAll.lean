import BoseBurton.GaussianAlternating

noncomputable section
namespace BoseBurton
open Finset

theorem gaussian_alternating_above (z : ℝ) (n i : ℕ) (hi : n < i) :
    (-1:ℝ)^i*z^(i.choose 2)*gaussian z n i=0 := by
  rw [gaussian_outside z n i hi,mul_zero]

theorem gaussian_partial_alternating_all (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (n b : ℕ) (hn : 1≤n) :
    (∑ i∈range (b+1),(-1:ℝ)^i*z^(i.choose 2)*gaussian z n i)=
      if b<n then (-1:ℝ)^b*z^((b+1).choose 2)*gaussian z (n-1) b else 0 := by
  by_cases hb : b<n
  · rw [ite_eq_left hb]
    have h := gaussian_partial_alternating z hz0 hz1 (n-1) b (by omega)
    simpa only [show n-1+1=n by omega] using h
  · rw [ite_eq_right hb]
    have he : (∑ i∈range (b+1),(-1:ℝ)^i*z^(i.choose 2)*gaussian z n i)=
        ∑ i∈range (n+1),(-1:ℝ)^i*z^(i.choose 2)*gaussian z n i := by
      symm
      apply sum_subset (range_mono (by omega))
      intro i _ hi
      exact gaussian_alternating_above z n i (by simp only [mem_range] at hi; omega)
    rw [he]
    have h := gaussian_full_alternating z hz0 hz1 (n-1)
    simpa only [show n-1+1=n by omega,show n-1+2=n+1 by omega] using h

end BoseBurton
