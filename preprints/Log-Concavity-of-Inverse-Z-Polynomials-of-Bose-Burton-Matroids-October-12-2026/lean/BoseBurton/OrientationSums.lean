import BoseBurton.GaussianFlags
import BoseBurton.GaussianPartialAll

noncomputable section
namespace BoseBurton
open Finset

theorem sum_range_min_support (f : ℕ→ℝ) (h n : ℕ) (hf : ∀ i, n < i→f i=0) :
    (∑ i∈range (min h n+1),f i)=∑ i∈range (h+1),f i := by
  apply sum_subset (range_mono (by omega))
  intro i hi hni
  apply hf
  simp only [mem_range] at hi hni
  omega

theorem first_orientation_sum (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (n h k : ℕ) (hk : 1≤k) :
    (∑ l∈range (min h n+1),(-1:ℝ)^l*z^(l.choose 2)*gaussian z n l*
      (if l≤k then gaussian z (n-l) (k-l) else 0))=
    if k≤n ∧ h<k then (-1:ℝ)^h*z^((h+1).choose 2)*gaussian z n k*gaussian z (k-1) h else 0 := by
  by_cases hkn : k≤n
  · have he : (∑ l∈range (min h n+1),(-1:ℝ)^l*z^(l.choose 2)*gaussian z n l*
        (if l≤k then gaussian z (n-l) (k-l) else 0))=
        gaussian z n k*(∑ l∈range (min h n+1),(-1:ℝ)^l*z^(l.choose 2)*gaussian z k l) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro l _
      by_cases hl : l≤k
      · rw [ite_eq_left hl]
        have hf := gaussian_flag z hz0 hz1 n k l hl hkn
        linear_combination (-1:ℝ)^l*z^(l.choose 2)*hf
      · simp [hl,gaussian_outside z k l (by omega)]
    rw [he,sum_range_min_support _ h n (by
      intro i hi
      exact gaussian_alternating_above z k i (by omega)),
      gaussian_partial_alternating_all z hz0 hz1 k h hk]
    by_cases hh : h<k <;> simp [hkn,hh]; ring
  · rw [ite_eq_right (by omega)]
    apply sum_eq_zero
    intro l hl
    have hln : l≤n := by simp only [mem_range] at hl; omega
    by_cases hlk : l≤k
    · simp [hlk,gaussian_outside z (n-l) (k-l) (by omega)]
    · simp [hlk]

theorem second_orientation_sum (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (n h k : ℕ) (hh : 1≤h) (hk : k<n) :
    (∑ l∈range (min h n+1),(-1:ℝ)^l*z^(l.choose 2)*gaussian z n l*
      (if l<h then gaussian z (n-l) k else 0))=
    if h≤n-k then (-1:ℝ)^(h-1)*z^(h.choose 2)*gaussian z n k*gaussian z (n-k-1) (h-1) else 0 := by
  have he : (∑ l∈range (min h n+1),(-1:ℝ)^l*z^(l.choose 2)*gaussian z n l*
      (if l<h then gaussian z (n-l) k else 0))=
      gaussian z n k*(∑ l∈range (min h n+1),
        if l<h then (-1:ℝ)^l*z^(l.choose 2)*gaussian z (n-k) l else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro l hl
    have hln : l≤n := by simp only [mem_range] at hl; omega
    by_cases hlh : l<h
    · rw [ite_eq_left hlh,ite_eq_left hlh]
      have hf := gaussian_disjoint_flag_all z hz0 hz1 n k l hk.le hln
      linear_combination (-1:ℝ)^l*z^(l.choose 2)*hf
    · simp [hlh]
  rw [he,sum_range_min_support _ h n (by
    intro i hi
    by_cases hh : i<h
    · simp [hh,gaussian_outside z (n-k) i (by omega)]
    · simp [hh]),sum_range_succ]
  simp only [lt_self_iff_false,ite_false,add_zero]
  have hs : (∑ l∈range h,if l<h then (-1:ℝ)^l*z^(l.choose 2)*gaussian z (n-k) l else 0)=
      ∑ l∈range h,(-1:ℝ)^l*z^(l.choose 2)*gaussian z (n-k) l := by
    apply sum_congr rfl
    intro l hl
    rw [ite_eq_left (mem_range.mp hl)]
  rw [hs,show h=(h-1)+1 by omega,
    gaussian_partial_alternating_all z hz0 hz1 (n-k) (h-1) (by omega),
    show h-1+1=h by omega]
  by_cases hle : h≤n-k
  · rw [ite_eq_left (by omega),ite_eq_left hle]
    ring
  · rw [ite_eq_right (by omega),ite_eq_right hle,mul_zero]

end BoseBurton
