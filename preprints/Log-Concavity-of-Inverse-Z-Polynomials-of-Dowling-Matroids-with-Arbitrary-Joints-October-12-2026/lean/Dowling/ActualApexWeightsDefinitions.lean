import Dowling.SingleJointBoundary
import Dowling.RetainedActualCoefficients

noncomputable section
namespace Dowling
open Finset Polynomial

/-- Exact actual odd-rank KL coefficient in the source factorial normalization. -/
def apexTauWeight (h : ℕ) : ℝ :=
  ((fullP Unit (2*h-1)).coeff (h-1) : ℝ)/((2*h).factorial : ℝ)

/-- The supported ratio of the shifted full-Dowling raised weight to its
original fixed-total counterpart, with natural powers only. -/
def apexF (n h j : ℕ) : ℝ :=
  if h≤j then (j.descFactorial h : ℝ)*(((n : ℝ)+1)/2-h)^(j-h)/(((n : ℝ)+1)/2)^j*
    (((n : ℝ)+1)/2)^2/(((n : ℝ)+1)/2-h)^2 else 0

def apexNormalizedWeight (n k j : ℕ) : ℝ :=
  (k : ℝ)/n+∑ h∈Icc 1 j,
    (((n-k : ℕ) : ℝ)/n-((n-k).choose (2*h) : ℝ)/(n.choose (2*h) : ℝ))*apexTauWeight h*apexF n h j

def apexRaisedWeight (n k j : ℕ) : ℝ := dowlingBaseWeight 1 n j*apexNormalizedWeight n k j

theorem apexTauWeight_pos (h : ℕ) (hh : 1≤h) : 0<apexTauWeight h := by
  apply div_pos
  · by_cases h1 : h=1
    · subst h
      norm_num [fullP_one]
    · have hs := fullP_odd_top_source Unit h (by omega)
      rw [hs]
      have hb : (0 : ℝ)<((2*h-1 : ℕ) : ℝ) := by exact_mod_cast (show 0<2*h-1 by omega)
      have hd : (0 : ℝ)<((2*h-3).doubleFactorial : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos (2*h-3)
      positivity
  · positivity

end Dowling
