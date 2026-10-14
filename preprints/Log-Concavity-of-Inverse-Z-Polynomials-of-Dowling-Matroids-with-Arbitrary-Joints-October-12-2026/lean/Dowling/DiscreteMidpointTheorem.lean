import Dowling.DiscreteMidpointSums

noncomputable section
namespace Dowling
open Finset

/-- The finite counting-measure midpoint inequality, with literal integer floor/ceiling. -/
theorem discrete_midpoint_four_functions (f g h l : ℤ→ℝ) (N : ℕ)
    (hf : ∀ i,0≤f i) (hg : ∀ i,0≤g i) (hh : ∀ i,0≤h i) (hl : ∀ i,0≤l i)
    (hg0 : ∀ i,i < 0 ∨ (N : ℤ) < i → g i=0)
    (hh0 : ∀ i,i < 0 ∨ (N : ℤ) < i → h i=0)
    (hl0 : ∀ i,i < 0 ∨ (N : ℤ) < i → l i=0)
    (hmid : ∀ i j,f i*g j≤h ((i+j)/2)*l ((i+j+1)/2)) :
    (∑ i ∈ range (N+1),f i)*(∑ i ∈ range (N+1),g i)≤
      (∑ i ∈ range (N+1),h i)*(∑ i ∈ range (N+1),l i) := by
  have hdiag (z : ℤ) :
      (∑ i ∈ range (N+1),f i*g (z-i))≤∑ i ∈ range (N+1),h i*l (z-i) := by
    let F : ℕ→ℝ := fun i=>f i*g (z-i)
    let H : ℤ→ℝ := fun i=>h i*l (z-i)
    have hF : ∀ i,0≤F i := fun i=>mul_nonneg (hf _) (hg _)
    have hH : ∀ i,0≤H i := fun i=>mul_nonneg (hh _) (hl _)
    have hsingle (i : ℕ) : F i≤H (z/2) := by
      have hm := hmid (i : ℤ) (z-i)
      have ha : (i : ℤ)+(z-i)=z := by omega
      have hb : (z+1)/2=z-z/2 := by omega
      simpa only [F,H,ha,hb] using hm
    have hcross (i j : ℕ) : F i*F j≤H ((z+i-j)/2)*H ((z+j-i)/2) := by
      have h1 := hmid (i : ℤ) (z-j)
      have h2 := hmid (j : ℤ) (z-i)
      have hp := mul_le_mul h1 h2 (mul_nonneg (hf _) (hg _)) (mul_nonneg (hh _) (hl _))
      have ha : ((i : ℤ)+(z-j))/2=(z+i-j)/2 := by omega
      have hb : ((j : ℤ)+(z-i))/2=(z+j-i)/2 := by omega
      have hc : ((i : ℤ)+(z-j)+1)/2=z-(z+j-i)/2 := by omega
      have hd : ((j : ℤ)+(z-i)+1)/2=z-(z+i-j)/2 := by omega
      rw [ha,hb,hc,hd] at hp
      dsimp only [F,H]
      nlinarith [hp]
    have hsupp (i : ℤ) (hi : i < 0 ∨ (N : ℤ) < i) : H i=0 := by
      simp only [H,hh0 i hi,zero_mul]
    exact (midpoint_diagonal_bound F H z hF hH hsingle hcross N).trans
      (midpointBand_le_supported_sum H z N N hH hsupp)
  rw [← midpoint_convolution_sum f g N hg0,← midpoint_convolution_sum h l N hl0]
  exact sum_le_sum (fun z _=>hdiag z)

end Dowling
