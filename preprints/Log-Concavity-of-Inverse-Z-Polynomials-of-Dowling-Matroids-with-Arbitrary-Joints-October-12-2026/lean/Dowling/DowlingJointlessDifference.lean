import Dowling.DowlingJointlessTilt
import Dowling.DowlingJointlessPositivity

noncomputable section
namespace Dowling

 theorem jointlessNormalizedWeight_difference (a μ : ℝ) (hμ : 0<μ) (j : ℕ) (hj : 1≤j) :
    jointlessNormalizedWeight a μ (j-1)+jointlessNormalizedWeight a μ (j+1)-
      2*jointlessNormalizedWeight a μ j=
        -((μ/(μ+1/2))^j*(μ+1/2)^2/μ^4)*
          jointlessTilt (μ/(μ+1/2)) (jointlessRatioFunction a μ) (μ+1/2-j) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  have hm : μ≠0 := ne_of_gt hμ
  have hp : μ+1/2≠0 := by linarith
  simp only [Nat.succ_sub_one,jointlessNormalizedWeight,Nat.cast_succ,
    jointlessTilt,pow_succ]
  have h1 : μ+1/2-(k : ℝ)=μ+1/2-((k : ℝ)+1)+1 := by ring
  have h2 : μ+1/2-((k : ℝ)+1+1)=μ+1/2-((k : ℝ)+1)-1 := by ring
  rw [h1,h2]
  field_simp
  ring

 theorem jointlessNormalizedWeight_difference_large (a μ : ℝ) (hμ : 0<μ) (j : ℕ) (hj : 2≤j) :
    jointlessNormalizedWeight a μ (j-1)+jointlessNormalizedWeight a μ (j+1)-
      2*jointlessNormalizedWeight a μ j=
        -(μ/(μ+1/2))^(j-2)/μ^2*
          jointlessTilt (μ/(μ+1/2)) (jointlessRatioFunction a μ) (μ+1/2-j) := by
  rw [jointlessNormalizedWeight_difference a μ hμ j (by omega)]
  have hm : μ≠0 := ne_of_gt hμ
  have hp : μ+1/2≠0 := by linarith
  nth_rw 1 [show j=j-2+2 by omega]
  rw [pow_add,div_pow]
  field_simp

 theorem jointlessNormalizedWeight_difference_one (a μ : ℝ) (hμ : 0<μ) :
    jointlessNormalizedWeight a μ 0+jointlessNormalizedWeight a μ 2-
      2*jointlessNormalizedWeight a μ 1=
        -((μ+1/2)/μ)/μ^2*
          jointlessTilt (μ/(μ+1/2)) (jointlessRatioFunction a μ) (μ-1/2) := by
  have h := jointlessNormalizedWeight_difference a μ hμ 1 le_rfl
  norm_num only at h
  rw [h]
  have hm : μ≠0 := ne_of_gt hμ
  have hp : μ+1/2≠0 := by linarith
  rw [show μ+1/2-1=μ-1/2 by ring]
  simp only [pow_one]
  field_simp

 theorem jointlessRatio_tilt_decomposition (a μ r s : ℝ) (hr : 1<r) :
    jointlessTilt s (jointlessRatioFunction a μ) r=
      jointlessTilt s (jointlessQuadratic a μ) r+
      (a*(1-a)*μ/4-a^2/2)*jointlessTilt s (fun x=>1/x) r+
      (3*a^2/16)*jointlessTilt s (fun x=>1/(x*(x+1))) r-
      (a^2*μ/8)*jointlessTilt s jointlessAdverse r := by
  unfold jointlessTilt
  rw [jointlessRatio_decomposition a μ (r-1) (by linarith),
    jointlessRatio_decomposition a μ (r+1) (by linarith),
    jointlessRatio_decomposition a μ r (by linarith)]
  ring

 theorem jointlessAdverse_pos {r : ℝ} (hr : 0<r) : 0<jointlessAdverse r := by
  unfold jointlessAdverse
  positivity

 theorem jointlessAdverse_tilt_upper {s r η : ℝ} (hs : 0<s) (hs1 : s≤1)
    (hr : 1<r) (hη : 0≤η) (hη1 : η≤1) :
    η*jointlessTilt s jointlessAdverse r≤jointlessAdverse (r-1)+s⁻¹*jointlessAdverse (r+1) := by
  have hm := jointlessAdverse_pos (show 0<r-1 by linarith)
  have hc := jointlessAdverse_pos (show 0<r by linarith)
  have hp := jointlessAdverse_pos (show 0<r+1 by linarith)
  have hηs : η*s≤1 := (mul_le_mul_of_nonneg_left hs1 hη).trans (by simpa using hη1)
  have hηsi : η*s⁻¹≤s⁻¹ := by simpa using mul_le_mul_of_nonneg_right hη1 (inv_nonneg.mpr hs.le)
  have h1 := mul_le_mul_of_nonneg_right hηs hm.le
  have h2 := mul_le_mul_of_nonneg_right hηsi hp.le
  have h3 : 0≤η*jointlessAdverse r := mul_nonneg hη hc.le
  unfold jointlessTilt
  nlinarith

end Dowling
