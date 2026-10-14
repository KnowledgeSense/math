import Dowling.DowlingJointlessCorrection

noncomputable section
namespace Dowling

 theorem jointlessNormalizedWeight_large (a μ : ℝ) (hμ : 0<μ) (j : ℕ) (hj : 2≤j) :
    jointlessNormalizedWeight a μ j=
      1-(μ/(μ+1/2))^(j-2)*jointlessRatioFunction a μ (μ+1/2-j)/μ^2 := by
  have hm : μ≠0 := ne_of_gt hμ
  have hLam : μ+1/2≠0 := by linarith
  unfold jointlessNormalizedWeight
  nth_rw 1 [show j=j-2+2 by omega]
  rw [pow_add,div_pow]
  field_simp

 theorem jointlessNormalizedWeight_lower {a μ K : ℝ} (hμ : 0<μ) (hK : 0<K)
    (j : ℕ) (hj : 2≤j)
    (hP : jointlessRatioFunction a μ (μ+1/2-j)<K*μ^2) :
    1-K<jointlessNormalizedWeight a μ j := by
  rw [jointlessNormalizedWeight_large a μ hμ j hj]
  have hs0 : 0≤μ/(μ+1/2) := by positivity
  have hs1 : μ/(μ+1/2)≤1 := (div_le_one (by linarith)).mpr (by linarith)
  have hpow0 : 0≤(μ/(μ+1/2))^(j-2) := pow_nonneg hs0 _
  have hpow1 : (μ/(μ+1/2))^(j-2)≤1 := pow_le_one₀ hs0 hs1
  have hbound : (μ/(μ+1/2))^(j-2)*jointlessRatioFunction a μ (μ+1/2-j)<K*μ^2 := by
    by_cases hp : 0≤jointlessRatioFunction a μ (μ+1/2-j)
    · have hh := mul_le_mul_of_nonneg_right hpow1 hp
      rw [one_mul] at hh
      exact hh.trans_lt hP
    · have hprod : (μ/(μ+1/2))^(j-2)*jointlessRatioFunction a μ (μ+1/2-j)≤0 :=
        mul_nonpos_of_nonneg_of_nonpos hpow0 (le_of_not_ge hp)
      exact hprod.trans_lt (by positivity)
  have hdiv := (div_lt_iff₀ (sq_pos_of_pos hμ)).mpr hbound
  linarith

 theorem jointlessNormalizedWeight_one_pos {a μ : ℝ} (ha : 0<a) (ha2 : a≤1/2)
    (hμ : 1/2<μ) : 0<jointlessNormalizedWeight a μ 1 := by
  rw [jointlessNormalizedWeight_one a μ hμ]
  have hr : 0<μ-1/2 := by linarith
  have hs := sq_nonneg (a/(μ-1/2)-(1-3*a/2))
  have haSq : a^2≤a/2 := by nlinarith
  have heq : a^2/(2*(μ-1/2)^2)=(a/(μ-1/2))^2/2 := by field_simp
  have hcross : a*(1-3*a/2)/(μ-1/2)=(a/(μ-1/2))*(1-3*a/2) := by ring
  rw [heq,hcross]
  nlinarith

 theorem jointlessNormalizedWeight_pos {a : ℝ} (ha : 0<a) (ha2 : a≤1/2)
    (n j : ℕ) (hn : 2≤n) (hj : 2*j≤n) :
    0<jointlessNormalizedWeight a ((n+a-1)/2) j := by
  let μ : ℝ := (n+a-1)/2
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hμ : 1/2<μ := by dsimp [μ]; linarith
  change 0<jointlessNormalizedWeight a μ j
  rcases j with _ | j
  · rw [jointlessNormalizedWeight_zero a μ (by linarith)]
    apply div_pos
    · apply mul_pos (by linarith)
      dsimp [μ]
      linarith
    · linarith
  rcases j with _ | j
  · exact jointlessNormalizedWeight_one_pos ha ha2 hμ
  have hj2 : 2≤j+1+1 := by omega
  let r : ℝ := μ+1/2-(j+1+1 : ℕ)
  have hjR : (2 : ℝ)*(j+1+1 : ℕ)≤n := by exact_mod_cast hj
  have hj2R : (2 : ℝ)≤(j+1+1 : ℕ) := by exact_mod_cast hj2
  have hr0 : 0<r := by dsimp [r,μ]; linarith
  have hK : 0<2*a-2*a^2/3 := by
    have hfactor : 0<a*(2-2*a/3) := mul_pos ha (by linarith)
    nlinarith
  have hP : jointlessRatioFunction a μ r<(2*a-2*a^2/3)*μ^2 := by
    by_cases heven : n=2*(j+1+1)
    · have hre : r=a/2 := by dsimp [r,μ]; rw [heven]; push_cast; ring
      rw [hre]
      exact jointlessRatio_terminal_lt ha ha2 (by linarith)
    · have hgap : (2 : ℝ)*(j+1+1 : ℕ)+1≤n := by exact_mod_cast (show 2*(j+1+1)+1≤n by omega)
      have hr : 1/2≤r := by dsimp [r,μ]; linarith
      have hm : r+3/2≤μ := by dsimp [r]; linarith
      have hres := jointlessReserve_pos ha ha2 hr hm
      unfold jointlessReserve at hres
      unfold jointlessRatioFunction
      apply (div_lt_iff₀ hr0).mpr
      nlinarith
  have hl := jointlessNormalizedWeight_lower (a := a) (μ := μ) (by linarith) hK (j+1+1) hj2 hP
  have hK1 : 2*a-2*a^2/3<1 := by nlinarith [sq_pos_of_pos ha]
  linarith

end Dowling
