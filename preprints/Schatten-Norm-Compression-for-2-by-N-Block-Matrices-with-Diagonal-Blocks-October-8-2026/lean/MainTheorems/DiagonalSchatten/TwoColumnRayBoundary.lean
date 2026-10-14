import MainTheorems.DiagonalSchatten.RayBoundaryContinuity

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

theorem two_column_nonzero_of_gram (X : Matrix (Fin 2) (Fin 2) ℝ)
    (hX : ∀ i j, 0 ≤ X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (j : Fin 2) :
    0 < X 0 j ∨ 0 < X 1 j := by
  have hd : X.det ≠ 0 := by
    rw [twoByTwo_gramDet_eq_det_sq] at hdet
    exact sq_pos_iff.mp hdet
  by_cases h0 : X 0 j = 0
  · right
    have h1 : X 1 j ≠ 0 := by
      intro h1
      apply hd
      fin_cases j
      · change X 0 0 = 0 at h0
        change X 1 0 = 0 at h1
        simp [Matrix.det_fin_two, h0, h1]
      · change X 0 1 = 0 at h0
        change X 1 1 = 0 at h1
        simp [Matrix.det_fin_two, h0, h1]
    exact lt_of_le_of_ne (hX 1 j) (Ne.symm h1)
  · exact Or.inl (lt_of_le_of_ne (hX 0 j) (Ne.symm h0))

theorem two_column_ray_boundary {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) (s : ℝ)
    (hbound : ∀ (T : Matrix (Fin 2) (Fin 2) ℝ) (Z : Fin 3 → ℝ),
      (∀ i j, 0 < T i j) →
      0 < gramFirst T * gramSecond T - gramCross T ^ 2 →
      s * (∑ j, (compressionRay p T Z).functional (fun i => T i j)) ≤
        s * (inverseGramQuadratic p T Z / 2))
    (X : Matrix (Fin 2) (Fin 2) ℝ) (Z : Fin 3 → ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (hc : 0 < gramCross X) :
    s * (∑ j, (compressionRay p X Z).functional (fun i => X i j)) ≤
      s * (inverseGramQuadratic p X Z / 2) := by
  let P : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun e => Matrix.of fun i j => X i j + e
  have hP : Continuous P := by unfold P; fun_prop
  have hP0 : P 0 = X := by ext i j; simp [P]
  have hD (j : Fin 2) : (compressionRay p X Z).denominator (fun i => X i j) ≠ 0 :=
    (compressionRay_denominator_nonnegative hp hp2 X Z _ hdet hc
      (fun i => hX i j) (two_column_nonzero_of_gram X hX hdet j)).ne'
  have hsum : ContinuousAt (fun T =>
      s * ∑ j, (compressionRay p T Z).functional (fun i => T i j)) X := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using
      ((continuousAt_compressionRay_functional p X Z 0 hdet hc.ne' (hD 0)).add
        (continuousAt_compressionRay_functional p X Z 1 hdet hc.ne' (hD 1))).const_mul s
  have hright : ContinuousAt (fun T => s * (inverseGramQuadratic p T Z / 2)) X :=
    ((continuousAt_inverseGramQuadratic hp2 X Z hdet hc).div_const 2).const_mul s
  have hdetC : ContinuousAt (fun e => gramFirst (P e) * gramSecond (P e) - gramCross (P e) ^ 2) 0 := by
    unfold P gramFirst gramSecond gramCross
    fun_prop
  have hedet : ∀ᶠ e in 𝓝 (0 : ℝ), 0 < gramFirst (P e) * gramSecond (P e) - gramCross (P e) ^ 2 :=
    hdetC.eventually (by simpa only [hP0] using eventually_gt_nhds hdet)
  have hleftP := hsum.comp_of_eq hP.continuousAt hP0
  have hrightP := hright.comp_of_eq hP.continuousAt hP0
  have he := le_of_tendsto_of_tendsto
    (hleftP.tendsto.mono_left nhdsWithin_le_nhds)
    (hrightP.tendsto.mono_left nhdsWithin_le_nhds)
    (show ∀ᶠ e in 𝓝[>] (0 : ℝ),
      s * (∑ j, (compressionRay p (P e) Z).functional (fun i => P e i j)) ≤
        s * (inverseGramQuadratic p (P e) Z / 2) by
      filter_upwards [self_mem_nhdsWithin, hedet.filter_mono nhdsWithin_le_nhds] with e he hde
      exact hbound (P e) Z (fun i j => add_pos_of_nonneg_of_pos (hX i j) he) hde)
  simpa only [Function.comp_def, hP0] using he

theorem two_column_ray_nonnegative_upper {p : ℝ} (hp : 2 < p)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (Z : Fin 3 → ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (hc : 0 < gramCross X) :
    (∑ j, (compressionRay p X Z).functional (fun i => X i j)) ≤ inverseGramQuadratic p X Z / 2 := by
  simpa only [one_mul] using two_column_ray_boundary (by linarith : 1 < p) (ne_of_gt hp) 1
    (fun T W hT hd => by simpa only [one_mul] using two_column_ray_bound_upper hp T W hT hd)
    X Z hX hdet hc

theorem two_column_ray_nonnegative_lower {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (Z : Fin 3 → ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (hc : 0 < gramCross X) :
    inverseGramQuadratic p X Z / 2 ≤
      ∑ j, (compressionRay p X Z).functional (fun i => X i j) := by
  simpa only [neg_one_mul, neg_le_neg_iff] using two_column_ray_boundary hp (ne_of_lt hp2) (-1)
    (fun T W hT hd => by simpa only [neg_one_mul, neg_le_neg_iff] using
      two_column_ray_bound_lower hp hp2 T W hT hd)
    X Z hX hdet hc

end

end ResearchMain.DiagonalSchatten
