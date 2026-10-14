import MainTheorems.DiagonalSchatten.CompressionRayParameters
import MainTheorems.DiagonalSchatten.TwoColumnSecondVariation

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def inverseGramQuadratic {J : Type*} [Fintype J] (p : ℝ)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) : ℝ :=
  symmetricTraceProduct Z
    (symmetricPowerVariation (1 / ((p - 2) / 2))
      (symmetricPower ((p - 2) / 2) (gramCoordinates X)) Z)

theorem symmetricTraceProduct_comm (Z J : Fin 3 → ℝ) :
    symmetricTraceProduct Z J = symmetricTraceProduct J Z := by
  unfold symmetricTraceProduct
  ring

theorem two_column_ray_bound_upper {p : ℝ} (hp : 2 < p)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (Z : Fin 3 → ℝ) (hX : ∀ i j, 0 < X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    (∑ j, (compressionRay p X Z).functional (fun i => X i j)) ≤ inverseGramQuadratic p X Z / 2 := by
  let g := compressionRay p X Z
  let Y := g.inverseRows X
  let J := gramVariation X Y
  let S := ∑ j, g.functional (fun i => X i j)
  let T := symmetricTraceProduct J
    (symmetricPowerVariation ((p - 2) / 2) (gramCoordinates X) J)
  let R := inverseGramQuadratic p X Z
  have hγ : 0 < (p - 2) / 2 := by linarith
  obtain ⟨ha, hb, hc⟩ := compressionRay_upper hp X Z hX hdet
  have hk : 0 < g.k := by change 0 < p - 2; linarith
  have hn : ∀ i j, X i j ≠ 0 := fun i j => (hX i j).ne'
  have hd : ∀ j, kernelFirst g.k g.a g.c (X 0 j) (X 1 j) *
      kernelSecond g.k g.b g.c (X 0 j) (X 1 j) - g.c ^ 2 ≠ 0 := fun j =>
    (compressionKernel_upper hk ha hb hc (hX 0 j) (hX 1 j)).2.ne'
  have henergy : S = compressionKernelEnergy p X Y := by
    dsimp only [S, Y]
    rw [g.inverseRows_energy X hn hd]
    exact compressionRay_energy p X (g.inverseRows X) Z
  have hS : 0 ≤ S := by
    rw [henergy, ← compressionRay_energy p X Y Z]
    exact Finset.sum_nonneg fun j _ =>
      compressionKernel_quadratic_upper hk ha hb hc (hX 0 j) (hX 1 j) (Y 0 j) (Y 1 j)
  have hA : T ≤ 2 * S := by
    rw [henergy]
    exact two_column_second_variation_upper hp X Y hX hdet
  have hR : 0 ≤ R := symmetricPowerVariation_inverse_nonnegative hγ
    (gramCoordinates X) Z (positiveRows_gramFirst X hX) hdet (positiveRows_gramCross X hX).ne'
  have htrace : symmetricTraceProduct Z J = 2 * S := by
    have h := g.inverseRows_trace X hn
    have he : ![g.z1, g.z2, g.z12] = Z := by
      funext i
      fin_cases i <;> simp [g, compressionRay]
    rw [he] at h
    exact h
  have hCS : (2 * S) ^ 2 ≤ T * R := by
    have h := symmetricPowerVariation_inverse_cauchy hγ.ne' (gramCoordinates X) J Z
      (positiveRows_gramFirst X hX) hdet (positiveRows_gramCross X hX).ne'
    rw [symmetricTraceProduct_comm J Z, htrace] at h
    simpa only [T, R, inverseGramQuadratic, mul_comm] using h
  exact positive_dual_bound hS hR hA hCS

theorem two_column_ray_bound_lower {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (Z : Fin 3 → ℝ) (hX : ∀ i j, 0 < X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    inverseGramQuadratic p X Z / 2 ≤
      ∑ j, (compressionRay p X Z).functional (fun i => X i j) := by
  let g := compressionRay p X Z
  let Y := g.inverseRows X
  let J := gramVariation X Y
  let S := ∑ j, g.functional (fun i => X i j)
  let T := symmetricTraceProduct J
    (symmetricPowerVariation ((p - 2) / 2) (gramCoordinates X) J)
  let R := inverseGramQuadratic p X Z
  have hγ : (p - 2) / 2 < 0 := by linarith
  obtain ⟨ha, hb, hc, hHdet⟩ := compressionRay_lower hp2 X Z hX hdet
  have hk1 : -1 < g.k := by change -1 < p - 2; linarith
  have hk : g.k < 0 := by change p - 2 < 0; linarith
  have hn : ∀ i j, X i j ≠ 0 := fun i j => (hX i j).ne'
  have hd : ∀ j, kernelFirst g.k g.a g.c (X 0 j) (X 1 j) *
      kernelSecond g.k g.b g.c (X 0 j) (X 1 j) - g.c ^ 2 ≠ 0 := fun j =>
    (compressionKernel_lower hk1 hk ha hb hc hHdet (hX 0 j) (hX 1 j)).2.ne'
  have henergy : S = compressionKernelEnergy p X Y := by
    dsimp only [S, Y]
    rw [g.inverseRows_energy X hn hd]
    exact compressionRay_energy p X (g.inverseRows X) Z
  have hS : S ≤ 0 := by
    rw [henergy, ← compressionRay_energy p X Y Z]
    exact Finset.sum_nonpos fun j _ =>
      compressionKernel_quadratic_lower hk1 hk ha hb hc hHdet
        (hX 0 j) (hX 1 j) (Y 0 j) (Y 1 j)
  have hA : -T ≤ -2 * S := by
    have h := two_column_second_variation_lower hp hp2 X Y hX hdet
    rw [← henergy] at h
    linarith
  have hR : R ≤ 0 := symmetricPowerVariation_inverse_nonpositive hγ
    (gramCoordinates X) Z (positiveRows_gramFirst X hX) hdet (positiveRows_gramCross X hX).ne'
  have htrace : symmetricTraceProduct Z J = 2 * S := by
    have h := g.inverseRows_trace X hn
    have he : ![g.z1, g.z2, g.z12] = Z := by
      funext i
      fin_cases i <;> simp [g, compressionRay]
    rw [he] at h
    exact h
  have hCS : (2 * S) ^ 2 ≤ (-T) * (-R) := by
    have h := symmetricPowerVariation_inverse_cauchy hγ.ne (gramCoordinates X) J Z
      (positiveRows_gramFirst X hX) hdet (positiveRows_gramCross X hX).ne'
    rw [symmetricTraceProduct_comm J Z, htrace] at h
    simpa only [T, R, inverseGramQuadratic, neg_mul_neg, mul_comm] using h
  exact negative_dual_bound hS hR hA hCS

end

end ResearchMain.DiagonalSchatten
