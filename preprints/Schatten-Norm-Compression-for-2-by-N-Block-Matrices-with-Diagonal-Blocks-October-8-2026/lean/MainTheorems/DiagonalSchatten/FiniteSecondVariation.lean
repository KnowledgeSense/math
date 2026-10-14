import MainTheorems.DiagonalSchatten.FiniteCompressionRayBound
import MainTheorems.DiagonalSchatten.RayEnergyDifference
import MainTheorems.DiagonalSchatten.PowerVariationInverse

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J] [Nonempty J]

theorem finite_second_variation {p sign : ℝ}
    (hp : (2 < p ∧ p < 4 ∧ sign = 1) ∨ (1 < p ∧ p < 2 ∧ sign = -1))
    (X Y : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 < X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    sign * symmetricTraceProduct (gramVariation X Y)
        (symmetricPowerVariation ((p - 2) / 2) (gramCoordinates X) (gramVariation X Y)) ≤
      2 * sign * compressionKernelEnergy p X Y := by
  let M := gramCoordinates X
  let V := gramVariation X Y
  let r := (p - 2) / 2
  let Z := symmetricPowerVariation r M V
  let g := compressionRay p X Z
  let T := symmetricTraceProduct V Z
  have hp2 : p ≠ 2 := by rcases hp with ⟨h, _, _⟩ | ⟨_, h, _⟩ <;> linarith
  have hr : r ≠ 0 := div_ne_zero (sub_ne_zero.mpr hp2) (by norm_num)
  have hA := positiveRows_gramFirst X hX
  have hC := positiveRows_gramCross X hX
  have hZ : ![g.z1, g.z2, g.z12] = Z := by
    funext i
    fin_cases i <;> simp [g, compressionRay]
  have hR : inverseGramQuadratic p X Z = T := by
    unfold inverseGramQuadratic
    rw [symmetricPowerVariation_inverse_apply hr M V hA hdet hC.ne', symmetricTraceProduct_comm]
  have hK (j : J) :
      0 < kernelFirst g.k g.a g.c (X 0 j) (X 1 j) *
        kernelSecond g.k g.b g.c (X 0 j) (X 1 j) - g.c ^ 2 ∧
      ∀ a b, 0 ≤ sign * (kernelFirst g.k g.a g.c (X 0 j) (X 1 j) * a ^ 2 -
        2 * g.c * a * b + kernelSecond g.k g.b g.c (X 0 j) (X 1 j) * b ^ 2) := by
    rcases hp with ⟨hp2, _, rfl⟩ | ⟨hp1, hp2, rfl⟩
    · obtain ⟨ha, hb, hc⟩ := compressionRay_upper hp2 X Z hX hdet
      have hk : 0 < g.k := by change 0 < p - 2; linarith
      refine ⟨(compressionKernel_upper hk ha hb hc (hX 0 j) (hX 1 j)).2, ?_⟩
      intro a b
      simpa only [one_mul] using compressionKernel_quadratic_upper hk ha hb hc
        (hX 0 j) (hX 1 j) a b
    · obtain ⟨ha, hb, hc, hd⟩ := compressionRay_lower hp2 X Z hX hdet
      have hk : g.k < 0 := by change p - 2 < 0; linarith
      have hk1 : -1 < g.k := by change -1 < p - 2; linarith
      refine ⟨(compressionKernel_lower hk1 hk ha hb hc hd (hX 0 j) (hX 1 j)).2, ?_⟩
      intro a b
      simpa only [neg_one_mul, neg_nonneg] using compressionKernel_quadratic_lower hk1 hk
        ha hb hc hd (hX 0 j) (hX 1 j) a b
  have henergy (W : Matrix (Fin 2) J ℝ) : 0 ≤ sign * g.energy X W := by
    unfold RayParameters.energy
    rw [Finset.mul_sum]
    exact Finset.sum_nonneg fun j _ => (hK j).2 (W 0 j) (W 1 j)
  have hdiff := g.energy_difference X Y (fun i j => (hX i j).ne')
    (fun j => (hK j).1.ne')
  rw [hZ, symmetricTraceProduct_comm] at hdiff
  have hbound := finite_compression_ray_bound hp X Z hX hdet
  rw [hR] at hbound
  have hnonneg := henergy (Y - g.inverseRows X)
  rw [hdiff] at hnonneg
  have hE : g.energy X Y = compressionKernelEnergy p X Y := rfl
  rw [hE] at hnonneg
  change sign * T ≤ 2 * sign * compressionKernelEnergy p X Y
  nlinarith [hbound, hnonneg]

variable [DecidableEq J]

theorem compressionHessian_finite_signed {p sign : ℝ}
    (hp : (2 < p ∧ p < 4 ∧ sign = 1) ∨ (1 < p ∧ p < 2 ∧ sign = -1))
    (B E : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) : sign * compressionHessian p B E E ≤ 0 := by
  have hp1 : 1 < p := by rcases hp with ⟨h, _, _⟩ | ⟨h, _, _⟩ <;> linarith
  rw [compressionHessian_second_variation hp1 B E hB hdet]
  have hX : ∀ i j, 0 < realEntryRoot p B i j :=
    fun i j => Real.rpow_pos_of_pos (hB i j) _
  have h := finite_second_variation hp (realEntryRoot p B) (entryRootDirection p B E) hX hdet
  nlinarith [mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ p / 2)]

end

end ResearchMain.DiagonalSchatten
