import MainTheorems.DiagonalSchatten.RayDualAlgebra

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

namespace RayParameters

def energy (g : RayParameters) (X Y : Matrix (Fin 2) J ℝ) : ℝ :=
  ∑ j, (kernelFirst g.k g.a g.c (X 0 j) (X 1 j) * Y 0 j ^ 2 -
    2 * g.c * Y 0 j * Y 1 j + kernelSecond g.k g.b g.c (X 0 j) (X 1 j) * Y 1 j ^ 2)

theorem trace_image (g : RayParameters) (X Y : Matrix (Fin 2) J ℝ) :
    symmetricTraceProduct ![g.z1, g.z2, g.z12] (gramVariation X Y) =
      2 * ∑ j, (g.image (fun i => X i j) 0 * Y 0 j +
        g.image (fun i => X i j) 1 * Y 1 j) := by
  simp only [image, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h := gramVariation_trace_product X Y ![g.z1, g.z2, g.z12]
  simp at h
  rw [h]
  simp [symmetricTraceProduct]
  ring

theorem energy_difference (g : RayParameters) (X Y : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, X i j ≠ 0)
    (hd : ∀ j, kernelFirst g.k g.a g.c (X 0 j) (X 1 j) *
      kernelSecond g.k g.b g.c (X 0 j) (X 1 j) - g.c ^ 2 ≠ 0) :
    g.energy X (Y - g.inverseRows X) = g.energy X Y -
      symmetricTraceProduct ![g.z1, g.z2, g.z12] (gramVariation X Y) +
      ∑ j, g.functional (fun i => X i j) := by
  have hcol (j : J) :
      kernelFirst g.k g.a g.c (X 0 j) (X 1 j) * (Y 0 j - g.inverseRows X 0 j) ^ 2 -
        2 * g.c * (Y 0 j - g.inverseRows X 0 j) * (Y 1 j - g.inverseRows X 1 j) +
        kernelSecond g.k g.b g.c (X 0 j) (X 1 j) * (Y 1 j - g.inverseRows X 1 j) ^ 2 =
      (kernelFirst g.k g.a g.c (X 0 j) (X 1 j) * Y 0 j ^ 2 -
        2 * g.c * Y 0 j * Y 1 j + kernelSecond g.k g.b g.c (X 0 j) (X 1 j) * Y 1 j ^ 2) -
        2 * (g.image (fun i => X i j) 0 * Y 0 j + g.image (fun i => X i j) 1 * Y 1 j) +
        g.functional (fun i => X i j) := by
    obtain ⟨h0, h1⟩ := g.inverseImage_equations (fun i => X i j) (hd j)
    have hE := g.inverseImage_energy (fun i => X i j) (hX 0 j) (hX 1 j) (hd j)
    dsimp only [inverseRows, Matrix.of_apply]
    linear_combination -hE - 2 * Y 0 j * h0 - 2 * Y 1 j * h1
  unfold energy
  simp only [Matrix.sub_apply]
  simp_rw [hcol]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← g.trace_image X Y]

end RayParameters

end

end ResearchMain.DiagonalSchatten
