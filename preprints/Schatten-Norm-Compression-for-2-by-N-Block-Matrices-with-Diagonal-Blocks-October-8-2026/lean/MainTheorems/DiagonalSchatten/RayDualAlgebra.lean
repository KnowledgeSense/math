import MainTheorems.DiagonalSchatten.RayFunctional
import MainTheorems.DiagonalSchatten.CompressionSecondVariation

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace RayParameters

def inverseImage (g : RayParameters) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let a := kernelFirst g.k g.a g.c (x 0) (x 1)
  let b := kernelSecond g.k g.b g.c (x 0) (x 1)
  ![(b * g.image x 0 + g.c * g.image x 1) / (a * b - g.c ^ 2),
    (g.c * g.image x 0 + a * g.image x 1) / (a * b - g.c ^ 2)]

theorem inverseImage_equations (g : RayParameters) (x : Fin 2 → ℝ)
    (hd : kernelFirst g.k g.a g.c (x 0) (x 1) *
      kernelSecond g.k g.b g.c (x 0) (x 1) - g.c ^ 2 ≠ 0) :
    kernelFirst g.k g.a g.c (x 0) (x 1) * g.inverseImage x 0 -
        g.c * g.inverseImage x 1 = g.image x 0 ∧
      kernelSecond g.k g.b g.c (x 0) (x 1) * g.inverseImage x 1 -
        g.c * g.inverseImage x 0 = g.image x 1 := by
  simp only [inverseImage, Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize hD : kernelFirst g.k g.a g.c (x 0) (x 1) *
    kernelSecond g.k g.b g.c (x 0) (x 1) - g.c ^ 2 = D
  have hDn : D ≠ 0 := by rw [← hD]; exact hd
  constructor <;> field_simp [hDn] <;> rw [← hD] <;> ring

theorem functional_inverseImage (g : RayParameters) (x : Fin 2 → ℝ)
    (hu : x 0 ≠ 0) (hv : x 1 ≠ 0) :
    g.functional x = g.image x 0 * g.inverseImage x 0 +
      g.image x 1 * g.inverseImage x 1 := by
  rw [functional, g.numerator_eq_kernel_adjugate x hu hv,
    g.denominator_eq_kernel_determinant x hu hv,
    g.kernel_determinant, mul_div_mul_left _ _ (mul_ne_zero hu hv)]
  simp only [inverseImage, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem inverseImage_energy (g : RayParameters) (x : Fin 2 → ℝ)
    (hu : x 0 ≠ 0) (hv : x 1 ≠ 0)
    (hd : kernelFirst g.k g.a g.c (x 0) (x 1) *
      kernelSecond g.k g.b g.c (x 0) (x 1) - g.c ^ 2 ≠ 0) :
    g.functional x =
      kernelFirst g.k g.a g.c (x 0) (x 1) * (g.inverseImage x 0) ^ 2 -
        2 * g.c * g.inverseImage x 0 * g.inverseImage x 1 +
        kernelSecond g.k g.b g.c (x 0) (x 1) * (g.inverseImage x 1) ^ 2 := by
  obtain ⟨h0, h1⟩ := g.inverseImage_equations x hd
  rw [g.functional_inverseImage x hu hv, ← h0, ← h1]
  ring

variable {J : Type*} [Fintype J]

def inverseRows (g : RayParameters) (X : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℝ :=
  Matrix.of fun i j => g.inverseImage (fun a => X a j) i

theorem inverseRows_trace (g : RayParameters) (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, X i j ≠ 0) :
    symmetricTraceProduct ![g.z1, g.z2, g.z12] (gramVariation X (g.inverseRows X)) =
      2 * ∑ j, g.functional (fun i => X i j) := by
  have hf : (∑ j, g.functional (fun i => X i j)) =
      ∑ j, ((g.z1 * X 0 j + g.z12 * X 1 j) * g.inverseRows X 0 j +
        (g.z12 * X 0 j + g.z2 * X 1 j) * g.inverseRows X 1 j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact g.functional_inverseImage (fun i => X i j) (hX 0 j) (hX 1 j)
  have ht := gramVariation_trace_product X (g.inverseRows X) ![g.z1, g.z2, g.z12]
  change (∑ j, ((g.z1 * X 0 j + g.z12 * X 1 j) * g.inverseRows X 0 j +
      (g.z12 * X 0 j + g.z2 * X 1 j) * g.inverseRows X 1 j)) =
    symmetricTraceProduct (gramVariation X (g.inverseRows X)) ![g.z1, g.z2, g.z12] / 2 at ht
  have hc : symmetricTraceProduct (gramVariation X (g.inverseRows X)) ![g.z1, g.z2, g.z12] =
      symmetricTraceProduct ![g.z1, g.z2, g.z12] (gramVariation X (g.inverseRows X)) := by
    unfold symmetricTraceProduct
    ring
  rw [hf]
  linarith

theorem inverseRows_energy (g : RayParameters) (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, X i j ≠ 0)
    (hd : ∀ j, kernelFirst g.k g.a g.c (X 0 j) (X 1 j) *
      kernelSecond g.k g.b g.c (X 0 j) (X 1 j) - g.c ^ 2 ≠ 0) :
    (∑ j, g.functional (fun i => X i j)) =
      ∑ j, (kernelFirst g.k g.a g.c (X 0 j) (X 1 j) * g.inverseRows X 0 j ^ 2 -
        2 * g.c * g.inverseRows X 0 j * g.inverseRows X 1 j +
        kernelSecond g.k g.b g.c (X 0 j) (X 1 j) * g.inverseRows X 1 j ^ 2) := by
  apply Finset.sum_congr rfl
  intro j _
  exact g.inverseImage_energy _ (hX 0 j) (hX 1 j) (hd j)

end RayParameters

end

end ResearchMain.DiagonalSchatten
