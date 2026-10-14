import MainTheorems.DiagonalSchatten.SymmetricPowerPositivity
import MainTheorems.DiagonalSchatten.RayDualAlgebra

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def compressionRay (p : ℝ) (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) : RayParameters where
  a := realGramPowerCoefficient ((p - 2) / 2) X 0
  b := realGramPowerCoefficient ((p - 2) / 2) X 1
  c := realGramPowerCoefficient ((p - 2) / 2) X 2
  k := p - 2
  z1 := Z 0
  z2 := Z 1
  z12 := Z 2

theorem compressionRay_energy (p : ℝ) (X Y : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) :
    (∑ j, (kernelFirst (compressionRay p X Z).k (compressionRay p X Z).a
        (compressionRay p X Z).c (X 0 j) (X 1 j) * Y 0 j ^ 2 -
      2 * (compressionRay p X Z).c * Y 0 j * Y 1 j +
      kernelSecond (compressionRay p X Z).k (compressionRay p X Z).b
        (compressionRay p X Z).c (X 0 j) (X 1 j) * Y 1 j ^ 2)) =
      compressionKernelEnergy p X Y := rfl

variable [Nonempty J]

theorem positiveRows_gramFirst (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 < X i j) :
    0 < gramFirst X :=
  Finset.sum_pos (fun j _ => sq_pos_of_pos (hX 0 j)) Finset.univ_nonempty

theorem positiveRows_gramCross (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 < X i j) :
    0 < gramCross X :=
  Finset.sum_pos (fun j _ => mul_pos (hX 0 j) (hX 1 j)) Finset.univ_nonempty

theorem compressionRay_upper {p : ℝ} (hp : 2 < p)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) (hX : ∀ i j, 0 < X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    0 < (compressionRay p X Z).a ∧ 0 < (compressionRay p X Z).b ∧
      0 < (compressionRay p X Z).c := by
  have hA := positiveRows_gramFirst X hX
  have hC := positiveRows_gramCross X hX
  have hpd := symmetricPower_positive_definite ((p - 2) / 2) (gramCoordinates X) hA hdet hC.ne'
  have hc := symmetricPower_cross_positive (by linarith : 0 < (p - 2) / 2)
    (gramCoordinates X) hA hdet hC
  simp only [gramCoordinates, symmetricPower_gram] at hpd hc
  exact ⟨hpd.1, hpd.2.1, hc⟩

theorem compressionRay_lower {p : ℝ} (hp2 : p < 2)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) (hX : ∀ i j, 0 < X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    0 < (compressionRay p X Z).a ∧ 0 < (compressionRay p X Z).b ∧
      (compressionRay p X Z).c < 0 ∧
      (compressionRay p X Z).c ^ 2 < (compressionRay p X Z).a * (compressionRay p X Z).b := by
  have hA := positiveRows_gramFirst X hX
  have hC := positiveRows_gramCross X hX
  have hpd := symmetricPower_positive_definite ((p - 2) / 2) (gramCoordinates X) hA hdet hC.ne'
  have hc := symmetricPower_cross_negative (by linarith : (p - 2) / 2 < 0)
    (gramCoordinates X) hA hdet hC
  simp only [gramCoordinates, symmetricPower_gram] at hpd hc
  refine ⟨hpd.1, hpd.2.1, hc, ?_⟩
  exact sub_pos.mp hpd.2.2

end

end ResearchMain.DiagonalSchatten
