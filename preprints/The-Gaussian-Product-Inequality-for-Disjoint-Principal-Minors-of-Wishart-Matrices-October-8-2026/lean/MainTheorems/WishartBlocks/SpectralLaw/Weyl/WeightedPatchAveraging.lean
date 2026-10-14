import MainTheorems.WishartBlocks.SpectralLaw.Weyl.CoordinateAveraging

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory
open scoped ENNReal

theorem orthogonalCongruence_inverse_cancel {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (W : LowerIndex n → ℝ) :
    orthogonalCongruenceLinearMap Q (orthogonalCongruenceLinearMap Q⁻¹ W) = W := by
  rw [orthogonalCongruenceLinearMap_mul Q Q⁻¹ W, mul_inv_cancel,
    orthogonalCongruenceLinearMap_one]

theorem coordinateProduct_lintegral_inverse {n : ℕ}
    {P G : (LowerIndex n → ℝ) → ℝ≥0∞} (hP : Measurable P) (hG : Measurable G)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (∫⁻ W, P W * G (orthogonalCongruenceLinearMap Q W)) =
      ∫⁻ W, P (orthogonalCongruenceLinearMap Q⁻¹ W) * G W := by
  have hGW : Measurable (fun W : LowerIndex n → ℝ =>
      G (orthogonalCongruenceLinearMap Q W)) :=
    hG.comp (orthogonalCongruenceLinearMap Q).continuous_of_finiteDimensional.measurable
  calc
    _ = ∫⁻ W, P (orthogonalCongruenceLinearMap Q⁻¹ W) *
        G (orthogonalCongruenceLinearMap Q (orthogonalCongruenceLinearMap Q⁻¹ W)) :=
      (orthogonalCongruence_lintegral Q⁻¹
        (G := fun W => P W * G (orthogonalCongruenceLinearMap Q W))
        (hP.mul hGW)).symm
    _ = _ := by
      apply lintegral_congr
      intro W
      rw [orthogonalCongruence_inverse_cancel Q W]

theorem coordinateOrthogonalAverageNN_inv_lintegral {n : ℕ}
    {P : (LowerIndex n → ℝ) → ℝ≥0∞} (hP : Measurable P)
    (W : LowerIndex n → ℝ) (c : ℝ≥0∞) :
    (∫⁻ Q : Matrix.orthogonalGroup (Fin n) ℝ,
      P (orthogonalCongruenceLinearMap Q⁻¹ W) * c ∂orthogonalHaar n) =
      c * coordinateOrthogonalAverageNN P W := by
  have hPQ : Measurable (fun Q : Matrix.orthogonalGroup (Fin n) ℝ =>
      P (orthogonalCongruenceLinearMap Q W)) :=
    hP.comp ((orthogonalCongruence_joint_continuous n).comp
      (continuous_id.prodMk continuous_const)).measurable
  rw [lintegral_mul_const (μ := orthogonalHaar n)
    (f := fun Q => P (orthogonalCongruenceLinearMap Q⁻¹ W))
    c (hPQ.comp measurable_inv),
    lintegral_inv_eq_self (μ := orthogonalHaar n)
      (fun Q => P (orthogonalCongruenceLinearMap Q W))]
  exact mul_comm _ _

theorem coordinateOrthogonalAverageNN_product_lintegral {n : ℕ}
    {P G : (LowerIndex n → ℝ) → ℝ≥0∞} (hP : Measurable P) (hG : Measurable G) :
    (∫⁻ W, P W * coordinateOrthogonalAverageNN G W) =
      ∫⁻ Q : Matrix.orthogonalGroup (Fin n) ℝ,
        (∫⁻ W, P W * G (orthogonalCongruenceLinearMap Q W)) ∂orthogonalHaar n := by
  unfold coordinateOrthogonalAverageNN
  have hGjoint := hG.comp (orthogonalCongruence_joint_continuous n).measurable
  have hGQ (W : LowerIndex n → ℝ) :
      Measurable (fun Q : Matrix.orthogonalGroup (Fin n) ℝ =>
        G (orthogonalCongruenceLinearMap Q W)) :=
    hG.comp ((orthogonalCongruence_joint_continuous n).comp
      (continuous_id.prodMk continuous_const)).measurable
  have hjoint : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (LowerIndex n → ℝ) => P p.2 * G (orthogonalCongruenceLinearMap p.1 p.2)) :=
    (hP.comp measurable_snd).mul hGjoint
  calc
    _ = ∫⁻ W, ∫⁻ Q : Matrix.orthogonalGroup (Fin n) ℝ,
        P W * G (orthogonalCongruenceLinearMap Q W) ∂orthogonalHaar n := by
      apply lintegral_congr
      intro W
      exact (lintegral_const_mul (μ := orthogonalHaar n)
        (f := fun Q => G (orthogonalCongruenceLinearMap Q W)) (P W) (hGQ W)).symm
    _ = _ :=
      (lintegral_lintegral_swap (μ := orthogonalHaar n) (ν := volume)
        (f := fun Q W => P W * G (orthogonalCongruenceLinearMap Q W))
        hjoint.aemeasurable).symm

theorem coordinateOrthogonalAverageNN_inverse_product_lintegral {n : ℕ}
    {P G : (LowerIndex n → ℝ) → ℝ≥0∞} (hP : Measurable P) (hG : Measurable G) :
    (∫⁻ Q : Matrix.orthogonalGroup (Fin n) ℝ,
      (∫⁻ W, P (orthogonalCongruenceLinearMap Q⁻¹ W) * G W) ∂orthogonalHaar n) =
      ∫⁻ W, G W * coordinateOrthogonalAverageNN P W := by
  have hInv : Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (LowerIndex n → ℝ) => (p.1⁻¹, p.2)) :=
    continuous_fst.inv.prodMk continuous_snd
  have hCinv := (orthogonalCongruence_joint_continuous n).comp hInv
  simp only [Function.comp_def] at hCinv
  have hInvjoint : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (LowerIndex n → ℝ) => P (orthogonalCongruenceLinearMap p.1⁻¹ p.2) * G p.2) :=
    (hP.comp hCinv.measurable).mul (hG.comp measurable_snd)
  calc
    _ = ∫⁻ W, ∫⁻ Q : Matrix.orthogonalGroup (Fin n) ℝ,
        P (orthogonalCongruenceLinearMap Q⁻¹ W) * G W ∂orthogonalHaar n :=
      lintegral_lintegral_swap (μ := orthogonalHaar n) (ν := volume)
        (f := fun Q W => P (orthogonalCongruenceLinearMap Q⁻¹ W) * G W)
        hInvjoint.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro W
      exact coordinateOrthogonalAverageNN_inv_lintegral hP W (G W)

theorem coordinateOrthogonalAverageNN_selfAdjoint {n : ℕ}
    {P G : (LowerIndex n → ℝ) → ℝ≥0∞} (hP : Measurable P) (hG : Measurable G) :
    (∫⁻ W, P W * coordinateOrthogonalAverageNN G W) =
      ∫⁻ W, G W * coordinateOrthogonalAverageNN P W := by
  rw [coordinateOrthogonalAverageNN_product_lintegral hP hG]
  calc
    _ = ∫⁻ Q : Matrix.orthogonalGroup (Fin n) ℝ,
        (∫⁻ W, P (orthogonalCongruenceLinearMap Q⁻¹ W) * G W) ∂orthogonalHaar n := by
      apply lintegral_congr
      intro Q
      exact coordinateProduct_lintegral_inverse hP hG Q
    _ = _ := coordinateOrthogonalAverageNN_inverse_product_lintegral hP hG

theorem angularPatch_lintegral_average {n : ℕ} {lam₀ : Fin n → ℝ}
    (hlam₀ : StrictMono lam₀) {G : (LowerIndex n → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ W, G W) = ∫⁻ W,
      angularPatchNNWeight lam₀ hlam₀.injective (symmetricMatrix W) *
        coordinateOrthogonalAverageNN G W := by
  have hP : Measurable (fun W : LowerIndex n → ℝ =>
      angularPatchNNWeight lam₀ hlam₀.injective (symmetricMatrix W)) :=
    (angularPatchNNWeight_measurable _ _).comp (symmetricMatrix_continuous n).measurable
  calc
    _ = ∫⁻ W, G W * coordinateOrthogonalAverageNN (fun x =>
        angularPatchNNWeight lam₀ hlam₀.injective (symmetricMatrix x)) W := by
      apply lintegral_congr_ae
      filter_upwards [angularPatchNNWeight_coordinateAverage_ae hlam₀] with W hW
      rw [hW, mul_one]
    _ = _ := (coordinateOrthogonalAverageNN_selfAdjoint hP hG).symm

end ResearchMain.WishartBlocks.Weyl
