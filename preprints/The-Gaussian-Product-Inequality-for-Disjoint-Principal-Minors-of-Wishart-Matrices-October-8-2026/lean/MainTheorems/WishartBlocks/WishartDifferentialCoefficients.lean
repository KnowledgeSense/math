import MainTheorems.WishartBlocks.GaussianMeanLaplaceDifference
import MainTheorems.WishartBlocks.MatrixDifferentialUniqueness

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace MatrixOrder Matrix.Norms.Elementwise

abbrev WishartDifferentialIndex (p : ℕ) :=
  (Fin p × Fin p) ⊕ ((Fin p × Fin p) × (Fin p × Fin p))

noncomputable def wishartDifferenceDirections {p : ℕ} (i : WishartDifferentialIndex p) :
    List (Matrix (Fin p) (Fin p) ℝ) :=
  match i with
  | Sum.inl ij => [symmetricDirection ij.1 ij.2]
  | Sum.inr (ij, kl) => [symmetricDirection ij.1 ij.2, symmetricDirection kl.1 kl.2]

noncomputable def wishartDifferenceCoefficient {p : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    (i : WishartDifferentialIndex p) (x : OneRowInput p) : ℝ :=
  match i with
  | Sum.inl ij => (q - 1) * (oneRowGaussianVector S v s x ij.1 * v ij.2 / s - v ij.1 * v ij.2)
  | Sum.inr (ij, kl) => -2 * x.1 ij.1 kl.1 * v ij.2 * v kl.2

noncomputable def wishartDifferenceBound {p : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℝ :=
  |q - 1| * (oneRowGaussianBound S v s * ‖v‖ / |s| + ‖v‖ ^ 2) + 2 * ‖v‖ ^ 2

theorem wishartDifferenceDirections_hermitian {p : ℕ} (i : WishartDifferentialIndex p)
    (H : Matrix (Fin p) (Fin p) ℝ) (hH : H ∈ wishartDifferenceDirections i) : H.IsHermitian := by
  have hs (j k : Fin p) : (symmetricDirection j k).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (symmetricDirection_transpose j k)
  cases i with
  | inl ij =>
      simp only [wishartDifferenceDirections, List.mem_singleton] at hH
      rw [hH]
      exact hs ij.1 ij.2
  | inr ijkl =>
      rcases ijkl with ⟨ij, kl⟩
      simp only [wishartDifferenceDirections, List.mem_cons, List.not_mem_nil, or_false] at hH
      rcases hH with rfl | rfl
      · exact hs ij.1 ij.2
      · exact hs kl.1 kl.2

theorem wishartDifferenceCoefficient_measurable {p : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    (i : WishartDifferentialIndex p) : Measurable (wishartDifferenceCoefficient q S v s i) := by
  cases i with
  | inl ij =>
      change Measurable (fun x => (q - 1) *
        (oneRowGaussianVector S v s x ij.1 * v ij.2 / s - v ij.1 * v ij.2))
      fun_prop
  | inr ijkl =>
      change Measurable (fun x : OneRowInput p =>
        -2 * x.1 ijkl.1.1 ijkl.2.1 * v ijkl.1.2 * v ijkl.2.2)
      fun_prop

theorem wishartDifferenceBound_nonneg {p : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    0 ≤ wishartDifferenceBound q S v s := by
  have hC := oneRowGaussianBound_nonneg S v s
  unfold wishartDifferenceBound
  positivity

theorem wishartDifferenceCoefficient_bound {p : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {s : ℝ} (hs : 0 < s) (i : WishartDifferentialIndex p) (x : OneRowInput p) :
    ‖wishartDifferenceCoefficient q S v s i x‖ ≤
      wishartDifferenceBound q S v s * (1 + ‖x‖) := by
  have hC := oneRowGaussianBound_nonneg S v s
  have hY (j : Fin p) : ‖oneRowGaussianVector S v s x j‖ ≤
      oneRowGaussianBound S v s * (1 + ‖x‖) :=
    (PiLp.norm_apply_le _ j).trans (oneRowGaussianVector_local_bound S v s (by simp) x)
  have hV (j : Fin p) : ‖v j‖ ≤ ‖v‖ := PiLp.norm_apply_le v j
  have hs' : 0 < |s| := abs_pos.mpr hs.ne'
  cases i with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      calc
        _ = |q - 1| * ‖oneRowGaussianVector S v s x i * v j / s - v i * v j‖ := by
          simp only [wishartDifferenceCoefficient, norm_mul, Real.norm_eq_abs]
        _ ≤ |q - 1| * (‖oneRowGaussianVector S v s x i‖ * ‖v j‖ / |s| + ‖v i‖ * ‖v j‖) := by
          gcongr
          simpa only [norm_div, norm_mul, Real.norm_eq_abs] using
            norm_sub_le (oneRowGaussianVector S v s x i * v j / s) (v i * v j)
        _ ≤ |q - 1| * (oneRowGaussianBound S v s * (1 + ‖x‖) * ‖v‖ / |s| + ‖v‖ * ‖v‖) := by
          gcongr
          · exact hY i
          · exact hV j
          · exact hV i
          · exact hV j
        _ ≤ wishartDifferenceBound q S v s * (1 + ‖x‖) := by
          dsimp [wishartDifferenceBound]
          have he : oneRowGaussianBound S v s * (1 + ‖x‖) * ‖v‖ / |s| =
              (oneRowGaussianBound S v s * ‖v‖ / |s|) * (1 + ‖x‖) := by ring
          rw [he]
          have hn := norm_nonneg x
          have hb : (oneRowGaussianBound S v s * ‖v‖ / |s|) * (1 + ‖x‖) +
              ‖v‖ * ‖v‖ ≤
              (oneRowGaussianBound S v s * ‖v‖ / |s| + ‖v‖ ^ 2) * (1 + ‖x‖) := by
            nlinarith [mul_nonneg (sq_nonneg ‖v‖) hn]
          calc
            _ ≤ |q - 1| *
                ((oneRowGaussianBound S v s * ‖v‖ / |s| + ‖v‖ ^ 2) * (1 + ‖x‖)) :=
              mul_le_mul_of_nonneg_left hb (abs_nonneg (q - 1))
            _ = (|q - 1| *
                (oneRowGaussianBound S v s * ‖v‖ / |s| + ‖v‖ ^ 2)) * (1 + ‖x‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * ‖v‖ ^ 2)) (by positivity)
  | inr ijkl =>
      rcases ijkl with ⟨⟨i, j⟩, ⟨k, l⟩⟩
      calc
        _ = 2 * ‖x.1 i k‖ * ‖v j‖ * ‖v l‖ := by
          simp only [wishartDifferenceCoefficient, norm_mul]
          norm_num
        _ ≤ 2 * ‖x‖ * ‖v‖ * ‖v‖ := by
          gcongr
          · exact (Matrix.norm_entry_le_entrywise_sup_norm x.1).trans (norm_fst_le x)
          · exact hV j
          · exact hV l
        _ ≤ wishartDifferenceBound q S v s * (1 + ‖x‖) := by
          dsimp [wishartDifferenceBound]
          have hd : 0 ≤ |q - 1| * (oneRowGaussianBound S v s * ‖v‖ / |s| + ‖v‖ ^ 2) := by positivity
          nlinarith [norm_nonneg x, norm_nonneg v]

noncomputable def oneRowMatrixBound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℝ :=
  1 + ((p : ℝ) * ‖CFC.sqrt S‖ + |s| * ‖v‖) ^ 2

theorem oneRowWishartValue_norm_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    ‖oneRowWishartValue S (s • v) x‖ ≤ oneRowMatrixBound S v s * (1 + ‖x‖) ^ 2 := by
  have hg := gaussianMeanGram_norm_bound S (s • v) x.2
  rw [norm_smul, Real.norm_eq_abs] at hg
  have hg' : ‖gaussianMeanGram S (s • v) x.2‖ ≤
      ((p : ℝ) * ‖CFC.sqrt S‖ + |s| * ‖v‖) ^ 2 * (1 + ‖x‖) ^ 2 := by
    apply hg.trans
    gcongr
    exact norm_snd_le x
  calc
    _ ≤ ‖x.1‖ + ‖gaussianMeanGram S (s • v) x.2‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ((p : ℝ) * ‖CFC.sqrt S‖ + |s| * ‖v‖) ^ 2 * (1 + ‖x‖) ^ 2 :=
      add_le_add (norm_fst_le x) hg'
    _ ≤ _ := by dsimp [oneRowMatrixBound]; nlinarith [norm_nonneg x]

theorem wishartDifferenceCoefficient_integrable {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (i : WishartDifferentialIndex p) :
    Integrable (wishartDifferenceCoefficient q S v s i) (oneRowInputLaw q S) := by
  apply oneRowInput_real_growth_integrable hq S
    (β := 1) (wishartDifferenceCoefficient_measurable q S v s i)
    (wishartDifferenceBound_nonneg q S v s)
  intro x
  simpa only [Real.rpow_one] using wishartDifferenceCoefficient_bound q S v hs i x

@[fun_prop] theorem oneRowWishartValue_norm_measurable {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (m : EuclideanSpace ℝ (Fin p)) :
    Measurable (fun x => ‖oneRowWishartValue S m x‖) := by
  have hW : Measurable (fun x : OneRowInput p =>
      (oneRowWishartValue S m x : Fin p → Fin p → ℝ)) :=
    measurable_oneRowWishartValue S m
  exact Measurable.norm (α := Fin p → Fin p → ℝ) hW

theorem wishartDifferenceCoefficient_matrix_growth_integrable {p : ℕ} {q s : ℝ}
    (hq : (p : ℝ) < q) (hs : 0 < s) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (i : WishartDifferentialIndex p) :
    Integrable (fun x => ‖oneRowWishartValue S (s • v) x‖ *
      ‖wishartDifferenceCoefficient q S v s i x‖) (oneRowInputLaw q S) := by
  have hC := wishartDifferenceBound_nonneg q S v s
  apply ((oneRowInput_polynomial_integrable hq S 3).const_mul
    (oneRowMatrixBound S v s * wishartDifferenceBound q S v s)).mono' (by
      exact ((oneRowWishartValue_norm_measurable S (s • v)).fun_mul
        (wishartDifferenceCoefficient_measurable q S v s i).norm).aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (oneRowMatrixBound S v s * (1 + ‖x‖) ^ 2) *
          (wishartDifferenceBound q S v s * (1 + ‖x‖)) :=
        mul_le_mul (oneRowWishartValue_norm_bound S v s x)
          (wishartDifferenceCoefficient_bound q S v hs i x) (norm_nonneg _) (by
            dsimp [oneRowMatrixBound]
            positivity)
      _ = _ := by ring

end ResearchMain.WishartBlocks
