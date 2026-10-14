import MainTheorems.WishartBlocks.RegularizedProductJetMoments
import MainTheorems.WishartBlocks.WishartSchwartzIdentity

namespace ResearchMain.WishartBlocks

open MeasureTheory Filter Matrix
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Elementwise

namespace BlockPartition

theorem smoothProduct_cutoff_direction_bound {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (L : List (MatrixEuclidean p))
    (hL : L.length ≤ 2) (C : ℕ → ℝ)
    (hC : ∀ k N (x : MatrixEuclidean p),
      ‖iteratedFDeriv ℝ k (expandingCutoff N) x‖ ≤ C k)
    (N : ℕ) {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    ‖functionDirections L (compactApproximation N (P.smoothProductEuclidean ν ε))
      (matrixCoordinates p W)‖ ≤
      ((∑ k ∈ Finset.range (L.length + 1),
        (L.length.choose k : ℝ) * C k * P.regularizedJetConstant ν ε (L.length - k)) *
          ∏ i : Fin L.length, ‖L.get i‖) *
            ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ := by
  have hf := P.smoothProductEuclidean_contDiff ν hε
  apply (functionDirections_norm (compactApproximation_contDiff N hf) L _).trans
  have hj := compactApproximation_jet_bound hf C hC N L.length (matrixCoordinates p W)
  have hJ : ‖iteratedFDeriv ℝ L.length
      (compactApproximation N (P.smoothProductEuclidean ν ε)) (matrixCoordinates p W)‖ ≤
      (∑ k ∈ Finset.range (L.length + 1), (L.length.choose k : ℝ) * C k *
        P.regularizedJetConstant ν ε (L.length - k)) *
          ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ := by
    apply hj.trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    have hC0 : 0 ≤ C k := (norm_nonneg _).trans (hC k N (matrixCoordinates p W))
    calc
      _ ≤ (L.length.choose k : ℝ) * C k *
          (‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖ *
            P.regularizedJetConstant ν ε (L.length - k)) :=
        mul_le_mul_of_nonneg_left
          (P.smoothProductEuclidean_jet_bound ν hε hW (Nat.sub_le _ _ |>.trans hL))
          (mul_nonneg (Nat.cast_nonneg _) hC0)
      _ = _ := by ring
  calc
    _ ≤ ((∑ k ∈ Finset.range (L.length + 1), (L.length.choose k : ℝ) * C k *
        P.regularizedJetConstant ν ε (L.length - k)) *
          ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν W‖) *
            ∏ i : Fin L.length, ‖L.get i‖ :=
      mul_le_mul_of_nonneg_right hJ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

theorem oneRowWishart_regularized_differential_identity {p d : ℕ} (P : BlockPartition p d)
    {q s : ℝ} (hq : (p : ℝ) < q) (hs : 0 < s)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) {ε : ℝ} (hε : 0 < ε)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    (∑ i : WishartDifferentialIndex p, ∫ x,
      (wishartDifferenceCoefficient q S v s i x : ℂ) *
        functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p))
          (P.smoothProductEuclidean ν ε)
            (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂(oneRowInputLaw q S)) = 0 := by
  classical
  let μ := oneRowInputLaw q S
  let f := P.smoothProductEuclidean ν ε
  let L (i : WishartDifferentialIndex p) :=
    (wishartDifferenceDirections i).map (matrixCoordinates p)
  choose C hCpos hC using fun k : ℕ => expandingCutoff_derivative_bound (E := MatrixEuclidean p) k
  let K (i : WishartDifferentialIndex p) : ℝ :=
    (∑ k ∈ Finset.range ((L i).length + 1), ((L i).length.choose k : ℝ) * C k *
      P.regularizedJetConstant ν ε ((L i).length - k)) *
        ∏ j : Fin (L i).length, ‖(L i).get j‖
  have hK (i : WishartDifferentialIndex p) : 0 ≤ K i := by
    dsimp [K]
    apply mul_nonneg
    · exact Finset.sum_nonneg fun k _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCpos k).le) (P.regularizedJetConstant_nonneg ν hε _)
    · exact Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hL (i : WishartDifferentialIndex p) : (L i).length ≤ 2 := by
    cases i <;> simp [L, wishartDifferenceDirections]
  have hT (i : WishartDifferentialIndex p) : Tendsto (fun N : ℕ =>
      ∫ x, (wishartDifferenceCoefficient q S v s i x : ℂ) *
        functionDirections (L i) (compactApproximation N f)
          (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂μ)
      atTop (𝓝 (∫ x, (wishartDifferenceCoefficient q S v s i x : ℂ) *
        functionDirections (L i) f (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => K i * (‖wishartDifferenceCoefficient q S v s i x‖ *
        ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν (oneRowWishartValue S (s • v) x)‖))
    · exact Eventually.of_forall fun N =>
        (((wishartDifferenceCoefficient_measurable q S v s i).complex_ofReal).mul
          (((functionDirections_contDiff (compactApproximation_contDiff N
            (P.smoothProductEuclidean_contDiff ν hε)) (L i)).continuous.measurable).comp
              ((matrixCoordinates p).continuous.measurable.comp
                (measurable_oneRowWishartValue S (s • v))))).aestronglyMeasurable
    · exact Eventually.of_forall fun N => by
        filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
        rw [norm_mul, Complex.norm_real]
        have hW := oneRowWishartValue_positive S v s hx
        have hB := P.smoothProduct_cutoff_direction_bound ν hε (L i) (hL i) C hC N hW
        change ‖wishartDifferenceCoefficient q S v s i x‖ *
          ‖functionDirections (L i) (compactApproximation N f)
            (matrixCoordinates p (oneRowWishartValue S (s • v) x))‖ ≤ _
        calc
          _ ≤ ‖wishartDifferenceCoefficient q S v s i x‖ *
              (K i * ‖P.shiftedDeterminantProduct (fun _ => ε • 1) ν
                (oneRowWishartValue S (s • v) x)‖) :=
            mul_le_mul_of_nonneg_left hB (norm_nonneg _)
          _ = _ := by ring
    · exact (P.regularizedProduct_coefficient_integrable hq hs S v ε ν hν i).const_mul (K i)
    · exact ae_of_all _ fun x => tendsto_const_nhds.mul
        (compactApproximation_directions_tendsto f (L i)
          (matrixCoordinates p (oneRowWishartValue S (s • v) x)))
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hT i)
  have he : (fun N : ℕ => ∑ i : WishartDifferentialIndex p,
      ∫ x, (wishartDifferenceCoefficient q S v s i x : ℂ) *
        functionDirections (L i) (compactApproximation N f)
          (matrixCoordinates p (oneRowWishartValue S (s • v) x)) ∂μ) = 0 := by
    funext N
    exact oneRowWishart_compact_differential_identity hq hs hS v
      (compactApproximation N f) (compactApproximation_contDiff N
        (P.smoothProductEuclidean_contDiff ν hε)) (compactApproximation_compact N f)
  rw [he] at hsum
  exact tendsto_nhds_unique hsum tendsto_const_nhds

end BlockPartition
end ResearchMain.WishartBlocks
