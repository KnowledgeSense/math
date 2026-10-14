import MainTheorems.AHOConstants.PhaseNormalization
import MainTheorems.AHOConstants.DiagonalPowers
import MainTheorems.AHOConstants.DiagonalTraceAMGM
import MainTheorems.AHOConstants.SingleInsertionPowers
import MainTheorems.AHOConstants.FeasibleWordBound

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

variable {m : ℕ}

theorem normalized_diagonal_pair_bound (v : Fin 2 → ℝ) (hv : ∀ i, 0 ≤ v i)
    {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : B.PosSemidef)
    (hentries : ∀ r : ℝ, 0 ≤ r → ∀ i j,
      0 ≤ (spectralPower B r i j).re ∧ (spectralPower B r i j).im = 0)
    (p q : Fin (m + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsum : (∑ i, p i) = 1) (hqsum : (∑ i, q i) = 1) :
    ‖Matrix.trace (List.ofFn (fun i =>
      spectralPower (Matrix.diagonal (fun a => (v a : ℂ))) (p i) *
        spectralPower B (q i))).prod‖ ≤
      (Matrix.trace (Matrix.diagonal (fun a => (v a : ℂ)) * B)).re := by
  let N : Fin (m + 1) → Matrix (Fin 2) (Fin 2) ℝ :=
    fun i a b => (spectralPower B (q i) a b).re
  have hN : ∀ i, EntryNonnegative (N i) := fun i a b => (hentries (q i) (hq i) a b).1
  have hcast : ∀ i, realCastMatrix (N i) = spectralPower B (q i) :=
    fun i => realCastMatrix_re (fun a b => (hentries (q i) (hq i) a b).2)
  have hfactor : ∀ i, realCastMatrix (diagonalWeightedMatrix v (p i) (N i)) =
      spectralPower (Matrix.diagonal (fun a => (v a : ℂ))) (p i) *
        spectralPower B (q i) := by
    intro i
    rw [diagonalWeightedMatrix, realCastMatrix_mul, realCastMatrix_diagonal,
      spectralPower_real_diagonal v hv (hp i), hcast i]
  have hW : ∀ i, EntryNonnegative (diagonalWeightedMatrix v (p i) (N i)) := by
    intro i a b
    rw [diagonalWeightedMatrix_entry]
    exact mul_nonneg (Real.rpow_nonneg (hv a) _) (hN i a b)
  have hprod : (List.ofFn (fun i =>
      spectralPower (Matrix.diagonal (fun a => (v a : ℂ))) (p i) *
        spectralPower B (q i))).prod =
      realCastMatrix (List.ofFn (fun i => diagonalWeightedMatrix v (p i) (N i))).prod := by
    rw [← realCastMatrix_product, List.map_ofFn]
    congr 2
    funext i
    exact (hfactor i).symm
  have hbasis : ∀ j : Fin (m + 1),
      Matrix.trace (List.ofFn (singleDiagonalMatrix v j N)).prod =
        (Matrix.trace (Matrix.diagonal (fun a => (v a : ℂ)) * B)).re := by
    intro j
    have hsingle : ∀ i,
        realCastMatrix (singleDiagonalMatrix v j N i) =
          insertedMatrix (Matrix.diagonal (fun a => (v a : ℂ))) j
            (fun i => spectralPower B (q i)) i := by
      intro i
      by_cases hij : i = j
      · subst i
        simp only [singleDiagonalMatrix, insertedMatrix, ite_true]
        rw [realCastMatrix_mul, realCastMatrix_diagonal, hcast j]
      · simp only [singleDiagonalMatrix, insertedMatrix, hij, ite_false, hcast i]
    have htrace : ((Matrix.trace (List.ofFn (singleDiagonalMatrix v j N)).prod : ℝ) : ℂ) =
        Matrix.trace (Matrix.diagonal (fun a => (v a : ℂ)) * B) := by
      rw [← realCastMatrix_trace, ← realCastMatrix_product, List.map_ofFn]
      simp_rw [Function.comp_def, hsingle]
      exact insertedMatrix_trace_of_powers _ hB j q hq hqsum
    simpa only [Complex.ofReal_re] using congrArg Complex.re htrace
  rw [hprod, realCastMatrix_trace, Complex.norm_real,
    Real.norm_of_nonneg (entryNonnegative_product _ (by
      intro M hM
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hM
      exact hW i)).trace]
  calc
    _ ≤ ∑ j, p j * Matrix.trace (List.ofFn (singleDiagonalMatrix v j N)).prod :=
      diagonal_weight_trace_AMGM v hv p hp hsum N hN
    _ = _ := by simp only [hbasis, ← Finset.sum_mul, hsum, one_mul]

theorem two_dimension_pair_bound {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p q : Fin (m + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsum : (∑ i, p i) = 1) (hqsum : (∑ i, q i) = 1) :
    ‖Matrix.trace (List.ofFn (fun i => spectralPower A (p i) * spectralPower B (q i))).prod‖ ≤
      (Matrix.trace (A * B)).re := by
  obtain ⟨U, v, hv, hdiag, hentries⟩ := twoDimension_normal_form hA hB
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U
  have hc := normalized_diagonal_pair_bound v hv (conjugation_posSemidef hB U)
    hentries p q hp hq hsum hqsum
  rw [← hdiag] at hc
  have hprod : (List.ofFn (fun i => spectralPower (φ A) (p i) *
      spectralPower (φ B) (q i))).prod =
      φ (List.ofFn (fun i => spectralPower A (p i) * spectralPower B (q i))).prod := by
    have hf : ∀ i, spectralPower (φ A) (p i) * spectralPower (φ B) (q i) =
        φ (spectralPower A (p i) * spectralPower B (q i)) := by
      intro i
      change spectralPower (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U A) (p i) *
          spectralPower (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U B) (q i) =
        Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U
          (spectralPower A (p i) * spectralPower B (q i))
      rw [spectralPower_conjugation hA U, spectralPower_conjugation hB U, map_mul]
    calc
      _ = (List.ofFn (fun i => φ (spectralPower A (p i) * spectralPower B (q i)))).prod := by
        apply congrArg List.prod
        apply congrArg List.ofFn
        funext i
        exact hf i
      _ = _ := by simp only [map_list_prod, List.map_ofFn, Function.comp_def]
  change ‖Matrix.trace (List.ofFn (fun i => spectralPower (φ A) (p i) *
      spectralPower (φ B) (q i))).prod‖ ≤ (Matrix.trace (φ A * φ B)).re at hc
  rw [hprod, trace_conjugation, ← map_mul φ, trace_conjugation] at hc
  exact hc

theorem two_dimension_word_bound {w : TraceWord} (hw : WordNonnegative w)
    (hAmass : exponentMass true w = 1) (hBmass : exponentMass false w = 1)
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖wordTrace A B w‖ ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨d, hred⟩ := normalized_reduced_data hw hAmass hBmass
  rw [hred.trace A B hA hB]
  unfold ExponentData.word wordTrace
  rw [← pairProduct_eq_matrixWord]
  unfold pairProduct
  rw [List.map_ofFn]
  exact two_dimension_pair_bound hA hB d.p d.q (fun i => (d.p_positive i).le)
    (fun i => (d.q_positive i).le) d.p_total d.q_total

theorem optimalConstant_two_dimension {w : TraceWord} (hw : WordNonnegative w)
    (hAmass : exponentMass true w = 1) (hBmass : exponentMass false w = 1) :
    optimalConstant 2 w = 1 := by
  apply le_antisymm
  · unfold optimalConstant
    apply iSup_le
    intro A
    apply iSup_le
    intro B
    apply iSup_le
    intro hA
    apply iSup_le
    intro hB
    apply ENNReal.ofReal_le_one.mpr
    unfold traceRatio
    exact (div_le_one (trace_product_positive hA hB)).mpr
      (two_dimension_word_bound hw hAmass hBmass hA.posSemidef hB.posSemidef)
  · exact optimalConstant_lower_bound 2 (by decide) w

end ResearchMain.AHOConstants
