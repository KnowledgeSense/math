import MainTheorems.AHOConstants.CounterexampleLowerBound
import MainTheorems.AHOConstants.CounterexampleTrace
import MainTheorems.AHOConstants.CounterexampleExponents
import MainTheorems.AHOConstants.ReducedData

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable def ExponentData.cutExponents (d : ExponentData)
    (S T : Finset (Fin (d.size + 1))) (hcut : cutCapacity d.p d.q S T < 1) :
    CutExponents where
  theta := 2 - cutMass d.p S - cutMass d.q T
  edges := (cutEdges S T).card
  theta_nonnegative := by
    have hS := cutMass_le_total (fun i => (d.p_positive i).le) S
    have hT := cutMass_le_total (fun i => (d.q_positive i).le) T
    rw [d.p_total] at hS
    rw [d.q_total] at hT
    linarith
  edges_le_one := strict_cut_has_at_most_one_edge (fun i => (d.p_positive i).le)
    (fun i => (d.q_positive i).le) d.p_total d.q_total hcut
  capacity_gap := hcut

theorem ExponentData.infeasible_psd_real_counterexample (d : ExponentData) (hd : ¬d.feasible)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℂ,
      A.PosSemidef ∧ B.PosSemidef ∧
        (∀ i j, (A i j).im = 0) ∧ (∀ i j, (B i j).im = 0) ∧
        0 < (Matrix.trace (A * B)).re ∧
          L * (Matrix.trace (A * B)).re < (wordTrace A B d.word).re := by
  obtain ⟨S, T, hcut⟩ := d.infeasible_cut hd
  let e := d.cutExponents S T hcut
  let c : ℝ := (1 / 16 : ℝ) ^ (d.size + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨ε, hε₀, hε₁, hzsmall, _, hgain⟩ :=
    divergent_ratio_parameter hc (by norm_num : (0 : ℝ) < 5) e.gap_positive
      e.height_positive hL 1 (by norm_num)
  let z := ε ^ e.height
  have hz : 0 < z := Real.rpow_pos_of_pos hε₀ _
  have hz' : z ≤ 1 / 8 := hzsmall.le
  have hzsquare : z ^ 2 = ε ^ (2 * e.height) := by
    dsimp [z]
    rw [← Real.rpow_mul_natCast hε₀.le]
    congr 1
    ring
  have hεz : ε ≤ z ^ 2 := by
    rw [hzsquare]
    have h := Real.rpow_le_rpow_of_exponent_ge hε₀ hε₁.le
      (show 2 * e.height ≤ 1 from by linarith [e.height_lt_half])
    simpa using h
  have hlower : c * ε ^ e.numeratorExponent ≤
      ‖wordTrace (counterexampleA ε z) (counterexampleB ε) d.word‖ := by
    have h := counterexample_actual_trace_lower hε₀ hε₁ hz hz' d.p d.q
      d.p_positive d.q_positive d.p_total d.q_total S T
    change c * ε ^ e.theta * z ^ e.edges ≤ _ at h
    have hp : ε ^ e.theta * z ^ e.edges = ε ^ e.numeratorExponent := by
      dsimp [z, CutExponents.numeratorExponent]
      rw [← Real.rpow_mul_natCast hε₀.le, ← Real.rpow_add hε₀]
      congr 1
      ring
    rw [mul_assoc, hp] at h
    exact h
  have hscaled : ((c / 5) * ε ^ (-e.gap)) * (5 * z ^ 2) =
      c * ε ^ e.numeratorExponent := by
    rw [hzsquare]
    calc
      _ = c * (ε ^ (-e.gap) * ε ^ (2 * e.height)) := by ring
      _ = c * ε ^ (-e.gap + 2 * e.height) := by rw [Real.rpow_add hε₀]
      _ = _ := by
        congr 2
        dsimp [CutExponents.gap]
        ring
  have hstrict : L * (5 * z ^ 2) < c * ε ^ e.numeratorExponent := by
    rw [← hscaled]
    exact mul_lt_mul_of_pos_right hgain (by positivity)
  have htrace : ‖wordTrace (counterexampleA ε z) (counterexampleB ε) d.word‖ =
      (wordTrace (counterexampleA ε z) (counterexampleB ε) d.word).re := by
    unfold ExponentData.word wordTrace
    rw [← pairProduct_eq_matrixWord]
    simp only [pairProduct, List.map_ofFn, Function.comp_def]
    exact counterexample_paired_trace_norm_eq_re hε₀ hε₁ hz hz' d.p d.q
      d.p_positive d.q_positive
  rw [htrace] at hlower
  refine ⟨counterexampleA ε z, counterexampleB ε,
    counterexampleA_posSemidef hε₀.le z, counterexampleB_posSemidef hε₀.le,
    counterexampleA_realEntries ε z, counterexampleB_realEntries ε,
    counterexample_denominator_positive hε₀ hz hz', ?_⟩
  calc
    _ ≤ L * (5 * z ^ 2) := mul_le_mul_of_nonneg_left
      (counterexample_denominator_upper hε₀.le hε₁.le hεz) hL
    _ < c * ε ^ e.numeratorExponent := hstrict
    _ ≤ _ := hlower

theorem ExponentData.infeasible_psd_counterexample (d : ExponentData) (hd : ¬d.feasible)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℂ,
      A.PosSemidef ∧ B.PosSemidef ∧
        0 < (Matrix.trace (A * B)).re ∧
          L * (Matrix.trace (A * B)).re < ‖wordTrace A B d.word‖ := by
  obtain ⟨A, B, hA, hB, _, _, hpos, hlarge⟩ :=
    d.infeasible_psd_real_counterexample hd L hL
  exact ⟨A, B, hA, hB, hpos, hlarge.trans_le (Complex.re_le_norm _)⟩

theorem word_infeasible_psd_counterexample {w : TraceWord} (d : ExponentData)
    (hred : WordReduction w d.word) (hd : ¬d.feasible) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℂ,
      A.PosSemidef ∧ B.PosSemidef ∧
        0 < (Matrix.trace (A * B)).re ∧
          L * (Matrix.trace (A * B)).re < ‖wordTrace A B w‖ := by
  obtain ⟨A, B, hA, hB, hpos, hlarge⟩ := d.infeasible_psd_counterexample hd L hL
  refine ⟨A, B, hA, hB, hpos, ?_⟩
  rw [hred.trace A B hA hB]
  exact hlarge

end ResearchMain.AHOConstants
