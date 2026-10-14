import SumsetRanges.ParameterWidths
import SumsetRanges.ParameterAdjacency

namespace SumsetRanges

theorem parameter_interval (h c b : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hkc : sparseThreshold (c+b)≤c) (z : ℤ)
    (hz : parameterValue h c b (admissibleCaps h c b)≤z)
    (hz' : z≤parameterValue h c b (fun _ => 0)) :
    ∃v,InNatBox (admissibleCaps h c b) v ∧ parameterValue h c b v=z := by
  exact integer_box_intermediate (parameterDimension h) (admissibleCaps h c b)
    (parameterValue h c b) (parameterStepBound h c b) (parameterWidthBound h c b)
    (parameter_antitone h c b hh hc hb) (parameter_step_bound h c b hh hc hb)
    (parameter_width_bound h c b hh hc hb hkc) (parameter_first_bound h c b hh)
    (parameter_next_bound h c b hh (by omega)) z hz hz'

theorem parameter_interval_realized (h c b : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hkc : sparseThreshold (c+b)≤c) (z : ℤ)
    (hz : parameterValue h c b (admissibleCaps h c b)≤z)
    (hz' : z≤parameterValue h c b (fun _ => 0)) :
    ∃B : Finset ℤ,B.card=c+b ∧ (∀a∈B,0≤a ∧ a≤((c+b)^(restrictedExponent h):ℕ)) ∧
      ((restrictedSums B h).card : ℤ)=z := by
  obtain ⟨v,hv,he⟩ := parameter_interval h c b hh hc hb hkc z hz hz'
  have hS := (large_caps_positive (by omega : 1≤h) hc).2
  have hbds := parameterCoordinates_bounds h (repetitionCap c) (sharedCap c) (denseWidth h b) v
    (by omega) hv
  have hnu := nonfreeSize_box_bound h c (repetitionParameters h v) (sharedParameters h v)
    (by omega) hc hbds.1 (fun m hm => (hbds.2.1 m hm).2)
  have hN : nonfreeSize h (repetitionParameters h v) (sharedParameters h v)≤c := by
    have ht := Nat.le_mul_of_pos_left (nonfreeSize h (repetitionParameters h v) (sharedParameters h v))
      (by omega : 0<8*h)
    omega
  have hx := parameter_dense_bounds h b v (by omega) hb hbds.2.2
  obtain ⟨B,hB,hBd,hBe⟩ := largeValue_realized h c b (denseMaximum h b-v (denseIndex h))
    (repetitionParameters h v) (sharedParameters h v) hh hb hN
    (fun m hm => (hbds.2.1 m hm).1) hx (by unfold denseMaximum; omega)
  exact ⟨B,hB,hBd,hBe.trans he⟩

end SumsetRanges
