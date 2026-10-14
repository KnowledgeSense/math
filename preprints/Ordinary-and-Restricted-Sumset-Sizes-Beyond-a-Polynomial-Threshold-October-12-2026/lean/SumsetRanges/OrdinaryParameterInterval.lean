import SumsetRanges.OrdinaryParameterWidths
import SumsetRanges.OrdinaryParameterAdjacency

namespace SumsetRanges

theorem ordinary_parameter_interval (h c b : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hkc : sparseThreshold (c+b)≤c) (z : ℤ)
    (hz : ordinaryParameterValue h c b (ordinaryCaps h c b)≤z)
    (hz' : z≤ordinaryParameterValue h c b (fun _ => 0)) :
    ∃v,InNatBox (ordinaryCaps h c b) v ∧ ordinaryParameterValue h c b v=z := by
  have hch : h≤c := by
    have hp := (large_c_elementary (by omega : 1≤h) hc).2
    nlinarith
  exact integer_box_intermediate (parameterDimension (h-1)) (ordinaryCaps h c b)
    (ordinaryParameterValue h c b) (ordinaryParameterStepBound h c b) (ordinaryParameterWidthBound h c b)
    (ordinary_parameter_antitone h c b hh hc hb) (ordinary_parameter_step_bound h c b hh hc hb)
    (ordinary_parameter_width_bound h c b hh hc hb hkc) (ordinary_parameter_first_bound h c b hh)
    (ordinary_parameter_next_bound h c b hh hch) z hz hz'

end SumsetRanges
