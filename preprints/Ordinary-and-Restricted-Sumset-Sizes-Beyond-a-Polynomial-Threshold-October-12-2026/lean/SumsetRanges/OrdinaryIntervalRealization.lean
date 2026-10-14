import SumsetRanges.OrdinaryLargeRealization
import SumsetRanges.OrdinaryParameterInterval

namespace SumsetRanges

theorem ordinary_parameter_interval_realized (h c b : ℕ) (hh : 3≤h)
    (hc : (32*h^3)^10≤c) (hb : 2≤b) (hkc : sparseThreshold (c+b)≤c)
    (z : ℤ) (hz : ordinaryParameterValue h c b (ordinaryCaps h c b)≤z)
    (hz' : z≤ordinaryParameterValue h c b (fun _ => 0)) :
    ∃B : Finset ℤ,B.card=c+b ∧
      (∀a∈B,0≤a ∧ a≤((c+b)^(ordinaryExponent h):ℕ)) ∧
      ((ordinarySums B h).card:ℤ)=z := by
  obtain ⟨v,hv,he⟩ := ordinary_parameter_interval h c b hh hc hb hkc z hz hz'
  have hcap := large_caps_positive (h:=h) (c:=c) (by omega) hc
  have hbds := parameterCoordinates_bounds (h-1) (repetitionCap c) (sharedCap c)
    (denseWidth h b) v (by omega) hv
  have hnu := ordinaryNonfreeSize_bound h c (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
    (by omega) hc hbds.1 (fun m hm => (hbds.2.1 m hm).2)
  have hnum : ordinaryNonfreeSize h (repetitionParameters (h-1) v) (sharedParameters (h-1) v)≤c := by
    nlinarith
  have hlarge := (large_c_elementary (h:=h) (c:=c) (by omega) hc).2
  have hk : h^2+2*h+2≤c+b := by nlinarith
  obtain ⟨B,hBc,hB,hBs⟩ := ordinary_large_value_realized h c b
    (denseMaximum h b-v (denseIndex (h-1))) (repetitionParameters (h-1) v) (sharedParameters (h-1) v)
    (by omega) hk hb hnum (ordinary_parameter_dense_bounds h b v (by omega) hb hbds.2.2)
    (Nat.sub_le _ _)
  exact ⟨B,hBc,hB,hBs.trans he⟩

end SumsetRanges
