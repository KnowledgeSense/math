import HardCoreActivityThreshold.GraftedCore
import HardCoreActivityThreshold.CriticalFixedPoint

/-! Finite free-boundary constant-activity trees with unbounded genuine correlation row norm. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

noncomputable def coreRootOccupation (a r : ℝ) (h : ℕ) : ℝ :=
  oddsOccupation (a/(1+iteratedOdds a 5 r h)^6)

noncomputable def coreRowBound (a r : ℝ) (h : ℕ) : ℝ :=
  24 * (coreRootOccupation a r h * (1-coreRootOccupation a r h)) * coreResponse a 5 r h

theorem coreRootOccupation_continuousAt {a omega : ℝ} (ha : 0 < a) (ho : 0 < omega)
    (hfix : a = omega*(1+omega)^5) (h : ℕ) :
    ContinuousAt (fun r => coreRootOccupation a r h) omega := by
  have hi := iteratedOdds_continuousAt ho 5 hfix h
  have hd : (1+iteratedOdds a 5 omega h)^6 ≠ 0 := by rw [iteratedOdds_fixed ho 5 hfix h]; positivity
  have hquot : ContinuousAt (fun r => a/(1+iteratedOdds a 5 r h)^6) omega :=
    continuousAt_const.div ((continuousAt_const.add hi).pow 6) hd
  apply ContinuousAt.comp (g := oddsOccupation) (f := fun r => a/(1+iteratedOdds a 5 r h)^6)
    (x := omega) _ hquot
  apply oddsOccupation_continuousAt
  rw [iteratedOdds_fixed ho 5 hfix h]
  positivity

theorem coreRowBound_continuousAt {a omega : ℝ} (ha : 0 < a) (ho : 0 < omega)
    (hfix : a = omega*(1+omega)^5) (h : ℕ) :
    ContinuousAt (fun r => coreRowBound a r h) omega := by
  have hq := coreRootOccupation_continuousAt ha ho hfix h
  exact (continuousAt_const.mul (hq.mul (continuousAt_const.sub hq))).mul
    (coreResponse_continuousAt ho 5 hfix h)

def graftedChildren (G : ForestExpr) (h : ℕ) : ForestExpr := rootCopies (coreChildren G 5 h) 6

theorem grafted_downwardOccupation (G : ForestExpr) {a : ℝ} (ha : 0 < a) (h : ℕ) :
    downwardOccupation (graftedChildren G h) (fun _ => a) = coreRootOccupation a (rootOdds G a) h := by
  rw [downwardOccupation_constant _ ha]
  unfold graftedChildren coreRootOccupation
  rw [rootOdds_copies _ ha, coreChildren_odds G ha]

theorem grafted_correlation_lower (G : ForestExpr) {a : ℝ} (ha : 0 < a) (h : ℕ) :
    coreRowBound a (rootOdds G a) h ≤
      ∑ v, (correlationMatrix (hardCoreLaw (graftedChildren G h).root.graph
        (fun _ => a) (fun _ => ha)) none v)^2 := by
  have hb := correlation_row_energy_lower (h+1) (graftedChildren G h) (fun _ => a) (fun _ => ha)
  rw [grafted_downwardOccupation G ha h] at hb
  unfold graftedChildren at hb
  rw [responseEnergy_copies, coreChildren_response G ha 5 h] at hb
  convert hb using 1
  · unfold coreRowBound; ring
  · rfl

theorem coreRootOccupation_fixed {a omega : ℝ} (ho : 0 < omega)
    (hfix : a = omega*(1+omega)^5) (h : ℕ) :
    coreRootOccupation a omega h = oddsOccupation (oddsOccupation omega) := by
  unfold coreRootOccupation
  rw [iteratedOdds_fixed ho 5 hfix h, hfix]
  congr 1
  unfold oddsOccupation
  have hd : 1+omega ≠ 0 := by positivity
  rw [show (6 : ℕ) = 5+1 by rfl, pow_succ]
  field_simp

private theorem oddsOccupation_mem_Ioo {r : ℝ} (hr : 0 < r) :
    0 < oddsOccupation r ∧ oddsOccupation r < 1 := by
  unfold oddsOccupation
  constructor
  · exact div_pos hr (by positivity)
  · apply (div_lt_one (by positivity : 0 < 1+r)).mpr; linarith

/-- All activities are exactly `a`; every tree and every boundary gadget is finite and unpinned. -/
theorem constant_activity_correlation_row_unbounded {a omega : ℝ} (ha : 0 < a) (ho : 0 < omega)
    (hfix : a = omega*(1+omega)^5) (hsq : 1 ≤ 5*(oddsOccupation omega)^2) (M : ℝ) :
    ∃ A : ForestExpr, M < ∑ v,
      (correlationMatrix (hardCoreLaw A.root.graph (fun _ => a) (fun _ => ha)) none v)^2 := by
  let p := oddsOccupation omega
  let m := oddsOccupation p
  have hp : 0 < p := (oddsOccupation_mem_Ioo ho).1
  have hm : 0 < m := (oddsOccupation_mem_Ioo hp).1
  have hm1 : m < 1 := (oddsOccupation_mem_Ioo hp).2
  let c : ℝ := 24*(m*(1-m))*p^2
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨h, hh⟩ := exists_nat_gt (M/c)
  have hM : M < c*(h+1) := by
    have ht : M < (h : ℝ)*c := (div_lt_iff₀ hc).mp hh
    nlinarith
  have hb : c*(h+1) ≤ coreRowBound a omega h := by
    unfold coreRowBound
    rw [coreRootOccupation_fixed ho hfix h]
    have h := coreResponse_fixed_lower ho 5 hfix hsq h
    have hw : 0 ≤ 24*(oddsOccupation (oddsOccupation omega)*(1-oddsOccupation (oddsOccupation omega))) := by
      change 0 ≤ 24*(m*(1-m))
      positivity
    have he := mul_le_mul_of_nonneg_left h hw
    simpa [c, p, m, mul_assoc] using he
  have hstrict : M < coreRowBound a omega h := lt_of_lt_of_le hM hb
  have hcont := coreRowBound_continuousAt ha ho hfix h
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hcont
    (coreRowBound a omega h - M) (by linarith)
  obtain ⟨G, hG⟩ := exists_rootOdds_approximation ha ho 5 hfix hδ
  refine ⟨graftedChildren G h, lt_of_lt_of_le ?_ (grafted_correlation_lower G ha h)⟩
  have hclose := hnear (by simpa [Real.dist_eq] using hG)
  rw [Real.dist_eq, abs_lt] at hclose
  linarith

/-- The source's critical activity and every larger constant activity force unbounded actual correlation rows. -/
theorem supercritical_correlation_row_unbounded {a : ℝ} (ha : criticalActivity ≤ a) (M : ℝ) :
    ∃ A : ForestExpr, M < ∑ v,
      (correlationMatrix (hardCoreLaw A.root.graph (fun _ => a)
        (fun _ => lt_of_lt_of_le criticalActivity_pos ha)) none v)^2 := by
  have hap : 0 < a := lt_of_lt_of_le criticalActivity_pos ha
  obtain ⟨p, hp, hfix⟩ := occupation_fixedpoint_exists hap 6 (show 0 < (6 : ℕ) by decide)
  have hsquare := supercritical_fixedpoint_square ha hp hfix
  have how : 0 < p/(1-p) := div_pos hp.1 (by linarith [hp.2])
  have hfix' := occupation_fixedpoint_to_odds hp 6 (show 0 < (6 : ℕ) by decide) hfix
  have hprob : oddsOccupation (p/(1-p)) = p := by
    unfold oddsOccupation
    have hd : 1-p ≠ 0 := by linarith [hp.2]
    field_simp
    ring
  apply constant_activity_correlation_row_unbounded hap how hfix'
  simpa [hprob] using hsquare

end HardCoreActivityThreshold
