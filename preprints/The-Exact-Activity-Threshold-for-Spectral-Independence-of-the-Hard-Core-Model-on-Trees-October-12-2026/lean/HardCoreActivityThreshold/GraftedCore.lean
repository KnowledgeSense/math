import HardCoreActivityThreshold.CorrelationEnergy
import HardCoreActivityThreshold.RootOddsApproximation

/-! Genuine constant-activity cores with finite free-boundary gadgets at their leaves. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

def coreChildren (G : ForestExpr) (b : ℕ) : ℕ → ForestExpr
  | 0 => G
  | h+1 => rootCopies (coreChildren G b h) b

noncomputable def iteratedOdds (a : ℝ) (b : ℕ) (r : ℝ) : ℕ → ℝ
  | 0 => r
  | h+1 => a / (1 + iteratedOdds a b r h)^b

noncomputable def oddsOccupation (r : ℝ) : ℝ := r/(1+r)

noncomputable def coreResponse (a : ℝ) (b : ℕ) (r : ℝ) : ℕ → ℝ
  | 0 => (oddsOccupation r)^2
  | h+1 => (oddsOccupation (iteratedOdds a b r (h+1)))^2 * (1+b*coreResponse a b r h)

theorem rootOdds_copies (G : ForestExpr) {a : ℝ} (ha : 0 < a) (b : ℕ) :
    rootOdds (rootCopies G b) a = a/(1+rootOdds G a)^b := by
  unfold rootOdds
  rw [mul_div_assoc, forestRatio_copies G ha]
  unfold rootOdds
  ring

theorem coreChildren_odds (G : ForestExpr) {a : ℝ} (ha : 0 < a) (b h : ℕ) :
    rootOdds (coreChildren G b h) a = iteratedOdds a b (rootOdds G a) h := by
  induction h with
  | zero => rfl
  | succ h ih => rw [coreChildren, rootOdds_copies _ ha, ih]; rfl

theorem downwardOccupation_constant (G : ForestExpr) {a : ℝ} (ha : 0 < a) :
    downwardOccupation G (fun _ => a) = oddsOccupation (rootOdds G a) := by
  rw [← forestMarginal_root_free G _ (fun _ => ha), forestMarginal_free_actual,
    root_marginal_from_odds G ha]
  rfl

theorem coreChildren_response (G : ForestExpr) {a : ℝ} (ha : 0 < a) (b h : ℕ) :
    responseEnergy (h+1) (coreChildren G b h).root (fun _ => a) (fun _ => ha) =
      coreResponse a b (rootOdds G a) h := by
  induction h with
  | zero => rw [responseEnergy_root, responseEnergy_zero, downwardOccupation_constant _ ha]; simp [coreChildren, coreResponse]
  | succ h ih =>
    rw [responseEnergy_root, downwardOccupation_constant _ ha, coreChildren_odds G ha b (h+1)]
    change (oddsOccupation (iteratedOdds a b (rootOdds G a) (h+1)))^2 *
      (1 + responseEnergy (h+1) (rootCopies (coreChildren G b h) b) (fun _ => a) (fun _ => ha)) = _
    rw [responseEnergy_copies, ih]
    rfl

theorem iteratedOdds_fixed {a omega : ℝ} (ho : 0 < omega) (b : ℕ)
    (hfix : a = omega*(1+omega)^b) (h : ℕ) : iteratedOdds a b omega h = omega := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [iteratedOdds, ih, hfix]
    exact mul_div_cancel_right₀ _ (pow_ne_zero _ (by positivity))

theorem iteratedOdds_continuousAt {a omega : ℝ} (ho : 0 < omega) (b : ℕ)
    (hfix : a = omega*(1+omega)^b) (h : ℕ) : ContinuousAt (fun r => iteratedOdds a b r h) omega := by
  induction h with
  | zero => exact continuousAt_id
  | succ h ih =>
    apply continuousAt_const.div ((continuousAt_const.add ih).pow b)
    change (1+iteratedOdds a b omega h)^b ≠ 0
    rw [iteratedOdds_fixed ho b hfix h]
    positivity

theorem oddsOccupation_continuousAt {r : ℝ} (hr : 0 ≤ r) : ContinuousAt oddsOccupation r :=
  continuousAt_id.div (continuousAt_const.add continuousAt_id) (by positivity)

theorem coreResponse_continuousAt {a omega : ℝ} (ho : 0 < omega) (b : ℕ)
    (hfix : a = omega*(1+omega)^b) (h : ℕ) : ContinuousAt (fun r => coreResponse a b r h) omega := by
  induction h with
  | zero => exact (oddsOccupation_continuousAt ho.le).pow 2
  | succ h ih =>
    apply ContinuousAt.mul
    · apply ContinuousAt.pow
      apply ContinuousAt.comp (g := oddsOccupation) (f := fun r => iteratedOdds a b r (h+1)) (x := omega) _ (iteratedOdds_continuousAt ho b hfix (h+1))
      rw [iteratedOdds_fixed ho b hfix (h+1)]
      exact oddsOccupation_continuousAt ho.le
    · exact continuousAt_const.add (continuousAt_const.mul ih)

/-- At or above the branching square threshold the finite-depth response grows linearly. -/
theorem coreResponse_fixed_lower {a omega : ℝ} (ho : 0 < omega) (b : ℕ)
    (hfix : a = omega*(1+omega)^b) (hsq : 1 ≤ b * (oddsOccupation omega)^2) (h : ℕ) :
    (oddsOccupation omega)^2 * (h+1) ≤ coreResponse a b omega h := by
  induction h with
  | zero => simp [coreResponse]
  | succ h ih =>
    rw [coreResponse, iteratedOdds_fixed ho b hfix (h+1)]
    have he : 0 ≤ coreResponse a b omega h := le_trans (by positivity) ih
    have hm := mul_le_mul_of_nonneg_right hsq he
    push_cast
    nlinarith

end HardCoreActivityThreshold
