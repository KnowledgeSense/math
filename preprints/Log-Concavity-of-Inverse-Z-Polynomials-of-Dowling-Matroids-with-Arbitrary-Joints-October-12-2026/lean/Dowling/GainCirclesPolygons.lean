import Dowling.GainCirclesGeometry

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ} {S : Set (Edge G n)}

namespace GainPath

/-- A vertex-simple closed traversal with the length-two inverse pair removed.
For canonical gain links, opposite traversals with inverse labels use the same link. -/
def IsPolygon {i : Fin n} (p : GainPath S i i) : Prop :=
  p.IsCircle ∧ (p.length = 2 → p.gain ≠ 1)

theorem parallel_isPolygon_iff {i j : Fin n} {g h : G}
    (a : Arc S i j g) (b : Arc S j i h) :
    (cons g a (cons h b (nil i))).IsPolygon ↔ h ≠ g⁻¹ := by
  simp only [IsPolygon, parallel_isCircle a b, true_and, length, gain, mul_one]
  simp only [forall_const]
  apply not_congr
  constructor
  · intro e
    have e' := congrArg (fun x => g⁻¹ * x) e
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using e'
  · intro e
    rw [e, mul_inv_cancel]

theorem circles_neutral_iff_polygons_neutral (i : Fin n) :
    (∀ p : GainPath S i i, p.IsCircle → p.gain = 1) ↔
      (∀ p : GainPath S i i, p.IsPolygon → p.gain = 1) := by
  constructor
  · intro h p hp
    exact h p hp.1
  · intro h p hp
    by_cases hg : p.gain = 1
    · exact hg
    · exact h p ⟨hp, fun _ => hg⟩

end GainPath

/-- The usual circle condition, excluding immediate reversal along one link. -/
def PolygonBalancedAt (S : Set (Edge G n)) (i : Fin n) : Prop :=
  (∀ j, Connected S i j → Sum.inl j ∉ S) ∧
  (∀ j, Connected S i j → ∀ p : GainPath S j j, p.IsPolygon → p.gain = 1)

theorem balancedAt_iff_polygonBalancedAt (i : Fin n) :
    BalancedAt S i ↔ PolygonBalancedAt S i := by
  rw [balancedAt_iff_circleBalancedAt]
  unfold CircleBalancedAt PolygonBalancedAt
  apply and_congr_right
  intro _
  exact forall_congr' fun j => forall_congr' fun _ =>
    GainPath.circles_neutral_iff_polygons_neutral j

theorem closed_gainWalks_iff_polygons :
    (∀ (i : Fin n) (g : G), GainWalk S i i g → g = 1) ↔
      (∀ (i : Fin n) (p : GainPath S i i), p.IsPolygon → p.gain = 1) := by
  rw [closed_gainWalks_iff_circles]
  exact forall_congr' GainPath.circles_neutral_iff_polygons_neutral

end Dowling
