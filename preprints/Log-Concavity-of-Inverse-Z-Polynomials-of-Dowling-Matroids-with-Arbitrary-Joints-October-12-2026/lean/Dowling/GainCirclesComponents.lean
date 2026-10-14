import Dowling.GainCirclesReduction
import Dowling.BalancedComponents

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ} {S : Set (Edge G n)}

theorem GainPath.gain_eq_one_of_component_circles (r : Fin n)
    (hcircle : ∀ (j:Fin n),Connected S r j → ∀ p:GainPath S j j,p.IsCircle → p.gain=1)
    {i : Fin n} (hi : Connected S r i) (p : GainPath S i i) : p.gain=1 := by
  have hmain (L:ℕ) : ∀ (i:Fin n),Connected S r i → ∀ p:GainPath S i i,
      p.length=L → p.gain=1 := by
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro i hi p hpL
      by_cases hzero : p.length=0
      · exact p.gain_eq_one_of_length_zero hzero
      by_cases hnodup : p.vertices.Nodup
      · exact hcircle i hi p ⟨Nat.pos_of_ne_zero hzero,hnodup⟩
      obtain ⟨v,a,b,c,hgain,hlen,hb,hc⟩ := p.repeated_vertex_decomposition hnodup
      have hv : Connected S r v := by
        obtain ⟨g,hg⟩ := hi
        exact ⟨g*a.gain,hg.trans a.to_walk⟩
      have hblt : b.length<L := by omega
      have hclt : (a.append c).length<L := by rw [GainPath.length_append]; omega
      have hbgain := ih b.length hblt v hv b rfl
      have hcgain := ih (a.append c).length hclt i hi (a.append c) rfl
      rw [GainPath.gain_append] at hcgain
      rw [hgain,hbgain,mul_one,hcgain]
  exact hmain p.length i hi p rfl

/-- The literal gain-graph balance condition: no selected joint in the component,
and every vertex-simple closed selected-link traversal has identity gain. -/
def CircleBalancedAt (S : Set (Edge G n)) (i : Fin n) : Prop :=
  (∀ j,Connected S i j → Sum.inl j∉S) ∧
  (∀ j,Connected S i j → ∀ p:GainPath S j j,p.IsCircle → p.gain=1)

theorem balancedAt_iff_circleBalancedAt (i : Fin n) : BalancedAt S i ↔ CircleBalancedAt S i := by
  constructor
  · intro hi
    refine ⟨hi.1,?_⟩
    intro j hj p _
    exact (hi.of_connected hj).2 p.gain p.to_walk
  · intro hi
    refine ⟨hi.1,?_⟩
    intro g hg
    obtain ⟨p,hp⟩ := hg.exists_gainPath
    rw [← hp]
    exact p.gain_eq_one_of_component_circles i hi.2 ⟨1,GainWalk.nil i⟩

end Dowling
