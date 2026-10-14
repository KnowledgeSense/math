import MeanMaximumForests.ForestRepresentation

namespace MeanMaximumForests
open Finset

/-- Structural realizations are invariant under injective relabeling of vertices. -/
theorem ForestRealization.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (he : ∀ u v, G.Adj u v ↔ H.Adj (f u) (f v))
    {s rs : Finset V} {A : ForestExpr} (h : ForestRealization G s rs A) :
    ForestRealization H (s.map f) (rs.map f) A := by
  induction h with
  | empty => simpa using ForestRealization.empty (G := H)
  | @union a b ra rb A B hd hs hA hB ihA ihB =>
    have hd' : Disjoint (a.map f) (b.map f) := by
      apply disjoint_left.mpr
      intro w ha hb
      obtain ⟨u, hu, rfl⟩ := mem_map.mp ha
      obtain ⟨v, hv, hvu⟩ := mem_map.mp hb
      have hvu' := f.injective hvu
      subst v
      exact disjoint_left.mp hd hu hv
    have hs' : Separated H (a.map f) (b.map f) := by
      intro u hu v hv hadj
      obtain ⟨u₀, hu₀, eu⟩ := mem_map.mp hu
      obtain ⟨v₀, hv₀, ev⟩ := mem_map.mp hv
      subst u
      subst v
      exact hs u₀ hu₀ v₀ hv₀ ((he u₀ v₀).mpr hadj)
    simpa only [Finset.map_union] using ForestRealization.union hd' hs' ihA ihB
  | @root s rs A r hr hed hA ih =>
    have hr' : f r ∉ s.map f := by simpa using hr
    have hed' : ∀ w ∈ s.map f, H.Adj (f r) w ↔ w ∈ rs.map f := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
      simpa using (he r v).symm.trans (hed v hv)
    simpa using ForestRealization.root (f r) hr' hed' ih

end MeanMaximumForests
