import Dowling.PartitionGluingRank
import Dowling.PartitionBounds

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem fiberTop_zero (p : GainPartition G n) : p.fiberTop none = zeroPartition := by
  apply code_injective
  funext i
  have hc := p.fiberEmbedding_color none i
  have hp : p.code (p.fiberEmbedding none i)=none := Option.map_eq_none_iff.mp hc
  have h := p.restrict_code_map (p.fiberEmbedding none) (p.fiber_rootClosed p le_rfl none) i
  rw [hp] at h
  exact Option.map_eq_none_iff.mp h

/-- Every nonempty nonzero fiber is literally a single balanced potential block. -/
theorem fiberTop_some_single (p : GainPartition G n) (r : Fin n)
    (hc : 0 < (p.fiber (some r)).card) :
    ∃ j, ∀ i, ∃ g, (p.fiberTop (some r)).code i=some (j,g) := by
  let i0 : Fin (p.fiber (some r)).card := ⟨0,hc⟩
  have h0 := p.fiberEmbedding_color (some r) i0
  have hroot : p.IsRoot r := by
    cases hi : p.code (p.fiberEmbedding (some r) i0) with
    | none => simp [blockColor,hi] at h0
    | some v =>
      rcases v with ⟨s,g⟩
      have hs : s=r := by simpa only [blockColor,hi,Option.map_some,Option.some.injEq] using h0
      subst s
      exact p.rooted _ r g hi
  have hr : p.blockColor r=some r := by
    change p.code r=some (r,1) at hroot
    simp only [blockColor,hroot,Option.map_some]
  obtain ⟨j,hj⟩ := p.fiberEmbedding_range (some r) r hr
  refine ⟨j,?_⟩
  intro i
  have hi := p.fiberEmbedding_color (some r) i
  have hmap := p.restrict_code_map (p.fiberEmbedding (some r)) (p.fiber_rootClosed p le_rfl (some r)) i
  cases hpi : p.code (p.fiberEmbedding (some r) i) with
  | none => simp [blockColor,hpi] at hi
  | some v =>
    rcases v with ⟨s,g⟩
    have hs : s=r := by simpa only [blockColor,hpi,Option.map_some,Option.some.injEq] using hi
    subst s
    refine ⟨g,?_⟩
    apply restrictionCode_map_injective (p.fiberEmbedding (some r))
    change ((p.fiberTop (some r)).code i).map _ = some (p.fiberEmbedding (some r) j,g)
    rw [hj]
    exact hmap.trans hpi

end Dowling.GainPartition
