import Dowling.BalancedPotentials

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem BalancedAt.of_connected {S : Set (Edge G n)} {i j : Fin n}
    (hi : BalancedAt S i) (hij : Connected S i j) : BalancedAt S j :=
  balanced_of_nonzero_solution S j (componentPotential_mem hi)
    ((componentPotential_nonzero S i j).mpr hij)

theorem balanced_congr {S : Set (Edge G n)} {i j : Fin n} (hij : Connected S i j) :
    BalancedAt S i ↔ BalancedAt S j := by
  obtain ⟨g,p⟩ := hij
  exact ⟨fun h => h.of_connected ⟨g,p⟩, fun h => h.of_connected ⟨g⁻¹,p.reverse⟩⟩

namespace GainPartition

theorem code_nonzero_iff_balanced (p : GainPartition G n) (S : Set (Edge G n))
    (hp : p.solutionSet = solutions G n S) (i : Fin n) :
    p.code i ≠ none ↔ BalancedAt S i := by
  constructor
  · intro hi
    cases hc : p.code i with
    | none => exact False.elim (hi hc)
    | some v =>
      rcases v with ⟨r,a⟩
      apply balanced_of_nonzero_solution S i (x := p.assignment (fun _ => some 1))
      · rw [← hp]
        exact p.assignment_mem _
      · simp [assignment, hc, gainAct]
  · intro hi hc
    obtain ⟨x,hx,hxi⟩ := (balanced_iff_nonzero_solution S i).mp hi
    rw [← hp] at hx
    exact hxi (((p.mem_solutionSet x).mp hx).1 i hc)

theorem root_balanced (p : GainPartition G n) (S : Set (Edge G n))
    (hp : p.solutionSet = solutions G n S) (r : Fin n) (hr : p.IsRoot r) : BalancedAt S r := by
  apply (p.code_nonzero_iff_balanced S hp r).mp
  change p.code r = some (r,1) at hr
  rw [hr]
  simp

theorem connected_to_root (p : GainPartition G n) (S : Set (Edge G n))
    (hp : p.solutionSet = solutions G n S) (i r : Fin n) (a : G)
    (hi : p.code i = some (r,a)) : Connected S r i := by
  have hr : p.IsRoot r := p.rooted i r a hi
  have hb := p.root_balanced S hp r hr
  have hx := componentPotential_mem hb
  rw [← hp] at hx
  have hi' := ((p.mem_solutionSet _).mp hx).2 i r a hi
  apply (componentPotential_nonzero S r i).mp
  rw [hi', ne_eq, gainAct_eq_none_iff]
  exact (componentPotential_nonzero S r r).mpr ⟨1,GainWalk.nil r⟩

theorem connected_roots_eq (p : GainPartition G n) (S : Set (Edge G n))
    (hp : p.solutionSet = solutions G n S) (r s : Fin n)
    (hr : p.IsRoot r) (hs : p.IsRoot s) (hc : Connected S r s) : r = s := by
  obtain ⟨g,w⟩ := hc
  have he : ∀ x ∈ p.solutionSet, x s = gainAct G (x r) g := by
    intro x hx
    rw [hp] at hx
    exact w.equation hx
  change p.code r = some (r,1) at hr
  change p.code s = some (s,1) at hs
  rcases (p.solution_link_iff r s g).mp he with ⟨hz,_⟩ | ⟨u,a,b,hra,hsb,_⟩
  · rw [hr] at hz
    cases hz
  · have h1 : (u,a) = (r,(1:G)) := Option.some.inj (hra.symm.trans hr)
    have h2 : (u,b) = (s,(1:G)) := Option.some.inj (hsb.symm.trans hs)
    exact (congrArg Prod.fst h1).symm.trans (congrArg Prod.fst h2)

end GainPartition
end Dowling
