import Dowling.PartitionRestriction
import Mathlib.Logic.Function.Basic

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n m : ℕ}

theorem restrict_assignment (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e)
    (a : Fin n → Option G) (i : Fin m) :
    (p.restrict e hc).assignment (fun j => a (e j)) i = p.assignment a (e i) := by
  have h := p.restrict_code_map e hc i
  cases hi : (p.restrict e hc).code i with
  | none =>
    rw [hi] at h
    have hp : p.code (e i)=none := h.symm
    simp only [assignment,hi,hp]
  | some v =>
    rcases v with ⟨r,g⟩
    rw [hi] at h
    have hp : p.code (e i)=some (e r,g) := h.symm
    simp only [assignment,hi,hp]

/-- Restricting the root-closed partition is exactly restricting its actual
solutions; every local assignment extends to a global one. -/
theorem restrict_solutionSet (p : GainPartition G n) (e : Fin m ↪o Fin n) (hc : p.RootClosed e) :
    (p.restrict e hc).solutionSet = (fun x : Fin n → Option G => fun i => x (e i)) '' p.solutionSet := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    let b := Function.extend e a (fun _ => none)
    refine ⟨p.assignment b,⟨b,rfl⟩,?_⟩
    funext i
    change p.assignment b (e i) = (p.restrict e hc).assignment a i
    rw [← p.restrict_assignment e hc b i]
    have hb : (fun j => b (e j))=a := by
      funext j
      exact e.injective.extend_apply a (fun _ => none) j
    rw [hb]
  · rintro ⟨x,⟨a,rfl⟩,rfl⟩
    refine ⟨fun j => a (e j),?_⟩
    funext i
    exact p.restrict_assignment e hc a i

theorem restrict_mono {p q : GainPartition G n} (e : Fin m ↪o Fin n)
    (hp : p.RootClosed e) (hq : q.RootClosed e) (hpq : p ≤ q) :
    p.restrict e hp ≤ q.restrict e hq := by
  change (q.restrict e hq).solutionSet ⊆ (p.restrict e hp).solutionSet
  rw [restrict_solutionSet,restrict_solutionSet]
  exact Set.image_mono hpq

end Dowling.GainPartition
