import MainTheorems.DominationRoots.GraphPolynomial
import Mathlib.Data.ZMod.Basic

namespace ResearchMain.DominationRoots

open Classical Polynomial ResearchMain.Domination

variable {V : Type*} [Fintype V]

def Compatible (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, u ≠ v ∧ ¬G.Adj u v

omit [Fintype V] in
theorem compatible_swap {G : SimpleGraph V} {A B : Finset V} (h : Compatible G A B) :
    Compatible G B A := by
  intro v hv u hu
  obtain ⟨hne, hadj⟩ := h u hu v hv
  exact ⟨Ne.symm hne, fun h => hadj h.symm⟩

omit [Fintype V] in
theorem compatible_self_iff (G : SimpleGraph V) (A : Finset V) :
    Compatible G A A ↔ A = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    exact (h v hv v hv).1 rfl
  · rintro rfl
    simp [Compatible]

noncomputable def compatiblePairs (G : SimpleGraph V) : Finset (Finset V × Finset V) :=
  Finset.univ.filter (fun p => Compatible G p.1 p.2)

theorem mem_compatiblePairs (G : SimpleGraph V) (p : Finset V × Finset V) :
    p ∈ compatiblePairs G ↔ Compatible G p.1 p.2 := by
  simp [compatiblePairs]

theorem empty_pair_mem (G : SimpleGraph V) : (∅, ∅) ∈ compatiblePairs G := by
  simp [mem_compatiblePairs, Compatible]

theorem compatible_fixed_pair {G : SimpleGraph V} {p : Finset V × Finset V}
    (hp : p ∈ compatiblePairs G) (he : p.swap = p) : p = (∅, ∅) := by
  have hparts : p.2 = p.1 := congrArg Prod.fst he
  have h := (mem_compatiblePairs G p).mp hp
  rw [hparts] at h
  have hempty := (compatible_self_iff G p.1).mp h
  exact Prod.ext hempty (hparts.trans hempty)

theorem compatiblePairs_mod_two (G : SimpleGraph V) :
    ((compatiblePairs G).card : ZMod 2) = 1 := by
  let s := (compatiblePairs G).erase (∅, ∅)
  have hmem : ∀ p ∈ s, p.swap ∈ s := by
    intro p hp
    have h := Finset.mem_erase.mp hp
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact h.1 (by simpa using congrArg Prod.swap he)
    · apply (mem_compatiblePairs G p.swap).mpr
      exact compatible_swap ((mem_compatiblePairs G p).mp h.2)
  have hsum : (∑ p ∈ s, (1 : ZMod 2)) = 0 :=
    Finset.sum_involution (fun p _ => p.swap)
      (fun _ _ => by change (2 : ZMod 2) = 0; exact ZMod.natCast_self 2)
      (fun p hp _ he => (Finset.mem_erase.mp hp).1
        (compatible_fixed_pair (Finset.mem_erase.mp hp).2 he))
      hmem (fun p _ => Prod.swap_swap p)
  have hsplit := Finset.sum_erase_add (compatiblePairs G) (fun _ => (1 : ZMod 2))
    (empty_pair_mem G)
  change (∑ p ∈ (compatiblePairs G).erase (∅, ∅), (1 : ZMod 2)) = 0 at hsum
  rw [hsum, zero_add] at hsplit
  simpa using hsplit.symm

noncomputable def compatibleVertices (G : SimpleGraph V) (A : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∀ u ∈ A, u ≠ v ∧ ¬G.Adj u v)

theorem compatible_iff_subset (G : SimpleGraph V) (A B : Finset V) :
    Compatible G A B ↔ B ⊆ compatibleVertices G A := by
  simp only [Compatible, compatibleVertices, Finset.subset_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h v hv u hu
    exact h u hu v hv
  · intro h u hu v hv
    exact h hv u hu

theorem compatibleVertices_empty_iff (G : SimpleGraph V) (A : Finset V) :
    compatibleVertices G A = ∅ ↔ Dominates G A := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [compatibleVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    not_forall, not_and, not_not, Dominates]
  constructor
  · intro h v
    obtain ⟨u, hu, h⟩ := h v
    exact ⟨u, hu, (Classical.or_iff_not_imp_left).mpr h⟩
  · intro h v
    obtain ⟨u, hu, h⟩ := h v
    exact ⟨u, hu, fun hne => h.resolve_left hne⟩

end ResearchMain.DominationRoots
