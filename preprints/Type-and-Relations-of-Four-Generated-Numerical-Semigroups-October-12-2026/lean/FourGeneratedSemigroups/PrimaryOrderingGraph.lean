import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

namespace FourGeneratedSemigroups
open scoped BigOperators

noncomputable def incomingDegree (E : Fin 4 → Fin 4 → Prop) (v : Fin 4) : ℕ := by
  classical
  exact ∑ u, if E u v then 1 else 0

noncomputable def outgoingDegree (E : Fin 4 → Fin 4 → Prop) (v : Fin 4) : ℕ := by
  classical
  exact ∑ u, if E v u then 1 else 0

theorem degree_sum_eq (E : Fin 4 → Fin 4 → Prop) :
    ∑ v, incomingDegree E v = ∑ v, outgoingDegree E v := by
  classical
  exact Finset.sum_comm

theorem incomingDegree_le_three (E : Fin 4 → Fin 4 → Prop)
    (hloop : ∀ v, ¬ E v v) (v : Fin 4) : incomingDegree E v ≤ 3 := by
  classical
  have hsub : Finset.univ.filter (fun u => E u v) ⊂ (Finset.univ : Finset (Fin 4)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hv : v ∈ Finset.univ.filter (fun u => E u v) := he.symm ▸ Finset.mem_univ v
    exact hloop v (Finset.mem_filter.mp hv).2
  have hc := Finset.card_lt_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  simpa [incomingDegree] using (show (Finset.univ.filter (fun u => E u v)).card ≤ 3 by omega)

/-- The directed-graph choice underlying a primary ordering on four generators. -/
theorem exists_primary_ordering_vertex (E : Fin 4 → Fin 4 → Prop)
    (Φ : Finset (Fin 4)) (hloop : ∀ v, ¬ E v v)
    (hout : ∀ v, 1 ≤ outgoingDegree E v)
    (hfull : ∀ v ∈ Φ, outgoingDegree E v = 3)
    (hin : ∃ v, 2 ≤ incomingDegree E v) :
    ∃ v, 2 ≤ incomingDegree E v ∧ (v ∉ Φ ∨ incomingDegree E v = 3) := by
  classical
  by_contra hn
  push Not at hn
  have hi : ∀ v, incomingDegree E v ≤ 1 + if v ∈ Φ then 1 else 0 := by
    intro v
    by_cases hv : v ∈ Φ
    · simp only [hv, ↓reduceIte]
      have hb := incomingDegree_le_three E hloop v
      by_cases ht : 2 ≤ incomingDegree E v
      · have hh := hn v ht
        omega
      · omega
    · simp only [hv, ↓reduceIte, add_zero]
      by_contra ht
      have hh := hn v (by omega)
      exact hv hh.1
  have ho : ∀ v, 1 + 2 * (if v ∈ Φ then 1 else 0) ≤ outgoingDegree E v := by
    intro v
    by_cases hv : v ∈ Φ
    · simp [hv, hfull v hv]
    · simpa [hv] using hout v
  have hsi := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin 4))) => hi v)
  have hso := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin 4))) => ho v)
  have he := degree_sum_eq E
  have hp : 0 < Φ.card := by
    obtain ⟨v, hv⟩ := hin
    exact Finset.card_pos.mpr ⟨v, (hn v hv).1⟩
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hsi hso
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsi hso
  rw [← Finset.mul_sum] at hso
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter] at hso
  norm_cast at hsi hso
  omega

/-- A finite directed graph with positive outdegree and indegree at most one
has exactly one incoming and one outgoing arc at every vertex. -/
theorem degrees_eq_one (E : Fin 4 → Fin 4 → Prop)
    (hout : ∀ v, 1 ≤ outgoingDegree E v)
    (hin : ∀ v, incomingDegree E v ≤ 1) :
    (∀ v, outgoingDegree E v = 1) ∧ (∀ v, incomingDegree E v = 1) := by
  classical
  have hupper := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin 4))) => hin v)
  have hlower := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin 4))) => hout v)
  have he := degree_sum_eq E
  constructor
  · intro v
    by_contra hv
    have ht : 1 < outgoingDegree E v := by have hh := hout v; omega
    have hs := Finset.sum_lt_sum
      (fun u (_ : u ∈ (Finset.univ : Finset (Fin 4))) => hout u)
      ⟨v, Finset.mem_univ v, ht⟩
    omega
  · intro v
    by_contra hv
    have ht : incomingDegree E v < 1 := by have hh := hin v; omega
    have hs := Finset.sum_lt_sum
      (fun u (_ : u ∈ (Finset.univ : Finset (Fin 4))) => hin u)
      ⟨v, Finset.mem_univ v, ht⟩
    omega

theorem existsUnique_outgoing_of_degrees (E : Fin 4 → Fin 4 → Prop)
    (hout : ∀ v, 1 ≤ outgoingDegree E v)
    (hin : ∀ v, incomingDegree E v ≤ 1) (v : Fin 4) : ∃! w, E v w := by
  classical
  have hv := (degrees_eq_one E hout hin).1 v
  have hc : (Finset.univ.filter (E v)).card = 1 := by simpa [outgoingDegree] using hv
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
  have hmem : ∀ u, E v u ↔ u = w := by
    intro u
    have h := congrArg (fun S : Finset (Fin 4) => u ∈ S) hw
    simpa using h
  exact ⟨w, (hmem w).mpr rfl, fun u hu => (hmem u).mp hu⟩

end FourGeneratedSemigroups
