import TerminalLogConcavity.GraphUnion
import TerminalLogConcavity.ForestExpressions

namespace TerminalLogConcavity
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- A rooted forest expression realized by vertices and edges of a simple graph.
The constructors assert only vertex disjointness and adjacency, not any counting inequality. -/
inductive ForestRealization : Finset V → Finset V → ForestExpr → Prop
  | empty : ForestRealization ∅ ∅ .empty
  | union {a b ra rb A B} : Disjoint a b → Separated G a b →
      ForestRealization a ra A → ForestRealization b rb B →
      ForestRealization (a ∪ b) (ra ∪ rb) (.union A B)
  | root {s rs A} (r : V) : r ∉ s →
      (∀ v ∈ s, G.Adj r v ↔ v ∈ rs) → ForestRealization s rs A →
      ForestRealization (insert r s) {r} (.root A)

theorem ForestRealization.roots_subset {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) : rs ⊆ s := by
  induction h with
  | empty => exact Subset.rfl
  | union _ _ _ _ ha hb => exact union_subset_union ha hb
  | root r _ _ _ _ => exact singleton_subset_iff.mpr (mem_insert_self _ _)

omit [DecidableEq V] in
theorem independenceNumber_mono {s t : Finset V} (h : s ⊆ t) :
    independenceNumber G s ≤ independenceNumber G t := by
  obtain ⟨u, hu, hi, he⟩ := exists_maximum_independentSet G s
  rw [← he]
  exact independent_card_le G t (Subset.trans hu h) hi

theorem roots_deleted_union {a b ra rb : Finset V} (hd : Disjoint a b)
    (ha : ra ⊆ a) (hb : rb ⊆ b) :
    (a ∪ b) \ (ra ∪ rb) = (a \ ra) ∪ (b \ rb) := by
  ext v
  simp only [mem_sdiff, mem_union, not_or]
  constructor
  · rintro ⟨hav | hbv, hnr, hns⟩
    · exact Or.inl ⟨hav, hnr⟩
    · exact Or.inr ⟨hbv, hns⟩
  · rintro (⟨hav, hnr⟩ | ⟨hbv, hns⟩)
    · exact ⟨Or.inl hav, hnr, fun h => disjoint_left.mp hd hav (hb h)⟩
    · exact ⟨Or.inr hbv, fun h => disjoint_left.mp hd (ha h) hbv, hns⟩

omit [DecidableEq V] in
theorem Separated.mono {a b s t : Finset V} (h : Separated G a b)
    (hs : s ⊆ a) (ht : t ⊆ b) : Separated G s t := fun u hu v hv => h u (hs hu) v (ht hv)

theorem compatibleVertices_root {s rs : Finset V} {r : V} (hr : r ∉ s)
    (he : ∀ v ∈ s, G.Adj r v ↔ v ∈ rs) :
    compatibleVertices G (insert r s) r = s \ rs := by
  ext v
  simp only [mem_compatibleVertices, mem_insert, mem_sdiff]
  constructor
  · rintro ⟨hne, hvr | hv, hna⟩
    · exact False.elim (hne hvr)
    · exact ⟨hv, fun h => hna ((he v hv).mpr h)⟩
  · rintro ⟨hv, hnr⟩
    exact ⟨fun h => hr (h ▸ hv), Or.inr hv, fun h => hnr ((he v hv).mp h)⟩

theorem ForestRealization.flag_semantics {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) :
    if flag A then independenceNumber G (s \ rs) < independenceNumber G s
    else independenceNumber G (s \ rs) = independenceNumber G s := by
  induction h with
  | empty => simp [flag]
  | @union a b ra rb A B hd he hA hB ihA ihB =>
    have hd' : Disjoint (a \ ra) (b \ rb) := hd.mono sdiff_subset sdiff_subset
    have he' := he.mono G (sdiff_subset (s := a) (t := ra)) (sdiff_subset (s := b) (t := rb))
    rw [roots_deleted_union hd (hA.roots_subset G) (hB.roots_subset G),
      independenceNumber_union G hd he, independenceNumber_union G hd' he']
    simp only [flag]
    by_cases hfA : flag A = true <;> by_cases hfB : flag B = true <;> simp_all ; omega
  | @root s rs A r hr he hA ih =>
    have hd : insert r s \ {r} = s := by rw [sdiff_singleton_eq_erase, erase_insert hr]
    have hrec := independenceNumber_recursion G (insert r s) r (mem_insert_self _ _)
    rw [erase_insert hr, compatibleVertices_root G hr he] at hrec
    rw [hd, hrec]
    simp only [flag]
    by_cases hf : flag A = true <;> simp_all ; omega

theorem ForestRealization.root_independenceNumber {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) {r : V} (hr : r ∉ s)
    (he : ∀ v ∈ s, G.Adj r v ↔ v ∈ rs) :
    independenceNumber G (insert r s) = independenceNumber G s + (if flag A then 0 else 1) := by
  have hf := h.flag_semantics G
  have hrec := independenceNumber_recursion G (insert r s) r (mem_insert_self _ _)
  rw [erase_insert hr, compatibleVertices_root G hr he] at hrec
  by_cases hh : flag A = true <;> simp_all ; omega

end TerminalLogConcavity
