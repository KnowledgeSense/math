import MeanMaximumForests.GraphSemantics
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace MeanMaximumForests
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Attaching a leaf preserves structural representability, with the old roots. -/
theorem ForestRealization.attach_leaf {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) {v l : V} (hv : v ∈ s) (hl : l ∉ s)
    (he : ∀ w ∈ s, G.Adj l w ↔ w = v) :
    ∃ B, ForestRealization G (insert l s) rs B := by
  induction h with
  | empty => simp at hv
  | @union a b ra rb A B hd hs hA hB ihA ihB =>
    have hla : l ∉ a := fun hm => hl (mem_union_left _ hm)
    have hlb : l ∉ b := fun hm => hl (mem_union_right _ hm)
    rcases mem_union.mp hv with hva | hvb
    · obtain ⟨A', hA'⟩ := ihA hva hla (fun w hw => he w (mem_union_left _ hw))
      have hd' : Disjoint (insert l a) b := disjoint_insert_left.mpr ⟨hlb, hd⟩
      have hs' : Separated G (insert l a) b := by
        intro u hu w hw
        rcases mem_insert.mp hu with rfl | hu
        · intro hadj
          have hwv := (he w (mem_union_right _ hw)).mp hadj
          exact disjoint_left.mp hd hva (hwv ▸ hw)
        · exact hs u hu w hw
      exact ⟨.union A' B, by simpa [insert_union] using ForestRealization.union hd' hs' hA' hB⟩
    · obtain ⟨B', hB'⟩ := ihB hvb hlb (fun w hw => he w (mem_union_right _ hw))
      have hd' : Disjoint a (insert l b) := disjoint_insert_right.mpr ⟨hla, hd⟩
      have hs' : Separated G a (insert l b) := by
        intro u hu w hw
        rcases mem_insert.mp hw with rfl | hw
        · intro hadj
          have huv := (he u (mem_union_left _ hu)).mp hadj.symm
          exact disjoint_left.mp hd (huv ▸ hu) hvb
        · exact hs u hu w hw
      exact ⟨.union A B', by simpa [union_insert] using ForestRealization.union hd' hs' hA hB'⟩
  | @root s rs A r hr hed hA ih =>
    have hls : l ∉ s := fun hm => hl (mem_insert_of_mem hm)
    have hlr : l ≠ r := fun hm => hl (hm ▸ mem_insert_self r s)
    by_cases hvr : v = r
    · subst v
      have hsingle : ForestRealization G {l} {l} (.root .empty) := by
        simpa using ForestRealization.root l (notMem_empty l) (by simp) (ForestRealization.empty (G := G))
      have hd : Disjoint s {l} := disjoint_singleton_right.mpr hls
      have hs : Separated G s {l} := by
        intro u hu w hw hadj
        have hwl : w = l := mem_singleton.mp hw
        subst w
        have hur := (he u (mem_insert_of_mem hu)).mp hadj.symm
        exact hr (hur ▸ hu)
      have hchild := ForestRealization.union hd hs hA hsingle
      have hr' : r ∉ s ∪ {l} := by simp [hr, Ne.symm hlr]
      have hed' : ∀ w ∈ s ∪ {l}, G.Adj r w ↔ w ∈ rs ∪ {l} := by
        intro w hw
        rcases mem_union.mp hw with hw | hw
        · have hwl : w ≠ l := fun hh => hls (hh ▸ hw)
          simpa [hwl] using hed w hw
        · have hwl : w = l := mem_singleton.mp hw
          subst w
          have hadj : G.Adj r l := ((he r (mem_insert_self _ _)).mpr rfl).symm
          simp [hadj]
      refine ⟨.root (.union A (.root .empty)), ?_⟩
      simpa [union_singleton, insert_comm] using ForestRealization.root r hr' hed' hchild
    · have hvs : v ∈ s := (mem_insert.mp hv).resolve_left hvr
      obtain ⟨B, hB⟩ := ih hvs hls (fun w hw => he w (mem_insert_of_mem hw))
      have hr' : r ∉ insert l s := by simp [hr, Ne.symm hlr]
      have hed' : ∀ w ∈ insert l s, G.Adj r w ↔ w ∈ rs := by
        intro w hw
        rcases mem_insert.mp hw with hwl | hw
        · subst w
          have hnr : l ∉ rs := fun hh => hls (hA.roots_subset G hh)
          have hna : ¬ G.Adj r l := fun hadj => hvr ((he r (mem_insert_self _ _)).mp hadj.symm).symm
          simp [hnr, hna]
        · exact hed w hw
      refine ⟨.root B, ?_⟩
      simpa [insert_comm] using ForestRealization.root r hr' hed' hB

/-- A finite acyclic graph has a vertex with at most one neighbor. -/
theorem exists_vertex_unique_neighbor [Finite V] [Nonempty V] (h : G.IsAcyclic) :
    ∃ r : V, ∀ u v : V, G.Adj r u → G.Adj r v → u = v := by
  classical
  obtain ⟨r, t, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hs : ∀ w, G.Adj r w → w ∈ p.support := by
    intro w hw
    by_contra hn
    have hp' := hp.cons (h := hw.symm) hn
    have hle := hmax w t (p.cons hw.symm) hp'
    simp only [SimpleGraph.Walk.length_cons] at hle
    omega
  exact ⟨r, fun u v hu hv => (h.eq_snd_of_adj_start hp hu (hs u hu)).trans
    (h.eq_snd_of_adj_start hp hv (hs v hv)).symm⟩

theorem exists_leaf_within (h : G.IsAcyclic) (s : Finset V) (hs : s.Nonempty) :
    ∃ r ∈ s, ∀ u ∈ s, ∀ v ∈ s, G.Adj r u → G.Adj r v → u = v := by
  classical
  let : Nonempty (↥(s : Set V)) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  obtain ⟨r, hr⟩ := exists_vertex_unique_neighbor (G.induce (s : Set V)) (h.induce _)
  refine ⟨r.val, r.property, fun u hu v hv hru hrv => ?_⟩
  exact congrArg Subtype.val (hr ⟨u, hu⟩ ⟨v, hv⟩ hru hrv)

/-- Every finite vertex subset of an acyclic simple graph has a rooted-forest expression. -/
theorem exists_forestRealization (h : G.IsAcyclic) (s : Finset V) :
    ∃ rs A, ForestRealization G s rs A := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s.Nonempty
  · obtain ⟨r, hr, huniq⟩ := exists_leaf_within G h s hs
    obtain ⟨rs, A, hA⟩ := ih (s.erase r) (erase_ssubset hr)
    by_cases hn : ∃ v ∈ s.erase r, G.Adj r v
    · obtain ⟨v, hv, hadj⟩ := hn
      have he : ∀ w ∈ s.erase r, G.Adj r w ↔ w = v := by
        intro w hw
        constructor
        · exact fun hwr => huniq w (mem_of_mem_erase hw) v (mem_of_mem_erase hv) hwr hadj
        · rintro rfl
          exact hadj
      obtain ⟨B, hB⟩ := hA.attach_leaf G hv (notMem_erase r s) he
      exact ⟨rs, B, by simpa [insert_erase hr] using hB⟩
    · have hsng : ForestRealization G {r} {r} (.root .empty) := by
        simpa using ForestRealization.root r (notMem_empty r) (by simp) (ForestRealization.empty (G := G))
      have hd : Disjoint (s.erase r) {r} := disjoint_singleton_right.mpr (notMem_erase _ _)
      have he : Separated G (s.erase r) {r} := by
        intro u hu v hv hadj
        have hvr : v = r := mem_singleton.mp hv
        subst v
        exact hn ⟨u, hu, hadj.symm⟩
      refine ⟨rs ∪ {r}, .union A (.root .empty), ?_⟩
      simpa [union_singleton, insert_erase hr] using ForestRealization.union hd he hA hsng
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    subst s
    exact ⟨∅, .empty, .empty⟩

/-- The invariant-cone criterion applied to every finite forest. -/
theorem finite_forest_mean_bound {c : ℝ} {C : Bool → Set ConeVector}
    (hc : InvariantConditions c C) (hG : G.IsAcyclic) (s : Finset V) :
    c * independenceNumber G s ≤ meanIndependentSetSize G s := by
  obtain ⟨rs, A, hA⟩ := exists_forestRealization G hG s
  exact hA.mean_bound G hc

end MeanMaximumForests
