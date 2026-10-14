import MainTheorems.Tuza.SteinerOperation
import MainTheorems.Tuza.RestrictedPacking

namespace ResearchMain.Tuza
namespace SteinerOperation

variable {V : Type*} [Fintype V] [DecidableEq V]

def restrictedGraph (S : SteinerOperation V) (p : V → Prop) : SimpleGraph {x // p x} where
  Adj x y := x ≠ y ∧ p (S.third x.val y.val)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa [S.comm y.val x.val] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

theorem exists_restricted_decomposition (S : SteinerOperation V) (p : V → Prop) :
    Nonempty (TriangleDecomposition (S.restrictedGraph p)) := by
  classical
  let R := S.blocks.filter (fun t => ∀ x ∈ t, p x)
  let T : R → Finset {x // p x} := fun t => t.val.subtype p
  have hmap (t : R) : (T t).map (Function.Embedding.subtype p) = t.val :=
    Finset.subtype_map_of_mem (Finset.mem_filter.mp t.property).2
  let F : PackingFamily (S.restrictedGraph p) R := {
    triangle := T
    clique := fun t => by
      have ht := S.blocks_packing.1 t.val (Finset.mem_filter.mp t.property).1
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        refine ⟨hxy, ?_⟩
        have hx' : x.val ∈ t.val := Finset.mem_subtype.mp hx
        have hy' : y.val ∈ t.val := Finset.mem_subtype.mp hy
        obtain ⟨a, b, _, hab⟩ := S.mem_blocks.mp (Finset.mem_filter.mp t.property).1
        have he : S.block x.val y.val = t.val := by
          rw [hab] at hx' hy' ⊢
          exact S.block_eq_of_pair hx' hy' (fun h => hxy (Subtype.ext h))
        apply (Finset.mem_filter.mp t.property).2 (S.third x.val y.val)
        rw [← he]
        simp [block]
      · have hc := congrArg Finset.card (hmap t)
        simpa using hc.trans ht.2
    disjoint := fun t u htu => by
      apply (Finset.disjoint_map (Function.Embedding.subtype p).sym2Map).mp
      rw [← triangleEdges_map, ← triangleEdges_map, hmap, hmap]
      exact S.blocks_packing.2 (Finset.mem_filter.mp t.property).1
        (Finset.mem_filter.mp u.property).1 (fun h => htu (Subtype.ext h)) }
  refine ⟨⟨F.carrier, F.packing, ?_⟩⟩
  intro z hz
  induction z using Sym2.inductionOn with
  | hf x y =>
    change x ≠ y ∧ p (S.third x.val y.val) at hz
    let t := S.block x.val y.val
    have ht : t ∈ R := by
      apply Finset.mem_filter.mpr
      refine ⟨S.mem_blocks.mpr ⟨x.val, y.val, (fun h => hz.1 (Subtype.ext h)), rfl⟩, ?_⟩
      intro a ha
      simp only [t, block, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact x.property
      · exact y.property
      · exact hz.2
    apply mem_packingEdges.mpr
    refine ⟨T ⟨t, ht⟩, ?_, mem_triangleEdges.mpr ⟨?_, ?_, hz.1⟩⟩
    · exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, rfl⟩
    · simp [T, t, block]
    · simp [T, t, block]

end SteinerOperation
end ResearchMain.Tuza
