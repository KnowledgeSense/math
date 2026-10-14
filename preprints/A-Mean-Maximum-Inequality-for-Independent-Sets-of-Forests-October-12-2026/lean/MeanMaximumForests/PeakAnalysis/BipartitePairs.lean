import MeanMaximumForests.PeakAnalysis.PartitionDeletion
import Mathlib.Data.Finset.Powerset

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def availableIn (G : SimpleGraph V) (L r : Finset V) : Finset V :=
  L.filter (fun v => ∀ u ∈ r, ¬ G.Adj v u)

@[simp] theorem mem_availableIn (G : SimpleGraph V) (L r : Finset V) (v : V) :
    v ∈ availableIn G L r ↔ v ∈ L ∧ ∀ u ∈ r, ¬ G.Adj v u := mem_filter

theorem availableIn_subset (G : SimpleGraph V) (L r : Finset V) : availableIn G L r ⊆ L :=
  filter_subset _ _

theorem bipartite_pair_independent (G : SimpleGraph V) (L R r l : Finset V)
    (hL : Independent G L) (hR : Independent G R)
    (hr : r ⊆ R) (hl : l ⊆ availableIn G L r) : Independent G (r ∪ l) := by
  intro u hu v hv
  rcases mem_union.mp hu with hu | hu <;> rcases mem_union.mp hv with hv | hv
  · exact hR u (hr hu) v (hr hv)
  · have h := (mem_availableIn G L r v).mp (hl hv)
    exact fun hadj => h.2 u hu hadj.symm
  · exact ((mem_availableIn G L r u).mp (hl hu)).2 v hv
  · exact hL u ((availableIn_subset G L r) (hl hu)) v ((availableIn_subset G L r) (hl hv))

noncomputable def independentBipartiteEquiv (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ) :
    {I : Finset V // Independent G I} ≃
      {p : Finset V × Finset V // p.1 ⊆ R ∧ p.2 ⊆ availableIn G L p.1} where
  toFun I := ⟨(I.val ∩ R, I.val ∩ L), inter_subset_right, by
    intro v hv
    obtain ⟨hvI, hvL⟩ := mem_inter.mp hv
    apply (mem_availableIn G L (I.val ∩ R) v).mpr
    refine ⟨hvL, ?_⟩
    intro u hu
    exact I.property v hvI u (mem_inter.mp hu).1⟩
  invFun p := ⟨p.val.1 ∪ p.val.2,
    bipartite_pair_independent G L R p.val.1 p.val.2 hL hR p.property.1 p.property.2⟩
  left_inv I := by
    apply Subtype.ext
    change (I.val ∩ R) ∪ (I.val ∩ L) = I.val
    rw [← inter_union_distrib_left, union_comm R L, hc, inter_univ]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · ext v
      simp only [mem_inter, mem_union]
      have hlsub := (p.property.2).trans (availableIn_subset G L p.val.1)
      have hdisj := disjoint_left.mp hd
      constructor
      · rintro ⟨hv | hv, hvR⟩
        · exact hv
        · exact False.elim (hdisj (hlsub hv) hvR)
      · intro hv
        exact ⟨Or.inl hv, p.property.1 hv⟩
    · ext v
      simp only [mem_inter, mem_union]
      have hlsub := (p.property.2).trans (availableIn_subset G L p.val.1)
      have hdisj := disjoint_left.mp hd
      constructor
      · rintro ⟨hv | hv, hvL⟩
        · exact False.elim (hdisj hvL (p.property.1 hv))
        · exact hv
      · intro hv
        exact ⟨Or.inr hv, hlsub hv⟩

end MeanMaximumForests.PeakAnalysis
