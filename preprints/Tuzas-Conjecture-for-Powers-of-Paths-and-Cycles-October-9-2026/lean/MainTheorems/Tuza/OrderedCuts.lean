import MainTheorems.Tuza.DenseCover
import MainTheorems.Tuza.IntervalRectangles

namespace ResearchMain.Tuza.FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

def orderedColor (r t : ℕ) (flip : Bool) : Fin a ⊕ Fin b → Bool :=
  Sum.elim (fun i => decide (i.val < r)) (fun j => (decide (j.val < t)) ^^ flip)

def orderedCross (r t : ℕ) (flip : Bool) (i : Fin a) (j : Fin b) : Prop :=
  j.val < d.degree i ∧ decide (i.val < r) = ((decide (j.val < t)) ^^ flip)

instance (r t : ℕ) (flip : Bool) : DecidableRel (d.orderedCross r t flip) := by
  unfold orderedCross
  infer_instance

def orderedCutCount (r t : ℕ) (flip : Bool) : ℕ :=
  r.choose 2 + (a - r).choose 2 + t.choose 2 + (b - t).choose 2 +
    ∑ i : Fin a, if (decide (i.val < r)) != flip then min (d.degree i) t else d.degree i - t

theorem orderedGraph_eq (r t : ℕ) (flip : Bool) :
    monochromeGraph d.graph (orderedColor r t flip) =
      sumInternalGraph (splitClique a r) (splitClique b t) ⊔
        crossRelationGraph (d.orderedCross r t flip) := by
  ext u v
  cases u <;> cases v <;> cases flip <;>
    simp [monochromeGraph, orderedColor, orderedCross, crossRelationGraph, graph,
      iff_comm]
  simp [Bool.eq_not_iff, iff_comm]

theorem cross_prefix_card (i : Fin a) (t : ℕ) :
    (Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ j.val < t)).card =
      min (d.degree i) t := by
  have he : Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ j.val < t) =
      Finset.univ.filter (fun j : Fin b => j.val < min (d.degree i) t) := by
    ext j
    simp [lt_min_iff]
  rw [he, prefix_filter_card b _ ((min_le_left _ _).trans (d.bound i))]

theorem cross_suffix_card (i : Fin a) (t : ℕ) :
    (Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ t ≤ j.val)).card =
      d.degree i - t := by
  by_cases h : t ≤ d.degree i
  · have he : Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ t ≤ j.val) =
        Finset.univ.filter (fun j : Fin b => t ≤ j.val ∧ j.val < d.degree i) := by
      ext j
      simp [and_comm]
    rw [he, interval_filter_card b t (d.degree i) h (d.bound i)]
  · have he : Finset.univ.filter (fun j : Fin b => j.val < d.degree i ∧ t ≤ j.val) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [he, Finset.card_empty, Nat.sub_eq_zero_of_le (by omega)]

theorem orderedCross_card (r t : ℕ) (flip : Bool) :
    (crossRelationGraph (d.orderedCross r t flip)).edgeFinset.card =
      ∑ i : Fin a, if (decide (i.val < r)) != flip then min (d.degree i) t else d.degree i - t := by
  rw [crossRelationGraph_card]
  have he : (Finset.univ.filter (fun v : Fin a × Fin b => d.orderedCross r t flip v.1 v.2)).card =
      ∑ i : Fin a, (Finset.univ.filter (fun j : Fin b => d.orderedCross r t flip i j)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r <;> cases flip
  · simpa [orderedCross, hi, eq_comm] using d.cross_prefix_card i t
  · simpa [orderedCross, hi, eq_comm, Bool.eq_not_iff] using d.cross_suffix_card i t
  · simpa [orderedCross, hi, eq_comm] using d.cross_suffix_card i t
  · simpa [orderedCross, hi, eq_comm, Bool.eq_not_iff] using d.cross_prefix_card i t

theorem ordered_cut_bound (r t : ℕ) (flip : Bool) (hra : r ≤ a) (htb : t ≤ b) :
    coverNumber d.graph ≤ d.orderedCutCount r t flip := by
  have he : (monochromeGraph d.graph (orderedColor r t flip)).edgeFinset =
      (sumInternalGraph (splitClique a r) (splitClique b t) ⊔
        crossRelationGraph (d.orderedCross r t flip)).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [orderedGraph_eq]
  have hc := number_le_cover (monochromeGraph_covers d.graph (orderedColor r t flip))
  rw [he, sumInternal_cross_card, splitClique_card a r hra, splitClique_card b t htb,
    d.orderedCross_card r t flip] at hc
  simpa only [orderedCutCount, Nat.add_assoc] using hc

end ResearchMain.Tuza.FerrersProfile
