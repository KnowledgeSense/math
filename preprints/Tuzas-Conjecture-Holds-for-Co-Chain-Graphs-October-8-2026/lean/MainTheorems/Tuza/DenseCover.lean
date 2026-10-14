import MainTheorems.Tuza.MonochromeGraph
import MainTheorems.Tuza.CrossRectangles
import MainTheorems.Tuza.MedianCuts

namespace ResearchMain.Tuza.FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

def cutColor (r t : ℕ) : Fin a ⊕ Fin b → Bool :=
  Sum.elim (fun i => decide (i.val < r)) (fun j => decide (j.val < t))

def cutCross (r t : ℕ) (i : Fin a) (j : Fin b) : Prop :=
  j.val < d.degree i ∧ (i.val < r ↔ j.val < t)

instance (r t : ℕ) : DecidableRel (d.cutCross r t) := by
  unfold cutCross
  infer_instance

def lowerCrossCount (r t : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : Fin a × Fin b =>
    v.2.val < d.degree v.1 ∧ r ≤ v.1.val ∧ t ≤ v.2.val)).card

theorem cutGraph_eq (r t : ℕ) :
    monochromeGraph d.graph (cutColor r t) =
      sumInternalGraph (splitClique a r) (splitClique b t) ⊔
        crossRelationGraph (d.cutCross r t) := by
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl j => simp [monochromeGraph, cutColor, crossRelationGraph]
    | inr j => simp [monochromeGraph, cutColor, crossRelationGraph, cutCross]
  | inr j =>
    cases v with
    | inl i => simp [monochromeGraph, cutColor, crossRelationGraph, cutCross, graph, iff_comm]
    | inr i => simp [monochromeGraph, cutColor, crossRelationGraph]

theorem cutCross_card (r t : ℕ) (hra : r ≤ a) (htb : t ≤ b)
    (hcomplete : ∀ i : Fin a, i.val < r → t ≤ d.degree i) :
    (crossRelationGraph (d.cutCross r t)).edgeFinset.card = r * t + d.lowerCrossCount r t := by
  let U := Finset.univ.filter (fun v : Fin a × Fin b => v.1.val < r ∧ v.2.val < t)
  let W := Finset.univ.filter (fun v : Fin a × Fin b =>
    v.2.val < d.degree v.1 ∧ r ≤ v.1.val ∧ t ≤ v.2.val)
  have hd : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact Nat.not_lt_of_ge (Finset.mem_filter.mp hv').2.2.1 (Finset.mem_filter.mp hv).2.1
  have he : Finset.univ.filter (fun v : Fin a × Fin b => d.cutCross r t v.1 v.2) = U ∪ W := by
    ext v
    rw [Finset.mem_filter]
    dsimp only [U, W]
    simp only [Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_filter]
    change (v.2.val < d.degree v.1 ∧ (v.1.val < r ↔ v.2.val < t)) ↔
      (v.1.val < r ∧ v.2.val < t) ∨
        (v.2.val < d.degree v.1 ∧ r ≤ v.1.val ∧ t ≤ v.2.val)
    have hi := hcomplete v.1
    omega
  rw [crossRelationGraph_card, he, Finset.card_union_of_disjoint hd,
    prefix_rectangle_card a b r t hra htb]
  rfl

theorem dense_cover_bound (r t : ℕ) (hra : r ≤ a) (htb : t ≤ b)
    (hcomplete : ∀ i : Fin a, i.val < r → t ≤ d.degree i) :
    coverNumber d.graph ≤ r.choose 2 + (a - r).choose 2 +
      t.choose 2 + (b - t).choose 2 + r * t + d.lowerCrossCount r t := by
  have he : (monochromeGraph d.graph (cutColor r t)).edgeFinset =
      (sumInternalGraph (splitClique a r) (splitClique b t) ⊔
        crossRelationGraph (d.cutCross r t)).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [cutGraph_eq]
  have hc := number_le_cover (monochromeGraph_covers d.graph (cutColor r t))
  rw [he, sumInternal_cross_card, splitClique_card a r hra, splitClique_card b t htb,
    d.cutCross_card r t hra htb hcomplete] at hc
  omega

theorem median_dense_cover (hd : halfUp a ≤ d.height (halfUp b)) :
    coverNumber d.graph ≤
      (halfUp a).choose 2 + (a - halfUp a).choose 2 +
      (halfUp b).choose 2 + (b - halfUp b).choose 2 +
      halfUp a * halfUp b + d.lowerCrossCount (halfUp a) (halfUp b) := by
  apply d.dense_cover_bound _ _ (halfUp_le a) (halfUp_le b)
  intro i hi
  exact (d.lt_height_iff (halfUp b) i).mp (lt_of_lt_of_le hi hd)

end ResearchMain.Tuza.FerrersProfile
