import MainTheorems.Tuza.CrossRectangles

namespace ResearchMain.Tuza

theorem interval_filter_card (n p q : ℕ) (hpq : p ≤ q) (hqn : q ≤ n) :
    (Finset.univ.filter (fun i : Fin n => p ≤ i.val ∧ i.val < q)).card = q - p := by
  have hs : Finset.univ.filter (fun i : Fin n => i.val < p) ⊆
      Finset.univ.filter (fun i : Fin n => i.val < q) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hpq⟩
  have he : Finset.univ.filter (fun i : Fin n => p ≤ i.val ∧ i.val < q) =
      Finset.univ.filter (fun i : Fin n => i.val < q) \
        Finset.univ.filter (fun i : Fin n => i.val < p) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  rw [he, Finset.card_sdiff_of_subset hs,
    prefix_filter_card n q hqn, prefix_filter_card n p (hpq.trans hqn)]

def intervalRectangle (a b r t x y : ℕ) (i : Fin a) (j : Fin b) : Prop :=
  r ≤ i.val ∧ i.val < x ∧ t ≤ j.val ∧ j.val < y

instance (a b r t x y : ℕ) : DecidableRel (intervalRectangle a b r t x y) := by
  unfold intervalRectangle
  infer_instance

theorem intervalRectangle_card (a b r t x y : ℕ) (hrx : r ≤ x) (hxa : x ≤ a)
    (hty : t ≤ y) (hyb : y ≤ b) :
    (crossRelationGraph (intervalRectangle a b r t x y)).edgeFinset.card = (x - r) * (y - t) := by
  have he : Finset.univ.filter (fun v : Fin a × Fin b => intervalRectangle a b r t x y v.1 v.2) =
      (Finset.univ.filter (fun i : Fin a => r ≤ i.val ∧ i.val < x)).product
        (Finset.univ.filter (fun j : Fin b => t ≤ j.val ∧ j.val < y)) := by
    ext v
    rw [Finset.mem_filter]
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact and_assoc.symm
  rw [crossRelationGraph_card, he, Finset.product_eq_sprod, Finset.card_product,
    interval_filter_card a r x hrx hxa, interval_filter_card b t y hty hyb]

end ResearchMain.Tuza
