import MainTheorems.Tuza.SplitClique

namespace ResearchMain.Tuza

theorem prefix_filter_card (n p : ℕ) (hp : p ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < p)).card = p := by
  rw [← Fintype.card_subtype, Fintype.card_congr (prefixEquiv n p hp), Fintype.card_fin]

theorem prefix_rectangle_card (a b p q : ℕ) (hp : p ≤ a) (hq : q ≤ b) :
    (Finset.univ.filter (fun v : Fin a × Fin b => v.1.val < p ∧ v.2.val < q)).card = p * q := by
  have he : Finset.univ.filter (fun v : Fin a × Fin b => v.1.val < p ∧ v.2.val < q) =
      (Finset.univ.filter (fun i : Fin a => i.val < p)).product
        (Finset.univ.filter (fun j : Fin b => j.val < q)) := by
    ext v
    simp
  rw [he, Finset.product_eq_sprod, Finset.card_product,
    prefix_filter_card a p hp, prefix_filter_card b q hq]

def sparseCross (a b r t x y : ℕ) (i : Fin a) (j : Fin b) : Prop :=
  (i.val < x ∧ j.val < t) ∨ (i.val < r ∧ j.val < y)

instance (a b r t x y : ℕ) : DecidableRel (sparseCross a b r t x y) := by
  unfold sparseCross
  infer_instance

theorem sparseCross_card (a b r t x y : ℕ) (hxr : x ≤ r) (hra : r ≤ a)
    (hyt : y ≤ t) (htb : t ≤ b) :
    (crossRelationGraph (sparseCross a b r t x y)).edgeFinset.card =
      x * t + (r - x) * y := by
  let U := Finset.univ.filter (fun i : Fin a => i.val < x)
  let W := Finset.univ.filter (fun i : Fin a => i.val < r)
  let T := Finset.univ.filter (fun j : Fin b => j.val < t)
  let Y := Finset.univ.filter (fun j : Fin b => j.val < y)
  have huv : U ⊆ W := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hxr⟩
  have hcard : (W \ U).card = r - x := by
    rw [Finset.card_sdiff_of_subset huv, prefix_filter_card a r hra, prefix_filter_card a x (hxr.trans hra)]
  have hd : Disjoint (U.product T) ((W \ U).product Y) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hv').1).2 (Finset.mem_product.mp hv).1
  have he : Finset.univ.filter (fun v : Fin a × Fin b => sparseCross a b r t x y v.1 v.2) =
      U.product T ∪ (W \ U).product Y := by
    ext v
    rw [Finset.mem_filter]
    dsimp only [U, W, T, Y]
    simp only [sparseCross, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union, Finset.mem_product, Finset.mem_sdiff]
    omega
  rw [crossRelationGraph_card, he, Finset.card_union_of_disjoint hd,
    Finset.product_eq_sprod, Finset.product_eq_sprod, Finset.card_product, Finset.card_product, hcard,
    prefix_filter_card a x (hxr.trans hra), prefix_filter_card b t htb,
    prefix_filter_card b y (hyt.trans htb)]

end ResearchMain.Tuza
