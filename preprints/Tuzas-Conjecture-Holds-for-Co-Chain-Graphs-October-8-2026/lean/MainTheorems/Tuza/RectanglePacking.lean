import MainTheorems.Tuza.CliqueUnion

namespace ResearchMain.Tuza

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure CliqueRectangle (G : SimpleGraph V) (p r k s : ℕ) where
  leftTop : Fin p ↪ V
  leftBottom : Fin r ↪ V
  rightTop : Fin k ↪ V
  rightBottom : Fin s ↪ V
  color : V → Fin 4
  color_leftTop : ∀ i, color (leftTop i) = 0
  color_leftBottom : ∀ i, color (leftBottom i) = 1
  color_rightTop : ∀ i, color (rightTop i) = 2
  color_rightBottom : ∀ i, color (rightBottom i) = 3
  clique_leftTop : ∀ i j, i ≠ j → G.Adj (leftTop i) (leftTop j)
  clique_leftBottom : ∀ i j, i ≠ j → G.Adj (leftBottom i) (leftBottom j)
  clique_rightTop : ∀ i j, i ≠ j → G.Adj (rightTop i) (rightTop j)
  clique_rightBottom : ∀ i j, i ≠ j → G.Adj (rightBottom i) (rightBottom j)
  cross_left : ∀ i j, G.Adj (leftTop i) (leftBottom j)
  cross_right : ∀ i j, G.Adj (rightTop i) (rightBottom j)
  cross_top : ∀ i j, G.Adj (leftTop i) (rightTop j)

namespace CliqueRectangle

variable {p r k s : ℕ} (R : CliqueRectangle G p r k s)

omit [DecidableEq V] in
theorem disjoint_left : ∀ i j, R.leftTop i ≠ R.leftBottom j := by
  intro i j
  apply color_ne (c := R.color)
  simp only [R.color_leftTop, R.color_leftBottom]
  decide

omit [DecidableEq V] in
theorem disjoint_right : ∀ i j, R.rightTop i ≠ R.rightBottom j := by
  intro i j
  apply color_ne (c := R.color)
  simp only [R.color_rightTop, R.color_rightBottom]
  decide

omit [DecidableEq V] in
theorem disjoint_top : ∀ i j, R.leftTop i ≠ R.rightTop j := by
  intro i j
  apply color_ne (c := R.color)
  simp only [R.color_leftTop, R.color_rightTop]
  decide

include R in
theorem packing_left_fans :
    ∃ P : Finset (Finset V), Packing G P ∧
      P.card = completeCount (p + r) + fanCount p k + fanCount k s := by
  let a := unionEmbedding R.leftTop R.leftBottom R.disjoint_left
  have ha : ∀ i j, i ≠ j → G.Adj (a i) (a j) :=
    unionEmbedding_clique _ _ _ R.clique_leftTop R.clique_leftBottom R.cross_left
  have hca : ∀ i, R.color (a i) ∈ ({0, 1} : Finset (Fin 4)) := by
    have h := unionEmbedding_color R.leftTop R.leftBottom R.disjoint_left
      R.color {0} {1}
      (fun i => by simp only [R.color_leftTop, Finset.mem_singleton])
      (fun i => by simp only [R.color_leftBottom, Finset.mem_singleton])
    simpa only [Finset.singleton_union] using h
  obtain ⟨P, hP, hp, hsP⟩ := exists_region_clique_packing a ha R.color {0, 1} hca
  obtain ⟨Q, hQ, hq, hsQ⟩ := exists_region_fan_packing R.leftTop R.rightTop
    R.disjoint_top R.cross_top R.clique_rightTop R.color {0} {2}
    (fun i => by simp only [R.color_leftTop, Finset.mem_singleton])
    (fun i => by simp only [R.color_rightTop, Finset.mem_singleton])
  obtain ⟨T, hT, ht, hsT⟩ := exists_region_fan_packing R.rightTop R.rightBottom
    R.disjoint_right R.cross_right R.clique_rightBottom R.color {2} {3}
    (fun i => by simp only [R.color_rightTop, Finset.mem_singleton])
    (fun i => by simp only [R.color_rightBottom, Finset.mem_singleton])
  have hpq : Disjoint ({0, 1} : Finset (Fin 4)).sym2
      (({2} : Finset (Fin 4)).sym2 ∪ colorPairs {0} {2}) := by decide
  obtain ⟨U, hU, hu, hsU⟩ := combine_region_packings hP hQ hsP hsQ hpq
  have hut : Disjoint (({0, 1} : Finset (Fin 4)).sym2 ∪
      (({2} : Finset (Fin 4)).sym2 ∪ colorPairs {0} {2}))
      (({3} : Finset (Fin 4)).sym2 ∪ colorPairs {2} {3}) := by decide
  obtain ⟨W, hW, hw, _⟩ := combine_region_packings hU hT hsU hsT hut
  exact ⟨W, hW, by rw [hw, hu, hp, hq, ht]⟩

include R in
theorem packing_top_fans :
    ∃ P : Finset (Finset V), Packing G P ∧
      P.card = completeCount (p + k) + fanCount p r + fanCount k s := by
  let a := unionEmbedding R.leftTop R.rightTop R.disjoint_top
  have ha : ∀ i j, i ≠ j → G.Adj (a i) (a j) :=
    unionEmbedding_clique _ _ _ R.clique_leftTop R.clique_rightTop R.cross_top
  have hca : ∀ i, R.color (a i) ∈ ({0, 2} : Finset (Fin 4)) := by
    have h := unionEmbedding_color R.leftTop R.rightTop R.disjoint_top
      R.color {0} {2}
      (fun i => by simp only [R.color_leftTop, Finset.mem_singleton])
      (fun i => by simp only [R.color_rightTop, Finset.mem_singleton])
    simpa only [Finset.singleton_union] using h
  obtain ⟨P, hP, hp, hsP⟩ := exists_region_clique_packing a ha R.color {0, 2} hca
  obtain ⟨Q, hQ, hq, hsQ⟩ := exists_region_fan_packing R.leftTop R.leftBottom
    R.disjoint_left R.cross_left R.clique_leftBottom R.color {0} {1}
    (fun i => by simp only [R.color_leftTop, Finset.mem_singleton])
    (fun i => by simp only [R.color_leftBottom, Finset.mem_singleton])
  obtain ⟨T, hT, ht, hsT⟩ := exists_region_fan_packing R.rightTop R.rightBottom
    R.disjoint_right R.cross_right R.clique_rightBottom R.color {2} {3}
    (fun i => by simp only [R.color_rightTop, Finset.mem_singleton])
    (fun i => by simp only [R.color_rightBottom, Finset.mem_singleton])
  have hpq : Disjoint ({0, 2} : Finset (Fin 4)).sym2
      (({1} : Finset (Fin 4)).sym2 ∪ colorPairs {0} {1}) := by decide
  obtain ⟨U, hU, hu, hsU⟩ := combine_region_packings hP hQ hsP hsQ hpq
  have hut : Disjoint (({0, 2} : Finset (Fin 4)).sym2 ∪
      (({1} : Finset (Fin 4)).sym2 ∪ colorPairs {0} {1}))
      (({3} : Finset (Fin 4)).sym2 ∪ colorPairs {2} {3}) := by decide
  obtain ⟨W, hW, hw, _⟩ := combine_region_packings hU hT hsU hsT hut
  exact ⟨W, hW, by rw [hw, hu, hp, hq, ht]⟩

end CliqueRectangle

end ResearchMain.Tuza
