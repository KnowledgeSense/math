import MainTheorems.Tuza.PrefixClique

namespace ResearchMain.Tuza.FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem prefix_near_packing_bound (x y : ℕ) (hxa : x ≤ a) (hyb : y ≤ b) :
    (completeCount (x + y) : ℝ) -
      ((prefixClique (a := a) (b := b) x y).edgeFinset \ d.graph.edgeFinset).card +
      fanCount x (a - x) + fanCount y (b - y) ≤ (packingNumber d.graph : ℝ) := by
  let X := (prefixEmbedding a x hxa).trans (Function.Embedding.inl (β := Fin b))
  let AL := (suffixEmbedding a x hxa).trans (Function.Embedding.inl (β := Fin b))
  let Y := (prefixEmbedding b y hyb).trans (Function.Embedding.inr (α := Fin a))
  let BL := (suffixEmbedding b y hyb).trans (Function.Embedding.inr (α := Fin a))
  let c : Fin a ⊕ Fin b → Fin 4 := Sum.elim (fun i => if i.val < x then 0 else 1)
    (fun j => if j.val < y then 2 else 3)
  have hX : ∀ i, c (X i) ∈ ({0} : Finset (Fin 4)) := by
    intro i
    change (if (prefixEmbedding a x hxa i).val < x then (0 : Fin 4) else 1) ∈ {0}
    rw [prefixEmbedding_val, ite_eq_left i.isLt]
    exact Finset.mem_singleton.mpr rfl
  have hAL : ∀ i, c (AL i) ∈ ({1} : Finset (Fin 4)) := by
    intro i
    change (if (suffixEmbedding a x hxa i).val < x then (0 : Fin 4) else 1) ∈ {1}
    rw [suffixEmbedding_val, ite_eq_right (by omega)]
    exact Finset.mem_singleton.mpr rfl
  have hY : ∀ i, c (Y i) ∈ ({2} : Finset (Fin 4)) := by
    intro i
    change (if (prefixEmbedding b y hyb i).val < y then (2 : Fin 4) else 3) ∈ {2}
    rw [prefixEmbedding_val, ite_eq_left i.isLt]
    exact Finset.mem_singleton.mpr rfl
  have hBL : ∀ i, c (BL i) ∈ ({3} : Finset (Fin 4)) := by
    intro i
    change (if (suffixEmbedding b y hyb i).val < y then (2 : Fin 4) else 3) ∈ {3}
    rw [suffixEmbedding_val, ite_eq_right (by omega)]
    exact Finset.mem_singleton.mpr rfl
  have hXY : ∀ i j, X i ≠ Y j := fun _ _ => Sum.inl_ne_inr
  let U := prefixUnionEmbedding x y hxa hyb
  have hU : ∀ i, c (U i) ∈ ({0, 2} : Finset (Fin 4)) := by
    change ∀ i, c (unionEmbedding X Y hXY i) ∈ ({0, 2} : Finset (Fin 4))
    simpa only [Finset.singleton_union] using unionEmbedding_color X Y hXY c {0} {2} hX hY
  have hXAL := color_disjoint_embeddings (by decide : Disjoint ({0} : Finset (Fin 4)) {1}) hX hAL
  have hYBL := color_disjoint_embeddings (by decide : Disjoint ({2} : Finset (Fin 4)) {3}) hY hBL
  obtain ⟨P, hP, hp, hsP⟩ := exists_region_near_clique_packing d.graph U c {0, 2} hU
  obtain ⟨Q, hQ, hq, hsQ⟩ := exists_region_fan_packing (G := d.graph) X AL hXAL
    (fun i j hh => hXAL i j (congrArg Sum.inl hh))
    (fun i j hij => (suffixEmbedding a x hxa).injective.ne hij) c {0} {1} hX hAL
  obtain ⟨S, hS, hs, hsS⟩ := exists_region_fan_packing (G := d.graph) Y BL hYBL
    (fun i j hh => hYBL i j (congrArg Sum.inr hh))
    (fun i j hij => (suffixEmbedding b y hyb).injective.ne hij) c {2} {3} hY hBL
  have hpq : Disjoint ({0, 2} : Finset (Fin 4)).sym2
      (({1} : Finset (Fin 4)).sym2 ∪ colorPairs {0} {1}) := by decide
  obtain ⟨P₁, hP₁, hc₁, hs₁⟩ := combine_region_packings hP hQ hsP hsQ hpq
  have hps : Disjoint (({0, 2} : Finset (Fin 4)).sym2 ∪
      (({1} : Finset (Fin 4)).sym2 ∪ colorPairs {0} {1}))
      (({3} : Finset (Fin 4)).sym2 ∪ colorPairs {2} {3}) := by decide
  obtain ⟨P₂, hP₂, hc₂, _⟩ := combine_region_packings hP₁ hS hs₁ hsS hps
  have hn : P₂.card ≤ packingNumber d.graph := packing_le_number hP₂
  rw [hc₂, hc₁, hq, hs] at hn
  have hem : missingCliqueEdges d.graph U =
      (prefixClique (a := a) (b := b) x y).edgeFinset \ d.graph.edgeFinset := by
    ext e
    change e ∈ (imageGraph (⊤ : SimpleGraph (Fin (x + y))) U).edgeFinset \ d.graph.edgeFinset ↔ _
    simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    rw [← prefixClique_eq_image x y hxa hyb]
  rw [hem] at hp
  have hp' : (completeCount (x + y) : ℝ) ≤ P.card +
      ((prefixClique (a := a) (b := b) x y).edgeFinset \ d.graph.edgeFinset).card := by
    exact_mod_cast hp
  have hn' : (P.card : ℝ) + fanCount x (a - x) + fanCount y (b - y) ≤ packingNumber d.graph := by
    exact_mod_cast hn
  linarith

theorem dense_near_bound (r t x y : ℕ) (hrx : r ≤ x) (hxa : x ≤ a)
    (hty : t ≤ y) (hyb : y ≤ b)
    (hxt : ∀ i : Fin a, i.val < x → t ≤ d.degree i)
    (hry : ∀ i : Fin a, i.val < r → y ≤ d.degree i)
    (hlow : ∀ i : Fin a, r ≤ i.val → d.degree i ≤ y)
    (hhigh : ∀ i : Fin a, t ≤ d.degree i → i.val < x) :
    (completeCount (x + y) : ℝ) - (x - r : ℕ) * (y - t : ℕ) + d.lowerCrossCount r t +
      fanCount x (a - x) + fanCount y (b - y) ≤ (packingNumber d.graph : ℝ) := by
  have hp := d.prefix_near_packing_bound x y hxa hyb
  have hd := d.rectangle_defect_bound r t x y hrx hxa hty hyb hxt hry hlow hhigh
  have hd' : (((prefixClique (a := a) (b := b) x y).edgeFinset \ d.graph.edgeFinset).card : ℝ) +
      d.lowerCrossCount r t ≤ (x - r : ℕ) * (y - t : ℕ) := by exact_mod_cast hd
  linarith

end ResearchMain.Tuza.FerrersProfile
