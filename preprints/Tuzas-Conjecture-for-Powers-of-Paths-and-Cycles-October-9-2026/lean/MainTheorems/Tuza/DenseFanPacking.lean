import MainTheorems.Tuza.IntervalBlocks

namespace ResearchMain.Tuza.FerrersProfile

variable {a b r t x y : ℕ} (d : FerrersProfile a b)

theorem dense_fan_bound (hrx : r ≤ x) (hxa : x ≤ a) (hty : t ≤ y) (hyb : y ≤ b)
    (hxt : ∀ i : Fin a, i.val < x → t ≤ d.degree i)
    (hry : ∀ i : Fin a, i.val < r → y ≤ d.degree i) :
    fanCount x t + fanCount (y - t) r + fanCount r (a - r) +
      fanCount t (b - t) ≤ packingNumber d.graph := by
  let X := (prefixEmbedding a x hxa).trans (Function.Embedding.inl (β := Fin b))
  let AH := (prefixEmbedding a r (hrx.trans hxa)).trans (Function.Embedding.inl (β := Fin b))
  let AL := (suffixEmbedding a r (hrx.trans hxa)).trans (Function.Embedding.inl (β := Fin b))
  let Z := (middleEmbedding b t y hty hyb).trans (Function.Embedding.inr (α := Fin a))
  let BH := (prefixEmbedding b t (hty.trans hyb)).trans (Function.Embedding.inr (α := Fin a))
  let BL := (suffixEmbedding b t (hty.trans hyb)).trans (Function.Embedding.inr (α := Fin a))
  let c := sixCutColor a b x y r t
  have hX : ∀ i, c (X i) ∈ ({0, 1} : Finset (Fin 6)) :=
    fun i => sixCutColor_left_prefix _ i.isLt
  have hAH : ∀ i, c (AH i) ∈ ({0} : Finset (Fin 6)) := by
    intro i
    apply Finset.mem_singleton.mpr
    exact sixCutColor_left_first _ i.isLt
  have hAL : ∀ i, c (AL i) ∈ ({1, 2} : Finset (Fin 6)) := by
    intro i
    apply sixCutColor_left_suffix
    simp only [suffixEmbedding_val]
    omega
  have hZ : ∀ i, c (Z i) ∈ ({4} : Finset (Fin 6)) := by
    intro i
    apply Finset.mem_singleton.mpr
    apply sixCutColor_right_middle
    · simp only [middleEmbedding_val]; omega
    · change t + i.val < y; have := i.isLt; omega
  have hBH : ∀ i, c (BH i) ∈ ({3} : Finset (Fin 6)) := by
    intro i
    apply Finset.mem_singleton.mpr
    exact sixCutColor_right_first _ i.isLt
  have hBL : ∀ i, c (BL i) ∈ ({4, 5} : Finset (Fin 6)) := by
    intro i
    apply sixCutColor_right_suffix
    simp only [suffixEmbedding_val]
    omega
  have hXB := color_disjoint_embeddings (by decide : Disjoint ({0, 1} : Finset (Fin 6)) {3}) hX hBH
  have hZA := color_disjoint_embeddings (by decide : Disjoint ({4} : Finset (Fin 6)) {0}) hZ hAH
  have hAHL := color_disjoint_embeddings (by decide : Disjoint ({0} : Finset (Fin 6)) {1, 2}) hAH hAL
  have hBHL := color_disjoint_embeddings (by decide : Disjoint ({3} : Finset (Fin 6)) {4, 5}) hBH hBL
  obtain ⟨P, hP, hp, hsP⟩ := exists_region_fan_packing (G := d.graph) X BH hXB
    (fun i j => lt_of_lt_of_le j.isLt (hxt _ i.isLt))
    (fun i j hij => (prefixEmbedding b t (hty.trans hyb)).injective.ne hij)
    c {0, 1} {3} hX hBH
  have hZAadj : ∀ i j, d.graph.Adj (Z i) (AH j) := by
    intro i j
    change (middleEmbedding b t y hty hyb i).val < d.degree (prefixEmbedding a r (hrx.trans hxa) j)
    apply lt_of_lt_of_le (b := y) _ (hry _ j.isLt)
    change t + i.val < y
    have := i.isLt
    omega
  obtain ⟨Q, hQ, hq, hsQ⟩ := exists_region_fan_packing (G := d.graph) Z AH hZA hZAadj
    (fun i j hij => (prefixEmbedding a r (hrx.trans hxa)).injective.ne hij) c {4} {0} hZ hAH
  obtain ⟨S, hS, hs, hsS⟩ := exists_region_fan_packing (G := d.graph) AH AL hAHL
    (fun i j hh => hAHL i j (congrArg Sum.inl hh))
    (fun i j hij => (suffixEmbedding a r (hrx.trans hxa)).injective.ne hij)
    c {0} {1, 2} hAH hAL
  obtain ⟨T, hT, ht, hsT⟩ := exists_region_fan_packing (G := d.graph) BH BL hBHL
    (fun i j hh => hBHL i j (congrArg Sum.inr hh))
    (fun i j hij => (suffixEmbedding b t (hty.trans hyb)).injective.ne hij)
    c {3} {4, 5} hBH hBL
  have hpq : Disjoint (({3} : Finset (Fin 6)).sym2 ∪ colorPairs {0, 1} {3})
      (({0} : Finset (Fin 6)).sym2 ∪ colorPairs {4} {0}) := by decide
  obtain ⟨P₁, hP₁, hc₁, hs₁⟩ := combine_region_packings hP hQ hsP hsQ hpq
  have hps : Disjoint ((({3} : Finset (Fin 6)).sym2 ∪ colorPairs {0, 1} {3}) ∪
      (({0} : Finset (Fin 6)).sym2 ∪ colorPairs {4} {0}))
      (({1, 2} : Finset (Fin 6)).sym2 ∪ colorPairs {0} {1, 2}) := by decide
  obtain ⟨P₂, hP₂, hc₂, hs₂⟩ := combine_region_packings hP₁ hS hs₁ hsS hps
  have hpt : Disjoint (((({3} : Finset (Fin 6)).sym2 ∪ colorPairs {0, 1} {3}) ∪
      (({0} : Finset (Fin 6)).sym2 ∪ colorPairs {4} {0})) ∪
      (({1, 2} : Finset (Fin 6)).sym2 ∪ colorPairs {0} {1, 2}))
      (({4, 5} : Finset (Fin 6)).sym2 ∪ colorPairs {3} {4, 5}) := by decide
  obtain ⟨P₃, hP₃, hc₃, _⟩ := combine_region_packings hP₂ hT hs₂ hsT hpt
  have hcard : P₃.card = fanCount x t + fanCount (y - t) r +
      fanCount r (a - r) + fanCount t (b - t) := by rw [hc₃, hc₂, hc₁, hp, hq, hs, ht]
  exact hcard ▸ packing_le_number hP₃

end ResearchMain.Tuza.FerrersProfile
