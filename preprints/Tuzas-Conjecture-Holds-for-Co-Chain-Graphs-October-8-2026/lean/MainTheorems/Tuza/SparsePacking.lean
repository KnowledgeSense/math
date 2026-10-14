import MainTheorems.Tuza.IntervalBlocks

namespace ResearchMain.Tuza.FerrersProfile

variable {a b r t x y : ℕ} (d : FerrersProfile a b)

theorem sparse_packing_bound (hxr : x ≤ r) (hra : r ≤ a) (hyt : y ≤ t) (htb : t ≤ b)
    (hxt : ∀ i : Fin a, i.val < x → t ≤ d.degree i)
    (hry : ∀ i : Fin a, i.val < r → y ≤ d.degree i) :
    completeCount (x + t) + fanCount (x + y) (r - x) +
      fanCount r (a - r) + fanCount t (b - t) ≤ packingNumber d.graph := by
  let X := (prefixEmbedding a x (hxr.trans hra)).trans (Function.Embedding.inl (β := Fin b))
  let M := (middleEmbedding a x r hxr hra).trans (Function.Embedding.inl (β := Fin b))
  let AH := (prefixEmbedding a r hra).trans (Function.Embedding.inl (β := Fin b))
  let AL := (suffixEmbedding a r hra).trans (Function.Embedding.inl (β := Fin b))
  let Y := (prefixEmbedding b y (hyt.trans htb)).trans (Function.Embedding.inr (α := Fin a))
  let BH := (prefixEmbedding b t htb).trans (Function.Embedding.inr (α := Fin a))
  let BL := (suffixEmbedding b t htb).trans (Function.Embedding.inr (α := Fin a))
  let c := sixCutColor a b r t x y
  have hX : ∀ i, c (X i) ∈ ({0} : Finset (Fin 6)) := by
    intro i
    apply Finset.mem_singleton.mpr
    exact sixCutColor_left_first _ i.isLt
  have hM : ∀ i, c (M i) ∈ ({1} : Finset (Fin 6)) := by
    intro i
    apply Finset.mem_singleton.mpr
    apply sixCutColor_left_middle
    · simp only [middleEmbedding_val]; omega
    · change x + i.val < r; have := i.isLt; omega
  have hAH : ∀ i, c (AH i) ∈ ({0, 1} : Finset (Fin 6)) :=
    fun i => sixCutColor_left_prefix _ i.isLt
  have hAL : ∀ i, c (AL i) ∈ ({2} : Finset (Fin 6)) := by
    intro i
    apply Finset.mem_singleton.mpr
    apply sixCutColor_left_last hxr
    simp only [suffixEmbedding_val]
    omega
  have hY : ∀ i, c (Y i) ∈ ({3} : Finset (Fin 6)) := by
    intro i
    apply Finset.mem_singleton.mpr
    exact sixCutColor_right_first _ i.isLt
  have hBH : ∀ i, c (BH i) ∈ ({3, 4} : Finset (Fin 6)) :=
    fun i => sixCutColor_right_prefix _ i.isLt
  have hBL : ∀ i, c (BL i) ∈ ({5} : Finset (Fin 6)) := by
    intro i
    apply Finset.mem_singleton.mpr
    apply sixCutColor_right_last hyt
    simp only [suffixEmbedding_val]
    omega
  have hXM := color_disjoint_embeddings (by decide : Disjoint ({0} : Finset (Fin 6)) {1}) hX hM
  have hXB := color_disjoint_embeddings (by decide : Disjoint ({0} : Finset (Fin 6)) {3, 4}) hX hBH
  have hXY := color_disjoint_embeddings (by decide : Disjoint ({0} : Finset (Fin 6)) {3}) hX hY
  let U := unionEmbedding X BH hXB
  let C := unionEmbedding X Y hXY
  have hU : ∀ i j, i ≠ j → d.graph.Adj (U i) (U j) := by
    apply unionEmbedding_clique
    · intro i j hij; exact (prefixEmbedding a x (hxr.trans hra)).injective.ne hij
    · intro i j hij; exact (prefixEmbedding b t htb).injective.ne hij
    · intro i j; exact lt_of_lt_of_le j.isLt (hxt _ i.isLt)
  have hCu : ∀ i, c (U i) ∈ ({0, 3, 4} : Finset (Fin 6)) := by
    simpa only [Finset.singleton_union] using unionEmbedding_color X BH hXB c {0} {3, 4} hX hBH
  have hCc : ∀ i, c (C i) ∈ ({0, 3} : Finset (Fin 6)) := by
    simpa only [Finset.singleton_union] using unionEmbedding_color X Y hXY c {0} {3} hX hY
  have hCM := color_disjoint_embeddings (by decide : Disjoint ({0, 3} : Finset (Fin 6)) {1}) hCc hM
  have hCMadj : ∀ i j, d.graph.Adj (C i) (M j) := by
    apply unionEmbedding_cross
    · intro i j hh; exact hXM i j (congrArg Sum.inl hh)
    · intro i j
      change (prefixEmbedding b y (hyt.trans htb) i).val <
        d.degree (middleEmbedding a x r hxr hra j)
      apply lt_of_lt_of_le i.isLt (hry _ ?_)
      change x + j.val < r
      have := j.isLt
      omega
  have hMcl : ∀ i j, i ≠ j → d.graph.Adj (M i) (M j) :=
    fun i j hij => (middleEmbedding a x r hxr hra).injective.ne hij
  have hAHL := color_disjoint_embeddings (by decide : Disjoint ({0, 1} : Finset (Fin 6)) {2}) hAH hAL
  have hBHL := color_disjoint_embeddings (by decide : Disjoint ({3, 4} : Finset (Fin 6)) {5}) hBH hBL
  obtain ⟨P, hP, hp, hsP⟩ := exists_region_clique_packing U hU c {0, 3, 4} hCu
  obtain ⟨Q, hQ, hq, hsQ⟩ := exists_region_fan_packing C M hCM hCMadj hMcl c {0, 3} {1} hCc hM
  obtain ⟨S, hS, hs, hsS⟩ := exists_region_fan_packing (G := d.graph) AH AL hAHL
    (fun i j hh => hAHL i j (congrArg Sum.inl hh))
    (fun i j hij => (suffixEmbedding a r hra).injective.ne hij) c {0, 1} {2} hAH hAL
  obtain ⟨T, hT, ht, hsT⟩ := exists_region_fan_packing (G := d.graph) BH BL hBHL
    (fun i j hh => hBHL i j (congrArg Sum.inr hh))
    (fun i j hij => (suffixEmbedding b t htb).injective.ne hij) c {3, 4} {5} hBH hBL
  have hpq : Disjoint ({0, 3, 4} : Finset (Fin 6)).sym2
      (({1} : Finset (Fin 6)).sym2 ∪ colorPairs {0, 3} {1}) := by decide
  obtain ⟨P₁, hP₁, hc₁, hs₁⟩ := combine_region_packings hP hQ hsP hsQ hpq
  have hps : Disjoint (({0, 3, 4} : Finset (Fin 6)).sym2 ∪
      (({1} : Finset (Fin 6)).sym2 ∪ colorPairs {0, 3} {1}))
      (({2} : Finset (Fin 6)).sym2 ∪ colorPairs {0, 1} {2}) := by decide
  obtain ⟨P₂, hP₂, hc₂, hs₂⟩ := combine_region_packings hP₁ hS hs₁ hsS hps
  have hpt : Disjoint ((({0, 3, 4} : Finset (Fin 6)).sym2 ∪
      (({1} : Finset (Fin 6)).sym2 ∪ colorPairs {0, 3} {1})) ∪
      (({2} : Finset (Fin 6)).sym2 ∪ colorPairs {0, 1} {2}))
      (({5} : Finset (Fin 6)).sym2 ∪ colorPairs {3, 4} {5}) := by decide
  obtain ⟨P₃, hP₃, hc₃, _⟩ := combine_region_packings hP₂ hT hs₂ hsT hpt
  have hcard : P₃.card = completeCount (x + t) + fanCount (x + y) (r - x) +
      fanCount r (a - r) + fanCount t (b - t) := by rw [hc₃, hc₂, hc₁, hp, hq, hs, ht]
  exact hcard ▸ packing_le_number hP₃

end ResearchMain.Tuza.FerrersProfile
