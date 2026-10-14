import TerminalLogConcavity.ReleaseCounts

namespace TerminalLogConcavity

theorem Block.card_rank_identity (b : Block) : Fintype.card b.Vertex + 1 = 2*b.rank := by
  induction b with
  | leaf => rw [Block.card_leaf]; rfl
  | binary a b ha hb => rw [Block.card_binary]; simp only [Block.rank]; omega

noncomputable def decorationDefect (D : Decoration) : ℤ :=
  2 * (D.forest.alpha : ℤ) - decorationCost D

@[simp] theorem block_decoration_defect (b : Block) : decorationDefect b.decoration = 0 := by
  change 2 * (b.toForest.alpha : ℤ) - ((Fintype.card b.Vertex : ℤ) + 1) = 0
  rw [b.toForest_alpha]
  have h : (Fintype.card b.Vertex : ℤ) + 1 = 2 * b.rank := by exact_mod_cast b.card_rank_identity
  omega

@[simp] theorem site_decoration_defect (q t i k : ℕ) : decorationDefect (siteDecoration q t i k) = 1 := by
  let p := Block.scaled t (siteParameter q i k)
  let m := Block.scaled t (interfaceParameter q i)
  change 2 * ((interfaceForest p m).alpha : ℤ) - ((Fintype.card (interfaceForest p m).Vertex : ℤ) + 1) = 1
  rw [interfaceForest_alpha,interface_card]
  have hp : (Fintype.card p.Vertex : ℤ) + 1 = 2*p.rank := by exact_mod_cast p.card_rank_identity
  have hm : (Fintype.card m.Vertex : ℤ) + 1 = 2*m.rank := by exact_mod_cast m.card_rank_identity
  push_cast
  omega

@[simp] theorem chain_defect (q t i : ℕ) (hq : 1 ≤ q) :
    ((chainDecorations q t i).map decorationDefect).sum = q := by
  unfold chainDecorations
  rw [sum_map_intersperse_int _ _ _ (by intro h; have := congrArg List.length h; simp at this; omega)]
  simp only [List.map_map,Function.comp_def,site_decoration_defect,couplerDecoration,block_decoration_defect,
    mul_zero,add_zero,List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul,mul_one]

@[simp] theorem release_defect {q : ℕ} (hq : 1 ≤ q) (t : ℕ) :
    ((releaseDecorations q t).map decorationDefect).sum = (q : ℤ)^2 := by
  unfold releaseDecorations
  rw [sum_map_flatten_int, sum_map_intersperse_int _ _ _
    (by intro h; have := congrArg List.length h; simp at this; omega)]
  simp only [List.map_map,Function.comp_def,chain_defect _ _ _ hq,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,block_decoration_defect,mul_zero,add_zero,
    List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul]
  ring

/-- The exact independence-number identity in the release construction. -/
theorem releaseForest_independence_identity {q : ℕ} (hq : 1 ≤ q) (t : ℕ) :
    2*(releaseForest q t).graph.indepNum = Fintype.card (releaseForest q t).Vertex + q^2 := by
  have h := release_defect hq t
  have he : ((releaseDecorations q t).map decorationDefect).sum =
      2*((releaseForest q t).graph.indepNum : ℤ) - Fintype.card (releaseForest q t).Vertex := by
    rw [ForestExpr.graph_alpha,releaseForest,decoratedPath_alpha,decoratedPath_card]
    simp only [Nat.cast_list_sum,List.map_map,Function.comp_def,
      Nat.cast_add,Nat.cast_one]
    induction releaseDecorations q t with
    | nil => simp
    | cons D ds ih => simp only [List.map_cons,List.sum_cons,decorationDefect,decorationCost] at *; omega
  rw [he] at h
  have hr : 2*((releaseForest q t).graph.indepNum : ℤ) =
      Fintype.card (releaseForest q t).Vertex + (q : ℤ)^2 := by omega
  exact_mod_cast hr

theorem releaseTree_independence_ge {r : ℕ} (hr : 1 ≤ r) (H : ℕ) :
    r+1 ≤ (releaseTree r H).graph.indepNum := by
  have h := releaseForest_independence_identity (show 1 ≤ r+1 by omega)
    (thresholdIndex (target (r+1) H))
  change 2*(releaseTree r H).graph.indepNum = _ at h
  nlinarith

end TerminalLogConcavity
