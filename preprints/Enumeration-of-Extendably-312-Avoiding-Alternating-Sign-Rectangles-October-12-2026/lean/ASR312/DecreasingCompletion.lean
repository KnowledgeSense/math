import ASR312.ColumnCompletion

namespace ASR312

noncomputable def completionColumn {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (i : Fin m) : Fin (r+m) :=
  (zeroSumColumns A).orderEmbOfFin hc i.rev

theorem completionColumn_injective {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) : Function.Injective (completionColumn A hc) :=
  ((zeroSumColumns A).orderEmbOfFin hc).injective.comp Fin.rev_injective

theorem completionColumn_strictAnti {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) : StrictAnti (completionColumn A hc) := by
  intro i j hij
  exact ((zeroSumColumns A).orderEmbOfFin hc).strictMono (Fin.rev_lt_rev.mpr hij)

theorem completionColumn_mem {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (i : Fin m) : completionColumn A hc i ∈ zeroSumColumns A :=
  Finset.orderEmbOfFin_mem _ _ _

theorem completionColumn_surjective {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (j : Fin (r+m)) (hj : j ∈ zeroSumColumns A) :
    ∃ i, completionColumn A hc i = j := by
  let i := ((zeroSumColumns A).orderIsoOfFin hc).symm ⟨j,hj⟩
  refine ⟨i.rev,?_⟩
  simp only [completionColumn,Fin.rev_rev,Finset.orderEmbOfFin]
  exact congrArg Subtype.val (((zeroSumColumns A).orderIsoOfFin hc).apply_symm_apply ⟨j,hj⟩)

noncomputable def decreasingCompletion {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) : Rectangle (r+m) (r+m) :=
  Fin.append A (fun i j => if j = completionColumn A hc i then .plus else .zero)

theorem decreasingCompletion_top {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (i : Fin r) (j : Fin (r+m)) :
    decreasingCompletion A hc (i.castAdd m) j = A i j := by simp [decreasingCompletion]

theorem decreasingCompletion_bottom {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (i : Fin m) (j : Fin (r+m)) :
    decreasingCompletion A hc (i.natAdd r) j = if j = completionColumn A hc i then .plus else .zero := by
  simp [decreasingCompletion]

theorem decreasingCompletion_row_top {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (i : Fin r) :
    row (decreasingCompletion A hc) (i.castAdd m) = row A i := by
  simp [row,decreasingCompletion]

theorem decreasingCompletion_row_bottom {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (i : Fin m) :
    nonzeroEntries (row (decreasingCompletion A hc) (i.natAdd r)) = [.plus] := by
  simp only [row,decreasingCompletion,Fin.append_right]
  exact nonzero_ofFn_single _

theorem decreasingCompletion_col {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (j : Fin (r+m)) :
    nonzeroEntries (col (decreasingCompletion A hc) j) = nonzeroEntries (col A j) ++
      if j ∈ zeroSumColumns A then [.plus] else [] := by
  classical
  have hf : (fun i => decreasingCompletion A hc i j) =
      Fin.append (fun i => A i j) (fun i => if j = completionColumn A hc i then Entry.plus else .zero) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [decreasingCompletion]
  rw [col,hf,List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  congr 1
  by_cases hj : j ∈ zeroSumColumns A
  · rw [ite_eq_left hj]
    obtain ⟨p,hp⟩ := completionColumn_surjective A hc j hj
    have he : (fun i => if j = completionColumn A hc i then Entry.plus else .zero) =
        (fun i => if i = p then Entry.plus else .zero) := by
      funext i
      have hiff : j = completionColumn A hc i ↔ i = p := by
        rw [← hp]
        exact ⟨fun h => (completionColumn_injective A hc h).symm,fun h => by rw [h]⟩
      simp only [hiff]
    rw [he]
    exact nonzero_ofFn_single p
  · rw [ite_eq_right hj]
    have he : (fun i => if j = completionColumn A hc i then Entry.plus else .zero) =
        (fun _ : Fin m => Entry.zero) := by
      funext i
      have hn : j ≠ completionColumn A hc i := fun h => hj (h ▸ completionColumn_mem A hc i)
      simp [hn]
    rw [he]
    exact nonzero_ofFn_zero _

end ASR312
