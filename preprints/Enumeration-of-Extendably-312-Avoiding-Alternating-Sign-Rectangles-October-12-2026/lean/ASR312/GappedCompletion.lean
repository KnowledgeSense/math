import ASR312.GappedCompletionColumns

namespace ASR312

theorem nonzero_ofFn_injection {n N : ℕ} (f : Fin n → Fin N) (hf : Function.Injective f) (j : Fin N) :
    nonzeroEntries (List.ofFn (fun i => if j = f i then Entry.plus else .zero)) =
      if ∃ i, f i = j then [.plus] else [] := by
  classical
  by_cases hj : ∃ i, f i = j
  · rw [ite_eq_left hj]
    obtain ⟨p,hp⟩ := hj
    have he : (fun i => if j = f i then Entry.plus else .zero) =
        (fun i => if i = p then Entry.plus else .zero) := by
      funext i
      have hiff : j = f i ↔ i = p := by
        rw [← hp]
        exact ⟨fun h => (hf h).symm,fun h => by rw [h]⟩
      simp only [hiff]
    rw [he]
    exact nonzero_ofFn_single _
  · rw [ite_eq_right hj]
    have he : (fun i => if j = f i then Entry.plus else .zero) =
        (fun _ : Fin n => Entry.zero) := by
      funext i
      have hn : j ≠ f i := fun h => hj ⟨i,h.symm⟩
      simp [hn]
    rw [he]
    exact nonzero_ofFn_zero _

noncomputable def gappedCompletion {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) : Rectangle (r+n) (r+n) :=
  Fin.append (fun i j => if h : j.val < r+m then A i ⟨j.val,h⟩ else .zero)
    (fun i j => if j = gappedColumn A hc s hs i then .plus else .zero)

theorem gappedCompletion_row_top {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) (i : Fin r) :
    nonzeroEntries (row (gappedCompletion A hc s hs) (i.castAdd n)) = nonzeroEntries (row A i) := by
  have hm : m ≤ n := by have hh := Finset.card_le_univ s; simpa [hs] using hh
  have hz (j : Fin (r+n)) (hj : r+m ≤ j.val) :
      gappedCompletion A hc s hs (i.castAdd n) j = .zero := by
    simp [gappedCompletion,show ¬j.val < r+m by omega]
  unfold row
  rw [← nonzeroEntries_take_ofFn _ hz,take_ofFn (by omega : r+m ≤ r+n)]
  congr 2
  funext j
  simp [gappedCompletion,j.isLt]

theorem gappedCompletion_row_bottom {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) (i : Fin n) :
    nonzeroEntries (row (gappedCompletion A hc s hs) (i.natAdd r)) = [.plus] := by
  simp only [row,gappedCompletion,Fin.append_right]
  exact nonzero_ofFn_single _

theorem gappedCompletion_col_small {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (j : Fin (r+n)) (hj : j.val < r+m) :
    nonzeroEntries (col (gappedCompletion A hc s hs) j) =
      nonzeroEntries (col A ⟨j.val,hj⟩) ++ if (⟨j.val,hj⟩ : Fin (r+m)) ∈ zeroSumColumns A then [.plus] else [] := by
  classical
  have hf : (fun i => gappedCompletion A hc s hs i j) =
      Fin.append (fun i => A i ⟨j.val,hj⟩) (fun i => if j = gappedColumn A hc s hs i then Entry.plus else .zero) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [gappedCompletion,hj]
  rw [col,hf,List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  change nonzeroEntries (col A ⟨j.val,hj⟩) ++ nonzeroEntries _ = _
  rw [nonzero_ofFn_injection _ (gappedColumn_injective A hc s hs)]
  have he : (∃ i, gappedColumn A hc s hs i = j) ↔ (⟨j.val,hj⟩ : Fin (r+m)) ∈ zeroSumColumns A := by
    rw [← gappedColumn_small_range_iff A hc s hs ⟨j.val,hj⟩]
    simp only [Fin.ext_iff]
  simp only [he]
  rfl

theorem gappedCompletion_col_large {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (j : Fin (r+n)) (hj : r+m ≤ j.val) :
    nonzeroEntries (col (gappedCompletion A hc s hs) j) = [.plus] := by
  classical
  have hf : (fun i => gappedCompletion A hc s hs i j) =
      Fin.append (fun _ : Fin r => Entry.zero) (fun i => if j = gappedColumn A hc s hs i then Entry.plus else .zero) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [gappedCompletion,show ¬j.val < r+m by omega]
  rw [col,hf,List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  change nonzeroEntries _ ++ nonzeroEntries _ = _
  rw [nonzero_ofFn_zero,List.nil_append,nonzero_ofFn_injection _ (gappedColumn_injective A hc s hs)]
  exact ite_eq_left (gappedColumn_large_surjective A hc s hs j hj)

end ASR312
