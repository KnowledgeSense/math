import ASR312.DecreasingCompletion

namespace ASR312

theorem decreasingCompletion_asm {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (ha : IsASR A) (hn : nonemptyRows A = r) :
    IsASM (decreasingCompletion A hc) := by
  have hrows (i : Fin (r+m)) : Alternates (row (decreasingCompletion A hc) i) ∧
      StartsPositive (row (decreasingCompletion A hc) i) ∧
      EndsPositive (row (decreasingCompletion A hc) i) := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [decreasingCompletion_row_top] using ha.1 i
    · simp [Alternates,StartsPositive,EndsPositive,decreasingCompletion_row_bottom]
  have hcols (j : Fin (r+m)) : Alternates (col (decreasingCompletion A hc) j) ∧
      StartsPositive (col (decreasingCompletion A hc) j) := by
    classical
    by_cases hj : j ∈ zeroSumColumns A
    · simp only [Alternates,StartsPositive,decreasingCompletion_col,hj,ite_true]
      refine ⟨column_append_plus_chain _ (ha.2 j).1 (ha.2 j).2 ((mem_zeroSumColumns A j).mp hj),?_⟩
      have hs := (ha.2 j).2
      cases hl : nonzeroEntries (col A j) with
      | nil => simp
      | cons x l => simpa only [StartsPositive,hl,List.cons_append,List.head?_cons] using hs
    · simpa only [Alternates,StartsPositive,decreasingCompletion_col,hj,ite_false,List.append_nil] using ha.2 j
  apply square_rowcomplete_asm _ ⟨hrows,hcols⟩
  apply (nonemptyRows_eq_rows_iff _).mpr
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · obtain ⟨j,hj⟩ := (nonemptyRows_eq_rows_iff A).mp hn i
    exact ⟨j,by simpa only [decreasingCompletion_top] using hj⟩
  · exact ⟨completionColumn A hc i,by simp [decreasingCompletion_bottom]⟩

theorem extendable_no_cross_zero_column {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) (i t : Fin r) (j u v : Fin k)
    (hit : i < t) (hju : j < u) (huv : u < v) (hiv : A i v = .plus) (htj : A t j = .plus)
    (hu : entrySum (col A u) = 0) : False := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  have hpre : prefixSum (fun q => B q (Fin.castLE hk u)) r = 0 := by
    rw [prefixSum_eq _ hr,take_ofFn hr]
    have hf : (fun q => B (Fin.castLE hr q) (Fin.castLE hk u)) = fun q => A q u := by
      funext q; exact hmatch q u
    rw [hf]
    exact hu
  obtain ⟨q,hq,hqu⟩ := plus_after_prefix_of_total (fun q => B q (Fin.castLE hk u))
    (asm_column_sum B hB _) hpre
  exact hav ⟨Fin.castLE hr i,Fin.castLE hr t,q,Fin.castLE hk j,Fin.castLE hk u,Fin.castLE hk v,
    hit,by change t.val < q.val; omega,hju,huv,(hmatch i v).trans hiv,(hmatch t j).trans htj,hqu⟩

theorem decreasingCompletion_avoids {r m : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (he : ExtendablyAvoids312 A) :
    Avoids312 (decreasingCompletion A hc) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  have top (i : Fin (r+m)) (j : Fin (r+m)) (hi : i.val < r) :
      decreasingCompletion A hc i j = A ⟨i.val,hi⟩ j := by
    have hei : i = (⟨i.val,hi⟩ : Fin r).castAdd m := Fin.ext rfl
    exact (congrArg (fun q => decreasingCompletion A hc q j) hei).trans (decreasingCompletion_top A hc _ j)
  have bottom (i : Fin (r+m)) (j : Fin (r+m)) (hi : r ≤ i.val)
      (hij : decreasingCompletion A hc i j = .plus) :
      j = completionColumn A hc ⟨i.val-r,by omega⟩ := by
    have hei : i = (⟨i.val-r,by omega⟩ : Fin m).natAdd r := Fin.ext (by simp; omega)
    rw [hei,decreasingCompletion_bottom] at hij
    simpa using hij
  by_cases h3 : i₃.val < r
  · have h2 : i₂.val < r := by change i₂.val < i₃.val at h23; omega
    have h1 : i₁.val < r := by change i₁.val < i₂.val at h12; omega
    rw [top i₁ j₃ h1] at h13
    rw [top i₂ j₁ h2] at h21
    rw [top i₃ j₂ h3] at h32
    exact extendable_implies_avoids he ⟨⟨i₁.val,h1⟩,⟨i₂.val,h2⟩,⟨i₃.val,h3⟩,
      j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  · have h3' : r ≤ i₃.val := by omega
    have hj₂ := bottom i₃ j₂ h3' h32
    by_cases h2 : i₂.val < r
    · have h1 : i₁.val < r := by change i₁.val < i₂.val at h12; omega
      rw [top i₁ j₃ h1] at h13
      rw [top i₂ j₁ h2] at h21
      exact extendable_no_cross_zero_column A he ⟨i₁.val,h1⟩ ⟨i₂.val,h2⟩ j₁ j₂ j₃
        h12 hj12 hj23 h13 h21 ((mem_zeroSumColumns A j₂).mp (hj₂ ▸ completionColumn_mem A hc _))
    · have h2' : r ≤ i₂.val := by omega
      have hj₁ := bottom i₂ j₁ h2' h21
      have hh := completionColumn_strictAnti A hc
        (show (⟨i₂.val-r,by omega⟩ : Fin m) < ⟨i₃.val-r,by omega⟩ from by
          change i₂.val-r < i₃.val-r; change i₂.val < i₃.val at h23; omega)
      rw [hj₁,hj₂] at hj12
      exact (not_lt_of_ge hh.le) hj12

end ASR312
