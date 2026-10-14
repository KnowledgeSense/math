import ASR312.DimensionBounds

namespace ASR312

 theorem column_sum_one_properties (l : List Entry) (ha : Alternates l)
    (hs : StartsPositive l) (hv : entrySum l = 1) :
    nonzeroEntries l ≠ [] ∧ EndsPositive l := by
  have hsum := alternating_sum_endpoints (nonzeroEntries l) ha (nonzeroEntries_ne_zero l)
  rw [nonzeroEntries_sum,hv] at hsum
  have hn : nonzeroEntries l ≠ [] := by
    intro hz
    rw [hz] at hsum
    norm_num [endValue,Entry.value] at hsum
  have hs' : (nonzeroEntries l).head? = some .plus := hs.resolve_left (by simpa using hn)
  rw [hs'] at hsum
  refine ⟨hn,Or.inr ?_⟩
  cases he : (nonzeroEntries l).getLast? with
  | none => rw [he] at hsum; norm_num [endValue,Entry.value] at hsum
  | some e =>
    rw [he] at hsum
    cases e <;> simp_all [endValue,Entry.value]

 theorem balanced_column_sums {r k : ℕ} (A : Rectangle r k) (ha : IsASR A)
    (hn : nonemptyRows A = k) (j : Fin k) : entrySum (col A j) = 1 := by
  have hb : ∀ j ∈ (Finset.univ : Finset (Fin k)), entrySum (col A j) ≤ (1 : ℤ) :=
    fun j _ => (column_sum_bounds _ (ha.2 j).1 (ha.2 j).2).2
  have hs : (∑ j, entrySum (col A j)) = ∑ _j : Fin k, (1 : ℤ) := by
    simp_rw [col_entrySum]
    rw [Finset.sum_comm,total_sum_nonemptyRows A ha,hn]
    simp
  exact (Finset.sum_eq_sum_iff_of_le hb).mp hs j (Finset.mem_univ _)

 theorem nonemptyRows_eq_rows_iff {r k : ℕ} (A : Rectangle r k) :
    nonemptyRows A = r ↔ ∀ i, ∃ j, A i j ≠ .zero := by
  classical
  have hh := Finset.card_filter_eq_iff (s:=(Finset.univ : Finset (Fin r)))
    (p:=fun i => ∃ j, A i j ≠ .zero)
  simpa only [nonemptyRows,Finset.card_univ,Fintype.card_fin,Finset.mem_univ,forall_true_left] using hh

 theorem square_rowcomplete_asm {n : ℕ} (A : Rectangle n n) (ha : IsASR A)
    (hn : nonemptyRows A = n) : IsASM A := by
  refine ⟨ha,(nonemptyRows_eq_rows_iff A).mp hn,?_⟩
  intro j
  have hh := column_sum_one_properties _ (ha.2 j).1 (ha.2 j).2 (balanced_column_sums A ha hn j)
  refine ⟨?_,hh.2⟩
  by_contra he
  have hz : ∀ i, A i j = .zero := by simpa using he
  apply hh.1
  have hc : col A j = List.ofFn (fun _ : Fin n => Entry.zero) := by
    unfold col
    congr 1
    funext i
    exact hz i
  rw [hc]
  exact nonzero_ofFn_zero n

 noncomputable def squareASMCount (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Rectangle n n // IsASM A ∧ Avoids312 A}

 theorem S_square (n : ℕ) : S n n n = squareASMCount n := by
  classical
  apply Fintype.card_congr
  refine {
    toFun := fun A => ⟨A.val,square_rowcomplete_asm A.val A.property.1 A.property.2.1,
      extendable_implies_avoids A.property.2.2⟩
    invFun := fun A => ⟨A.val,A.property.1.1,
      (nonemptyRows_eq_rows_iff A.val).mpr A.property.1.2.1,
      (asm_extendable_iff A.val A.property.1).mpr A.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end ASR312
