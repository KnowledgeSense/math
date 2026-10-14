import ASR312.SparseDescendingUniqueness

namespace ASR312

def rowPrefix {p n k : ℕ} (A : Rectangle (p+n) k) : Rectangle p k :=
  fun i j => A (i.castAdd n) j

def rowSuffix {p n k : ℕ} (A : Rectangle (p+n) k) : Rectangle n k :=
  fun i j => A (i.natAdd p) j

theorem rowSlices_reconstruction {p n k : ℕ} (A : Rectangle (p+n) k) :
    Fin.append (rowPrefix A) (rowSuffix A) = A := by
  funext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [rowPrefix,rowSuffix]

theorem rowPrefix_row {p n k : ℕ} (A : Rectangle (p+n) k) (i : Fin p) :
    row (rowPrefix A) i = row A (i.castAdd n) := rfl

theorem rowSuffix_row {p n k : ℕ} (A : Rectangle (p+n) k) (i : Fin n) :
    row (rowSuffix A) i = row A (i.natAdd p) := rfl

theorem rowSlices_col {p n k : ℕ} (A : Rectangle (p+n) k) (j : Fin k) :
    col A j = col (rowPrefix A) j ++ col (rowSuffix A) j := by
  have hf : (fun i => A i j) = Fin.append (fun i => rowPrefix A i j) (fun i => rowSuffix A i j) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [rowPrefix,rowSuffix]
  simp [col,hf,List.ofFn_fin_append]

theorem rowPrefix_asr {p n k : ℕ} (A : Rectangle (p+n) k) (ha : IsASR A) : IsASR (rowPrefix A) := by
  refine ⟨fun i => ha.1 (i.castAdd n),fun j => ?_⟩
  have hp : col (rowPrefix A) j <+: col A j := by rw [rowSlices_col]; exact List.prefix_append _ _
  exact ⟨alternates_prefix hp (ha.2 j).1,startsPositive_prefix hp (ha.2 j).2⟩

theorem rowPrefix_extendable {p n k : ℕ} (A : Rectangle (p+n) k) (he : ExtendablyAvoids312 A) :
    ExtendablyAvoids312 (rowPrefix A) := by
  obtain ⟨N,hr,hk,B,hB,hav,hmatch⟩ := he
  refine ⟨N,by omega,hk,B,hB,hav,?_⟩
  intro i j
  exact hmatch (i.castAdd n) j

theorem rowSlices_nonemptyRows {p n k : ℕ} (A : Rectangle (p+n) k) :
    nonemptyRows A = nonemptyRows (rowPrefix A) + nonemptyRows (rowSuffix A) := by
  classical
  have count {r k : ℕ} (B : Rectangle r k) :
      nonemptyRows B = ∑ i : Fin r, if ∃ j, B i j ≠ .zero then 1 else 0 := by
    simp [nonemptyRows]
  rw [count,Fin.sum_univ_add,count,count]
  rfl

theorem rowSlices_col_sum {p n k : ℕ} (A : Rectangle (p+n) k) (j : Fin k) :
    entrySum (col A j) = entrySum (col (rowPrefix A) j) + entrySum (col (rowSuffix A) j) := by
  rw [rowSlices_col]
  simp [entrySum,List.map_append,List.sum_append]

end ASR312
