import SumsetRanges.RowFibers

open Finset
namespace SumsetRanges

def rowPart {m u : ℕ} (S : Finset (SharedIndex m u)) (i : Fin u) : Finset (RowIndex m) :=
  Finset.univ.filter (fun j => (i,j) ∈ S)

def assembleRows {m u : ℕ} (R : Fin u → Finset (RowIndex m)) : Finset (SharedIndex m u) :=
  Finset.univ.biUnion (fun i => (R i).image (fun j => (i,j)))

@[simp] theorem mem_rowPart {m u : ℕ} (S : Finset (SharedIndex m u))
    (i : Fin u) (j : RowIndex m) : j ∈ rowPart S i ↔ (i,j) ∈ S := by simp [rowPart]

@[simp] theorem mem_assembleRows {m u : ℕ} (R : Fin u → Finset (RowIndex m))
    (i : Fin u) (j : RowIndex m) : (i,j) ∈ assembleRows R ↔ j ∈ R i := by
  simp [assembleRows]

@[simp] theorem assembleRows_rowPart {m u : ℕ} (S : Finset (SharedIndex m u)) :
    assembleRows (rowPart S) = S := by
  ext ⟨i,j⟩
  simp

@[simp] theorem rowPart_assembleRows {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    rowPart (assembleRows R) = R := by
  funext i
  ext j
  simp

theorem assembleRows_injective {m u : ℕ} :
    Function.Injective (assembleRows (m := m) (u := u)) := by
  intro R T he
  have h := congrArg rowPart he
  simpa using h

theorem card_assembleRows {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    (assembleRows R).card = ∑ i, (R i).card := by
  unfold assembleRows
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.card_image_of_injective _ (fun a b he => (Prod.mk.inj he).2)
  · intro i _ k _ hik
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hy
    exact hik (Prod.mk.inj he).1.symm

theorem card_eq_sum_card_rowPart {m u : ℕ} (S : Finset (SharedIndex m u)) :
    S.card = ∑ i, (rowPart S i).card := by
  rw [← card_assembleRows, assembleRows_rowPart]

@[simp] theorem sharedRowValue_assembleRows {m u : ℕ}
    (R : Fin u → Finset (RowIndex m)) (i : Fin u) (j : Fin (m-1)) :
    sharedRowValue (assembleRows R) i j = rowValue (R i) j := by
  simp [sharedRowValue,rowValue]

theorem sharedAlphaCount_assembleRows {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    sharedAlphaCount (assembleRows R) = (Finset.univ.filter (fun i => none ∈ R i)).card := by
  unfold sharedAlphaCount
  have he : (assembleRows R).filter (fun a => a.2=none) =
      (Finset.univ.filter (fun i => none ∈ R i)).image (fun i => (i,none)) := by
    ext ⟨i, _ | j⟩ <;> simp
  rw [he, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]

/-- The exact collision test expressed entirely in row subsets. -/
theorem assembled_rows_collision {m u : ℕ} (R T : Fin u → Finset (RowIndex m)) :
    (∑ a ∈ assembleRows R, sharedPoint a = ∑ a ∈ assembleRows T, sharedPoint a) ↔
      (Finset.univ.filter (fun i => none ∈ R i)).card =
        (Finset.univ.filter (fun i => none ∈ T i)).card ∧
      ∀ i, rowValue (R i) = rowValue (T i) := by
  rw [sharedAtomBlock_subset_collision, sharedAlphaCount_assembleRows,
    sharedAlphaCount_assembleRows]
  simp only [sharedRowValue_assembleRows, funext_iff]

end SumsetRanges
