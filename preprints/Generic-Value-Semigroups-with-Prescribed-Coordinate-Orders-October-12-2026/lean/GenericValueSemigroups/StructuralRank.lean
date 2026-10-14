import GenericValueSemigroups.GreedySequence
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Pi

namespace GenericValueSemigroups
open scoped BigOperators Classical

/-- A row-column cover of the nonzero entries bounds the actual matrix rank. -/
theorem rank_le_row_column_cover {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) (R : Finset m) (C : Finset n)
    (hz : ∀ i j, i ∉ R → j ∉ C → A i j=0) : A.rank ≤ R.card+C.card := by
  classical
  let S : Finset (m → K) := C.image A.col ∪ R.image (fun i => Pi.single i (1:K))
  have hspan : Submodule.span K (Set.range A.col) ≤ Submodule.span K (S : Set (m → K)) := by
    apply Submodule.span_le.mpr
    rintro v ⟨j,rfl⟩
    by_cases hj : j ∈ C
    · apply Submodule.subset_span
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    · rw [pi_eq_sum_univ' (A.col j)]
      apply Submodule.sum_mem
      intro i _
      by_cases hi : i ∈ R
      · apply Submodule.smul_mem
        apply Submodule.subset_span
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
      · have hh : A.col j i=0 := hz i j hi hj
        rw [hh,zero_smul]
        exact Submodule.zero_mem _
  rw [Matrix.rank_eq_finrank_span_cols]
  calc
    _ ≤ Module.finrank K (Submodule.span K (S : Set (m → K))) := Submodule.finrank_mono hspan
    _ ≤ S.card := finrank_span_finset_le_card S
    _ ≤ (C.image A.col).card+(R.image (fun i => Pi.single i (1:K))).card := Finset.card_union_le _ _
    _ ≤ C.card+R.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := Nat.add_comm _ _

/-- The structural upper bound at a single column cut. -/
theorem rank_le_weight_cut {K : Type*} [Field K] {L p : ℕ}
    (A : Matrix (Fin L) (Fin p) K) (w : ℕ → ℕ) (hw : Monotone w)
    (hz : ∀ a b, a.val < w b.val → A a b=0)
    (i : ℕ) : A.rank ≤ i+(L-w i) := by
  let C : Finset (Fin p) := Finset.univ.filter (fun b => b.val < i)
  let R : Finset (Fin L) := Finset.univ.filter (fun a => w i ≤ a.val)
  have hcover := rank_le_row_column_cover A R C (by
    intro a b ha hb
    have hai : a.val < w i := by simp only [R,Finset.mem_filter,Finset.mem_univ,true_and] at ha; omega
    have hbi : i≤b.val := by simp only [C,Finset.mem_filter,Finset.mem_univ,true_and] at hb; omega
    exact hz a b (lt_of_lt_of_le hai (hw hbi)))
  have hC : C.card ≤ i := by
    let f : C → Fin i := fun b => ⟨b.val.val,(Finset.mem_filter.mp b.property).2⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Fin.ext
      have he := congrArg Fin.val h
      exact he
    simpa using Fintype.card_le_of_injective f hf
  have hR : R.card ≤ L-w i := by
    let f : R → Fin (L-w i) := fun a => ⟨a.val.val-w i, by
      have ha := (Finset.mem_filter.mp a.property).2
      have hb := a.val.isLt
      omega⟩
    have hf : Function.Injective f := by
      intro a b h
      have he := congrArg Fin.val h
      have ha := (Finset.mem_filter.mp a.property).2
      have hb := (Finset.mem_filter.mp b.property).2
      apply Subtype.ext
      apply Fin.ext
      change a.val.val-w i=b.val.val-w i at he
      omega
    simpa using Fintype.card_le_of_injective f hf
  omega

/-- A structural-zero pattern has rank at most the number of its greedy positions below L. -/
theorem rank_le_greedy_count {K : Type*} [Field K] {L p : ℕ}
    (A : Matrix (Fin L) (Fin p) K) (w : ℕ → ℕ) (hw : Monotone w)
    (hz : ∀ a b, a.val < w b.val → A a b = 0) :
    A.rank ≤ ((Finset.range p).filter (fun j => greedy w j < L)).card := by
  let m := ((Finset.range p).filter (fun j => greedy w j < L)).card
  have hmp : m ≤ p := by
    have hh := Finset.card_filter_le (Finset.range p) (fun j => greedy w j < L)
    simpa only [Finset.card_range] using hh
  by_cases he : m=p
  · change A.rank ≤ m
    rw [he]
    exact A.rank_le_width
  by_cases hLm : L ≤ m
  · exact le_trans A.rank_le_height hLm
  have hm : m < p := by omega
  have hgm : L ≤ greedy w m := by
    by_contra hbad
    have hsub : Finset.range (m+1) ⊆ (Finset.range p).filter (fun j => greedy w j < L) := by
      intro j hj
      have hjm : j ≤ m := by have hh := Finset.mem_range.mp hj; omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      have hg := (greedy_strictMono w).monotone hjm
      omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    change m+1 ≤ m at hc
    omega
  obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_sup (Finset.range (m+1))
    (by simp) (fun j => w j-j)
  have hpos : 0 < (Finset.range (m+1)).sup (fun j => w j-j) := by
    have hh := greedy_eq_running_deficit w m
    omega
  have hir : i ≤ m := by have hh := Finset.mem_range.mp hi; omega
  have hwi : i + (L-w i) ≤ m := by
    have hh := greedy_eq_running_deficit w m
    omega
  exact le_trans (rank_le_weight_cut A w hw hz i) hwi

end GenericValueSemigroups
