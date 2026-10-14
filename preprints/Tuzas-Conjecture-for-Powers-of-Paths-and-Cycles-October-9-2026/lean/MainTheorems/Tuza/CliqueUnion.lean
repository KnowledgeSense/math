import MainTheorems.Tuza.EdgeRegions

namespace ResearchMain.Tuza

variable {V K : Type*}

@[simp]
theorem sumEmbedding_inl {C Q : Type*} [DecidableEq C] [DecidableEq Q]
    (a : C ↪ V) (b : Q ↪ V) (h : ∀ i j, a i ≠ b j) (i : C) :
    sumEmbedding a b h (.inl i) = a i := rfl

@[simp]
theorem sumEmbedding_inr {C Q : Type*} [DecidableEq C] [DecidableEq Q]
    (a : C ↪ V) (b : Q ↪ V) (h : ∀ i j, a i ≠ b j) (j : Q) :
    sumEmbedding a b h (.inr j) = b j := rfl

theorem color_ne {c : V → K} {x y : V} (h : c x ≠ c y) : x ≠ y :=
  fun hxy => h (congrArg c hxy)

def unionEmbedding {n q : ℕ} (a : Fin n ↪ V) (b : Fin q ↪ V)
    (h : ∀ i j, a i ≠ b j) : Fin (n + q) ↪ V :=
  finSumFinEquiv.symm.toEmbedding.trans (sumEmbedding a b h)

theorem unionEmbedding_clique {G : SimpleGraph V} {n q : ℕ}
    (a : Fin n ↪ V) (b : Fin q ↪ V) (h : ∀ i j, a i ≠ b j)
    (ha : ∀ i j, i ≠ j → G.Adj (a i) (a j))
    (hb : ∀ i j, i ≠ j → G.Adj (b i) (b j))
    (hab : ∀ i j, G.Adj (a i) (b j)) :
    ∀ i j, i ≠ j → G.Adj (unionEmbedding a b h i) (unionEmbedding a b h j) := by
  intro i j hij
  have hd : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j :=
    fun hh => hij (finSumFinEquiv.symm.injective hh)
  change G.Adj (sumEmbedding a b h (finSumFinEquiv.symm i))
    (sumEmbedding a b h (finSumFinEquiv.symm j))
  generalize finSumFinEquiv.symm i = x at *
  generalize finSumFinEquiv.symm j = y at *
  cases x with
  | inl i =>
    cases y with
    | inl j => exact ha i j (fun hh => hd (congrArg Sum.inl hh))
    | inr j => exact hab i j
  | inr i =>
    cases y with
    | inl j => exact (hab j i).symm
    | inr j => exact hb i j (fun hh => hd (congrArg Sum.inr hh))

theorem unionEmbedding_color [DecidableEq K] {n q : ℕ} (a : Fin n ↪ V) (b : Fin q ↪ V)
    (h : ∀ i j, a i ≠ b j) (c : V → K) (A B : Finset K)
    (ha : ∀ i, c (a i) ∈ A) (hb : ∀ j, c (b j) ∈ B) :
    ∀ i, c (unionEmbedding a b h i) ∈ A ∪ B := by
  intro i
  change c (sumEmbedding a b h (finSumFinEquiv.symm i)) ∈ A ∪ B
  cases finSumFinEquiv.symm i with
  | inl j => exact Finset.mem_union_left _ (ha j)
  | inr j => exact Finset.mem_union_right _ (hb j)

theorem unionEmbedding_cross {G : SimpleGraph V} {n q m : ℕ}
    (a : Fin n ↪ V) (b : Fin q ↪ V) (h : ∀ i j, a i ≠ b j) (e : Fin m ↪ V)
    (ha : ∀ i j, G.Adj (a i) (e j)) (hb : ∀ i j, G.Adj (b i) (e j)) :
    ∀ i j, G.Adj (unionEmbedding a b h i) (e j) := by
  intro i j
  change G.Adj (sumEmbedding a b h (finSumFinEquiv.symm i)) (e j)
  cases finSumFinEquiv.symm i with
  | inl k => exact ha k j
  | inr k => exact hb k j

theorem color_disjoint_embeddings [DecidableEq K] {I J : Type*} {c : V → K}
    {a : I → V} {b : J → V} {A B : Finset K} (h : Disjoint A B)
    (ha : ∀ i, c (a i) ∈ A) (hb : ∀ j, c (b j) ∈ B) :
    ∀ i j, a i ≠ b j := by
  intro i j hij
  apply Finset.disjoint_left.mp h (ha i)
  simpa only [hij] using hb j

end ResearchMain.Tuza
