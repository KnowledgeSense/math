import MainTheorems.Tuza.GraphCovers
import MainTheorems.Tuza.CrossRectangles

namespace ResearchMain.Tuza

def sparseCoverGraph (a b r t x y : ℕ) : SimpleGraph (Fin a ⊕ Fin b) :=
  sumInternalGraph (splitClique a r) (splitClique b t) ⊔
    crossRelationGraph (sparseCross a b r t x y)

instance (a b r t x y : ℕ) : DecidableRel (sparseCoverGraph a b r t x y).Adj := by
  unfold sparseCoverGraph
  infer_instance

@[simp]
theorem sparseCoverGraph_left (a b r t x y : ℕ) (i j : Fin a) :
    (sparseCoverGraph a b r t x y).Adj (.inl i) (.inl j) ↔
      i ≠ j ∧ (i.val < r ↔ j.val < r) := by
  simp [sparseCoverGraph, crossRelationGraph]

@[simp]
theorem sparseCoverGraph_right (a b r t x y : ℕ) (i j : Fin b) :
    (sparseCoverGraph a b r t x y).Adj (.inr i) (.inr j) ↔
      i ≠ j ∧ (i.val < t ↔ j.val < t) := by
  simp [sparseCoverGraph, crossRelationGraph]

@[simp]
theorem sparseCoverGraph_cross (a b r t x y : ℕ) (i : Fin a) (j : Fin b) :
    (sparseCoverGraph a b r t x y).Adj (.inl i) (.inr j) ↔
      (i.val < x ∧ j.val < t) ∨ (i.val < r ∧ j.val < y) := by
  simp [sparseCoverGraph, crossRelationGraph, sparseCross]

theorem sparseCoverGraph_card (a b r t x y : ℕ) (hxr : x ≤ r) (hra : r ≤ a)
    (hyt : y ≤ t) (htb : t ≤ b) :
    (sparseCoverGraph a b r t x y).edgeFinset.card =
      r.choose 2 + (a - r).choose 2 + t.choose 2 + (b - t).choose 2 +
        x * t + (r - x) * y := by
  have he : (sparseCoverGraph a b r t x y).edgeFinset =
      (sumInternalGraph (splitClique a r) (splitClique b t) ⊔
        crossRelationGraph (sparseCross a b r t x y)).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rfl
  rw [he, sumInternal_cross_card, splitClique_card a r hra, splitClique_card b t htb,
    sparseCross_card a b r t x y hxr hra hyt htb]
  omega

namespace FerrersProfile

variable {a b r t x y : ℕ} (d : FerrersProfile a b)

theorem sparseCoverGraph_le (hxt : ∀ i : Fin a, i.val < x → t ≤ d.degree i)
    (hry : ∀ i : Fin a, i.val < r → y ≤ d.degree i) :
    sparseCoverGraph a b r t x y ≤ d.graph := by
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => exact ((sparseCoverGraph_left _ _ _ _ _ _ _ _).mp huv).1
    | inr j =>
      rcases (sparseCoverGraph_cross _ _ _ _ _ _ _ _).mp huv with h | h
      · exact lt_of_lt_of_le h.2 (hxt i h.1)
      · exact lt_of_lt_of_le h.2 (hry i h.1)
  | inr j =>
    cases v with
    | inl i =>
      rcases (sparseCoverGraph_cross _ _ _ _ _ _ _ _).mp huv.symm with h | h
      · exact lt_of_lt_of_le h.2 (hxt i h.1)
      · exact lt_of_lt_of_le h.2 (hry i h.1)
    | inr i => exact ((sparseCoverGraph_right _ _ _ _ _ _ _ _).mp huv).1

theorem sparse_left_triangle (hlow : ∀ i : Fin a, r ≤ i.val → d.degree i ≤ y)
    (i l : Fin a) (j : Fin b) (hil : i ≠ l)
    (hij : j.val < d.degree i) (hlj : j.val < d.degree l) :
    (sparseCoverGraph a b r t x y).Adj (.inl i) (.inl l) ∨
      (sparseCoverGraph a b r t x y).Adj (.inl i) (.inr j) ∨
      (sparseCoverGraph a b r t x y).Adj (.inl l) (.inr j) := by
  have hi := hlow i
  have hl := hlow l
  simp only [sparseCoverGraph_left, sparseCoverGraph_cross]
  omega

theorem sparse_right_triangle
    (hhigh : ∀ i : Fin a, t ≤ d.degree i → i.val < x)
    (i : Fin a) (j k : Fin b) (hjk : j ≠ k)
    (hij : j.val < d.degree i) (hik : k.val < d.degree i) :
    (sparseCoverGraph a b r t x y).Adj (.inr j) (.inr k) ∨
      (sparseCoverGraph a b r t x y).Adj (.inl i) (.inr j) ∨
      (sparseCoverGraph a b r t x y).Adj (.inl i) (.inr k) := by
  have hi := hhigh i
  simp only [sparseCoverGraph_right, sparseCoverGraph_cross]
  omega

theorem sparseCover_covers
    (hxt : ∀ i : Fin a, i.val < x → t ≤ d.degree i)
    (hry : ∀ i : Fin a, i.val < r → y ≤ d.degree i)
    (hlow : ∀ i : Fin a, r ≤ i.val → d.degree i ≤ y)
    (hhigh : ∀ i : Fin a, t ≤ d.degree i → i.val < x) :
    Cover d.graph (sparseCoverGraph a b r t x y).edgeFinset := by
  apply graph_triangle_cover (d.sparseCoverGraph_le hxt hry)
  intro u v w huv huw hvw
  cases u with
  | inl i =>
    cases v with
    | inl l =>
      cases w with
      | inl m =>
        simp only [adj_left] at huv huw hvw
        simp only [sparseCoverGraph_left]
        omega
      | inr j => exact d.sparse_left_triangle hlow i l j huv huw hvw
    | inr j =>
      cases w with
      | inl l =>
        have h := d.sparse_left_triangle (t := t) (x := x) hlow i l j huw huv hvw
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
      | inr k =>
        have h := d.sparse_right_triangle (r := r) (y := y) hhigh i j k hvw huv huw
        rcases h with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  | inr j =>
    cases v with
    | inl i =>
      cases w with
      | inl l =>
        have h := d.sparse_left_triangle (t := t) (x := x) hlow i l j hvw huv huw
        rcases h with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl h.symm)
      | inr k =>
        have h := d.sparse_right_triangle (r := r) (y := y) hhigh i j k huw huv hvw
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
    | inr k =>
      cases w with
      | inl i =>
        have h := d.sparse_right_triangle (r := r) (y := y) hhigh i j k huv huw hvw
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inr (Or.inr h.symm)
      | inr l =>
        simp only [adj_right] at huv huw hvw
        simp only [sparseCoverGraph_right]
        omega

end FerrersProfile

end ResearchMain.Tuza
