import MainTheorems.Tuza.EdgeCounting
import MainTheorems.Tuza.FerrersCuts

namespace ResearchMain.Tuza

variable {V : Type*}

def withinGraph (p : V → Prop) : SimpleGraph V where
  Adj x y := x ≠ y ∧ p x ∧ p y
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance [DecidableEq V] (p : V → Prop) [DecidablePred p] :
    DecidableRel (withinGraph p).Adj := by
  intro x y
  change Decidable (x ≠ y ∧ p x ∧ p y)
  infer_instance

theorem withinGraph_eq_image (p : V → Prop) :
    withinGraph p = imageGraph (⊤ : SimpleGraph {x // p x}) (Function.Embedding.subtype p) := by
  ext x y
  constructor
  · rintro ⟨hne, hx, hy⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, rfl, rfl, fun h => hne (congrArg Subtype.val h)⟩
  · rintro ⟨u, v, rfl, rfl, huv⟩
    exact ⟨fun h => huv (Subtype.ext h), u.property, v.property⟩

theorem withinGraph_card [Fintype V] [DecidableEq V] (p : V → Prop) [DecidablePred p] :
    (withinGraph p).edgeFinset.card = (Fintype.card {x // p x}).choose 2 := by
  have h : (withinGraph p).edgeFinset =
      (imageGraph (⊤ : SimpleGraph {x // p x}) (Function.Embedding.subtype p)).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [withinGraph_eq_image]
  rw [h, imageGraph_card_edges, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

def splitClique (n p : ℕ) : SimpleGraph (Fin n) :=
  withinGraph (fun i => i.val < p) ⊔ withinGraph (fun i => p ≤ i.val)

instance (n p : ℕ) : DecidableRel (splitClique n p).Adj := by
  unfold splitClique
  infer_instance

@[simp]
theorem splitClique_adj (n p : ℕ) (i j : Fin n) :
    (splitClique n p).Adj i j ↔ i ≠ j ∧ (i.val < p ↔ j.val < p) := by
  change (i ≠ j ∧ i.val < p ∧ j.val < p) ∨ (i ≠ j ∧ p ≤ i.val ∧ p ≤ j.val) ↔ _
  omega

def prefixEquiv (n p : ℕ) (h : p ≤ n) : {i : Fin n // i.val < p} ≃ Fin p where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨prefixEmbedding n p h i, i.isLt⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := rfl

def suffixEquiv (n p : ℕ) (h : p ≤ n) : {i : Fin n // p ≤ i.val} ≃ Fin (n - p) where
  toFun i := ⟨i.val.val - p, by have := i.val.isLt; have := i.property; omega⟩
  invFun i := ⟨suffixEmbedding n p h i, by simp only [suffixEmbedding_val]; omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change p + (i.val.val - p) = i.val.val
    exact Nat.add_sub_of_le i.property
  right_inv i := by apply Fin.ext; simp only [suffixEmbedding_val]; omega

theorem splitClique_card (n p : ℕ) (h : p ≤ n) :
    (splitClique n p).edgeFinset.card = p.choose 2 + (n - p).choose 2 := by
  have hd : ∀ x y : Fin n, (withinGraph (fun i : Fin n => i.val < p)).Adj x y →
      ¬ (withinGraph (fun i : Fin n => p ≤ i.val)).Adj x y := by
    intro x y hx hy
    exact Nat.not_lt_of_ge hy.2.1 hx.2.1
  have he : (splitClique n p).edgeFinset =
      (withinGraph (fun i : Fin n => i.val < p) ⊔ withinGraph (fun i : Fin n => p ≤ i.val)).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rfl
  rw [he]
  rw [card_union_graph hd, withinGraph_card, withinGraph_card,
    Fintype.card_congr (prefixEquiv n p h), Fintype.card_congr (suffixEquiv n p h),
    Fintype.card_fin, Fintype.card_fin]

end ResearchMain.Tuza
