import MainTheorems.Tuza.MatchingFactors
import MainTheorems.Tuza.Transfer

namespace ResearchMain.Tuza

variable {V W I : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem clique_map_of_adj {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) (hf : ∀ x y, G.Adj x y → H.Adj (f x) (f y))
    {n : ℕ} {s : Finset V} (hs : G.IsNClique n s) : H.IsNClique n (s.map f) := by
  have hmap : G.map f ≤ H := SimpleGraph.map_le_of_le_comap hf
  exact hs.map.mono hmap

def PackingFamily.map {G : SimpleGraph V} {H : SimpleGraph W} (P : PackingFamily G I)
    (f : V ↪ W) (hf : ∀ x y, G.Adj x y → H.Adj (f x) (f y)) : PackingFamily H I where
  triangle i := (P.triangle i).map f
  clique i := clique_map_of_adj f hf (P.clique i)
  disjoint i j hij := by
    rw [triangleEdges_map, triangleEdges_map]
    exact (Finset.disjoint_map _).mpr (P.disjoint i j hij)

variable {C Q F : Type*} [DecidableEq C] [DecidableEq Q]

def sumEmbedding (a : C ↪ V) (b : Q ↪ V) (h : ∀ c q, a c ≠ b q) : C ⊕ Q ↪ V where
  toFun := Sum.elim a b
  inj' := by
    intro x y hxy
    cases x with
    | inl c =>
      cases y with
      | inl d => exact congrArg Sum.inl (a.injective hxy)
      | inr q => exact False.elim (h c q hxy)
    | inr q =>
      cases y with
      | inl c => exact False.elim (h c q hxy.symm)
      | inr q' => exact congrArg Sum.inr (b.injective hxy)

omit [DecidableEq V] [DecidableEq C] [DecidableEq Q] in
theorem sumEmbedding_adj {G : SimpleGraph V} (a : C ↪ V) (b : Q ↪ V)
    (hd : ∀ c q, a c ≠ b q)
    (hc : ∀ c q, G.Adj (a c) (b q)) (hb : ∀ q q', q ≠ q' → G.Adj (b q) (b q')) :
    ∀ x y, (fanGraph C Q).Adj x y → G.Adj (sumEmbedding a b hd x) (sumEmbedding a b hd y) := by
  intro x y hxy
  cases x with
  | inl c =>
    cases y with
    | inl d => exact False.elim hxy
    | inr q => exact hc c q
  | inr q =>
    cases y with
    | inl c => exact (hc c q).symm
    | inr q' => exact hb q q' hxy

variable [Fintype C] [Fintype Q]

theorem exists_fan_packing {G : SimpleGraph V} (M : MatchingFactors Q F) (f : C ↪ F)
    (a : C ↪ V) (b : Q ↪ V) (hd : ∀ c q, a c ≠ b q)
    (hc : ∀ c q, G.Adj (a c) (b q)) (hb : ∀ q q', q ≠ q' → G.Adj (b q) (b q'))
    (k : ℕ) (hk : ∀ c, Nat.card (M.graph (f c)).edgeSet = k) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = Fintype.card C * k := by
  classical
  let P := (M.packingFamily f).map (sumEmbedding a b hd) (sumEmbedding_adj a b hd hc hb)
  exact ⟨P.carrier, P.packing, P.card.trans (M.index_card f k hk)⟩

end ResearchMain.Tuza
