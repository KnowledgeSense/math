import MainTheorems.Tuza.FanPacking

namespace ResearchMain.Tuza

variable {C Q F V : Type*} [DecidableEq C] [DecidableEq Q] [DecidableEq V]

def FanSupport (a : C → V) (b : Q → V) (P : Finset (Finset V)) : Prop :=
  ∀ t ∈ P, ∀ e ∈ triangleEdges t,
    (∃ q q', e = s(b q, b q')) ∨ ∃ c q, e = s(a c, b q)

theorem fanTriangle_map_support (a : C ↪ V) (b : Q ↪ V) (hd : ∀ c q, a c ≠ b q)
    (c : C) (e : Sym2 Q) (w : Sym2 V)
    (hw : w ∈ triangleEdges ((fanTriangle c e).map (sumEmbedding a b hd))) :
    (∃ q q', w = s(b q, b q')) ∨ ∃ c q, w = s(a c, b q) := by
  rw [triangleEdges_map] at hw
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
  induction z using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨hx, hy, hxy⟩ := mem_triangleEdges.mp hz
    cases x with
    | inl v =>
      have hv : v = c := (mem_fanTriangle_left _ _ _).mp hx
      cases y with
      | inl v' =>
        have hv' : v' = c := (mem_fanTriangle_left _ _ _).mp hy
        exact False.elim (hxy (congrArg Sum.inl (hv.trans hv'.symm)))
      | inr q => exact Or.inr ⟨v, q, rfl⟩
    | inr q =>
      cases y with
      | inl v =>
        right
        refine ⟨v, q, ?_⟩
        exact Sym2.eq_swap
      | inr q' => exact Or.inl ⟨q, q', rfl⟩

variable [Fintype C] [Fintype Q]

theorem exists_fan_packing_supported {G : SimpleGraph V} (M : MatchingFactors Q F) (f : C ↪ F)
    (a : C ↪ V) (b : Q ↪ V) (hd : ∀ c q, a c ≠ b q)
    (hc : ∀ c q, G.Adj (a c) (b q)) (hb : ∀ q q', q ≠ q' → G.Adj (b q) (b q'))
    (k : ℕ) (hk : ∀ c, Nat.card (M.graph (f c)).edgeSet = k) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = Fintype.card C * k ∧ FanSupport a b P := by
  classical
  let P := (M.packingFamily f).map (sumEmbedding a b hd) (sumEmbedding_adj a b hd hc hb)
  refine ⟨P.carrier, P.packing, P.card.trans (M.index_card f k hk), ?_⟩
  intro t ht w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  exact fanTriangle_map_support a b hd i.val.1 i.val.2 w hw

omit [DecidableEq C] [DecidableEq Q] [Fintype C] [Fintype Q] in
theorem FanSupport.extend {C' Q' : Type*} {a : C → V} {b : Q → V}
    {a' : C' → V} {b' : Q' → V} {P : Finset (Finset V)}
    (hP : FanSupport a b P) (f : C → C') (g : Q → Q')
    (ha : ∀ c, a c = a' (f c)) (hb : ∀ q, b q = b' (g q)) : FanSupport a' b' P := by
  intro t ht e he
  rcases hP t ht e he with ⟨q, q', hh⟩ | ⟨c, q, hh⟩
  · left
    exact ⟨g q, g q', by simpa [ha, hb] using hh⟩
  · right
    exact ⟨f c, g q, by simpa [ha, hb] using hh⟩

end ResearchMain.Tuza
