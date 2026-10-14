import MainTheorems.Tuza.PerfectFactors

namespace ResearchMain.Tuza

def diagonalGraph {V Q : Type*} (G : SimpleGraph V) : SimpleGraph (V × Q) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 = y.2
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.1⟩

namespace PerfectFactors

variable {V F F' Q : Type*}

def reindex (M : PerfectFactors V F) (f : F' ↪ F) : PerfectFactors V F' where
  graph i := M.graph (f i)
  matching i := M.matching (f i)
  separated i j x y hi hj := f.injective (M.separated (f i) (f j) x y hi hj)
  perfect i := M.perfect (f i)

def diagonal (M : PerfectFactors V F) (Q : Type*) : PerfectFactors (V × Q) F where
  graph i := diagonalGraph (M.graph i)
  matching := by
    intro i x y z hy hz
    exact Prod.ext (M.matching i x.1 y.1 z.1 hy.1 hz.1) (hy.2.symm.trans hz.2)
  separated := by
    intro i j x y hi hj
    exact M.separated i j x.1 y.1 hi.1 hj.1
  perfect := by
    intro i x
    obtain ⟨y, hy⟩ := M.perfect i x.1
    exact ⟨(y, x.2), hy, rfl⟩

theorem diagonal_union_iff (M : PerfectFactors V F) (x y : V × Q) :
    ((M.diagonal Q).unionGraph).Adj x y ↔ M.unionGraph.Adj x.1 y.1 ∧ x.2 = y.2 := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨⟨i, hi.1⟩, hi.2⟩
  · rintro ⟨⟨i, hi⟩, hlabel⟩
    exact ⟨i, hi, hlabel⟩

def sum (M : PerfectFactors V F) (N : PerfectFactors V F')
    (hdis : ∀ i j x y, (M.graph i).Adj x y → ¬(N.graph j).Adj x y) :
    PerfectFactors V (F ⊕ F') where
  graph := Sum.elim M.graph N.graph
  matching := by intro i; cases i with | inl i => exact M.matching i | inr i => exact N.matching i
  separated := by
    intro i j x y hi hj
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (M.separated i j x y hi hj)
      | inr j => exact False.elim (hdis i j x y hi hj)
    | inr i =>
      cases j with
      | inl j => exact False.elim (hdis j i x y hj hi)
      | inr j => exact congrArg Sum.inr (N.separated i j x y hi hj)
  perfect := by intro i; cases i with | inl i => exact M.perfect i | inr i => exact N.perfect i

theorem sum_union_iff (M : PerfectFactors V F) (N : PerfectFactors V F')
    (hdis : ∀ i j x y, (M.graph i).Adj x y → ¬(N.graph j).Adj x y) (x y : V) :
    (M.sum N hdis).unionGraph.Adj x y ↔ M.unionGraph.Adj x y ∨ N.unionGraph.Adj x y := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl i => exact Or.inl ⟨i, hi⟩
    | inr i => exact Or.inr ⟨i, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨Sum.inr i, hi⟩

end PerfectFactors
end ResearchMain.Tuza
