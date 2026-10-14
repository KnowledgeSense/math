import MainTheorems.Tuza.BlowupDecomposition
import MainTheorems.Tuza.DecompositionTransport

namespace ResearchMain.Tuza

def fiberGraph {I V : Type*} (G : SimpleGraph V) : SimpleGraph (I × V) where
  Adj x y := x.1 = y.1 ∧ G.Adj x.2 y.2
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.2⟩

def fiberEmbedding {I V : Type*} (i : I) : V ↪ (I × V) where
  toFun x := (i, x)
  inj' := by intro x y h; exact congrArg Prod.snd h

theorem image_fiber_iff {I V : Type*} (G : SimpleGraph V) (i : I) (x y : I × V) :
    (imageGraph G (fiberEmbedding i)).Adj x y ↔ x.1 = i ∧ y.1 = i ∧ G.Adj x.2 y.2 := by
  constructor
  · rintro ⟨u, v, rfl, rfl, huv⟩
    exact ⟨rfl, rfl, huv⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨x.2, y.2, Prod.ext hx.symm rfl, Prod.ext hy.symm rfl, hxy⟩

theorem TriangleDecomposition.copies {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph V} (D : TriangleDecomposition G) :
    Nonempty (TriangleDecomposition (fiberGraph (I := I) G)) := by
  classical
  let H (i : I) := imageGraph G (fiberEmbedding i)
  let E (i : I) := Classical.choice (D.map (fiberEmbedding i))
  apply TriangleDecomposition.of_partition H E
  · intro i x y hxy
    obtain ⟨hx, hy, h⟩ := (image_fiber_iff G i x y).mp hxy
    exact ⟨hx.trans hy.symm, h⟩
  · intro i j hij x y hxy hxy'
    have hi := ((image_fiber_iff G i x y).mp hxy).1
    have hj := ((image_fiber_iff G j x y).mp hxy').1
    exact hij (hi.symm.trans hj)
  · intro x y hxy
    exact ⟨x.1, (image_fiber_iff G x.1 x y).mpr ⟨rfl, hxy.1.symm, hxy.2⟩⟩

namespace PerfectFactors

def copies {I V F : Type*} (M : PerfectFactors V F) : PerfectFactors (I × V) F where
  graph i := fiberGraph (M.graph i)
  matching := by
    intro i x y z hy hz
    exact Prod.ext (hy.1.symm.trans hz.1) (M.matching i x.2 y.2 z.2 hy.2 hz.2)
  separated := by
    intro i j x y hi hj
    exact M.separated i j x.2 y.2 hi.2 hj.2
  perfect := by
    intro i x
    obtain ⟨y, hy⟩ := M.perfect i x.2
    exact ⟨(x.1, y), rfl, hy⟩

theorem copies_union_iff {I V F : Type*} (M : PerfectFactors V F) (x y : I × V) :
    M.copies.unionGraph.Adj x y ↔ x.1 = y.1 ∧ M.unionGraph.Adj x.2 y.2 := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨hi.1, i, hi.2⟩
  · rintro ⟨he, i, hi⟩
    exact ⟨i, he, hi⟩

end PerfectFactors

theorem factor_decomposition_of_cross {I Q F : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq Q] (B : TriangleDecomposition (crossGraph (⊤ : SimpleGraph I) Q))
    (E : FactorDecomposition Q F) :
    Nonempty (FactorDecomposition (I × Q) F) := by
  classical
  obtain ⟨C⟩ := E.triangles.copies (I := I)
  have hdis : ∀ x y, (crossGraph (⊤ : SimpleGraph I) Q).Adj x y →
      ¬(fiberGraph (I := I) (⊤ \ E.factors.unionGraph)).Adj x y := by
    intro x y hxy hxy'
    exact hxy hxy'.1
  obtain ⟨T⟩ := B.join C hdis
  have hgraph : crossGraph (⊤ : SimpleGraph I) Q ⊔ fiberGraph (I := I) (⊤ \ E.factors.unionGraph) =
      ⊤ \ E.factors.copies.unionGraph := by
    ext x y
    change ((x.1 ≠ y.1) ∨ (x.1 = y.1 ∧ x.2 ≠ y.2 ∧ ¬E.factors.unionGraph.Adj x.2 y.2)) ↔
      x ≠ y ∧ ¬E.factors.copies.unionGraph.Adj x y
    rw [E.factors.copies_union_iff]
    by_cases hb : x.1 = y.1
    · have hneq : x ≠ y ↔ x.2 ≠ y.2 :=
        ⟨fun h he => h (Prod.ext hb he), fun h he => h (congrArg Prod.snd he)⟩
      tauto
    · have hne : x ≠ y := fun he => hb (congrArg Prod.fst he)
      tauto
  rw [hgraph] at T
  exact ⟨⟨E.factors.copies, T⟩⟩

theorem inflate_complete_decomposition {I Q F : Type*} [Fintype I] [DecidableEq I]
    [Fintype Q] [DecidableEq Q] [AddCommGroup Q]
    (D : TriangleDecomposition (⊤ : SimpleGraph I)) (E : FactorDecomposition Q F) :
    Nonempty (FactorDecomposition (I × Q) F) := by
  obtain ⟨B⟩ := exists_blowup_decomposition (Q := Q) D
  exact factor_decomposition_of_cross B E

end ResearchMain.Tuza
