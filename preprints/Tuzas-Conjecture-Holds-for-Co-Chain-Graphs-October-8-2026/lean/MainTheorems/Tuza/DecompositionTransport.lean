import MainTheorems.Tuza.DecompositionAssembly
import MainTheorems.Tuza.FactorOperations

namespace ResearchMain.Tuza

theorem imageGraph_eq_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : imageGraph G f.toEquiv.toEmbedding = H := by
  ext x y
  constructor
  · rintro ⟨u, v, rfl, rfl, huv⟩
    exact f.map_rel_iff.mpr huv
  · intro hxy
    refine ⟨f.symm x, f.symm y, f.toEquiv.apply_symm_apply x, f.toEquiv.apply_symm_apply y, ?_⟩
    exact f.symm.map_rel_iff.mpr hxy

theorem TriangleDecomposition.congr {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (D : TriangleDecomposition G) (f : G ≃g H) :
    Nonempty (TriangleDecomposition H) := by
  have h := D.map f.toEquiv.toEmbedding
  rwa [imageGraph_eq_of_iso f] at h

namespace PerfectFactors

variable {V W F F' : Type*}

def congr (M : PerfectFactors V F) (e : V ≃ W) : PerfectFactors W F where
  graph i := (M.graph i).comap e.symm
  matching := by
    intro i x y z hy hz
    exact e.symm.injective (M.matching i (e.symm x) (e.symm y) (e.symm z) hy hz)
  separated := by
    intro i j x y hi hj
    exact M.separated i j (e.symm x) (e.symm y) hi hj
  perfect := by
    intro i x
    obtain ⟨y, hy⟩ := M.perfect i (e.symm x)
    exact ⟨e y, by simpa using hy⟩

theorem congr_union_iff (M : PerfectFactors V F) (e : V ≃ W) (x y : W) :
    (M.congr e).unionGraph.Adj x y ↔ M.unionGraph.Adj (e.symm x) (e.symm y) := Iff.rfl

theorem reindex_equiv_union_iff (M : PerfectFactors V F) (e : F' ≃ F) (x y : V) :
    (M.reindex e.toEmbedding).unionGraph.Adj x y ↔ M.unionGraph.Adj x y := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨e.symm i, ?_⟩
    change (M.graph (e (e.symm i))).Adj x y
    rw [e.apply_symm_apply]
    exact hi

end PerfectFactors

theorem FactorDecomposition.congr {V W F F' : Type*} [DecidableEq V] [DecidableEq W]
    (D : FactorDecomposition V F) (e : V ≃ W) (f : F ≃ F') :
    Nonempty (FactorDecomposition W F') := by
  let N := (D.factors.congr e).reindex f.symm.toEmbedding
  let g : (⊤ \ D.factors.unionGraph) ≃g (⊤ \ N.unionGraph) := {
    toEquiv := e
    map_rel_iff' := by
      intro x y
      change (e x ≠ e y ∧ ¬N.unionGraph.Adj (e x) (e y)) ↔
        x ≠ y ∧ ¬D.factors.unionGraph.Adj x y
      have hu := (D.factors.congr e).reindex_equiv_union_iff f.symm (e x) (e y)
      have hc := D.factors.congr_union_iff e (e x) (e y)
      have hiff : N.unionGraph.Adj (e x) (e y) ↔ D.factors.unionGraph.Adj x y := by
        simpa using hu.trans hc
      rw [hiff, ne_eq, e.injective.eq_iff]
  }
  obtain ⟨E⟩ := D.triangles.congr g
  exact ⟨⟨N, E⟩⟩

theorem FactorDecomposition.toFinite {V F : Type*} [DecidableEq V] [Fintype V] [Fintype F]
    (D : FactorDecomposition V F) (n k : ℕ) (hv : Fintype.card V = n) (hf : Fintype.card F = k) :
    Nonempty (FactorDecomposition (Fin n) (Fin k)) := by
  classical
  let e : V ≃ Fin n := Fintype.equivOfCardEq (by simpa using hv)
  let f : F ≃ Fin k := Fintype.equivOfCardEq (by simpa using hf)
  exact D.congr e f

end ResearchMain.Tuza
