import ThagomizerTuran.IncidenceDefinitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-! The fan is the join of one apex with the path on `n` vertices.
Its invariant is evaluated on actual connectivity flats. -/
namespace Fan

abbrev Vertex (n : ℕ) := Option (Fin n)

def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj v w := match v,w with
    | none, some _ => True
    | some _, none => True
    | some i, some j => i.val+1=j.val ∨ j.val+1=i.val
    | none, none => False
  symm := ⟨by intro v w; cases v <;> cases w <;> simp [or_comm]⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

def spoke {n : ℕ} (i : Fin n) : Sym2 (Vertex n) := s(none,some i)
def rim {n : ℕ} (i j : Fin n) : Sym2 (Vertex n) := s(some i,some j)

def IsGraphicFlat {V : Type*} (G : SimpleGraph V) (F : Set (Sym2 V)) : Prop :=
  F ⊆ G.edgeSet ∧ ∀ v w, G.Adj v w →
    (SimpleGraph.fromEdgeSet F).Reachable v w → s(v,w) ∈ F

noncomputable def graphicRank {V : Type*} [Fintype V] (F : Set (Sym2 V)) : ℕ :=
  Fintype.card V - Nat.card (SimpleGraph.fromEdgeSet F).ConnectedComponent

abbrev GraphicFlat (n : ℕ) := {F : Set (Sym2 (Vertex n)) // IsGraphicFlat (graph n) F}
noncomputable instance (n : ℕ) : Fintype (GraphicFlat n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : DecidableEq (GraphicFlat n) := Classical.decEq _
noncomputable instance (n : ℕ) : LocallyFiniteOrder (GraphicFlat n) := by
  classical
  exact Fintype.toLocallyFiniteOrder

theorem isGraphicFlat_empty (n : ℕ) : IsGraphicFlat (graph n) ∅ := by
  refine ⟨Set.empty_subset _, ?_⟩
  intro v w hadj hreach
  rw [SimpleGraph.fromEdgeSet_empty, SimpleGraph.reachable_bot] at hreach
  exact False.elim (hadj.ne hreach)

def bottomFlat (n : ℕ) : GraphicFlat n := ⟨∅,isGraphicFlat_empty n⟩
def topFlat (n : ℕ) : GraphicFlat n :=
  ⟨(graph n).edgeSet, Set.Subset.rfl, fun _ _ h _ => h⟩

noncomputable def inverseZ (n : ℕ) : Polynomial ℤ :=
  MatroidInverseZ.inverseZ (fun F : GraphicFlat n => graphicRank F.val)
    (bottomFlat n) (topFlat n)

/-- The local triangle closure condition, stated on actual selected edges. -/
def TriangleClosed {n : ℕ} (F : Set (Sym2 (Vertex n))) : Prop :=
  ∀ i j : Fin n, i.val+1=j.val →
    (rim i j ∈ F → (spoke i ∈ F ↔ spoke j ∈ F)) ∧
    (spoke i ∈ F → spoke j ∈ F → rim i j ∈ F)

theorem selected_spoke_reachable {n : ℕ} {F : Set (Sym2 (Vertex n))}
    {i : Fin n} (hi : spoke i ∈ F) :
    (SimpleGraph.fromEdgeSet F).Reachable none (some i) := by
  exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj F).mpr ⟨hi, by simp⟩)

theorem selected_rim_reachable {n : ℕ} {F : Set (Sym2 (Vertex n))}
    {i j : Fin n} (hij : i.val+1=j.val) (hi : rim i j ∈ F) :
    (SimpleGraph.fromEdgeSet F).Reachable (some i) (some j) := by
  apply SimpleGraph.Adj.reachable
  apply (SimpleGraph.fromEdgeSet_adj F).mpr
  refine ⟨hi, ?_⟩
  intro h
  have := congrArg Fin.val (Option.some.inj h)
  omega

theorem IsGraphicFlat.triangleClosed {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) : TriangleClosed F := by
  intro i j hij
  constructor
  · intro hr
    constructor
    · intro hi
      exact hF.2 none (some j) trivial
        ((selected_spoke_reachable hi).trans (selected_rim_reachable hij hr))
    · intro hj
      exact hF.2 none (some i) trivial
        ((selected_spoke_reachable hj).trans (selected_rim_reachable hij hr).symm)
  · intro hi hj
    exact hF.2 (some i) (some j) (Or.inl hij)
      ((selected_spoke_reachable hi).symm.trans (selected_spoke_reachable hj))

end Fan
