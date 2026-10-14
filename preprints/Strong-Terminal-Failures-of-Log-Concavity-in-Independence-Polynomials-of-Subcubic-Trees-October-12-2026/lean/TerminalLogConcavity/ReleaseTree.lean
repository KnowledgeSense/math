import TerminalLogConcavity.DecoratedPath
import TerminalLogConcavity.SiteParameters
import TerminalLogConcavity.BlockCard

namespace TerminalLogConcavity
set_option backward.isDefEq.respectTransparency false

noncomputable def siteDecoration (q t i k : ℕ) : Decoration :=
  interfaceDecoration (Block.scaled t (siteParameter q i k))
    (Block.scaled t (interfaceParameter q i))
noncomputable def couplerDecoration (q t : ℕ) : Decoration :=
  (Block.scaled t (2 * baseCoupling q)).decoration

noncomputable def chainDecorations (q t i : ℕ) : List Decoration :=
  ((List.range q).map (fun k => siteDecoration q t i (k + 1))).intersperse (couplerDecoration q t)

/-- The exact ordered site/coupler/bridge skeleton of the release construction. -/
noncomputable def releaseDecorations (q t : ℕ) : List Decoration :=
  (((List.range q).map (fun i => chainDecorations q t (i + 1))).intersperse
    [Block.leaf.decoration]).flatten
noncomputable def releaseForest (q t : ℕ) : ForestExpr := decoratedPath (releaseDecorations q t)
noncomputable def releaseTree (r H : ℕ) : ForestExpr :=
  releaseForest (r + 1) (thresholdIndex (target (r + 1) H))

theorem chainDecorations_nonempty {q : ℕ} (hq : 0 < q) (t i : ℕ) :
    chainDecorations q t i ≠ [] := by
  have hlen : (chainDecorations q t i).length = 2 * q - 1 := by
    simp [chainDecorations]
  intro h
  simp [h] at hlen
  omega

theorem mem_intersperse_of_mem {α : Type*} {l : List α} {x sep : α} (h : x ∈ l) : x ∈ l.intersperse sep := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    cases l with
    | nil => simpa using h
    | cons b l =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · simp [h]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih (List.mem_cons.mpr h)))

theorem releaseDecorations_nonempty {q : ℕ} (hq : 0 < q) (t : ℕ) :
    releaseDecorations q t ≠ [] := by
  cases q with
  | zero => omega
  | succ q =>
    have hmem : chainDecorations (q + 1) t 1 ∈
        (((List.range (q + 1)).map (fun i => chainDecorations (q + 1) t (i + 1))).intersperse
          [Block.leaf.decoration]) := by
      apply mem_intersperse_of_mem
      exact List.mem_map.mpr ⟨0, by simp, rfl⟩
    intro he
    have hc := (List.flatten_eq_nil_iff.mp he) _ hmem
    exact chainDecorations_nonempty (by omega) t 1 hc

theorem releaseTree_isTree (r H : ℕ) : (releaseTree r H).graph.IsTree := by
  have hn := releaseDecorations_nonempty (show 0 < r + 1 by omega) (thresholdIndex (target (r + 1) H))
  unfold releaseTree releaseForest
  generalize he : releaseDecorations (r + 1) (thresholdIndex (target (r + 1) H)) = ds at *
  cases ds with
  | nil => contradiction
  | cons D ds => exact decoratedPath_isTree D ds

theorem releaseTree_subcubic (r H : ℕ) (v : (releaseTree r H).Vertex) :
    ((releaseTree r H).graph.neighborSet v).ncard ≤ 3 :=
  decoratedPath_subcubic _ v

theorem releaseTree_polynomial (r H : ℕ) :
    (pathStateSum (releaseDecorations (r + 1) (thresholdIndex (target (r + 1) H)))).1 =
      Polynomial.reflect (releaseTree r H).graph.indepNum
        (independencePolynomial (releaseTree r H).graph Finset.univ) :=
  pathStateSum_graph _

theorem ForestExpr.card_root (F : ForestExpr) : Fintype.card F.root.Vertex = Fintype.card F.Vertex + 1 := by
  simp [ForestExpr.Vertex]
theorem ForestExpr.card_union (F G : ForestExpr) :
    Fintype.card (F.union G).Vertex = Fintype.card F.Vertex + Fintype.card G.Vertex := by
  simp [ForestExpr.Vertex, Fintype.card_sum]

theorem decoratedPath_card (ds : List Decoration) :
    Fintype.card (decoratedPath ds).Vertex = (ds.map (fun D => Fintype.card D.forest.Vertex + 1)).sum := by
  induction ds with
  | nil => simp [decoratedPath, ForestExpr.Vertex]
  | cons D ds ih =>
    rw [decoratedPath, ForestExpr.card_root, ForestExpr.card_union, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem interface_card (p m : Block) :
    Fintype.card (interfaceForest p m).Vertex = Fintype.card p.Vertex + 2 * Fintype.card m.Vertex + 3 := by
  simp [interfaceForest, interfaceChildren, Block.Vertex]
  omega

end TerminalLogConcavity
