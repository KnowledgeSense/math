import MeanMaximumForests.Witness
import MeanMaximumForests.GraphRelabeling
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace MeanMaximumForests

/-- Ratios for all nonempty finite trees, independently of vertex labeling. -/
def treeRatios : Set ℝ := {r | ∃ (V : Type) (i : Fintype V) (G : SimpleGraph V),
  G.IsTree ∧ r = @graphMean V G i / G.indepNum}

/-- The limiting-peak candidate from the release: the infimum of the tree ratios. -/
noncomputable def beta : ℝ := sInf treeRatios

theorem witness_ratio_mem : graphMean Witness.tree.graph / Witness.tree.graph.indepNum ∈ treeRatios :=
  ⟨Witness.tree.Vertex, inferInstance, Witness.tree.graph, Witness.graph_isTree, rfl⟩

theorem treeRatios_nonempty : treeRatios.Nonempty := ⟨_, witness_ratio_mem⟩

theorem treeRatios_bddBelow : BddBelow treeRatios := by
  refine ⟨0, ?_⟩
  rintro r ⟨V, i, G, hG, rfl⟩
  exact div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- The release's strict upper bound for the infimum follows from the actual witness tree. -/
theorem beta_lt : beta < (473403 / 1000000 : ℝ) :=
  (csInf_le treeRatios_bddBelow witness_ratio_mem).trans_lt Witness.graph_ratio_lt

/-- The independence number of a finite nonempty graph is positive. -/
theorem indepNum_pos {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) : 0 < G.indepNum := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  have hi : Independent G {v} := by
    intro u hu w hw
    have hu' : u = v := Finset.mem_singleton.mp hu
    have hw' : w = v := Finset.mem_singleton.mp hw
    subst u
    subst w
    exact G.irrefl
  have hl := independent_card_le G Finset.univ (Finset.subset_univ {v}) hi
  rw [independenceNumber_univ G] at hl
  simp only [Finset.card_singleton] at hl
  omega

/-- Any invariant-cone lower bound applies to the infimum over actual finite trees. -/
theorem beta_lower_bound {c : ℝ} {C : Bool → Set ConeVector} (hc : InvariantConditions c C) : c ≤ beta := by
  apply le_csInf treeRatios_nonempty
  rintro r ⟨V, i, G, hG, rfl⟩
  let := i
  let := hG.connected.nonempty
  have ha : (0 : ℝ) < G.indepNum := Nat.cast_pos.mpr (indepNum_pos G)
  apply (le_div_iff₀ ha).mpr
  classical
  exact graphMean_lower_bound G hc hG.isAcyclic

/-- Relabeling by `Fin` places every finite tree, in any universe, in the defining set. -/
theorem tree_ratio_mem {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    graphMean G / G.indepNum ∈ treeRatios := by
  let e := (Fintype.equivFin V).symm
  let H := G.comap e
  let f : H ≃g G := SimpleGraph.Iso.comap e G
  refine ⟨Fin (Fintype.card V), inferInstance, H, f.isTree_iff.mpr hG, ?_⟩
  rw [graphMean_iso f, indepNum_iso f]

theorem beta_le_tree_ratio {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    beta ≤ graphMean G / G.indepNum := csInf_le treeRatios_bddBelow (tree_ratio_mem G hG)

/-- Component additivity transfers the tree infimum to all forests. -/
theorem ForestRealization.beta_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {s rs : Finset V} {A : ForestExpr} (h : ForestRealization G s rs A) :
    beta * independenceNumber G s ≤ meanIndependentSetSize G s := by
  induction h with
  | empty => simp [meanIndependentSetSize]
  | union hd he hA hB ihA ihB =>
    rw [independenceNumber_union G hd he, meanIndependentSetSize_union G hd he]
    push_cast
    nlinarith
  | @root s rs A r hr he hA ih =>
    have hT := A.root_graph_isTree
    have hb := beta_le_tree_ratio (ForestExpr.root A).graph hT
    have ha : (0 : ℝ) < (ForestExpr.root A).graph.indepNum := Nat.cast_pos.mpr (indepNum_pos _)
    have hb' := (le_div_iff₀ ha).mp hb
    rw [(ForestExpr.root A).graphMean_statistics, (ForestExpr.root A).graph_indepNum_statistics] at hb'
    have hroot := ForestRealization.root r hr he hA
    rw [hroot.alpha_statistics G]
    unfold meanIndependentSetSize
    rw [hroot.count_statistics G, hroot.sizeSum_statistics G]
    exact hb'

/-- Every finite forest has normalized mean at least the infimum over finite trees. -/
theorem forest_beta_bound {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    beta * G.indepNum ≤ graphMean G := by
  classical
  obtain ⟨rs, A, hA⟩ := exists_forestRealization G hG Finset.univ
  rw [← independenceNumber_univ G]
  exact hA.beta_bound G

end MeanMaximumForests
