import TerminalLogConcavity.WeightedPath
import TerminalLogConcavity.SiteEnvelope

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

theorem weightedPath_scale_vertices {α : Type*} (l : List α) (w : α → ℕ[X] × ℕ[X]) (R : α → ℕ[X]) :
    weightedPath (l.map (fun x => (R x * (w x).1,R x * (w x).2))) =
      ((l.map R).prod * (weightedPath (l.map w)).1,
       (l.map R).prod * (weightedPath (l.map w)).2) := by
  induction l with
  | nil => simp [weightedPath,weightedPathFrom]
  | cons x l ih =>
    simp only [List.map_cons,List.prod_cons,weightedPath,weightedPathFrom] at ih ⊢
    rw [ih]
    congr 1 <;> ring

theorem linearProduct_flatMap {α : Type*} (l : List α) (f : α → List ℕ) :
    linearProduct (l.flatMap f) = (l.map (fun x => linearProduct (f x))).prod := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons,linearProduct_append,ih,List.map_cons,List.prod_cons]

theorem weightedPath_envelope {α : Type*} (l : List α) (w m : α → ℕ[X] × ℕ[X]) (R : α → List ℕ)
    (h : ∀ x ∈ l, CoeffLE (w x).1 (linearProduct (R x) * (m x).1) ∧
      CoeffLE (w x).2 (linearProduct (R x) * (m x).2)) :
    CoeffLE (weightedPath (l.map w)).1
      (linearProduct (l.flatMap R) * (weightedPath (l.map m)).1) := by
  rw [linearProduct_flatMap]
  have he : List.Forall₂ (fun x y => CoeffLE x.1 y.1 ∧ CoeffLE x.2 y.2)
      (l.map w) (l.map (fun x => (linearProduct (R x)*(m x).1,linearProduct (R x)*(m x).2))) := by
    induction l with
    | nil => exact .nil
    | cons x l ih => exact .cons (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
  have hh := (weightedPath_mono he).1
  rw [weightedPath_scale_vertices] at hh
  exact hh

inductive ChainNode where
  | site (index : ℕ)
  | coupler

def chainNodes (q : ℕ) : List ChainNode :=
  ((List.range q).map (fun k => ChainNode.site (k+1))).intersperse .coupler
noncomputable def ChainNode.decoration (q t i : ℕ) : ChainNode → Decoration
  | .site k => siteDecoration q t i k
  | .coupler => couplerDecoration q t
noncomputable def ChainNode.upperWeight (q t i : ℕ) : ChainNode → ℕ[X] × ℕ[X]
  | .site k => upperSiteWeight q t i k
  | .coupler => upperCouplerWeight q t
noncomputable def ChainNode.envelopeWeights (q t i : ℕ) : ChainNode → List ℕ
  | .site k => siteEnvelopeWeights q t i k
  | .coupler => couplerEnvelopeWeights q t

noncomputable def upperChain (q t i : ℕ) : ℕ[X] :=
  (weightedPath ((chainNodes q).map (ChainNode.upperWeight q t i))).1
noncomputable def chainEnvelopeWeights (q t i : ℕ) : List ℕ :=
  (chainNodes q).flatMap (ChainNode.envelopeWeights q t i)

theorem chain_nodes_decorations (q t i : ℕ) :
    (chainNodes q).map (ChainNode.decoration q t i) = chainDecorations q t i := by
  simp only [chainNodes,map_intersperse,List.map_map,Function.comp_def,ChainNode.decoration,chainDecorations]

theorem chain_common_envelope (q t i : ℕ) :
    CoeffLE (pathStateSum (chainDecorations q t i)).1
      (linearProduct (chainEnvelopeWeights q t i) * upperChain q t i) := by
  rw [← chain_nodes_decorations,pathStateSum_eq_weightedPath,List.map_map]
  apply weightedPath_envelope
  intro v _
  cases v with
  | site k =>
    simp only [Function.comp_def,ChainNode.decoration,siteDecoration,interfaceDecoration_A,
      interfaceDecoration_B,ChainNode.upperWeight,upperSiteWeight,ChainNode.envelopeWeights,siteEnvelopeWeights]
    exact interface_envelope _ _
  | coupler =>
    simp only [Function.comp_def,ChainNode.decoration,couplerDecoration,Block.decoration_A,
      Block.decoration_B,ChainNode.upperWeight,upperCouplerWeight,ChainNode.envelopeWeights,couplerEnvelopeWeights,mul_one]
    have h := (Block.scaled t (2*baseCoupling q)).node_envelope
    simpa only [mul_comm] using h

end TerminalLogConcavity
