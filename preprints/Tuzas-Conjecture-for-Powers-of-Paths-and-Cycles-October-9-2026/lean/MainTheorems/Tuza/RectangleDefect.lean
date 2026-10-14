import MainTheorems.Tuza.IntervalRectangles
import MainTheorems.Tuza.DenseCover

namespace ResearchMain.Tuza.FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

def prefixUnion (x y : ℕ) : Fin a ⊕ Fin b → Prop :=
  Sum.elim (fun i => i.val < x) (fun j => j.val < y)

instance (x y : ℕ) : DecidablePred (prefixUnion (a := a) (b := b) x y) := by
  intro v
  cases v <;> unfold prefixUnion <;> dsimp <;> infer_instance

def prefixClique (x y : ℕ) : SimpleGraph (Fin a ⊕ Fin b) :=
  withinGraph (prefixUnion x y)

instance (x y : ℕ) : DecidableRel (prefixClique (a := a) (b := b) x y).Adj := by
  unfold prefixClique
  infer_instance

def lowerCrossGraph (r t : ℕ) : SimpleGraph (Fin a ⊕ Fin b) :=
  crossRelationGraph (fun i j => j.val < d.degree i ∧ r ≤ i.val ∧ t ≤ j.val)

instance (r t : ℕ) : DecidableRel (d.lowerCrossGraph r t).Adj := by
  unfold lowerCrossGraph
  infer_instance

theorem lowerCrossGraph_card (r t : ℕ) :
    (d.lowerCrossGraph r t).edgeFinset.card = d.lowerCrossCount r t := by
  apply crossRelationGraph_card

theorem lowerCrossGraph_le (r t : ℕ) : d.lowerCrossGraph r t ≤ d.graph := by
  intro u v huv
  cases u <;> cases v
  · exact False.elim huv
  · exact huv.1
  · exact huv.1
  · exact False.elim huv

theorem rectangle_defect_bound (r t x y : ℕ) (hrx : r ≤ x) (hxa : x ≤ a)
    (hty : t ≤ y) (hyb : y ≤ b)
    (hxt : ∀ i : Fin a, i.val < x → t ≤ d.degree i)
    (hry : ∀ i : Fin a, i.val < r → y ≤ d.degree i)
    (hlow : ∀ i : Fin a, r ≤ i.val → d.degree i ≤ y)
    (hhigh : ∀ i : Fin a, t ≤ d.degree i → i.val < x) :
    ((prefixClique (a := a) (b := b) x y).edgeFinset \ d.graph.edgeFinset).card +
      d.lowerCrossCount r t ≤ (x - r) * (y - t) := by
  let H := prefixClique (a := a) (b := b) x y
  let M := H.edgeFinset \ d.graph.edgeFinset
  let E := (d.lowerCrossGraph r t).edgeFinset
  let R := crossRelationGraph (intervalRectangle a b r t x y)
  have hm : M ⊆ R.edgeFinset := by
    intro e he
    obtain ⟨heH, heG⟩ := Finset.mem_sdiff.mp he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hh : H.Adj u v := H.mem_edgeFinset.mp heH
      have hn : ¬ d.graph.Adj u v := fun h => heG (d.graph.mem_edgeFinset.mpr h)
      apply R.mem_edgeFinset.mpr
      cases u with
      | inl i =>
        cases v with
        | inl j => exact False.elim (hn (fun hij => hh.1 (congrArg Sum.inl hij)))
        | inr j =>
          change (Sum.inl i ≠ Sum.inr j ∧ i.val < x ∧ j.val < y) at hh
          change ¬ j.val < d.degree i at hn
          change r ≤ i.val ∧ i.val < x ∧ t ≤ j.val ∧ j.val < y
          have hi := hxt i
          have hj := hry i
          omega
      | inr j =>
        cases v with
        | inl i =>
          change (Sum.inr j ≠ Sum.inl i ∧ j.val < y ∧ i.val < x) at hh
          change ¬ j.val < d.degree i at hn
          change r ≤ i.val ∧ i.val < x ∧ t ≤ j.val ∧ j.val < y
          have hi := hxt i
          have hj := hry i
          omega
        | inr i => exact False.elim (hn (fun hji => hh.1 (congrArg Sum.inr hji)))
  have he : E ⊆ R.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hh : (d.lowerCrossGraph r t).Adj u v := (d.lowerCrossGraph r t).mem_edgeFinset.mp he
      apply R.mem_edgeFinset.mpr
      cases u with
      | inl i =>
        cases v with
        | inl j => exact False.elim hh
        | inr j =>
          change j.val < d.degree i ∧ r ≤ i.val ∧ t ≤ j.val at hh
          change r ≤ i.val ∧ i.val < x ∧ t ≤ j.val ∧ j.val < y
          have hi := hlow i
          have hj := hhigh i
          omega
      | inr j =>
        cases v with
        | inl i =>
          change j.val < d.degree i ∧ r ≤ i.val ∧ t ≤ j.val at hh
          change r ≤ i.val ∧ i.val < x ∧ t ≤ j.val ∧ j.val < y
          have hi := hlow i
          have hj := hhigh i
          omega
        | inr i => exact False.elim hh
  have hd : Disjoint M E := by
    apply Finset.disjoint_left.mpr
    intro e hm he
    exact (Finset.mem_sdiff.mp hm).2
      (d.graph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono (d.lowerCrossGraph_le r t)
        ((d.lowerCrossGraph r t).mem_edgeFinset.mp he)))
  have hc := Finset.card_le_card (Finset.union_subset hm he)
  rw [Finset.card_union_of_disjoint hd, d.lowerCrossGraph_card r t,
    intervalRectangle_card a b r t x y hrx hxa hty hyb] at hc
  exact hc

end ResearchMain.Tuza.FerrersProfile
