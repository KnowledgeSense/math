import MainTheorems.PreorderReciprocity.PotentialNormalization
import MainTheorems.PreorderGamma.ScaledCore

namespace ResearchMain.PreorderReciprocity

open scoped BigOperators Classical
open PreorderGamma

variable {L R : Type*} [Fintype L] [Fintype R]

theorem positiveDemand_basis_core_flow (r : L → R → Prop) (x : PositiveDemand r)
    (a : Option L) (b : R) :
    (basisOneTransport r (positiveDemandBase r x)).flow a b =
      if b ∈ (positiveDemandBase r x).val then (positiveDemandTransport r x).flow a b
      else a.elim (positiveDemandScale L) (fun _ => 0) := by
  classical
  let p := positiveDemandTransport r x
  let B := positiveDemandBase r x
  have hB : B.val = transportSplitColumns p := positiveDemandBase_underlying r x
  let core := scaledCoreTransport r (fun a => (x.val a).val) x.property.2
    (positiveDemandScale L) positiveDemandScale_gt_card p (positiveDemandTransport_tree r x)
  let q : NaturalTransport (augmentedRelation (basisRelation r B.val))
      (scaledDemand (R := R) (positiveDemandScale L) (fun _ => 1))
      (fun _ : R => positiveDemandScale L) :=
    { flow := core.flow
      supported := by
        intro a b hab
        apply core.supported a b
        change ¬augmentedRelation (fun a b => r a b ∧ b ∈ B.val) a b at hab
        rwa [hB] at hab
      row_sum := core.row_sum
      column_sum := core.column_sum }
  have hqmin : ∀ t : NaturalTransport (augmentedRelation (basisRelation r B.val))
      (scaledDemand (R := R) (positiveDemandScale L) (fun _ => 1))
      (fun _ : R => positiveDemandScale L), transportCost q ≤ transportCost t := by
    intro t
    let u : NaturalTransport
        (augmentedRelation (fun a b => r a b ∧ b ∈ transportSplitColumns p))
        (scaledDemand (R := R) (positiveDemandScale L) (fun _ => 1))
        (fun _ : R => positiveDemandScale L) :=
      { flow := t.flow
        supported := by
          intro a b hab
          apply t.supported a b
          change ¬augmentedRelation (fun a b => r a b ∧ b ∈ B.val) a b
          rw [hB]
          exact hab
        row_sum := t.row_sum
        column_sum := t.column_sum }
    exact scaledCoreTransport_minimum r (fun a => (x.val a).val) x.property.2
      (positiveDemandScale L) positiveDemandScale_gt_card p
      (positiveDemandTransport_minimum r x) (positiveDemandTransport_tree r x) u
  have heq : q = basisOneTransport r B := by
    apply transportCost_injective
    exact le_antisymm (hqmin _) (basisOneTransport_minimum r B q)
  calc
    _ = q.flow a b := congrArg (fun t => t.flow a b) heq.symm
    _ = _ := by
      change core.flow a b = _
      rw [scaledCoreTransport_flow, ← hB]

theorem positiveDemand_basis_rowPotential (r : L → R → Prop) (x : PositiveDemand r)
    (a : Option L) :
    basisRowPotential r (positiveDemandBase r x) a =
      transportTreeVertexPotential (positiveDemandTransport r x) (positiveDemandTransport_tree r x)
        (Sum.inl none) (Sum.inl a) -
      transportTreeVertexPotential (positiveDemandTransport r x) (positiveDemandTransport_tree r x)
        (Sum.inl none) (Sum.inl none) := by
  classical
  let p := positiveDemandTransport r x
  let B := positiveDemandBase r x
  let α : Option L → ℤ := fun a => transportTreeVertexPotential p
    (positiveDemandTransport_tree r x) (Sum.inl none) (Sum.inl a)
  let β : R → ℤ := fun b => if b ∈ B.val then transportTreeVertexPotential p
    (positiveDemandTransport_tree r x) (Sum.inl none) (Sum.inr b) else
      (transportEdgeWeight (fun _ : R => positiveDemandScale L) (none : Option L) b : ℤ) + α none
  have htight : ∀ c b, 0 < (basisOneTransport r B).flow c b →
      (transportEdgeWeight (fun _ : R => positiveDemandScale L) c b : ℤ) + α c = β b := by
    intro c b hflow
    rw [positiveDemand_basis_core_flow] at hflow
    change 0 < (if b ∈ B.val then p.flow c b
      else c.elim (positiveDemandScale L) (fun _ => 0)) at hflow
    by_cases hb : b ∈ B.val
    · simp only [ite_eq_left hb] at hflow
      simp only [β, ite_eq_left hb, α]
      exact minimum_transport_tree_potential_tight p (positiveDemandTransport_tree r x)
        (Sum.inl none) c b hflow
    · simp only [ite_eq_right hb] at hflow
      cases c with
      | none => simp only [β, ite_eq_right hb]
      | some c => simp only [Option.elim_some] at hflow; omega
  exact transportTreeVertexPotential_of_tight (basisOneTransport r B)
    (basisOneTransport_tree r B) α β htight (Sum.inl none) (Sum.inl a)

theorem basisColumnChoice_forward_positive (r : L → R → Prop) (x : PositiveDemand r)
    (b : R) :
    0 < (positiveDemandTransport r x).flow (basisColumnChoice r (positiveDemandBase r x) b) b := by
  classical
  let p := positiveDemandTransport r x
  let B := positiveDemandBase r x
  let c := basisColumnChoice r B b
  have hc : augmentedRelation r c b := basisColumnChoice_supported r B b
  have hnonempty := transportColumnRows_nonempty p b
    (show 0 < positiveDemandScale L by simp [positiveDemandScale])
  obtain ⟨a, ha⟩ := hnonempty
  have hflow := mem_transportColumnRows.mp ha
  have hrel : augmentedRelation r a b := by
    by_contra h
    have hz := p.supported a b h
    omega
  have hmin := basisColumnChoice_minimum r B b a hrel
  rw [positiveDemand_basis_rowPotential r x c, positiveDemand_basis_rowPotential r x a] at hmin
  have hdual := minimum_transport_tree_potential_dual p (positiveDemandTransport_minimum r x)
    (positiveDemandTransport_tree r x) (Sum.inl none) c b hc
  have htight := minimum_transport_tree_potential_tight p (positiveDemandTransport_tree r x)
    (Sum.inl none) a b hflow
  apply (minimum_transport_tree_potential_tight_iff p (positiveDemandTransport_tree r x)
    (Sum.inl none) c b hc).mp
  linarith

theorem basisColumnChoice_forward_iff (r : L → R → Prop) (x : PositiveDemand r)
    (b : R) (hb : b ∉ (positiveDemandBase r x).val) (a : Option L) :
    basisColumnChoice r (positiveDemandBase r x) b = a ↔
      0 < (positiveDemandTransport r x).flow a b := by
  classical
  let p := positiveDemandTransport r x
  let c := basisColumnChoice r (positiveDemandBase r x) b
  have hc : 0 < p.flow c b := basisColumnChoice_forward_positive r x b
  constructor
  · intro heq
    exact heq ▸ hc
  · intro ha
    have hn : b ∉ transportSplitColumns p := by
      change b ∉ transportSplitColumns (positiveDemandTransport r x)
      rw [← positiveDemandBase_underlying r x]
      exact hb
    have hlow := Finset.card_pos.mpr (transportColumnRows_nonempty p b
      (show 0 < positiveDemandScale L by simp [positiveDemandScale]))
    have hhigh := scaled_column_support_card_le_two r (fun a => (x.val a).val) x.property.2
      (positiveDemandScale L) positiveDemandScale_gt_card p (positiveDemandTransport_tree r x) b
    have hne : (transportColumnRows p b).card ≠ 2 := fun h => hn (mem_transportSplitColumns.mpr h)
    have hcard : (transportColumnRows p b).card ≤ 1 := by omega
    exact Finset.card_le_one.mp hcard c (mem_transportColumnRows.mpr hc)
      a (mem_transportColumnRows.mpr ha)

theorem basisChoiceCount_forward (r : L → R → Prop) (x : PositiveDemand r)
    (a : Option L) :
    basisChoiceCount r (positiveDemandBase r x) a =
      (transportSingletonColumns (positiveDemandTransport r x) a).card := by
  classical
  have hpred : ∀ b : R,
      (b ∉ (positiveDemandBase r x).val ∧ basisColumnChoice r (positiveDemandBase r x) b = a) ↔
      (b ∉ transportSplitColumns (positiveDemandTransport r x) ∧
        0 < (positiveDemandTransport r x).flow a b) := by
    intro b
    constructor
    · rintro ⟨hb, heq⟩
      refine ⟨?_, (basisColumnChoice_forward_iff r x b hb a).mp heq⟩
      simpa only [← positiveDemandBase_underlying r x] using hb
    · rintro ⟨hn, hflow⟩
      have hb : b ∉ (positiveDemandBase r x).val := by
        simpa only [positiveDemandBase_underlying r x] using hn
      exact ⟨hb, (basisColumnChoice_forward_iff r x b hb a).mpr hflow⟩
  unfold basisChoiceCount
  simp_rw [hpred]
  rw [← Finset.card_filter]
  congr 1
  ext b
  simp [transportSingletonColumns]

theorem basisToPositiveDemand_left_inverse (r : L → R → Prop) (x : PositiveDemand r) :
    basisToPositiveDemand r (positiveDemandBase r x) = x := by
  apply Subtype.ext
  funext a
  apply Fin.ext
  change basisExtensionDemand r (positiveDemandBase r x) a = (x.val a).val
  unfold basisExtensionDemand
  rw [basisChoiceCount_forward]
  exact (scaled_demand_eq_one_add_singletons r (fun a => (x.val a).val) x.property.2
    (positiveDemandScale L) positiveDemandScale_gt_card (positiveDemandTransport r x)
    (positiveDemandTransport_tree r x) a).symm

noncomputable def positiveDemandMatchedSupportEquiv (r : L → R → Prop) :
    PositiveDemand r ≃ MatchedSupport (fun b : R => fun a : L => r a b) where
  toFun := positiveDemandBase r
  invFun := basisToPositiveDemand r
  left_inv := basisToPositiveDemand_left_inverse r
  right_inv := basisToPositiveDemand_right_inverse r

theorem positive_demand_matched_support_count (r : L → R → Prop) :
    Fintype.card (PositiveDemand r) =
      Fintype.card (MatchedSupport (fun b : R => fun a : L => r a b)) :=
  Fintype.card_congr (positiveDemandMatchedSupportEquiv r)

theorem supportEnumerator_extreme_coeff_duality (r : L → R → Prop) :
    (supportEnumerator r).coeff (Fintype.card L) =
      (supportEnumerator (fun b : R => fun a : L => r a b)).coeff (Fintype.card L) := by
  rw [← positiveDemand_count, positive_demand_matched_support_count,
    supportEnumerator_maximal_coeff]

end ResearchMain.PreorderReciprocity
