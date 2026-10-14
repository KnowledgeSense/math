import MainTheorems.PreorderGamma.TransportBases
import MainTheorems.PreorderGamma.PositivePatternDemands
import MainTheorems.PreorderGamma.PerfectSubsetCount

namespace ResearchMain.PreorderGamma

open PreorderReciprocity

variable {L R : Type*} [Fintype L] [Fintype R]

def positiveDemandScale (L : Type*) [Fintype L] : ℕ := 2 * Fintype.card L + 1

theorem positiveDemandScale_gt_card : Fintype.card L < positiveDemandScale L := by
  unfold positiveDemandScale
  omega

noncomputable def positiveDemandTransport (r : L → R → Prop) (x : PositiveDemand r) :
    NaturalTransport (augmentedRelation r)
      (scaledDemand (R := R) (positiveDemandScale L) (fun a => (x.val a).val))
      (fun _ : R => positiveDemandScale L) :=
  Classical.choose (scaled_minimum_tree_exists r (fun a => (x.val a).val)
    x.property.1 x.property.2 (positiveDemandScale L) positiveDemandScale_gt_card)

theorem positiveDemandTransport_minimum (r : L → R → Prop) (x : PositiveDemand r) :
    ∀ q : NaturalTransport (augmentedRelation r)
      (scaledDemand (R := R) (positiveDemandScale L) (fun a => (x.val a).val))
      (fun _ : R => positiveDemandScale L),
      transportCost (positiveDemandTransport r x) ≤ transportCost q :=
  (Classical.choose_spec (scaled_minimum_tree_exists r (fun a => (x.val a).val)
    x.property.1 x.property.2 (positiveDemandScale L) positiveDemandScale_gt_card)).1

theorem positiveDemandTransport_tree (r : L → R → Prop) (x : PositiveDemand r) :
    (transportSupportGraph (positiveDemandTransport r x)).IsTree :=
  (Classical.choose_spec (scaled_minimum_tree_exists r (fun a => (x.val a).val)
    x.property.1 x.property.2 (positiveDemandScale L) positiveDemandScale_gt_card)).2

noncomputable def positiveDemandBase (r : L → R → Prop) (x : PositiveDemand r) :
    MatchedSupport (fun b : R => fun a : L => r a b) := by
  classical
  let p := positiveDemandTransport r x
  have ht := positiveDemandTransport_tree r x
  refine ⟨transportSplitColumns p, ?_⟩
  constructor
  · exact scaled_split_columns_card r (fun a => (x.val a).val) x.property.2
      (positiveDemandScale L) positiveDemandScale_gt_card p ht
  · obtain ⟨f, hf⟩ := scaled_split_columns_hasPerfectMatching r (fun a => (x.val a).val)
      x.property.2 (positiveDemandScale L) positiveDemandScale_gt_card p ht
    refine ⟨f.symm, ?_⟩
    intro b
    have h := hf (f.symm b)
    simpa only [f.apply_symm_apply] using h

theorem positiveDemandBase_underlying (r : L → R → Prop) (x : PositiveDemand r) :
    (positiveDemandBase r x).val = transportSplitColumns (positiveDemandTransport r x) := by
  classical
  unfold positiveDemandBase
  rfl

end ResearchMain.PreorderGamma
