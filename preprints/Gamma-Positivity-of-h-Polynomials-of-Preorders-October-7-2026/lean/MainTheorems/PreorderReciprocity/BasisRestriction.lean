import MainTheorems.PreorderGamma.PositiveDemandBases
import MainTheorems.PreorderGamma.TransportPotentials

namespace ResearchMain.PreorderReciprocity

open scoped BigOperators
open PreorderGamma

variable {L R : Type*} [Fintype L] [Fintype R]

def basisRelation (r : L → R → Prop) (B : Finset R) (a : L) (b : R) : Prop :=
  r a b ∧ b ∈ B

theorem basis_one_demand (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    IsDemand (basisRelation r B.val) (fun _ => 1) := by
  classical
  obtain ⟨f, hf⟩ := B.property.2
  have htrans : HasTransversal (basisRelation r B.val) := by
    refine ⟨fun a => (f.symm a).val, ?_, ?_⟩
    · intro a c h
      exact f.symm.injective (Subtype.ext h)
    · intro a
      exact ⟨by simpa only [f.apply_symm_apply] using hf (f.symm a),
        (f.symm a).property⟩
  intro A
  simpa using (hasTransversal_iff_hall _).mp htrans A

noncomputable def basisOneTransport (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    NaturalTransport (augmentedRelation (basisRelation r B.val))
      (scaledDemand (R := R) (positiveDemandScale L) (fun _ => 1))
      (fun _ : R => positiveDemandScale L) :=
  Classical.choose (scaled_minimum_tree_exists (basisRelation r B.val) (fun _ => 1)
    (basis_one_demand r B) (fun _ => Nat.zero_lt_one)
    (positiveDemandScale L) positiveDemandScale_gt_card)

theorem basisOneTransport_minimum (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    ∀ q : NaturalTransport (augmentedRelation (basisRelation r B.val))
      (scaledDemand (R := R) (positiveDemandScale L) (fun _ => 1))
      (fun _ : R => positiveDemandScale L),
      transportCost (basisOneTransport r B) ≤ transportCost q :=
  (Classical.choose_spec (scaled_minimum_tree_exists (basisRelation r B.val) (fun _ => 1)
    (basis_one_demand r B) (fun _ => Nat.zero_lt_one)
    (positiveDemandScale L) positiveDemandScale_gt_card)).1

theorem basisOneTransport_tree (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    (transportSupportGraph (basisOneTransport r B)).IsTree :=
  (Classical.choose_spec (scaled_minimum_tree_exists (basisRelation r B.val) (fun _ => 1)
    (basis_one_demand r B) (fun _ => Nat.zero_lt_one)
    (positiveDemandScale L) positiveDemandScale_gt_card)).2

theorem basisOneTransport_original_outside (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (a : L) (b : R)
    (hb : b ∉ B.val) : (basisOneTransport r B).flow (some a) b = 0 :=
  (basisOneTransport r B).supported (some a) b (fun h => hb h.2)

theorem basisOneTransport_dummy_outside (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (b : R)
    (hb : b ∉ B.val) :
    (basisOneTransport r B).flow none b = positiveDemandScale L := by
  have h := (basisOneTransport r B).column_sum b
  rw [Fintype.sum_option] at h
  simp only [basisOneTransport_original_outside r B _ b hb, Finset.sum_const_zero,
    add_zero] at h
  exact h

theorem basisOneTransport_columnRows_outside (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (b : R)
    (hb : b ∉ B.val) :
    transportColumnRows (basisOneTransport r B) b = {none} := by
  classical
  ext a
  rw [mem_transportColumnRows]
  cases a with
  | none =>
    rw [basisOneTransport_dummy_outside r B b hb]
    simp [positiveDemandScale]
  | some a =>
    rw [basisOneTransport_original_outside r B a b hb]
    simp

theorem basisOneTransport_split (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    transportSplitColumns (basisOneTransport r B) = B.val := by
  classical
  have hsub : transportSplitColumns (basisOneTransport r B) ⊆ B.val := by
    intro b hb
    by_contra hnot
    have hc := mem_transportSplitColumns.mp hb
    rw [basisOneTransport_columnRows_outside r B b hnot, Finset.card_singleton] at hc
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [scaled_split_columns_card (basisRelation r B.val) (fun _ => 1)
    (fun _ => Nat.zero_lt_one) (positiveDemandScale L) positiveDemandScale_gt_card
    (basisOneTransport r B) (basisOneTransport_tree r B)]
  exact B.property.1.le

theorem basisOneTransport_original_split_sum (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (a : L) :
    (∑ b ∈ B.val, (basisOneTransport r B).flow (some a) b) =
      positiveDemandScale L - 1 := by
  classical
  calc
    _ = ∑ b, (basisOneTransport r B).flow (some a) b :=
      Finset.sum_subset (Finset.subset_univ B.val)
        (fun b _ hb => basisOneTransport_original_outside r B a b hb)
    _ = _ := by simpa only [scaledDemand, mul_one] using
      (basisOneTransport r B).row_sum (some a)

theorem basisOneTransport_dummy_split_sum (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    (∑ b ∈ B.val, (basisOneTransport r B).flow none b) = Fintype.card L := by
  classical
  have htotal :
      (∑ a : Option L, ∑ b ∈ B.val, (basisOneTransport r B).flow a b) =
        positiveDemandScale L * Fintype.card L := by
    rw [Finset.sum_comm]
    simp_rw [(basisOneTransport r B).column_sum]
    simp only [Finset.sum_const, nsmul_eq_mul, B.property.1, Nat.cast_id]
    exact Nat.mul_comm _ _
  rw [Fintype.sum_option] at htotal
  simp_rw [basisOneTransport_original_split_sum r B] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at htotal
  have hk : 1 ≤ positiveDemandScale L := by simp [positiveDemandScale]
  have hmul := congrArg (fun t => Fintype.card L * t) (Nat.sub_add_cancel hk)
  simp only [Nat.mul_add, mul_one] at hmul
  rw [Nat.mul_comm (Fintype.card L) (positiveDemandScale L)] at hmul
  omega

end ResearchMain.PreorderReciprocity
