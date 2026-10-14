import MainTheorems.PreorderReciprocity.BasisRestriction
import Mathlib.Data.Set.Finite.Lemmas

namespace ResearchMain.PreorderReciprocity

open scoped BigOperators
open PreorderGamma

variable {L R : Type*} [Fintype L] [Fintype R]

theorem scaled_transport_demand (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) : IsDemand r x := by
  classical
  intro I
  let N := graphNeighbors r I
  have hrow : ∀ a ∈ I, (∑ b ∈ N, p.flow (some a) b) = k * x a - 1 := by
    intro a ha
    calc
      _ = ∑ b, p.flow (some a) b := by
        apply Finset.sum_subset (Finset.subset_univ N)
        intro b _ hb
        apply p.supported (some a) b
        exact fun h => hb (mem_graphNeighbors.mpr ⟨a, ha, h⟩)
      _ = _ := p.row_sum (some a)
  have hcol : ∀ b, (∑ a ∈ I, p.flow (some a) b) ≤ k := by
    intro b
    have hsub : (∑ a ∈ I, p.flow (some a) b) ≤ ∑ a : L, p.flow (some a) b :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ I)
    have hsum := p.column_sum b
    rw [Fintype.sum_option] at hsum
    omega
  have hbound : (∑ a ∈ I, (k * x a - 1)) ≤ k * N.card := by
    calc
      _ = ∑ a ∈ I, ∑ b ∈ N, p.flow (some a) b :=
        Finset.sum_congr rfl fun a ha => (hrow a ha).symm
      _ = ∑ b ∈ N, ∑ a ∈ I, p.flow (some a) b := Finset.sum_comm
      _ ≤ ∑ _b ∈ N, k := Finset.sum_le_sum fun b _ => hcol b
      _ = _ := by simp [Nat.mul_comm]
  rw [scaled_subsum k (by omega) x I (fun a _ => hpos a)] at hbound
  by_contra hnot
  change ¬(∑ a ∈ I, x a) ≤ N.card at hnot
  have hlarge : N.card + 1 ≤ ∑ a ∈ I, x a := by omega
  have hmul := Nat.mul_le_mul_left k hlarge
  rw [Nat.mul_add, mul_one] at hmul
  have hcard := Finset.card_le_univ I
  omega

noncomputable def basisRowPotential (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (a : Option L) : ℤ :=
  transportTreeVertexPotential (basisOneTransport r B) (basisOneTransport_tree r B)
    (Sum.inl none) (Sum.inl a)

noncomputable def basisColumnPotential (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (b : R) : ℤ :=
  transportTreeVertexPotential (basisOneTransport r B) (basisOneTransport_tree r B)
    (Sum.inl none) (Sum.inr b)

theorem basis_column_choice_exists (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (b : R) :
    ∃ a : Option L, augmentedRelation r a b ∧
      ∀ c : Option L, augmentedRelation r c b →
        (transportEdgeWeight (fun _ : R => positiveDemandScale L) a b : ℤ) +
          basisRowPotential r B a ≤
        (transportEdgeWeight (fun _ : R => positiveDemandScale L) c b : ℤ) +
          basisRowPotential r B c := by
  exact Set.exists_min_image {a : Option L | augmentedRelation r a b}
    (fun a => (transportEdgeWeight (fun _ : R => positiveDemandScale L) a b : ℤ) +
      basisRowPotential r B a) (Set.toFinite _) ⟨none, trivial⟩

noncomputable def basisColumnChoice (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (b : R) : Option L :=
  Classical.choose (basis_column_choice_exists r B b)

theorem basisColumnChoice_supported (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (b : R) :
    augmentedRelation r (basisColumnChoice r B b) b :=
  (Classical.choose_spec (basis_column_choice_exists r B b)).1

theorem basisColumnChoice_minimum (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (b : R)
    (a : Option L) (ha : augmentedRelation r a b) :
    (transportEdgeWeight (fun _ : R => positiveDemandScale L)
      (basisColumnChoice r B b) b : ℤ) + basisRowPotential r B (basisColumnChoice r B b) ≤
    (transportEdgeWeight (fun _ : R => positiveDemandScale L) a b : ℤ) +
      basisRowPotential r B a :=
  (Classical.choose_spec (basis_column_choice_exists r B b)).2 a ha

noncomputable def basisChoiceCount (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (a : Option L) : ℕ := by
  classical
  exact ∑ b : R, if b ∉ B.val ∧ basisColumnChoice r B b = a then 1 else 0

theorem basisChoiceCount_total (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    (∑ a : Option L, basisChoiceCount r B a) = Fintype.card R - Fintype.card L := by
  classical
  change (∑ a : Option L, ∑ b : R,
    if b ∉ B.val ∧ basisColumnChoice r B b = a then 1 else 0) =
      Fintype.card R - Fintype.card L
  rw [Finset.sum_comm]
  have hterm : ∀ b : R,
      (∑ a : Option L, if b ∉ B.val ∧ basisColumnChoice r B b = a then 1 else 0) =
        if b ∉ B.val then 1 else 0 := by
    intro b
    by_cases hb : b ∈ B.val <;> simp [hb]
  simp_rw [hterm]
  have hf : (Finset.univ.filter fun b : R => b ∉ B.val) = Finset.univ \ B.val := by
    ext b
    simp
  rw [← Finset.card_filter, hf, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, B.property.1]

noncomputable def basisExtensionDemand (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (a : L) : ℕ :=
  1 + basisChoiceCount r B (some a)

theorem basisExtensionDemand_positive (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (a : L) :
    0 < basisExtensionDemand r B a := by
  unfold basisExtensionDemand
  omega

theorem basisExtensionDemand_complement (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    Fintype.card R - (∑ a : L, basisExtensionDemand r B a) = basisChoiceCount r B none := by
  have h := basisChoiceCount_total r B
  rw [Fintype.sum_option] at h
  have hcard : Fintype.card L ≤ Fintype.card R := by
    rw [← B.property.1]
    exact Finset.card_le_univ _
  have hdem : (∑ a : L, basisExtensionDemand r B a) =
      Fintype.card L + ∑ a : L, basisChoiceCount r B (some a) := by
    simp [basisExtensionDemand, Finset.sum_add_distrib]
  rw [hdem]
  omega

noncomputable def basisExtensionFlow (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (a : Option L) (b : R) : ℕ := by
  classical
  exact if b ∈ B.val then (basisOneTransport r B).flow a b
    else if basisColumnChoice r B b = a then positiveDemandScale L else 0

theorem basisExtensionFlow_row (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (a : Option L) :
    (∑ b : R, basisExtensionFlow r B a b) =
      (∑ b ∈ B.val, (basisOneTransport r B).flow a b) +
        positiveDemandScale L * basisChoiceCount r B a := by
  classical
  have hentry : ∀ b : R, basisExtensionFlow r B a b =
      (if b ∈ B.val then (basisOneTransport r B).flow a b else 0) +
        positiveDemandScale L * (if b ∉ B.val ∧ basisColumnChoice r B b = a then 1 else 0) := by
    intro b
    by_cases hb : b ∈ B.val <;> by_cases ha : basisColumnChoice r B b = a <;>
      simp [basisExtensionFlow, hb, ha]
  simp_rw [hentry]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [basisChoiceCount]
  congr 1
  exact Finset.sum_ite_mem_eq _ _

noncomputable def basisExtensionTransport (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    NaturalTransport (augmentedRelation r)
      (scaledDemand (R := R) (positiveDemandScale L) (basisExtensionDemand r B))
      (fun _ : R => positiveDemandScale L) := by
  classical
  refine ⟨basisExtensionFlow r B, ?_, ?_, ?_⟩
  · intro a b hrel
    by_cases hb : b ∈ B.val
    · have hmask : ¬augmentedRelation (basisRelation r B.val) a b := by
        intro h
        apply hrel
        cases a with
        | none => trivial
        | some a => exact h.1
      simp only [basisExtensionFlow, ite_eq_left hb]
      exact (basisOneTransport r B).supported a b hmask
    · have hchoice : basisColumnChoice r B b ≠ a := by
        intro h
        exact hrel (h ▸ basisColumnChoice_supported r B b)
      simp [basisExtensionFlow, hb, hchoice]
  · intro a
    rw [basisExtensionFlow_row]
    cases a with
    | none =>
      rw [basisOneTransport_dummy_split_sum, scaledDemand,
        basisExtensionDemand_complement]
      exact Nat.add_comm _ _
    | some a =>
      rw [basisOneTransport_original_split_sum]
      change positiveDemandScale L - 1 + positiveDemandScale L * basisChoiceCount r B (some a) =
        positiveDemandScale L * (1 + basisChoiceCount r B (some a)) - 1
      rw [Nat.mul_add, mul_one]
      have hk : 0 < positiveDemandScale L := by simp [positiveDemandScale]
      omega
  · intro b
    by_cases hb : b ∈ B.val
    · simpa only [basisExtensionFlow, ite_eq_left hb] using (basisOneTransport r B).column_sum b
    · simp [basisExtensionFlow, hb]

theorem basisExtensionDemand_demand (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    IsDemand r (basisExtensionDemand r B) :=
  scaled_transport_demand r (basisExtensionDemand r B) (basisExtensionDemand_positive r B)
    (positiveDemandScale L) positiveDemandScale_gt_card (basisExtensionTransport r B)

noncomputable def basisExtensionColumnPotential (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) (b : R) : ℤ := by
  classical
  exact if b ∈ B.val then basisColumnPotential r B b else
    (transportEdgeWeight (fun _ : R => positiveDemandScale L) (basisColumnChoice r B b) b : ℤ) +
      basisRowPotential r B (basisColumnChoice r B b)

theorem basisExtensionTransport_minimum (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    ∀ q : NaturalTransport (augmentedRelation r)
      (scaledDemand (R := R) (positiveDemandScale L) (basisExtensionDemand r B))
      (fun _ : R => positiveDemandScale L),
      transportCost (basisExtensionTransport r B) ≤ transportCost q := by
  classical
  apply transport_potential_certificate_minimum (basisExtensionTransport r B)
    (basisRowPotential r B) (basisExtensionColumnPotential r B)
  · intro a b hab
    by_cases hb : b ∈ B.val
    · have hmask : augmentedRelation (basisRelation r B.val) a b := by
        cases a with
        | none => trivial
        | some a => exact ⟨hab, hb⟩
      simpa only [basisExtensionColumnPotential, ite_eq_left hb,
        basisRowPotential, basisColumnPotential] using
        minimum_transport_tree_potential_dual (basisOneTransport r B)
          (basisOneTransport_minimum r B) (basisOneTransport_tree r B) (Sum.inl none) a b hmask
    · simpa only [basisExtensionColumnPotential, ite_eq_right hb] using
        basisColumnChoice_minimum r B b a hab
  · intro a b hflow
    by_cases hb : b ∈ B.val
    · have hbase : 0 < (basisOneTransport r B).flow a b := by
        simpa only [basisExtensionTransport, basisExtensionFlow, ite_eq_left hb] using hflow
      simpa only [basisExtensionColumnPotential, ite_eq_left hb,
        basisRowPotential, basisColumnPotential] using
        minimum_transport_tree_potential_tight (basisOneTransport r B)
          (basisOneTransport_tree r B) (Sum.inl none) a b hbase
    · have ha : basisColumnChoice r B b = a := by
        by_contra h
        simp only [basisExtensionTransport, basisExtensionFlow, ite_eq_right hb,
          ite_eq_right h] at hflow
        omega
      simp only [basisExtensionColumnPotential, ite_eq_right hb, ha]

theorem basisExtensionTransport_split (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    transportSplitColumns (basisExtensionTransport r B) = B.val := by
  classical
  ext b
  by_cases hb : b ∈ B.val
  · have hrows : transportColumnRows (basisExtensionTransport r B) b =
        transportColumnRows (basisOneTransport r B) b := by
      ext a
      simp only [mem_transportColumnRows, basisExtensionTransport, basisExtensionFlow,
        ite_eq_left hb]
    rw [mem_transportSplitColumns, hrows, ← mem_transportSplitColumns,
      basisOneTransport_split]
  · have hrows : transportColumnRows (basisExtensionTransport r B) b =
        {basisColumnChoice r B b} := by
      ext a
      simp only [mem_transportColumnRows, basisExtensionTransport, basisExtensionFlow,
        ite_eq_right hb, Finset.mem_singleton]
      by_cases ha : basisColumnChoice r B b = a
      · simp [ha, positiveDemandScale]
      · simp [ha, Ne.symm ha]
    rw [mem_transportSplitColumns, hrows, Finset.card_singleton]
    simp [hb]

noncomputable def basisToPositiveDemand (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) : PositiveDemand r :=
  ⟨fun a => ⟨basisExtensionDemand r B a,
      Nat.lt_succ_of_le (demand_coordinate_bound (basisExtensionDemand_demand r B) a)⟩,
    basisExtensionDemand_demand r B, basisExtensionDemand_positive r B⟩

theorem basisToPositiveDemand_right_inverse (r : L → R → Prop)
    (B : MatchedSupport (fun b : R => fun a : L => r a b)) :
    positiveDemandBase r (basisToPositiveDemand r B) = B := by
  classical
  have hmin₁ := positiveDemandTransport_minimum r (basisToPositiveDemand r B)
  have hmin₂ := basisExtensionTransport_minimum r B
  have heq : positiveDemandTransport r (basisToPositiveDemand r B) =
      basisExtensionTransport r B := by
    apply transportCost_injective
    exact le_antisymm (hmin₁ _) (hmin₂ _)
  apply Subtype.ext
  change transportSplitColumns (positiveDemandTransport r (basisToPositiveDemand r B)) = B.val
  calc
    _ = transportSplitColumns (basisExtensionTransport r B) := congrArg transportSplitColumns heq
    _ = B.val := basisExtensionTransport_split r B

end ResearchMain.PreorderReciprocity
