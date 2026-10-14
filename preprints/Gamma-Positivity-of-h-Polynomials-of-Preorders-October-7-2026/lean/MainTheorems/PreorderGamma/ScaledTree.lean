import MainTheorems.PreorderGamma.TransportTree
import MainTheorems.PreorderReciprocity.ScaledCuts

namespace ResearchMain.PreorderGamma

open scoped BigOperators
open PreorderReciprocity

variable {L R : Type*} [Fintype L] [Fintype R]

theorem scaled_minimum_support_tree (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k))
    (hp : ∀ q : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k), transportCost p ≤ transportCost q) :
    (transportSupportGraph p).IsTree := by
  apply minimum_transport_support_tree p none hp
  intro A B hA hout hin
  exact scaled_closed_cut_eq_univ r x hpos k hk p A B hA hout hin

theorem scaled_minimum_tree_exists (r : L → R → Prop) (x : L → ℕ)
    (hx : IsDemand r x) (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k) :
    ∃ p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k),
      (∀ q : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
        (fun _ : R => k), transportCost p ≤ transportCost q) ∧
      (transportSupportGraph p).IsTree := by
  obtain ⟨p, hp, _⟩ := exists_unique_minimum_transport
    (scaled_positive_transport_exists r x hx hpos k (by omega))
  exact ⟨p, hp, scaled_minimum_support_tree r x hpos k hk p hp⟩

noncomputable def scaledBranchOriginalRows (r : L → R → Prop) (x : L → ℕ) (k : ℕ)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (a : L) (b : R) : Finset L := by
  classical
  exact Finset.univ.filter fun c => some c ∈ transportBranchRows p (some a) b

@[simp] theorem mem_scaledBranchOriginalRows {r : L → R → Prop} {x : L → ℕ} {k : ℕ}
    {p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)} {a c : L} {b : R} :
    c ∈ scaledBranchOriginalRows r x k p a b ↔
      some c ∈ transportBranchRows p (some a) b := by
  classical
  simp [scaledBranchOriginalRows]

theorem scaled_branch_boundary_flow (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k))
    (hacyc : (transportSupportGraph p).IsAcyclic) (a : L) (b : R)
    (hflow : 0 < p.flow (some a) b)
    (hdummy : none ∉ transportBranchRows p (some a) b) :
    p.flow (some a) b = k - (scaledBranchOriginalRows r x k p a b).card := by
  classical
  let A := transportBranchRows p (some a) b
  let B := transportBranchColumns p (some a) b
  let S := scaledBranchOriginalRows r x k p a b
  have hmap : A = S.map Function.Embedding.some := by
    ext c
    cases c with
    | none => simp [A, hdummy]
    | some c => simp [A, S, scaledBranchOriginalRows]
  have ha : some a ∈ A := by simp [A]
  have hb : b ∉ B := transportBranchColumns_not_boundary p hacyc (some a) b hflow
  have hS : S.Nonempty := ⟨a, by simp [S]⟩
  have hcard : S.card < k := (Finset.card_le_univ S).trans_lt hk
  have hcut := transport_single_edge_cut p A B (some a) b ha hb
    (fun c hc e he hne => transportBranch_outside_flow_zero p (some a) b c hc e he hne)
    (fun e he c hc => transportBranch_incoming_flow_zero p hacyc (some a) b hflow e he c hc)
  rw [hmap, Finset.sum_map] at hcut
  simp only [Function.Embedding.some_apply, scaledDemand, Finset.sum_const,
    nsmul_eq_mul] at hcut
  have hbalance : (∑ c ∈ S, (k * x c - 1)) = k * B.card + p.flow (some a) b := by
    simpa only [Nat.cast_id, Nat.mul_comm B.card k] using hcut
  exact scaled_boundary_flow k (by omega) x S (fun c hc => hpos c) hS hcard
    B.card (p.flow (some a) b) hflow (p.entry_le (some a) b) hbalance

theorem scaled_column_child_unique (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k))
    (hacyc : (transportSupportGraph p).IsAcyclic) (a₁ a₂ : L) (b : R)
    (hflow₁ : 0 < p.flow (some a₁) b) (hflow₂ : 0 < p.flow (some a₂) b)
    (hdummy₁ : none ∉ transportBranchRows p (some a₁) b)
    (hdummy₂ : none ∉ transportBranchRows p (some a₂) b) : a₁ = a₂ := by
  classical
  by_contra hne
  let S₁ := scaledBranchOriginalRows r x k p a₁ b
  let S₂ := scaledBranchOriginalRows r x k p a₂ b
  have hne' : (some a₁ : Option L) ≠ some a₂ := fun h => hne (Option.some.inj h)
  have hdis := transportBranchRows_disjoint_same_column p hacyc (some a₁) (some a₂) b
    hflow₁ hflow₂ hne'
  have hSdis : Disjoint S₁ S₂ := by
    apply Finset.disjoint_left.mpr
    intro a ha₁ ha₂
    exact Finset.disjoint_left.mp hdis
      (mem_scaledBranchOriginalRows.mp ha₁) (mem_scaledBranchOriginalRows.mp ha₂)
  have hsumcard : S₁.card + S₂.card < k := by
    rw [← Finset.card_union_of_disjoint hSdis]
    exact (Finset.card_le_univ (S₁ ∪ S₂)).trans_lt hk
  have hboundary₁ := scaled_branch_boundary_flow r x hpos k hk p hacyc a₁ b hflow₁ hdummy₁
  have hboundary₂ := scaled_branch_boundary_flow r x hpos k hk p hacyc a₂ b hflow₂ hdummy₂
  have hlarge : k < p.flow (some a₁) b + p.flow (some a₂) b := by
    rw [hboundary₁, hboundary₂]
    exact two_subtree_flows_exceed_capacity k S₁.card S₂.card hsumcard
  have hsmall : p.flow (some a₁) b + p.flow (some a₂) b ≤ k := by
    calc
      _ = ∑ a ∈ ({some a₁, some a₂} : Finset (Option L)), p.flow a b := by
        simp [hne']
      _ ≤ ∑ a, p.flow a b := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun a ha hnot => Nat.zero_le _)
      _ = k := p.column_sum b
  omega

noncomputable def transportColumnRows {A B : Type*} [Fintype A] [Fintype B]
    {rel : A → B → Prop} {dem : A → ℕ} {sup : B → ℕ}
    (p : NaturalTransport rel dem sup) (b : B) : Finset A := by
  classical
  exact Finset.univ.filter fun a => 0 < p.flow a b

@[simp] theorem mem_transportColumnRows {A B : Type*} [Fintype A] [Fintype B]
    {rel : A → B → Prop} {dem : A → ℕ} {sup : B → ℕ}
    {p : NaturalTransport rel dem sup} {a : A} {b : B} :
    a ∈ transportColumnRows p b ↔ 0 < p.flow a b := by
  classical
  simp [transportColumnRows]

theorem scaled_column_support_card_le_two (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) (b : R) :
    (transportColumnRows p b).card ≤ 2 := by
  classical
  obtain ⟨parent, hparent, hroot⟩ := transport_column_parent_exists p htree none b
  have hchild : ∀ a₁ a₂ : Option L, 0 < p.flow a₁ b → 0 < p.flow a₂ b →
      a₁ ≠ parent → a₂ ≠ parent → a₁ = a₂ := by
    intro a₁ a₂ hf₁ hf₂ hn₁ hn₂
    have hd₁ : none ∉ transportBranchRows p a₁ b := fun h =>
      hn₁ (transport_column_parent_unique p htree.isAcyclic none a₁ parent b hf₁ hparent h hroot)
    have hd₂ : none ∉ transportBranchRows p a₂ b := fun h =>
      hn₂ (transport_column_parent_unique p htree.isAcyclic none a₂ parent b hf₂ hparent h hroot)
    cases a₁ with
    | none => exact False.elim (hd₁ (by simp))
    | some a₁ =>
      cases a₂ with
      | none => exact False.elim (hd₂ (by simp))
      | some a₂ =>
        exact congrArg some (scaled_column_child_unique r x hpos k hk p htree.isAcyclic
          a₁ a₂ b hf₁ hf₂ hd₁ hd₂)
  by_cases hex : ∃ child ∈ transportColumnRows p b, child ≠ parent
  · obtain ⟨child, hmem, hne⟩ := hex
    have hsubset : transportColumnRows p b ⊆ {parent, child} := by
      intro a ha
      by_cases hp : a = parent
      · simp [hp]
      · have heq := hchild a child (mem_transportColumnRows.mp ha)
          (mem_transportColumnRows.mp hmem) hp hne
        simp [heq]
    exact (Finset.card_le_card hsubset).trans (Finset.card_le_two)
  · have hsubset : transportColumnRows p b ⊆ {parent} := by
      intro a ha
      have heq : a = parent := by
        by_contra h
        exact hex ⟨a, ha, h⟩
      simp [heq]
    have hcard := Finset.card_le_card hsubset
    simp only [Finset.card_singleton] at hcard
    omega

end ResearchMain.PreorderGamma
