import MainTheorems.PreorderGamma.ScaledTree

namespace ResearchMain.PreorderGamma

open scoped BigOperators
open PreorderReciprocity

variable {L R : Type*} [Fintype L] [Fintype R]
variable {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}

noncomputable def transportEdgeEquiv (p : NaturalTransport r d s) :
    (Σ b : R, {a : L // 0 < p.flow a b}) ≃ (transportSupportGraph p).edgeSet := by
  classical
  apply Equiv.ofBijective (fun ab => ⟨s(Sum.inl ab.2.val, Sum.inr ab.1), ab.2.property⟩)
  constructor
  · rintro ⟨b, ⟨a, ha⟩⟩ ⟨c, ⟨e, he⟩⟩ h
    have hval := congrArg Subtype.val h
    have hp : a = e ∧ b = c := by
      simpa only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
        Sum.inr_ne_inl, false_and, or_false] using hval
    obtain ⟨rfl, rfl⟩ := hp
    rfl
  · intro e
    obtain ⟨u, v, he⟩ : ∃ u v : L ⊕ R, s(u, v) = e.val := by
      obtain ⟨⟨u, v⟩, he⟩ := Sym2.mk_surjective e.val
      exact ⟨u, v, he⟩
    have hedge : s(u, v) ∈ (transportSupportGraph p).edgeSet := by
      rw [he]
      exact e.property
    have hadj : (transportSupportGraph p).Adj u v := hedge
    cases u with
    | inl a =>
      cases v with
      | inl a' => exact False.elim hadj
      | inr b => exact ⟨⟨b, ⟨a, hadj⟩⟩, Subtype.ext he⟩
    | inr b =>
      cases v with
      | inl a => exact ⟨⟨b, ⟨a, hadj⟩⟩, Subtype.ext (Sym2.eq_swap.trans he)⟩
      | inr b' => exact False.elim hadj

theorem transport_support_edge_card (p : NaturalTransport r d s) :
    Nat.card (transportSupportGraph p).edgeSet = ∑ b, (transportColumnRows p b).card := by
  classical
  calc
    _ = Nat.card (Σ b : R, {a : L // 0 < p.flow a b}) :=
      (Nat.card_congr (transportEdgeEquiv p)).symm
    _ = ∑ b : R, Nat.card {a : L // 0 < p.flow a b} := Nat.card_sigma
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype, transportColumnRows]

noncomputable def transportSplitColumns (p : NaturalTransport r d s) : Finset R := by
  classical
  exact Finset.univ.filter fun b => (transportColumnRows p b).card = 2

@[simp] theorem mem_transportSplitColumns {p : NaturalTransport r d s} {b : R} :
    b ∈ transportSplitColumns p ↔ (transportColumnRows p b).card = 2 := by
  classical
  simp [transportSplitColumns]

theorem transportColumnRows_nonempty (p : NaturalTransport r d s) (b : R)
    (hs : 0 < s b) : (transportColumnRows p b).Nonempty := by
  classical
  by_contra hn
  have hz : ∀ a, p.flow a b = 0 := by
    intro a
    by_contra ha
    have hp : 0 < p.flow a b := Nat.pos_of_ne_zero ha
    exact hn ⟨a, mem_transportColumnRows.mpr hp⟩
  have hcol := p.column_sum b
  simp only [hz, Finset.sum_const_zero] at hcol
  omega

theorem scaled_split_columns_card (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) :
    (transportSplitColumns p).card = Fintype.card L := by
  classical
  have hcol : ∀ b, (transportColumnRows p b).card =
      1 + if (transportColumnRows p b).card = 2 then 1 else 0 := by
    intro b
    have hlow := Finset.card_pos.mpr (transportColumnRows_nonempty p b (by omega))
    have hhigh := scaled_column_support_card_le_two r x hpos k hk p htree b
    split_ifs <;> omega
  have hsum : (∑ b, (transportColumnRows p b).card) =
      Fintype.card R + (transportSplitColumns p).card := by
    rw [show (∑ b, (transportColumnRows p b).card) =
      ∑ b, (1 + if (transportColumnRows p b).card = 2 then 1 else 0) from
        Finset.sum_congr rfl (fun b hb => hcol b)]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id]
    rw [transportSplitColumns, Finset.card_filter]
  have hedges := (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
  rw [transport_support_edge_card] at hedges
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_option] at hedges
  omega

theorem scaled_row_parent_is_split (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) (a : L) (b : R)
    (hflow : 0 < p.flow (some a) b)
    (hdummy : none ∉ transportBranchRows p (some a) b) : b ∈ transportSplitColumns p := by
  classical
  obtain ⟨parent, hp, hroot⟩ := transport_column_parent_exists p htree none b
  have hne : some a ≠ parent := by
    intro h
    exact hdummy (h.symm ▸ hroot)
  have hsub : ({some a, parent} : Finset (Option L)) ⊆ transportColumnRows p b := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact mem_transportColumnRows.mpr hflow
    · obtain rfl := Finset.mem_singleton.mp hc
      exact mem_transportColumnRows.mpr hp
  have hlow := Finset.card_le_card hsub
  simp only [Finset.card_pair hne] at hlow
  have hhigh := scaled_column_support_card_le_two r x hpos k hk p htree b
  exact mem_transportSplitColumns.mpr (by omega)

theorem scaled_split_columns_hasPerfectMatching (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) :
    ∃ f : L ≃ transportSplitColumns p, ∀ a : L, r a (f a).val := by
  classical
  have hex : ∀ a : L, ∃ b : R, 0 < p.flow (some a) b ∧
      none ∉ transportBranchRows p (some a) b := by
    intro a
    exact transport_row_parent_exists p htree none (some a) (by simp)
  choose f hf hroot using hex
  let g : L → transportSplitColumns p := fun a =>
    ⟨f a, scaled_row_parent_is_split r x hpos k hk p htree a (f a) (hf a) (hroot a)⟩
  have hginj : Function.Injective g := by
    intro a c h
    have hfc : f a = f c := congrArg Subtype.val h
    apply scaled_column_child_unique r x hpos k hk p htree.isAcyclic a c (f a)
      (hf a) (hfc.symm ▸ hf c) (hroot a) (hfc.symm ▸ hroot c)
  have hgcard : Fintype.card L = Fintype.card (transportSplitColumns p) := by
    simpa only [Fintype.card_coe] using (scaled_split_columns_card r x hpos k hk p htree).symm
  let e := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hgcard⟩)
  refine ⟨e, ?_⟩
  intro a
  by_contra hrel
  have hz := p.supported (some a) (f a) hrel
  have hp := hf a
  omega

end ResearchMain.PreorderGamma
