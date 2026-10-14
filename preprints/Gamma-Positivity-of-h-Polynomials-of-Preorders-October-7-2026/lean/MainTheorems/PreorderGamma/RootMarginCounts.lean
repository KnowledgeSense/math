import MainTheorems.PreorderGamma.RootLattice
import MainTheorems.PreorderGamma.GeneratingFunctions
import MainTheorems.PreorderGamma.SupportDuality
import MainTheorems.PreorderReciprocity.DemandCounts

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {L R : Type*} [Fintype L] [Fintype R]

def twoUniversalRelation (r : L → R → Prop) : Option L → Option R → Prop
  | none, _ => True
  | some a, b => rightUniversalRelation r a b

noncomputable def completedDemand (t : ℕ) (x : L → ℕ) : Option L → ℕ :=
  Option.elim' (t - ∑ a, x a) x

@[simp] theorem completedDemand_some (t : ℕ) (x : L → ℕ) (a : L) :
    completedDemand t x (some a) = x a := rfl

@[simp] theorem completedDemand_none (t : ℕ) (x : L → ℕ) :
    completedDemand t x none = t - ∑ a, x a := rfl

theorem completedDemand_sum (t : ℕ) (x : L → ℕ) (hx : (∑ a, x a) ≤ t) :
    (∑ a, completedDemand t x a) = t := by
  rw [Fintype.sum_option, completedDemand_none]
  exact Nat.sub_add_cancel hx

omit [Fintype L] in
theorem twoUniversal_neighbors_some (r : L → R → Prop) (A : Finset L) :
    graphNeighbors (twoUniversalRelation r) (A.map Function.Embedding.some) =
      graphNeighbors (rightUniversalRelation r) A := by
  classical
  ext b
  simp only [mem_graphNeighbors, Finset.mem_map]
  constructor
  · rintro ⟨a, ⟨c, hc, rfl⟩, hab⟩
    exact ⟨c, hc, hab⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨some a, ⟨a, ha, rfl⟩, hab⟩

theorem completedDemand_supply_iff (r : L → R → Prop) (s : Option R → ℕ)
    (x : L → ℕ) :
    IsSupplyDemand (twoUniversalRelation r) (completedDemand (∑ b, s b) x) s ↔
      IsDemand (fun a : L => fun c : DemandCells s => rightUniversalRelation r a c.1) x := by
  classical
  rw [supplyCell_demand_iff]
  constructor
  · intro hd A
    have h := hd (A.map Function.Embedding.some)
    rw [twoUniversal_neighbors_some, Finset.sum_map] at h
    exact h
  · intro hd A
    have htotal : (∑ a, x a) ≤ ∑ b, s b := hd Finset.univ |>.trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun b hb hn => Nat.zero_le _))
    by_cases hnone : none ∈ A
    · have hneighbors : graphNeighbors (twoUniversalRelation r) A = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro b
        exact mem_graphNeighbors.mpr ⟨none, hnone, trivial⟩
      rw [hneighbors]
      calc
        _ ≤ ∑ a : Option L, completedDemand (∑ b, s b) x a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun a ha hn => Nat.zero_le _)
        _ = _ := completedDemand_sum _ _ htotal
    · let B := Finset.univ.filter fun a : L => some a ∈ A
      have hA : A = B.map Function.Embedding.some := by
        ext a
        cases a with
        | none => simp [hnone]
        | some a => simp [B]
      rw [hA, twoUniversal_neighbors_some, Finset.sum_map]
      exact hd B

abbrev BipartiteNaturalMargins (r : L → R → Prop) (t : ℕ) :=
  {z : (Option L → ℕ) × (Option R → ℕ) //
    (∑ i, z.1 i) = t ∧ (∑ j, z.2 j) = t ∧
      Nonempty (NaturalTransport (twoUniversalRelation r) z.1 z.2)}

noncomputable def marginCloneDemandEquiv (r : L → R → Prop) (t : ℕ) :
    BipartiteNaturalMargins r t ≃
      Σ s : MarginVectors (Option R) t,
        {x : L → ℕ // IsDemand
          (fun a : L => fun c : DemandCells s.val => rightUniversalRelation r a c.1) x} := by
  classical
  refine
    { toFun := fun z => ?_
      invFun := fun q => ?_
      left_inv := ?_
      right_inv := ?_ }
  · let x : L → ℕ := fun a => z.val.1 (some a)
    have hcomplete : completedDemand t x = z.val.1 := by
      funext a
      cases a with
      | none =>
        have h := z.property.1
        rw [Fintype.sum_option] at h
        change t - ∑ a, z.val.1 (some a) = z.val.1 none
        omega
      | some a => rfl
    refine ⟨⟨z.val.2, z.property.2.1⟩, x, ?_⟩
    obtain ⟨p⟩ := z.property.2.2
    apply (completedDemand_supply_iff r z.val.2 x).mp
    rw [z.property.2.1, hcomplete]
    exact p.supplyDemand
  · have hD := (completedDemand_supply_iff r q.1.val q.2.val).mpr q.2.property
    have htotal : (∑ a, q.2.val a) ≤ t := by
      have h := demand_total_bound q.2.property
      simpa only [Fintype.card_sigma, Fintype.card_fin, q.1.property] using h
    refine ⟨(completedDemand t q.2.val, q.1.val),
      completedDemand_sum t q.2.val htotal, q.1.property, ?_⟩
    apply naturalTransport_supplyDemand _ _ _
    · simpa only [q.1.property] using hD
    · rw [completedDemand_sum t q.2.val htotal, q.1.property]
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · funext a
      cases a with
      | none =>
        have h := z.property.1
        rw [Fintype.sum_option] at h
        change t - ∑ a, z.val.1 (some a) = z.val.1 none
        omega
      | some a => rfl
    · rfl
  · rintro ⟨s, x⟩
    rfl

instance naturalDemandFinite (r : L → R → Prop) :
    Finite {x : L → ℕ // IsDemand r x} :=
  Finite.of_equiv (demandVectors r) (PreorderReciprocity.boundedDemandEquiv r).symm

noncomputable instance naturalDemandFintype (r : L → R → Prop) :
    Fintype {x : L → ℕ // IsDemand r x} := Fintype.ofFinite _

instance bipartiteNaturalMarginsFinite (r : L → R → Prop) (t : ℕ) :
    Finite (BipartiteNaturalMargins r t) :=
  Finite.of_equiv (Σ s : MarginVectors (Option R) t,
    {x : L → ℕ // IsDemand
      (fun a : L => fun c : DemandCells s.val => rightUniversalRelation r a c.1) x})
      (marginCloneDemandEquiv r t).symm

theorem demand_count_transpose (r : L → R → Prop) :
    Nat.card {x : L → ℕ // IsDemand r x} =
      Nat.card {x : R → ℕ // IsDemand (fun b a => r a b) x} := by
  rw [PreorderReciprocity.demand_point_count_eval,
    PreorderReciprocity.demand_point_count_eval, supportEnumerator_transpose]

theorem bipartite_margin_count (r : L → R → Prop) (t : ℕ) :
    Nat.card (BipartiteNaturalMargins r t) =
      ∑ s : MarginVectors (Option R) t,
        ∑ a ∈ demandVectors (fun b : Option R => fun e : L => rightUniversalRelation r e b),
          ∏ b : Option R, Nat.multichoose (s.val b) (a b).val := by
  classical
  rw [Nat.card_congr (marginCloneDemandEquiv r t), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  rw [demand_count_transpose]
  exact clone_demand_count (fun b : Option R => fun e : L => rightUniversalRelation r e b) s.val

noncomputable def rightUniversalDemandEquiv (r : L → R → Prop) :
    {a : Option R → ℕ // IsDemand
      (fun b : Option R => fun e : L => rightUniversalRelation r e b) a} ≃
      Σ d : demandVectors (fun b : R => fun e : L => r e b),
        Fin (Fintype.card L - (∑ b, (d.val b).val) + 1) := by
  classical
  refine
    { toFun := fun a => ?_
      invFun := fun q => ?_
      left_inv := ?_
      right_inv := ?_ }
  · have ha := (rightUniversal_demand_iff r a.val).mp a.property
    let d : R → Fin (Fintype.card L + 1) := fun b =>
      ⟨a.val (some b), Nat.lt_succ_of_le (demand_coordinate_bound ha.1 b)⟩
    refine ⟨⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.1⟩⟩, a.val none, ?_⟩
    change a.val none < Fintype.card L - (∑ b, a.val (some b)) + 1
    omega
  · refine ⟨Option.elim' q.2.val (fun b => (q.1.val b).val),
      (rightUniversal_demand_iff r _).mpr ⟨(Finset.mem_filter.mp q.1.property).2, ?_⟩⟩
    have ht := demand_total_bound (Finset.mem_filter.mp q.1.property).2
    have hj := q.2.isLt
    change q.2.val + (∑ b, (q.1.val b).val) ≤ Fintype.card L
    omega
  · intro a
    apply Subtype.ext
    funext b
    cases b <;> rfl
  · rintro ⟨d, j⟩
    rfl

theorem rightUniversal_weighted_sum (r : L → R → Prop) (s : Option R → ℕ) :
    (∑ a ∈ demandVectors (fun b : Option R => fun e : L => rightUniversalRelation r e b),
        ∏ b : Option R, Nat.multichoose (s b) (a b).val) =
      ∑ d : demandVectors (fun b : R => fun e : L => r e b),
        (∏ b : R, Nat.multichoose (s (some b)) (d.val b).val) *
          ∑ j ∈ Finset.range (Fintype.card L - (∑ b, (d.val b).val) + 1),
            Nat.multichoose (s none) j := by
  classical
  rw [← Finset.sum_coe_sort]
  calc
    _ = ∑ a : {a : Option R → ℕ // IsDemand
          (fun b : Option R => fun e : L => rightUniversalRelation r e b) a},
        ∏ b : Option R, Nat.multichoose (s b) (a.val b) := by
      apply Fintype.sum_equiv (PreorderReciprocity.boundedDemandEquiv _).symm
      intro a
      rfl
    _ = ∑ q : (Σ d : demandVectors (fun b : R => fun e : L => r e b),
          Fin (Fintype.card L - (∑ b, (d.val b).val) + 1)),
        (∏ b : R, Nat.multichoose (s (some b)) (q.1.val b).val) *
          Nat.multichoose (s none) q.2.val := by
      apply Fintype.sum_equiv (rightUniversalDemandEquiv r)
      intro a
      rw [Fintype.prod_option, mul_comm]
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [← Finset.mul_sum, Fin.sum_univ_eq_sum_range]

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

instance rootNaturalMarginsFinite (t : ℕ) : Finite (RootNaturalMargins (E := E) t) := by
  apply Finite.of_injective
    (fun z : RootNaturalMargins (E := E) t =>
      ((⟨z.val.1, z.property.1⟩ : MarginVectors (Option E) t),
        (⟨z.val.2, z.property.2.1⟩ : MarginVectors (Option E) t)))
  intro a b hab
  apply Subtype.ext
  exact Prod.ext (congrArg (fun q => q.1.val) hab) (congrArg (fun q => q.2.val) hab)

instance rootIntegerPointsFinite (t : ℕ) :
    Finite {z : (Option E → ℤ) × (Option E → ℤ) // RootIntegerPoints t z} :=
  Finite.of_equiv (RootNaturalMargins (E := E) t) (rootIntegerNaturalEquiv t).symm

omit [Fintype E] [DecidableEq E] in
theorem twoUniversal_preorder :
    twoUniversalRelation (fun a b : E => b ≤ a) = augmentedRelation := by
  funext i j
  cases i <;> cases j <;> rfl

theorem rootLatticeCount_clone_formula (t : ℕ) :
    rootLatticeCount (E := E) t =
      ∑ s : MarginVectors (Option E) t,
        ∑ d : demandVectors (fun b a : E => b ≤ a),
          (∏ b : E, Nat.multichoose (s.val (some b)) (d.val b).val) *
            ∑ j ∈ Finset.range (Fintype.card E - (∑ b, (d.val b).val) + 1),
              Nat.multichoose (s.val none) j := by
  rw [rootLatticeCount_natural]
  have h := bipartite_margin_count (fun a b : E => b ≤ a) t
  unfold BipartiteNaturalMargins at h
  rw [twoUniversal_preorder] at h
  change Nat.card (RootNaturalMargins (E := E) t) = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro s hs
  exact rightUniversal_weighted_sum _ s.val

end ResearchMain.PreorderGamma
