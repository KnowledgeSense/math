import MainTheorems.PreorderGamma.TransportHall
import MainTheorems.PreorderReciprocity.Compositions
import MainTheorems.PreorderGamma.Enumerators

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {L R : Type*} [Fintype L] [Fintype R]

noncomputable def cloneAggregate (s : L → ℕ) (d : DemandCells s → ℕ) (a : L) : ℕ :=
  ∑ i : Fin (s a), d ⟨a, i⟩

omit [Fintype L] in
theorem cloneAggregate_demand_iff (r : L → R → Prop) (s : L → ℕ)
    (d : DemandCells s → ℕ) :
    IsDemand (fun c : DemandCells s => r c.1) d ↔ IsDemand r (cloneAggregate s d) := by
  classical
  constructor
  · intro hd A
    let C := A.sigma (fun a => (Finset.univ : Finset (Fin (s a))))
    have hsum : (∑ a ∈ A, cloneAggregate s d a) = ∑ c ∈ C, d c := by
      simp only [C, cloneAggregate, Finset.sum_sigma]
    have hsub : graphNeighbors (fun c : DemandCells s => r c.1) C ⊆ graphNeighbors r A := by
      intro b hb
      obtain ⟨c, hc, hcb⟩ := mem_graphNeighbors.mp hb
      exact mem_graphNeighbors.mpr ⟨c.1, (Finset.mem_sigma.mp hc).1, hcb⟩
    rw [hsum]
    exact (hd C).trans (Finset.card_le_card hsub)
  · intro hd C
    let A := C.image Sigma.fst
    have hsub : C ⊆ A.sigma (fun a => (Finset.univ : Finset (Fin (s a)))) := by
      intro c hc
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_image.mpr ⟨c, hc, rfl⟩, Finset.mem_univ _⟩
    have hsum : (∑ c ∈ C, d c) ≤ ∑ a ∈ A, cloneAggregate s d a := by
      calc
        _ ≤ ∑ c ∈ A.sigma (fun a => (Finset.univ : Finset (Fin (s a)))), d c :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c hc hn => Nat.zero_le _)
        _ = _ := by simp only [Finset.sum_sigma, cloneAggregate]
    have hn : graphNeighbors (fun c : DemandCells s => r c.1) C = graphNeighbors r A := by
      ext b
      constructor
      · intro hb
        obtain ⟨c, hc, hcb⟩ := mem_graphNeighbors.mp hb
        exact mem_graphNeighbors.mpr ⟨c.1, Finset.mem_image.mpr ⟨c, hc, rfl⟩, hcb⟩
      · intro hb
        obtain ⟨a, ha, hab⟩ := mem_graphNeighbors.mp hb
        obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
        exact mem_graphNeighbors.mpr ⟨c, hc, hca.symm ▸ hab⟩
    rw [hn]
    exact hsum.trans (hd A)

abbrev CloneDemandFiber (s : L → ℕ) (a : L → Fin (Fintype.card R + 1)) :=
  ∀ b : L, {d : Fin (s b) → ℕ // ∑ i, d i = (a b).val}

omit [Fintype L] in
theorem cloneDemandFiber_heq (s : L → ℕ)
    {a b : L → Fin (Fintype.card R + 1)}
    (h : ∀ c, (a c).val = (b c).val)
    (f : CloneDemandFiber s a) (g : CloneDemandFiber s b)
    (hfg : ∀ c, (f c).val = (g c).val) : HEq f g := by
  have hab : a = b := funext fun c => Fin.ext (h c)
  subst b
  apply heq_of_eq
  funext c
  exact Subtype.ext (hfg c)

noncomputable def cloneDemandEquiv (r : L → R → Prop) (s : L → ℕ) :
    {d : DemandCells s → ℕ // IsDemand (fun c : DemandCells s => r c.1) d} ≃
      Σ a : demandVectors r, CloneDemandFiber s a.val := by
  classical
  refine
    { toFun := fun d => ?_
      invFun := fun q => ?_
      left_inv := ?_
      right_inv := ?_ }
  · have hd := (cloneAggregate_demand_iff r s d.val).mp d.property
    let a : L → Fin (Fintype.card R + 1) := fun b =>
      ⟨cloneAggregate s d.val b, Nat.lt_succ_of_le (demand_coordinate_bound hd b)⟩
    refine ⟨⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩,
      fun b => ⟨fun i => d.val ⟨b, i⟩, rfl⟩⟩
  · let d : DemandCells s → ℕ := fun c => (q.2 c.1).val c.2
    have hagg : ∀ b, cloneAggregate s d b = (q.1.val b).val := fun b => (q.2 b).property
    refine ⟨d, (cloneAggregate_demand_iff r s d).mpr ?_⟩
    rw [show cloneAggregate s d = (fun b => (q.1.val b).val) from funext hagg]
    exact (Finset.mem_filter.mp q.1.property).2
  · intro d
    apply Subtype.ext
    funext c
    cases c
    rfl
  · rintro ⟨a, f⟩
    apply Sigma.ext
    · apply Subtype.ext
      funext b
      apply Fin.ext
      exact (f b).property
    · exact cloneDemandFiber_heq s (fun b => (f b).property) _ _ (fun b => rfl)

theorem cloneDemandFiber_count (s : L → ℕ) (a : L → Fin (Fintype.card R + 1)) :
    Nat.card (CloneDemandFiber s a) = ∏ b : L, Nat.multichoose (s b) (a b).val := by
  rw [Nat.card_pi]
  simp_rw [PreorderReciprocity.weak_composition_count]

theorem clone_demand_count (r : L → R → Prop) (s : L → ℕ) :
    Nat.card {d : DemandCells s → ℕ // IsDemand (fun c : DemandCells s => r c.1) d} =
      ∑ a ∈ demandVectors r, ∏ b : L, Nat.multichoose (s b) (a b).val := by
  rw [Nat.card_congr (cloneDemandEquiv r s), Nat.card_sigma]
  simp_rw [cloneDemandFiber_count]
  exact Finset.sum_coe_sort (demandVectors r)
    (fun a : L → Fin (Fintype.card R + 1) =>
      ∏ b : L, Nat.multichoose (s b) (a b).val)

def rightUniversalRelation (r : L → R → Prop) (a : L) : Option R → Prop
  | none => True
  | some b => r a b

theorem rightUniversal_demand_iff (r : L → R → Prop) (a : Option R → ℕ) :
    IsDemand (fun b : Option R => fun e : L => rightUniversalRelation r e b) a ↔
      IsDemand (fun b : R => fun e : L => r e b) (fun b => a (some b)) ∧
        a none + (∑ b, a (some b)) ≤ Fintype.card L := by
  classical
  have hn : ∀ B : Finset R,
      graphNeighbors (fun b : Option R => fun e : L => rightUniversalRelation r e b)
        (B.map Function.Embedding.some) = graphNeighbors (fun b : R => fun e : L => r e b) B := by
    intro B
    ext e
    simp only [mem_graphNeighbors, Finset.mem_map]
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, he⟩
      exact ⟨c, hc, he⟩
    · rintro ⟨b, hb, he⟩
      exact ⟨some b, ⟨b, hb, rfl⟩, he⟩
  constructor
  · intro hd
    constructor
    · intro B
      have h := hd (B.map Function.Embedding.some)
      rw [hn, Finset.sum_map] at h
      exact h
    · have h := demand_total_bound hd
      rwa [Fintype.sum_option] at h
  · rintro ⟨hd, htotal⟩ A
    by_cases hnone : none ∈ A
    · have hneighbors : graphNeighbors
          (fun b : Option R => fun e : L => rightUniversalRelation r e b) A = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro e
        exact mem_graphNeighbors.mpr ⟨none, hnone, trivial⟩
      rw [hneighbors, Finset.card_univ]
      calc
        _ ≤ ∑ b : Option R, a b := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ A) (fun b hb hn => Nat.zero_le _)
        _ ≤ _ := by rwa [Fintype.sum_option]
    · let B : Finset R := Finset.univ.filter fun b => some b ∈ A
      have hA : A = B.map Function.Embedding.some := by
        ext b
        cases b with
        | none => simp [hnone]
        | some b => simp [B]
      rw [hA, hn, Finset.sum_map]
      exact hd B

end ResearchMain.PreorderGamma
