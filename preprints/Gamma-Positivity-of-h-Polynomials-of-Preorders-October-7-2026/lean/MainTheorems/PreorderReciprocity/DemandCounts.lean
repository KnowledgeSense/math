import MainTheorems.PreorderReciprocity.CapacityMatching
import MainTheorems.PreorderReciprocity.IntegerCounting
import MainTheorems.PreorderGamma.Enumerators
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace ResearchMain.PreorderReciprocity

variable {L R : Type*} [Fintype L] [Fintype R]

noncomputable def boundedDemandEquiv (r : L → R → Prop) :
    {x : L → ℕ // PreorderGamma.IsDemand r x} ≃ (PreorderGamma.demandVectors r) := by
  classical
  refine
    { toFun := fun x => ⟨fun a => ⟨x.val a,
        Nat.lt_succ_of_le (PreorderGamma.demand_coordinate_bound x.property a)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩⟩
      invFun := fun d => ⟨fun a => (d.val a).val,
        (Finset.mem_filter.mp d.property).2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rfl
  · intro d
    apply Subtype.ext
    funext a
    rfl

theorem demand_point_count (r : L → R → Prop) :
    Nat.card {x : L → ℕ // PreorderGamma.IsDemand r x} =
      (PreorderGamma.demandVectors r).card := by
  rw [Nat.card_congr (boundedDemandEquiv r), Nat.card_eq_fintype_card,
    Fintype.card_coe]

theorem supportEnumerator_eval_one (r : L → R → Prop) :
    (PreorderGamma.supportEnumerator r).eval 1 = (PreorderGamma.demandVectors r).card := by
  classical
  simp [PreorderGamma.supportEnumerator, Polynomial.eval_finsetSum]

theorem demand_point_count_eval (r : L → R → Prop) :
    Nat.card {x : L → ℕ // PreorderGamma.IsDemand r x} =
      (PreorderGamma.supportEnumerator r).eval 1 := by
  rw [demand_point_count, supportEnumerator_eval_one]

noncomputable def boundedPositiveDemandEquiv (r : L → R → Prop) :
    {x : L → ℕ // PreorderGamma.IsDemand r x ∧ ∀ a, 0 < x a} ≃
      ((PreorderGamma.demandVectors r).filter fun d => ∀ a, 0 < (d a).val) := by
  classical
  refine
    { toFun := fun x => ⟨fun a => ⟨x.val a,
        Nat.lt_succ_of_le (PreorderGamma.demand_coordinate_bound x.property.1 a)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, x.property.1⟩, x.property.2⟩⟩
      invFun := fun d => ⟨fun a => (d.val a).val,
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp d.property).1).2,
          (Finset.mem_filter.mp d.property).2⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rfl
  · intro d
    apply Subtype.ext
    funext a
    rfl

theorem positive_demand_point_count (r : L → R → Prop) :
    Nat.card {x : L → ℕ // PreorderGamma.IsDemand r x ∧ ∀ a, 0 < x a} =
      (PreorderGamma.supportEnumerator r).coeff (Fintype.card L) := by
  classical
  rw [Nat.card_congr (boundedPositiveDemandEquiv r), Nat.card_eq_fintype_card,
    Fintype.card_coe, PreorderGamma.supportEnumerator_fullSupport_coeff]

variable {E : Type*} [Fintype E] [Preorder E]

omit [Fintype E] [Fintype L] [Fintype R] in
def naturalIntegerPointsEquiv (r s : ℕ) :
    {x : E → ℕ // NatIntegerPoints r s x} ≃
      {x : E → ℤ // ClosedIntegerPoints (r : ℤ) (s : ℤ) x} where
  toFun x := ⟨fun a => (x.val a : ℤ), (natIntegerPoints_iff_int r s x.val).mp x.property⟩
  invFun x := ⟨fun a => (x.val a).toNat, by
    apply (natIntegerPoints_iff_int r s _).mpr
    have hval : (fun a => ((x.val a).toNat : ℤ)) = x.val :=
      funext fun a => Int.toNat_of_nonneg (x.property.1 a)
    rw [hval]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    exact Int.toNat_natCast _
  right_inv x := by
    apply Subtype.ext
    funext a
    exact Int.toNat_of_nonneg (x.property.1 a)

omit [Fintype E] [Fintype L] [Fintype R] in
theorem natural_integer_point_count (r s : ℕ) :
    Nat.card {x : E → ℕ // NatIntegerPoints r s x} =
      closedCount (E := E) (r : ℤ) (s : ℤ) :=
  Nat.card_congr (naturalIntegerPointsEquiv r s)

omit [Fintype L] [Fintype R] in
theorem capacity_lattice_count (r s : ℕ) :
    latticeCount (E := E) (r : ℤ) (s : ℤ) =
      (PreorderGamma.supportEnumerator (capacityRelation (E := E) r s)).eval 1 := by
  rw [latticeCount_eq_closedCount, ← natural_integer_point_count]
  have heq := Nat.card_congr
    (Equiv.subtypeEquivRight fun x : E → ℕ => natIntegerPoints_iff_demand r s x)
  exact heq.trans (demand_point_count_eval _)

omit [Fintype E] [Fintype L] [Fintype R] in
theorem strict_successor_iff (r s : ℤ) (x : E → ℤ) :
    StrictIntegerPoints r (s + 1) x ↔
      ClosedIntegerPoints r s x ∧ ∀ a, 0 < x a := by
  constructor
  · intro hx
    refine ⟨⟨fun a => (hx.1 a).le, ?_⟩, hx.1⟩
    intro I hI hIdeal
    have h := hx.2 I hI hIdeal
    omega
  · rintro ⟨hx, hpos⟩
    refine ⟨hpos, ?_⟩
    intro I hI hIdeal
    have h := hx.2 I hI hIdeal
    omega

omit [Fintype E] [Fintype L] [Fintype R] in
def positiveNaturalIntegerPointsEquiv (r s : ℕ) :
    {x : E → ℕ // NatIntegerPoints r s x ∧ ∀ a, 0 < x a} ≃
      {x : E → ℤ // StrictIntegerPoints (r : ℤ) ((s : ℤ) + 1) x} where
  toFun x := ⟨fun a => (x.val a : ℤ), by
    apply (strict_successor_iff _ _ _).mpr
    refine ⟨(natIntegerPoints_iff_int r s x.val).mp x.property.1, ?_⟩
    intro a
    exact_mod_cast x.property.2 a⟩
  invFun x := ⟨fun a => (x.val a).toNat, by
    have hval : (fun a => ((x.val a).toNat : ℤ)) = x.val :=
      funext fun a => Int.toNat_of_nonneg (x.property.1 a).le
    refine ⟨(natIntegerPoints_iff_int r s _).mpr ?_, ?_⟩
    · rw [hval]
      exact ((strict_successor_iff _ _ _).mp x.property).1
    · intro a
      exact Int.pos_iff_toNat_pos.mp (x.property.1 a)⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    exact Int.toNat_natCast _
  right_inv x := by
    apply Subtype.ext
    funext a
    exact Int.toNat_of_nonneg (x.property.1 a).le

omit [Fintype L] [Fintype R] in
theorem capacity_fullSupport_coeff (r s : ℕ) :
    (PreorderGamma.supportEnumerator (capacityRelation (E := E) r s)).coeff
      (Fintype.card E) = latticeCount (E := E) ((r : ℤ) - 1) (s : ℤ) := by
  rw [← positive_demand_point_count]
  have heq := Nat.card_congr (Equiv.subtypeEquivRight fun x : E → ℕ =>
    and_congr (natIntegerPoints_iff_demand r s x)
      (Iff.rfl : (∀ a, 0 < x a) ↔ (∀ a, 0 < x a)))
  rw [← heq, Nat.card_congr (positiveNaturalIntegerPointsEquiv r s)]
  change strictCount (E := E) (r : ℤ) ((s : ℤ) + 1) = _
  rw [strictCount_eq_closedCount]
  have hs : ((s : ℤ) + 1) - 1 = s := by omega
  rw [hs, latticeCount_eq_closedCount]

end ResearchMain.PreorderReciprocity
