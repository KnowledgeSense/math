import HardCoreActivityThreshold.BooleanConfigurations
import HardCoreActivityThreshold.WeightedForest

/-! Exact product and root decompositions of the hard-core probability on a forest. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

def RootsVacant (A : ForestExpr) (x : A.Vertex → Bool) : Prop :=
  ∀ v, A.IsRoot v → x v = false

theorem booleanIndependent_union (A B : ForestExpr) (x : (A.union B).Vertex → Bool) :
    BooleanIndependent (A.union B).graph x ↔
      BooleanIndependent A.graph (fun v => x (.inl v)) ∧
      BooleanIndependent B.graph (fun v => x (.inr v)) := by
  constructor
  · intro h
    exact ⟨fun u hu v hv => h (.inl u) hu (.inl v) hv,
      fun u hu v hv => h (.inr u) hu (.inr v) hv⟩
  · rintro ⟨ha, hb⟩ u hu v hv
    cases u <;> cases v
    · exact ha _ hu _ hv
    · exact id
    · exact id
    · exact hb _ hu _ hv

theorem booleanIndependent_root (A : ForestExpr) (x : A.root.Vertex → Bool) :
    BooleanIndependent A.root.graph x ↔
      BooleanIndependent A.graph (fun v => x (some v)) ∧
        (x none = true → RootsVacant A (fun v => x (some v))) := by
  constructor
  · intro h
    refine ⟨fun u hu v hv => h (some u) hu (some v) hv, ?_⟩
    intro hn v hv
    cases hx : x (some v)
    · exact hx
    · exact False.elim (h none hn (some v) hx hv)
  · rintro ⟨h, hr⟩ u hu v hv
    cases u with
    | none =>
      cases v with
      | none => exact id
      | some v => intro hadj; have := hr hu v hadj; simp_all
    | some u =>
      cases v with
      | none => intro hadj; have := hr hv u hadj; simp_all
      | some v => exact h u hu v hv

theorem rootsVacant_union (A B : ForestExpr) (x : (A.union B).Vertex → Bool) :
    RootsVacant (A.union B) x ↔
      RootsVacant A (fun v => x (.inl v)) ∧ RootsVacant B (fun v => x (.inr v)) := by
  constructor
  · intro h
    exact ⟨fun v hv => h (.inl v) hv, fun v hv => h (.inr v) hv⟩
  · rintro ⟨ha, hb⟩ v hv
    cases v
    · exact ha _ hv
    · exact hb _ hv

@[simp] theorem rootsVacant_root (A : ForestExpr) (x : A.root.Vertex → Bool) :
    RootsVacant A.root x ↔ x none = false := by
  constructor
  · intro h; exact h none trivial
  · intro h v hv
    cases v
    · exact h
    · exact False.elim hv

theorem booleanWeight_union (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ)
    (x : (A.union B).Vertex → Bool) :
    booleanWeight (A.union B).graph activity x =
      booleanWeight A.graph (fun v => activity (.inl v)) (fun v => x (.inl v)) *
      booleanWeight B.graph (fun v => activity (.inr v)) (fun v => x (.inr v)) := by
  unfold booleanWeight
  rw [booleanIndependent_union]
  rw [Fintype.prod_sum_type]
  split_ifs <;> simp_all

theorem booleanWeight_root (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (x : A.root.Vertex → Bool) :
    booleanWeight A.root.graph activity x =
      if x none then activity none *
        (if RootsVacant A (fun v => x (some v)) then
          booleanWeight A.graph (fun v => activity (some v)) (fun v => x (some v)) else 0)
      else booleanWeight A.graph (fun v => activity (some v)) (fun v => x (some v)) := by
  unfold booleanWeight
  rw [booleanIndependent_root]
  rw [Fintype.prod_option]
  cases x none <;> simp
  split_ifs <;> simp_all

noncomputable def forestLaw (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) : FiniteLaw (A.Vertex → Bool) :=
  booleanWithinLaw A.graph activity ha (if parent then univ.filter (fun v => ¬ A.IsRoot v) else univ)

noncomputable def forestNormalizer (A : ForestExpr) (activity : A.Vertex → ℝ) (parent : Bool) : ℝ :=
  if parent then weightedAvoidRoots A activity else weightedTotal A activity

theorem forestNormalizer_pos (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) : 0 < forestNormalizer A activity parent := by
  cases parent <;> exact partitionWithin_pos _ _ ha _

theorem forestLaw_mass (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) (x : A.Vertex → Bool) :
    (forestLaw A activity ha parent).mass x =
      (if parent = true ∧ ¬ RootsVacant A x then 0 else booleanWeight A.graph activity x) /
        forestNormalizer A activity parent := by
  unfold forestLaw
  rw [booleanWithinLaw_mass]
  have he : (∀ v, x v = true → ¬ A.IsRoot v) ↔ RootsVacant A x := by
    unfold RootsVacant
    constructor
    · intro h v hv
      cases hx : x v
      · rfl
      · exact False.elim (h v hx hv)
    · intro h v hx hv
      have := h v hv
      simp_all
  cases parent <;> simp [forestNormalizer, weightedTotal, weightedAvoidRoots, he]

theorem forestLaw_free (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    forestLaw A activity ha false = booleanHardCoreLaw A.graph activity ha := by
  unfold forestLaw booleanWithinLaw booleanHardCoreLaw
  simp only [Bool.false_eq_true, ↓reduceIte, hardCoreWithin_univ]

 theorem forestNormalizer_union (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ)
    (parent : Bool) :
    forestNormalizer (A.union B) activity parent =
      forestNormalizer A (fun v => activity (.inl v)) parent *
      forestNormalizer B (fun v => activity (.inr v)) parent := by
  cases parent
  · exact weightedTotal_union A B activity
  · exact weightedAvoidRoots_union A B activity

theorem forestLaw_union_mass (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) (x : (A.union B).Vertex → Bool) :
    (forestLaw (A.union B) activity ha parent).mass x =
      (forestLaw A (fun v => activity (.inl v)) (fun v => ha (.inl v)) parent).mass (fun v => x (.inl v)) *
      (forestLaw B (fun v => activity (.inr v)) (fun v => ha (.inr v)) parent).mass (fun v => x (.inr v)) := by
  simp only [forestLaw_mass, rootsVacant_union, forestNormalizer_union]
  rw [booleanWeight_union A B activity x]
  by_cases hA : RootsVacant A (fun v => x (.inl v)) <;>
    by_cases hB : RootsVacant B (fun v => x (.inr v)) <;>
    cases parent <;> simp [hA, hB, div_mul_div_comm]

noncomputable def downwardOccupation (A : ForestExpr) (activity : A.root.Vertex → ℝ) : ℝ :=
  activity none * weightedAvoidRoots A (fun v => activity (some v)) /
    weightedTotal A.root activity

theorem downwardOccupation_pos (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : 0 < downwardOccupation A activity := by
  exact div_pos (mul_pos (ha none) (partitionWithin_pos _ _ (fun v => ha (some v)) _))
    (partitionWithin_pos _ _ ha _)

theorem downwardOccupation_lt_one (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) : downwardOccupation A activity < 1 := by
  have ht : 0 < weightedTotal A (fun v => activity (some v)) := partitionWithin_pos _ _ (fun v => ha (some v)) _
  unfold downwardOccupation
  have hz : 0 < weightedTotal A.root activity := partitionWithin_pos _ _ ha _
  apply (div_lt_one hz).mpr
  rw [weightedTotal_root]
  linarith

/-- The actual free-boundary law is sampled by the exact root occupation and its conditional child laws. -/
theorem forestLaw_root_free_mass (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (x : A.root.Vertex → Bool) :
    (forestLaw A.root activity ha false).mass x =
      if x none then downwardOccupation A activity *
        (forestLaw A (fun v => activity (some v)) (fun v => ha (some v)) true).mass (fun v => x (some v))
      else (1 - downwardOccupation A activity) *
        (forestLaw A (fun v => activity (some v)) (fun v => ha (some v)) false).mass (fun v => x (some v)) := by
  have ht : weightedTotal A (fun v => activity (some v)) ≠ 0 :=
    ne_of_gt (partitionWithin_pos _ _ (fun v => ha (some v)) _)
  have hu : weightedAvoidRoots A (fun v => activity (some v)) ≠ 0 :=
    ne_of_gt (partitionWithin_pos _ _ (fun v => ha (some v)) _)
  have hz : weightedTotal A.root activity ≠ 0 := ne_of_gt (partitionWithin_pos _ _ ha _)
  simp only [forestLaw_mass, Bool.false_eq_true, false_and, ↓reduceIte,
    true_and, forestNormalizer]
  rw [booleanWeight_root A activity x]
  cases hx : x none
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold downwardOccupation
    rw [weightedTotal_root] at hz ⊢
    field_simp
    ring
  · simp only [↓reduceIte]
    by_cases hr : RootsVacant A (fun v => x (some v))
    · simp only [hr, not_true_eq_false, ↓reduceIte]
      unfold downwardOccupation
      field_simp
    · simp [hr]

/-- An occupied parent forces the root vacant, leaving the original child forest law. -/
theorem forestLaw_root_forced_mass (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (x : A.root.Vertex → Bool) :
    (forestLaw A.root activity ha true).mass x =
      if x none then 0 else
        (forestLaw A (fun v => activity (some v)) (fun v => ha (some v)) false).mass (fun v => x (some v)) := by
  simp only [forestLaw_mass, true_and, rootsVacant_root,
    Bool.false_eq_true, false_and, ↓reduceIte, forestNormalizer, weightedAvoidRoots_root,
    ]
  rw [booleanWeight_root A activity x]
  cases x none <;> simp

end HardCoreActivityThreshold
