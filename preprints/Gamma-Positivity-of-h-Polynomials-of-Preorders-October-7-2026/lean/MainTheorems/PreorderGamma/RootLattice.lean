import MainTheorems.PreorderGamma.RootExposedFaces
import MainTheorems.PreorderGamma.TransportHall
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Field

namespace ResearchMain.PreorderGamma

open scoped BigOperators Pointwise Classical

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem rootPolytope_left_nonnegative
    {x : (Option E → ℝ) × (Option E → ℝ)} (hx : x ∈ rootPolytope (E := E))
    (i : Option E) : 0 ≤ x.1 i := by
  let d : RootSupportingData E :=
    ⟨fun a => if a = i then -1 else 0, fun _ => 0, 0,
      by intro a b hab; split_ifs <;> norm_num⟩
  have h := rootSupportingMap_le d hx
  have heq : rootSupportingMap d x = -x.1 i := by
    simp [d, rootSupportingMap, ite_mul, eq_comm]
  rw [heq] at h
  linarith

theorem rootPolytope_right_nonnegative
    {x : (Option E → ℝ) × (Option E → ℝ)} (hx : x ∈ rootPolytope (E := E))
    (i : Option E) : 0 ≤ x.2 i := by
  let d : RootSupportingData E :=
    ⟨fun _ => 0, fun a => if a = i then -1 else 0, 0,
      by intro a b hab; split_ifs <;> norm_num⟩
  have h := rootSupportingMap_le d hx
  have heq : rootSupportingMap d x = -x.2 i := by
    simp [d, rootSupportingMap, ite_mul, eq_comm]
  rw [heq] at h
  linarith

theorem rootPolytope_margin_totals
    {x : (Option E → ℝ) × (Option E → ℝ)} (hx : x ∈ rootPolytope (E := E)) :
    (∑ i, x.1 i) = 1 ∧ (∑ j, x.2 j) = 1 := by
  have h₁ := rootSupportingMap_le
    (⟨fun _ => 1, fun _ => 0, 1, by intro a b hab; norm_num⟩ : RootSupportingData E) hx
  have h₂ := rootSupportingMap_le
    (⟨fun _ => -1, fun _ => 0, -1, by intro a b hab; norm_num⟩ : RootSupportingData E) hx
  have h₃ := rootSupportingMap_le
    (⟨fun _ => 0, fun _ => 1, 1, by intro a b hab; norm_num⟩ : RootSupportingData E) hx
  have h₄ := rootSupportingMap_le
    (⟨fun _ => 0, fun _ => -1, -1, by intro a b hab; norm_num⟩ : RootSupportingData E) hx
  simp [rootSupportingMap, Finset.sum_neg_distrib] at h₁ h₂ h₃ h₄
  constructor <;> simp only [Fintype.sum_option] <;> linarith

theorem rootPolytope_supply_inequality
    {x : (Option E → ℝ) × (Option E → ℝ)} (hx : x ∈ rootPolytope (E := E))
    (A : Finset (Option E)) :
    (∑ i ∈ A, x.1 i) ≤ ∑ j ∈ graphNeighbors augmentedRelation A, x.2 j := by
  classical
  let B := graphNeighbors augmentedRelation A
  let d : RootSupportingData E :=
    { left := fun i => if i ∈ A then 1 else 0
      right := fun j => if j ∈ B then -1 else 0
      maximum := 0
      bound := by
        intro i j hij
        by_cases hi : i ∈ A
        · have hj : j ∈ B := mem_graphNeighbors.mpr ⟨i, hi, hij⟩
          simp [hi, hj]
        · simp [hi]
          split_ifs <;> norm_num }
  have h := rootSupportingMap_le d hx
  have heq : rootSupportingMap d x = (∑ i ∈ A, x.1 i) - ∑ j ∈ B, x.2 j := by
    simp [rootSupportingMap, d, ite_mul, Finset.sum_ite_mem,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [heq] at h
  linarith

def RootIntegerPoints (t : ℕ)
    (z : (Option E → ℤ) × (Option E → ℤ)) : Prop :=
  ((fun i => (z.1 i : ℝ)), fun j => (z.2 j : ℝ)) ∈
    (t : ℝ) • rootPolytope (E := E)

abbrev RootNaturalMargins (t : ℕ) :=
  {z : (Option E → ℕ) × (Option E → ℕ) //
    (∑ i, z.1 i) = t ∧ (∑ j, z.2 j) = t ∧
      Nonempty (NaturalTransport augmentedRelation z.1 z.2)}

theorem rootIntegerPoints_nonnegative {t : ℕ}
    {z : (Option E → ℤ) × (Option E → ℤ)} (hz : RootIntegerPoints t z) :
    (∀ i, 0 ≤ z.1 i) ∧ ∀ j, 0 ≤ z.2 j := by
  obtain ⟨x, hx, heq⟩ := Set.mem_smul_set.mp hz
  constructor
  · intro i
    have hi := mul_nonneg (Nat.cast_nonneg t) (rootPolytope_left_nonnegative hx i)
    have he := congrArg (fun y => y.1 i) heq
    change (t : ℝ) * x.1 i = (z.1 i : ℝ) at he
    rw [he] at hi
    exact_mod_cast hi
  · intro j
    have hj := mul_nonneg (Nat.cast_nonneg t) (rootPolytope_right_nonnegative hx j)
    have he := congrArg (fun y => y.2 j) heq
    change (t : ℝ) * x.2 j = (z.2 j : ℝ) at he
    rw [he] at hj
    exact_mod_cast hj

theorem rootIntegerPoints_transport {t : ℕ}
    (u v : Option E → ℕ)
    (hz : RootIntegerPoints t ((fun i => (u i : ℤ)), fun j => (v j : ℤ))) :
    (∑ i, u i) = t ∧ (∑ j, v j) = t ∧
      Nonempty (NaturalTransport augmentedRelation u v) := by
  obtain ⟨x, hx, heq⟩ := Set.mem_smul_set.mp hz
  have hl : ∀ i, (t : ℝ) * x.1 i = (u i : ℝ) := by
    intro i
    simpa only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Int.cast_natCast] using
      congrArg (fun y => y.1 i) heq
  have hr : ∀ j, (t : ℝ) * x.2 j = (v j : ℝ) := by
    intro j
    simpa only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Int.cast_natCast] using
      congrArg (fun y => y.2 j) heq
  have hsum := rootPolytope_margin_totals hx
  have hu : (∑ i, u i) = t := by
    have h : (∑ i, (u i : ℝ)) = t := by
      simp_rw [← hl]
      rw [← Finset.mul_sum, hsum.1, mul_one]
    exact_mod_cast h
  have hv : (∑ j, v j) = t := by
    have h : (∑ j, (v j : ℝ)) = t := by
      simp_rw [← hr]
      rw [← Finset.mul_sum, hsum.2, mul_one]
    exact_mod_cast h
  refine ⟨hu, hv, naturalTransport_supplyDemand _ _ _ ?_ (hu.trans hv.symm)⟩
  intro A
  have h := mul_le_mul_of_nonneg_left (rootPolytope_supply_inequality hx A)
    (Nat.cast_nonneg t : 0 ≤ (t : ℝ))
  simp only [Finset.mul_sum, hl, hr] at h
  exact_mod_cast h

theorem transport_rootIntegerPoints {t : ℕ} (u v : Option E → ℕ)
    (hu : (∑ i, u i) = t) (hv : (∑ j, v j) = t)
    (p : NaturalTransport augmentedRelation u v) :
    RootIntegerPoints t ((fun i => (u i : ℤ)), fun j => (v j : ℤ)) := by
  classical
  by_cases ht : t = 0
  · rw [ht] at hu hv ⊢
    have hu₀ : ∀ i, u i = 0 := fun i => by
      have h := Finset.single_le_sum (fun a ha => Nat.zero_le (u a)) (Finset.mem_univ i)
      rw [hu] at h
      omega
    have hv₀ : ∀ j, v j = 0 := fun j => by
      have h := Finset.single_le_sum (fun a ha => Nat.zero_le (v a)) (Finset.mem_univ j)
      rw [hv] at h
      omega
    apply Set.mem_smul_set.mpr
    refine ⟨rootVertex none none, rootVertex_mem_rootPolytope ⟨(none, none), trivial⟩, ?_⟩
    ext <;> simp [hu₀, hv₀]
  · have htℝ : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    let w : Option E × Option E → ℝ := fun e => (p.flow e.1 e.2 : ℝ) / t
    let z : Option E × Option E → (Option E → ℝ) × (Option E → ℝ) := fun e =>
      if augmentedRelation e.1 e.2 then rootVertex e.1 e.2 else rootVertex none none
    have hw₀ : ∀ e, 0 ≤ w e := fun e => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg t)
    have hw₁ : (∑ e, w e) = 1 := by
      simp only [w, Fintype.sum_prod_type, ← Finset.sum_div, ← Nat.cast_sum, p.row_sum, hu]
      exact div_self htℝ
    have hz : ∀ e, z e ∈ rootVertices (E := E) := by
      intro e
      by_cases he : augmentedRelation e.1 e.2
      · exact ⟨⟨e, he⟩, by simp [z, he]⟩
      · exact ⟨⟨(none, none), trivial⟩, by simp [z, he]⟩
    have hpoint : (∑ e, w e • z e) =
        ((fun i => (u i : ℝ) / t), fun j => (v j : ℝ) / t) := by
      have hreplace : ∀ e, w e • z e = w e • rootVertex e.1 e.2 := by
        intro e
        by_cases he : augmentedRelation e.1 e.2
        · simp [z, he]
        · simp [w, z, he, p.supported e.1 e.2 he]
      simp_rw [hreplace]
      apply Prod.ext
      · funext i
        simp only [Fintype.sum_prod_type, Prod.fst_sum, rootVertex, Prod.smul_fst,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          w, ← Finset.sum_div, ← Nat.cast_sum, p.row_sum]
      · funext j
        simp only [Fintype.sum_prod_type, Prod.snd_sum, rootVertex, Prod.smul_snd,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          w, ← Finset.sum_div, ← Nat.cast_sum, p.column_sum]
    have hmem : ((fun i => (u i : ℝ) / t), fun j => (v j : ℝ) / t) ∈ rootPolytope (E := E) :=
      mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hpoint
    apply Set.mem_smul_set.mpr
    refine ⟨_, hmem, ?_⟩
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      smul_eq_mul, Int.cast_natCast] <;> field_simp [htℝ]

theorem rootIntegerPoints_natural_iff (t : ℕ) (u v : Option E → ℕ) :
    RootIntegerPoints t ((fun i => (u i : ℤ)), fun j => (v j : ℤ)) ↔
      (∑ i, u i) = t ∧ (∑ j, v j) = t ∧
        Nonempty (NaturalTransport augmentedRelation u v) := by
  constructor
  · exact rootIntegerPoints_transport u v
  · rintro ⟨hu, hv, ⟨p⟩⟩
    exact transport_rootIntegerPoints u v hu hv p

noncomputable def rootIntegerNaturalEquiv (t : ℕ) :
    {z : (Option E → ℤ) × (Option E → ℤ) // RootIntegerPoints t z} ≃
      RootNaturalMargins (E := E) t where
  toFun z := ⟨((fun i => (z.val.1 i).toNat), fun j => (z.val.2 j).toNat), by
    apply (rootIntegerPoints_natural_iff t _ _).mp
    have hpos := rootIntegerPoints_nonnegative z.property
    simpa only [Int.toNat_of_nonneg (hpos.1 _), Int.toNat_of_nonneg (hpos.2 _)] using z.property⟩
  invFun z := ⟨((fun i => (z.val.1 i : ℤ)), fun j => (z.val.2 j : ℤ)),
    (rootIntegerPoints_natural_iff t _ _).mpr z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> funext i
    · exact Int.toNat_of_nonneg ((rootIntegerPoints_nonnegative z.property).1 i)
    · exact Int.toNat_of_nonneg ((rootIntegerPoints_nonnegative z.property).2 i)
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> exact Int.toNat_natCast _

noncomputable def rootLatticeCount (t : ℕ) : ℕ :=
  Nat.card {z : (Option E → ℤ) × (Option E → ℤ) // RootIntegerPoints t z}

theorem rootLatticeCount_natural (t : ℕ) :
    rootLatticeCount (E := E) t = Nat.card (RootNaturalMargins (E := E) t) :=
  Nat.card_congr (rootIntegerNaturalEquiv t)

end ResearchMain.PreorderGamma
