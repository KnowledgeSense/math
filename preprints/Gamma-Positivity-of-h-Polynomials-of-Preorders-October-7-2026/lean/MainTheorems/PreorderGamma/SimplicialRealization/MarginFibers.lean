import MainTheorems.PreorderGamma.SimplicialRealization.DiagonalLifting
import MainTheorems.PreorderReciprocity.Compositions

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

structure ProjectedMargins (z : E → ℤ) (t : ℕ) where
  left : Option E → ℕ
  right : Option E → ℕ
  left_total : (∑ a, left a) = t
  right_total : (∑ b, right b) = t
  projection : marginProjection left right = z
  feasible : Nonempty (NaturalTransport augmentedRelation left right)

omit [DecidableEq E] in
theorem ProjectedMargins.ext {z : E → ℤ} {t : ℕ} {p q : ProjectedMargins z t}
    (hl : p.left = q.left) (hr : p.right = q.right) : p = q := by
  cases p
  cases q
  cases hl
  cases hr
  rfl

abbrev DiagonalFiber (z : E → ℤ) (t : ℕ) :=
  {g : E → ℕ // quotientLatticeDegree z + (∑ i, g i) ≤ t}

instance diagonalFiberFinite (z : E → ℤ) (t : ℕ) : Finite (DiagonalFiber z t) := by
  let f : DiagonalFiber z t → E → Fin (t + 1) := fun g i =>
    ⟨g.val i, Nat.lt_succ_of_le (by
      have hs := g.property
      have hi : g.val i ≤ ∑ j, g.val j :=
        Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      omega)⟩
  apply Finite.of_injective f
  intro g h heq
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun heq i)

def projectedMarginOverlap {z : E → ℤ} {t : ℕ}
    (p : ProjectedMargins z t) : DiagonalFiber z t :=
  ⟨originalOverlap p.left p.right, by
    obtain ⟨q⟩ := p.feasible
    have h := quotientLatticeDegree_projection_bound p.left p.right t
      p.left_total p.right_total q
    rw [p.projection] at h
    change quotientLatticeDegree z + overlapMass p.left p.right ≤ t
    omega⟩

def liftProjectedMargins {z : E → ℤ} {t : ℕ} (g : DiagonalFiber z t) :
    ProjectedMargins z t where
  left := liftedLeftMargin z g.val t
  right := liftedRightMargin z g.val t
  left_total := liftedLeftMargin_total z g.val t g.property
  right_total := liftedRightMargin_total z g.val t g.property
  projection := liftedMargins_projection z g.val t
  feasible := liftedMargins_nonempty z g.val t g.property

def projectedMarginFiberEquiv (z : E → ℤ) (t : ℕ) :
    ProjectedMargins z t ≃ DiagonalFiber z t where
  toFun := projectedMarginOverlap
  invFun := liftProjectedMargins
  left_inv := by
    intro p
    apply ProjectedMargins.ext
    · change liftedLeftMargin z (originalOverlap p.left p.right) t = p.left
      have h := lift_original_left p.left p.right t p.left_total
      simpa only [p.projection] using h
    · change liftedRightMargin z (originalOverlap p.left p.right) t = p.right
      have h := lift_original_right p.left p.right t p.right_total
      simpa only [p.projection] using h
  right_inv := by
    intro g
    apply Subtype.ext
    exact liftedMargins_overlap z g.val t

noncomputable def boundedFunctionEquivFin (k : ℕ) :
    {g : E → ℕ // (∑ i, g i) ≤ k} ≃
      {g : Fin (Fintype.card E) → ℕ // (∑ i, g i) ≤ k} := by
  let e := Fintype.equivFin E
  refine
    { toFun := fun g => ⟨fun i => g.val (e.symm i), ?_⟩
      invFun := fun g => ⟨fun i => g.val (e i), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h : (∑ i : Fin (Fintype.card E), g.val (e.symm i)) = ∑ i : E, g.val i := by
      apply Fintype.sum_equiv e.symm
      intro i
      rfl
    rw [h]
    exact g.property
  · have h : (∑ i : E, g.val (e i)) = ∑ i : Fin (Fintype.card E), g.val i := by
      apply Fintype.sum_equiv e
      intro i
      rfl
    rw [h]
    exact g.property
  · intro g
    apply Subtype.ext
    funext i
    simp
  · intro g
    apply Subtype.ext
    funext i
    simp

def diagonalFiberBoundEquiv (z : E → ℤ) (t : ℕ) (ht : quotientLatticeDegree z ≤ t) :
    DiagonalFiber z t ≃ {g : E → ℕ // (∑ i, g i) ≤ t - quotientLatticeDegree z} where
  toFun := fun g => ⟨g.val, by have h := g.property; omega⟩
  invFun := fun g => ⟨g.val, by have h := g.property; omega⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

omit [DecidableEq E] in
theorem diagonalFiber_count (z : E → ℤ) (t : ℕ) (ht : quotientLatticeDegree z ≤ t) :
    Nat.card (DiagonalFiber z t) =
      Nat.choose (Fintype.card E + (t - quotientLatticeDegree z)) (t - quotientLatticeDegree z) := by
  rw [Nat.card_congr (diagonalFiberBoundEquiv z t ht),
    Nat.card_congr (boundedFunctionEquivFin (E := E) (t - quotientLatticeDegree z))]
  exact PreorderReciprocity.bounded_composition_count _ _

theorem projectedMarginFiber_count (z : E → ℤ) (t : ℕ) (ht : quotientLatticeDegree z ≤ t) :
    Nat.card (ProjectedMargins z t) =
      Nat.choose (Fintype.card E + (t - quotientLatticeDegree z)) (t - quotientLatticeDegree z) := by
  rw [Nat.card_congr (projectedMarginFiberEquiv z t)]
  exact diagonalFiber_count z t ht

theorem projectedMarginFiber_isEmpty (z : E → ℤ) (t : ℕ)
    (ht : t < quotientLatticeDegree z) : IsEmpty (ProjectedMargins z t) := by
  refine ⟨fun p => ?_⟩
  have h := (projectedMarginOverlap p).property
  omega

instance projectedMarginFiberFinite (z : E → ℤ) (t : ℕ) : Finite (ProjectedMargins z t) :=
  Finite.of_equiv (DiagonalFiber z t) (projectedMarginFiberEquiv z t).symm

theorem projectedMarginFiber_count_all (z : E → ℤ) (t : ℕ) :
    Nat.card (ProjectedMargins z t) = if quotientLatticeDegree z ≤ t then
      Nat.choose (Fintype.card E + (t - quotientLatticeDegree z)) (t - quotientLatticeDegree z)
      else 0 := by
  by_cases ht : quotientLatticeDegree z ≤ t
  · rw [ite_eq_left ht]
    exact projectedMarginFiber_count z t ht
  · rw [ite_eq_right ht]
    let := projectedMarginFiber_isEmpty z t (lt_of_not_ge ht)
    exact Nat.card_of_isEmpty

end ResearchMain.PreorderGamma.SimplicialRealization
