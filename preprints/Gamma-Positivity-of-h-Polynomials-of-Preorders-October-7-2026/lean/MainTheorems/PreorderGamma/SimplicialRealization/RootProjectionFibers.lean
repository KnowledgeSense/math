import MainTheorems.PreorderGamma.SimplicialRealization.QuotientLattice
import MainTheorems.PreorderGamma.SimplicialRealization.MarginFibers

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

abbrev QuotientPoints (t : ℕ) := {z : E → ℤ // QuotientIntegerPoint t z}

noncomputable instance quotientPointsFintype (t : ℕ) : Fintype (QuotientPoints (E := E) t) :=
  Fintype.ofFinite _

def rootProjectedMarginEquiv (t : ℕ) :
    RootNaturalMargins (E := E) t ≃
      Σ z : QuotientPoints (E := E) t, ProjectedMargins z.val t where
  toFun p :=
    let q : ProjectedMargins (marginProjection p.val.1 p.val.2) t :=
      ⟨p.val.1, p.val.2, p.property.1, p.property.2.1, rfl, p.property.2.2⟩
    ⟨⟨marginProjection p.val.1 p.val.2, by
      apply (quotientIntegerPoint_iff_degree t _).mpr
      have h := (projectedMarginOverlap q).property
      omega⟩, q⟩
  invFun p := ⟨(p.2.left, p.2.right), p.2.left_total, p.2.right_total, p.2.feasible⟩
  left_inv := fun p => rfl
  right_inv := by
    rintro ⟨⟨z, hz⟩, p⟩
    rcases p with ⟨left, right, hl, hr, hproj, hfeas⟩
    cases hproj
    rfl

theorem rootLatticeCount_projected_fibers (t : ℕ) :
    rootLatticeCount (E := E) t =
      ∑ z : QuotientPoints (E := E) t,
        Nat.choose (Fintype.card E + (t - quotientLatticeDegree z.val))
          (t - quotientLatticeDegree z.val) := by
  classical
  rw [rootLatticeCount_natural, Nat.card_congr (rootProjectedMarginEquiv t), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro z hz
  exact projectedMarginFiber_count z.val t
    ((quotientIntegerPoint_iff_degree t z.val).mp z.property)

def quotientPointsNestedEquiv {j t : ℕ} (hjt : j ≤ t) :
    QuotientPoints (E := E) j ≃
      {z : QuotientPoints (E := E) t // quotientLatticeDegree z.val ≤ j} where
  toFun z := ⟨⟨z.val, (quotientIntegerPoint_iff_degree t z.val).mpr
    (((quotientIntegerPoint_iff_degree j z.val).mp z.property).trans hjt)⟩,
      (quotientIntegerPoint_iff_degree j z.val).mp z.property⟩
  invFun z := ⟨z.val.val, (quotientIntegerPoint_iff_degree j z.val.val).mpr z.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem quotientLatticeCount_nested {j t : ℕ} (hjt : j ≤ t) :
    quotientLatticeCount (E := E) j =
      ∑ z : QuotientPoints (E := E) t, if quotientLatticeDegree z.val ≤ j then 1 else 0 := by
  classical
  rw [quotientLatticeCount, Nat.card_congr (quotientPointsNestedEquiv (E := E) hjt),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

end ResearchMain.PreorderGamma.SimplicialRealization
