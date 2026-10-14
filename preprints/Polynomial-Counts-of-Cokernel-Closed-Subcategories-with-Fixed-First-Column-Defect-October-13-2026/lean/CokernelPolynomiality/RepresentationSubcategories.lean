import CokernelPolynomiality.IntervalMorphisms
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CokernelPolynomiality

/-- A replete full additive, idempotent-split subcategory of actual finite
chain representations, closed under the ambient categorical cokernel. -/
structure CokernelSubcategory (n : ℕ) where
  contains : ChainRep n → Prop
  iso_closed : ∀ {X Y}, (X ≅ Y) → contains X → contains Y
  zero_mem : contains 0
  biprod_mem : ∀ {X Y}, contains X → contains Y → contains (biprod X Y)
  retract_mem : ∀ {X Y}, (i : X ⟶ Y) → (p : Y ⟶ X) → i ≫ p=𝟙 X →
    contains Y → contains X
  cokernel_mem : ∀ {X Y}, (f : X ⟶ Y) → contains X → contains Y → contains (cokernel f)

@[ext] theorem CokernelSubcategory.ext {n : ℕ} {C D : CokernelSubcategory n}
    (h : ∀ X, C.contains X ↔ D.contains X) : C=D := by
  cases C with
  | mk c hc hcz hcb hcr hcc =>
    cases D with
    | mk d hd hdz hdb hdr hdc =>
      have he : c=d := funext (fun X => propext (h X))
      subst d
      rfl

/-- The full subcategory associated to the object predicate. -/
abbrev CokernelSubcategory.category {n : ℕ} (C : CokernelSubcategory n) :=
  ObjectProperty.FullSubcategory C.contains

/-- The literal set of interval isomorphism classes selected by the subcategory. -/
def CokernelSubcategory.intervalSet {n : ℕ} (C : CokernelSubcategory n) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n+1)).product (Finset.range (n+1))).filter
    (fun p => p.1 ≤ p.2 ∧ C.contains (intervalRep n p.1 p.2))

@[simp] theorem CokernelSubcategory.mem_intervalSet {n a b : ℕ} (C : CokernelSubcategory n) :
    (a,b) ∈ C.intervalSet ↔ a ≤ b ∧ b ≤ n ∧ C.contains (intervalRep n a b) := by
  classical
  unfold intervalSet
  rw [Finset.mem_filter]
  change ((a,b) ∈ ((Finset.range (n+1)).product (Finset.range (n+1))) ∧
    a ≤ b ∧ C.contains (intervalRep n a b)) ↔ _
  rw [Finset.product_eq_sprod,Finset.mem_product]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨⟨ha,hb⟩,hab,hC⟩
    exact ⟨hab,by omega,hC⟩
  · rintro ⟨hab,hb,hC⟩
    exact ⟨⟨by omega,by omega⟩,hab,hC⟩

end CokernelPolynomiality
