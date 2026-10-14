import CokernelPolynomiality.FamilyPartitionMaps
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

private theorem directPair_hom_ext' {n : ℕ} {V W A : ChainRep n}
    {f g : directPair V W ⟶ A}
    (hV : directPairInl V W ≫ f = directPairInl V W ≫ g)
    (hW : directPairInr V W ≫ f = directPairInr V W ≫ g) : f = g := by
  calc
    f = (directPairFst V W ≫ directPairInl V W +
      directPairSnd V W ≫ directPairInr V W) ≫ f := by rw [directPair_total, Category.id_comp]
    _ = (directPairFst V W ≫ directPairInl V W +
      directPairSnd V W ≫ directPairInr V W) ≫ g := by
        simp only [Preadditive.add_comp, Category.assoc, hV, hW]
    _ = g := by rw [directPair_total, Category.id_comp]

private theorem comp_directPairLift {n : ℕ} {A X V W : ChainRep n}
    (k : A ⟶ X) (f : X ⟶ V) (g : X ⟶ W) :
    k ≫ directPairLift f g = directPairLift (k ≫ f) (k ≫ g) := rfl

private def pairQuotient {n : ℕ} {X V : ChainRep n} (f : X ⟶ V) (W : ChainRep n) :
    directPair V W ⟶ directPair (cokernel f) W :=
  directPairLift (directPairFst V W ≫ cokernel.π f) (directPairSnd V W)

private theorem pairQuotient_inl {n : ℕ} {X V : ChainRep n} (f : X ⟶ V) (W : ChainRep n) :
    directPairInl V W ≫ pairQuotient f W = cokernel.π f ≫ directPairInl (cokernel f) W := by
  apply directPair_hom_ext
  all_goals simp [pairQuotient, Category.assoc]
  all_goals simp [← Category.assoc]

private theorem pairQuotient_inr {n : ℕ} {X V : ChainRep n} (f : X ⟶ V) (W : ChainRep n) :
    directPairInr V W ≫ pairQuotient f W = directPairInr (cokernel f) W := by
  apply directPair_hom_ext
  all_goals simp [pairQuotient, Category.assoc]
  all_goals simp [← Category.assoc]

private theorem pairQuotient_condition {n : ℕ} {X V : ChainRep n}
    (f : X ⟶ V) (W : ChainRep n) : directPairLift f (0 : X ⟶ W) ≫ pairQuotient f W = 0 := by
  apply directPair_hom_ext
  all_goals simp [pairQuotient, Category.assoc]
  all_goals simp [← Category.assoc]

private def pairQuotientIsColimit {n : ℕ} {X V : ChainRep n} (f : X ⟶ V) (W : ChainRep n) :
    IsColimit (CokernelCofork.ofπ (pairQuotient f W) (pairQuotient_condition f W)) := by
  have hin : directPairLift f (0 : X ⟶ W) = f ≫ directPairInl V W := by
    apply directPair_hom_ext <;> simp [Category.assoc]
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {A} k hk =>
    directPairFst (cokernel f) W ≫ cokernel.desc f (directPairInl V W ≫ k)
        (by simpa [hin, Category.assoc] using hk) +
      directPairSnd (cokernel f) W ≫ directPairInr V W ≫ k) ?_ ?_
  · intro A k hk
    apply directPair_hom_ext'
    · simp [Preadditive.comp_add, pairQuotient_inl, ← Category.assoc]
      simp [Category.assoc]
    · simp [Preadditive.comp_add, pairQuotient_inr, ← Category.assoc]
  · intro A k hk m hm
    apply directPair_hom_ext'
    · apply (cancel_epi (cokernel.π f)).mp
      have h := congrArg (fun q => directPairInl V W ≫ q) hm
      simpa [Preadditive.comp_add, pairQuotient_inl, ← Category.assoc] using h
    · have h := congrArg (fun q => directPairInr V W ≫ q) hm
      simpa [Preadditive.comp_add, pairQuotient_inr, ← Category.assoc] using h

/-- A zero component is untouched by the quotient of a map into a direct sum. -/
def directPairCokernelIso {n : ℕ} {X V : ChainRep n} (f : X ⟶ V) (W : ChainRep n) :
    cokernel (directPairLift f (0 : X ⟶ W)) ≅ directPair (cokernel f) W :=
  colimit.isoColimitCocone ⟨_, pairQuotientIsColimit f W⟩

end CokernelPolynomiality
