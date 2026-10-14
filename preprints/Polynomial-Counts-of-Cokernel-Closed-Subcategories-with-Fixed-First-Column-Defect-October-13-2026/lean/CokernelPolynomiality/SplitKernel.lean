import CokernelPolynomiality.RepresentationSubcategories
import CokernelPolynomiality.IntervalSeedExistence
import Mathlib.Algebra.Homology.ShortComplex.Exact

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def splitKernelProjection {n : ℕ} {X Y : ChainRep n} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r=𝟙 X) : Y ⟶ kernel r :=
  kernel.lift r (𝟙 Y-r ≫ i) (by simp [Preadditive.sub_comp,Category.assoc,h])

@[simp] theorem splitKernelProjection_ι {n : ℕ} {X Y : ChainRep n} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r=𝟙 X) : splitKernelProjection i r h ≫ kernel.ι r=𝟙 Y-r ≫ i := by
  apply kernel.lift_ι

theorem kernel_ι_splitKernelProjection {n : ℕ} {X Y : ChainRep n} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r=𝟙 X) : kernel.ι r ≫ splitKernelProjection i r h=𝟙 (kernel r) := by
  apply (cancel_mono (kernel.ι r)).mp
  rw [Category.assoc,splitKernelProjection_ι]
  simp [Preadditive.comp_sub,← Category.assoc]

/-- Splitting off an actual interval retract leaves the categorical kernel. -/
def splitKernelIso {n : ℕ} {X Y : ChainRep n} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r=𝟙 X) : Y ≅ biprod (kernel r) X := by
  let S : ShortComplex (ChainRep n) := ShortComplex.mk (kernel.ι r) r (kernel.condition r)
  let s : S.Splitting :=
    { r := splitKernelProjection i r h
      s := i
      f_r := kernel_ι_splitKernelProjection i r h
      s_g := h
      id := by simp [S] }
  exact s.isoBinaryBiproduct

end CokernelPolynomiality
