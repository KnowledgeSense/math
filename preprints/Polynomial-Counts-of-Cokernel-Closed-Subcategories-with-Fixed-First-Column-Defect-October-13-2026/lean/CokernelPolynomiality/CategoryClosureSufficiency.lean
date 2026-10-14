import CokernelPolynomiality.NormalizedPartition
import CokernelPolynomiality.FamilyPresentation
import CokernelPolynomiality.DirectPairCokernel
import CokernelPolynomiality.IteratedCokernels

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

theorem intervalFamily_cokernel_mem_hull {n m a b : ℕ} {Y : Finset (ℕ × ℕ)}
    (hY : IsClosed Y) (hab : a ≤ b) (hbn : b ≤ n) (hmem : (a,b) ∈ Y)
    (c d : Fin m → ℕ) (hcd : ∀ j, c j ≤ d j ∧ d j ≤ n ∧ (c j,d j) ∈ Y)
    (f : intervalRep n a b ⟶ intervalFamily n m c d) :
    IntervalHull n Y (cokernel f) := by
  classical
  let R := Classical.choice (endpoint_reduction_exists m (familyActive f) c d)
  let eQ := (Finset.univ \ R.P).equivFin.symm
  let cp := fun j => c (R.enumeration j).val
  let dp := fun j => d (R.enumeration j).val
  have ho (j : Fin R.P.card) : a ≤ cp j ∧ cp j ≤ b ∧ b ≤ dp j :=
    intervalHom_order_of_ne_zero (f ≫ intervalFamilyProj n m c d (R.enumeration j).val)
      ((mem_familyActive f _).mp (R.subset (R.enumeration j).property)) hbn
  let g := orderedFamilySource n a b cp dp (fun j => (ho j).1) (fun j => (ho j).2.2)
  have hg : IntervalHull n Y (cokernel g) := orderedFamily_cokernel_mem_hull hY hmem cp dp
    R.increasing R.decreasing (fun j => (ho j).1) (fun j => (ho j).2.1)
    (fun j => (ho j).2.2) (fun j => (hcd _).2.1) (fun j => (hcd _).2.2)
  let W := intervalFamily n (Finset.univ \ R.P).card
    (fun j => c (eQ j).val) (fun j => d (eQ j).val)
  have hW : IntervalHull n Y W := intervalFamily_mem_hull _ _ (fun j =>
    .interval _ _ (hcd (eQ j).val).1 (hcd (eQ j).val).2.1 (hcd (eQ j).val).2.2)
  let e := familyNormalization f hab hbn R ≪≫ intervalFamilyPartitionIso n m c d R.P R.enumeration eQ
  have he : f ≫ e.hom = (Iso.refl (intervalRep n a b)).hom ≫ directPairLift g (0 : intervalRep n a b ⟶ W) := by
    simpa only [e,Iso.trans_hom,Iso.refl_hom,Category.id_comp] using
      familyNormalization_partition f hab hbn R eQ (fun j => (ho j).1) (fun j => (ho j).2.2)
  let ei := cokernel.mapIso f (directPairLift g (0 : intervalRep n a b ⟶ W)) (Iso.refl _) e he
  apply IntervalHull.iso ei.symm
  apply IntervalHull.iso (directPairCokernelIso g W).symm
  exact .iso (directPairIsoBiprod _ _).symm (.biprod _ _ hg hW)

theorem IntervalHull.interval_source_cokernel_mem {n a b : ℕ} {Y : Finset (ℕ × ℕ)}
    (hY : IsClosed Y) (hab : a ≤ b) (hbn : b ≤ n) (hmem : (a,b) ∈ Y)
    {V : ChainRep.{0} n} (hV : IntervalHull n Y V) (f : intervalRep n a b ⟶ V) :
    IntervalHull n Y (cokernel f) := by
  obtain ⟨m,c,d,hcd,⟨e⟩⟩ := hV.family_presentation
  exact .iso (cokernelCompIsIso f e.hom)
    (intervalFamily_cokernel_mem_hull hY hab hbn hmem c d hcd (f ≫ e.hom))

/-- The finite three-point rule implies closure under every actual categorical
cokernel, with arbitrary source and target representations. -/
theorem IntervalHull.cokernel_mem {n : ℕ} {Y : Finset (ℕ × ℕ)} (hY : IsClosed Y)
    {V W : ChainRep.{0} n} (hV : IntervalHull n Y V) (hW : IntervalHull n Y W) (f : V ⟶ W) :
    IntervalHull n Y (cokernel f) :=
  IntervalHull.cokernel_mem_of_interval_sources
    (fun _ _ hab hbn hmem _ hZ f => IntervalHull.interval_source_cokernel_mem hY hab hbn hmem hZ f) hV hW f

end CokernelPolynomiality
