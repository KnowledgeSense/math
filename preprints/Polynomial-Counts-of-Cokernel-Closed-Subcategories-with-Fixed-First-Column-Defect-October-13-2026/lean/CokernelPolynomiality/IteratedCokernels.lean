import CokernelPolynomiality.IntervalHull

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def iteratedCokernelProjection {n : ℕ} {X Y Z : ChainRep n} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Z ⟶ cokernel (g ≫ cokernel.π f) := cokernel.π f ≫ cokernel.π (g ≫ cokernel.π f)

theorem iteratedCokernel_condition {n : ℕ} {X Y Z : ChainRep n} (f : X ⟶ Z) (g : Y ⟶ Z) :
    biprod.desc f g ≫ iteratedCokernelProjection f g=0 := by
  apply biprod.hom_ext'
  · simp [iteratedCokernelProjection]
  · simpa only [iteratedCokernelProjection,Category.assoc,biprod.inr_desc_assoc,comp_zero] using
      cokernel.condition (g ≫ cokernel.π f)

def iteratedCokernelIsColimit {n : ℕ} {X Y Z : ChainRep n} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsColimit (CokernelCofork.ofπ (iteratedCokernelProjection f g) (iteratedCokernel_condition f g)) := by
  let : Epi (iteratedCokernelProjection f g) := by
    dsimp [iteratedCokernelProjection]
    infer_instance
  apply CokernelCofork.IsColimit.ofπ'
  intro A k hk
  have hfk : f ≫ k=0 := by
    have h := congrArg (fun q => (biprod.inl : X ⟶ biprod X Y) ≫ q) hk
    simpa only [biprod.inl_desc_assoc,comp_zero] using h
  have hgk : g ≫ k=0 := by
    have h := congrArg (fun q => (biprod.inr : Y ⟶ biprod X Y) ≫ q) hk
    simpa only [biprod.inr_desc_assoc,comp_zero] using h
  let q := cokernel.desc f k hfk
  have hq : (g ≫ cokernel.π f) ≫ q=0 := by
    simp only [q,Category.assoc,cokernel.π_desc,hgk]
  refine ⟨cokernel.desc (g ≫ cokernel.π f) q hq,?_⟩
  simp only [iteratedCokernelProjection,Category.assoc,cokernel.π_desc,q]

def iteratedCokernelIso {n : ℕ} {X Y Z : ChainRep n} (f : X ⟶ Z) (g : Y ⟶ Z) :
    cokernel (biprod.desc f g) ≅ cokernel (g ≫ cokernel.π f) :=
  colimit.isoColimitCocone ⟨_,iteratedCokernelIsColimit f g⟩

/-- Once cokernels with one interval source stay in an additive hull, arbitrary
source sums do as well, by genuine successive quotient universal properties. -/
theorem IntervalHull.cokernel_mem_of_interval_sources {n : ℕ} {Y : Finset (ℕ × ℕ)}
    (hI : ∀ (a b : ℕ), a ≤ b → b ≤ n → (a,b) ∈ Y →
      ∀ (Z : ChainRep n), IntervalHull n Y Z →
      ∀ f : intervalRep n a b ⟶ Z, IntervalHull n Y (cokernel f))
    {X Z : ChainRep n} (hX : IntervalHull n Y X) (hZ : IntervalHull n Y Z)
    (f : X ⟶ Z) : IntervalHull n Y (cokernel f) := by
  induction hX generalizing Z with
  | zero X hX =>
    have hf : f=0 := hX.eq_of_src f 0
    exact .iso ((cokernelIsoOfEq hf) ≪≫ cokernelZeroIsoTarget).symm hZ
  | interval a b hab hbn hY => exact hI a b hab hbn hY Z hZ f
  | biprod V W hV hW ihV ihW =>
    let fV : V ⟶ Z := biprod.inl ≫ f
    let fW : W ⟶ Z := biprod.inr ≫ f
    have hCV := ihV hZ fV
    have hCW := ihW hCV (fW ≫ cokernel.π fV)
    have he : biprod.desc fV fW=f := by
      apply biprod.hom_ext' <;> simp [fV,fW]
    have hi := iteratedCokernelIso fV fW
    rw [he] at hi
    exact .iso hi.symm hCW
  | iso e hV ih =>
    exact .iso (cokernelEpiComp e.hom f) (ih hZ (e.hom ≫ f))

end CokernelPolynomiality
