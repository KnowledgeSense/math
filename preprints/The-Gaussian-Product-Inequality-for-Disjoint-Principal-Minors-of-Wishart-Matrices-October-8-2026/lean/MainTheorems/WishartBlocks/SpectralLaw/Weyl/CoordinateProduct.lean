import MainTheorems.WishartBlocks.SpectralLaw.Weyl.PatchChange
import Mathlib.MeasureTheory.Constructions.Pi

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set
open scoped ENNReal

abbrev StrictLowerIndex (n : ℕ) :=
  {e : Fin n ×ₗ Fin n // e.2 < e.1}

noncomputable def lowerIndexEquiv (n : ℕ) : Fin n ⊕ StrictLowerIndex n ≃ LowerIndex n where
  toFun
    | .inl i => ⟨toLex (i, i), le_refl _⟩
    | .inr e => ⟨e.val, e.property.le⟩
  invFun e := if h : e.val.1 = e.val.2 then .inl e.val.1
    else .inr ⟨e.val, lt_of_le_of_ne e.property (Ne.symm h)⟩
  left_inv := by
    rintro (i | e)
    · change (if h : i = i then Sum.inl i else
        Sum.inr (⟨toLex (i, i), lt_of_le_of_ne (le_refl i) (Ne.symm h)⟩ :
          StrictLowerIndex n)) = Sum.inl i
      rw [dite_eq_left rfl]
    · simp [ne_of_gt e.property]
  right_inv := by
    intro e
    dsimp only
    by_cases h : e.val.1 = e.val.2
    · rw [dite_eq_left h]
      apply Subtype.ext
      exact Prod.ext rfl h
    · rw [dite_eq_right h]

noncomputable def coordinateProductEquiv (n : ℕ) :
    ((Fin n → ℝ) × (StrictLowerIndex n → ℝ)) ≃ᵐ (LowerIndex n → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ StrictLowerIndex n => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : LowerIndex n => ℝ) (lowerIndexEquiv n))

theorem coordinateProductEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (coordinateProductEquiv n) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : LowerIndex n => ℝ)
    (lowerIndexEquiv n)).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin n ⊕ StrictLowerIndex n => ℝ))

noncomputable def jointParameters {n : ℕ}
    (lam : Fin n → ℝ) (θ : StrictLowerIndex n → ℝ) : LowerIndex n → ℝ :=
  coordinateProductEquiv n (lam, θ)

@[simp] theorem jointParameters_diagonal {n : ℕ}
    (lam : Fin n → ℝ) (θ : StrictLowerIndex n → ℝ) (i : Fin n) :
    jointParameters lam θ ⟨toLex (i, i), le_refl _⟩ = lam i := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : LowerIndex n => ℝ)
    (lowerIndexEquiv n)
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin n ⊕ StrictLowerIndex n => ℝ)).symm (lam, θ)) (.inl i)

@[simp] theorem jointParameters_strictLower {n : ℕ}
    (lam : Fin n → ℝ) (θ : StrictLowerIndex n → ℝ) (e : StrictLowerIndex n) :
    jointParameters lam θ ⟨e.val, e.property.le⟩ = θ e := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : LowerIndex n => ℝ)
    (lowerIndexEquiv n)
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin n ⊕ StrictLowerIndex n => ℝ)).symm (lam, θ)) (.inr e)

@[simp] theorem diagonalCoordinates_jointParameters {n : ℕ}
    (lam : Fin n → ℝ) (θ : StrictLowerIndex n → ℝ) :
    diagonalCoordinates (jointParameters lam θ) = lam := by
  funext i
  exact jointParameters_diagonal lam θ i

noncomputable def angleParameters {n : ℕ} (θ : StrictLowerIndex n → ℝ) :
    LowerIndex n → ℝ := jointParameters 0 θ

@[simp] theorem angleCoordinates_jointParameters {n : ℕ}
    (lam : Fin n → ℝ) (θ : StrictLowerIndex n → ℝ) :
    angleCoordinates (jointParameters lam θ) = angleParameters θ := by
  funext e
  by_cases h : e.val.1 = e.val.2
  · have he : (⟨toLex (e.val.1, e.val.1), le_refl _⟩ : LowerIndex n) = e :=
      Subtype.ext (Prod.ext rfl h)
    rw [← he]
    change (if e.val.1 = e.val.1 then (0 : ℝ) else
      jointParameters lam θ ⟨toLex (e.val.1, e.val.1), le_refl _⟩) =
      jointParameters 0 θ ⟨toLex (e.val.1, e.val.1), le_refl _⟩
    rw [ite_eq_left rfl, jointParameters_diagonal]
    rfl
  · let off : StrictLowerIndex n := ⟨e.val, lt_of_le_of_ne e.property (Ne.symm h)⟩
    have he : (⟨off.val, off.property.le⟩ : LowerIndex n) = e := rfl
    have hoff : off.val.1 ≠ off.val.2 := ne_of_gt off.property
    rw [← he]
    simp [angleCoordinates, spectralParameters, hoff,
      angleParameters, jointParameters_strictLower]

theorem jointParameters_continuous (n : ℕ) :
    Continuous (fun p : (Fin n → ℝ) × (StrictLowerIndex n → ℝ) =>
      jointParameters p.1 p.2) := by
  apply continuous_pi
  intro e
  by_cases h : e.val.1 = e.val.2
  · have he : (⟨toLex (e.val.1, e.val.1), le_refl _⟩ : LowerIndex n) = e :=
      Subtype.ext (Prod.ext rfl h)
    have hvalue (p : (Fin n → ℝ) × (StrictLowerIndex n → ℝ)) :
        jointParameters p.1 p.2 e = p.1 e.val.1 := by
      simpa only [he] using jointParameters_diagonal p.1 p.2 e.val.1
    convert (continuous_apply e.val.1).comp
      (continuous_fst : Continuous (Prod.fst :
        (Fin n → ℝ) × (StrictLowerIndex n → ℝ) → (Fin n → ℝ))) using 1
    funext p
    exact hvalue p
  · let off : StrictLowerIndex n := ⟨e.val, lt_of_le_of_ne e.property (Ne.symm h)⟩
    have he : (⟨off.val, off.property.le⟩ : LowerIndex n) = e := rfl
    have hvalue (p : (Fin n → ℝ) × (StrictLowerIndex n → ℝ)) :
        jointParameters p.1 p.2 e = p.2 off := by
      simpa only [he] using jointParameters_strictLower p.1 p.2 off
    convert (continuous_apply off).comp
      (continuous_snd : Continuous (Prod.snd :
        (Fin n → ℝ) × (StrictLowerIndex n → ℝ) → (StrictLowerIndex n → ℝ))) using 1
    funext p
    exact hvalue p

theorem angleParameters_continuous (n : ℕ) : Continuous (angleParameters (n := n)) :=
  (jointParameters_continuous n).comp (continuous_const.prodMk continuous_id)

def angularParameterPatch {n : ℕ} (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀) :
    Set (StrictLowerIndex n → ℝ) :=
  angleParameters ⁻¹' (exponentialSpectralChart lam₀ hlam₀).source

theorem angularParameterPatch_isOpen {n : ℕ} (lam₀ : Fin n → ℝ)
    (hlam₀ : Function.Injective lam₀) : IsOpen (angularParameterPatch lam₀ hlam₀) :=
  (exponentialSpectralChart lam₀ hlam₀).open_source.preimage (angleParameters_continuous n)

theorem jointParameters_mem_angularPatchDomain_iff {n : ℕ}
    (lam₀ : Fin n → ℝ) (hlam₀ : Function.Injective lam₀)
    (lam : Fin n → ℝ) (θ : StrictLowerIndex n → ℝ) :
    jointParameters lam θ ∈ angularPatchDomain lam₀ hlam₀ ↔
      StrictMono lam ∧ θ ∈ angularParameterPatch lam₀ hlam₀ := by
  simp only [angularPatchDomain, mem_ofPred_eq, diagonalCoordinates_jointParameters,
    angleCoordinates_jointParameters, angularParameterPatch, mem_preimage]

theorem lintegral_coordinateProduct {n : ℕ}
    {F : (LowerIndex n → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z) = ∫⁻ lam, ∫⁻ θ, F (jointParameters lam θ) := by
  rw [(coordinateProductEquiv_measurePreserving n).lintegral_map_equiv F
    (coordinateProductEquiv n)]
  exact lintegral_prod _ (hF.comp (coordinateProductEquiv n).measurable).aemeasurable

end ResearchMain.WishartBlocks.Weyl
