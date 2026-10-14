import HonestEmbeddingDimension.FormalNormalization

namespace HonestEmbeddingDimension

/-- An invertible formal reparametrization preserves every formal order. -/
theorem order_subst_eq_of_inverse (θ η : PowerSeries ℂ)
    (hθ0 : θ.constantCoeff=0) (hη0 : η.constantCoeff=0)
    (hθη : θ.subst η=PowerSeries.X) (f : PowerSeries ℂ) :
    PowerSeries.order (f.subst θ)=f.order := by
  apply le_antisymm
  · have hh := PowerSeries.le_order_subst_left' (φ := f.subst θ) hη0
    rw [PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' hθ0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hη0), hθη, PowerSeries.X_subst] at hh
    exact hh
  · exact PowerSeries.le_order_subst_left' hθ0

/-- Actual polynomial values are invariant under invertible formal reparametrization. -/
theorem polynomialValues_reparametrization {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (θ η : PowerSeries ℂ) (hθ0 : θ.constantCoeff=0) (hη0 : η.constantCoeff=0)
    (hθη : θ.subst η=PowerSeries.X) :
    polynomialValues (fun i => (f i).subst θ)=polynomialValues f := by
  have hs : PowerSeries.HasSubst θ := PowerSeries.HasSubst.of_constantCoeff_zero' hθ0
  have he (p : MvPolynomial (Fin d) ℂ) :
      MvPolynomial.aeval (fun i => (f i).subst θ) p = (MvPolynomial.aeval f p).subst θ :=
    by simpa only [PowerSeries.coe_substAlgHom] using
      (MvPolynomial.comp_aeval_apply f (PowerSeries.substAlgHom (R := ℂ) hs) p).symm
  ext n
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨p, ?_⟩
    rw [he, order_subst_eq_of_inverse θ η hθ0 hη0 hθη] at hp
    exact hp
  · rintro ⟨p,hp⟩
    refine ⟨p, ?_⟩
    rw [he, order_subst_eq_of_inverse θ η hθ0 hη0 hθη]
    exact hp

/-- Actual multivariate formal value algebras are invariant under this reparametrization. -/
theorem formalValues_reparametrization {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff=0)
    (θ η : PowerSeries ℂ) (hθ0 : θ.constantCoeff=0) (hη0 : η.constantCoeff=0)
    (hθη : θ.subst η=PowerSeries.X) :
    formalValues (fun i => (f i).subst θ)=formalValues f := by
  have hg0 : ∀ i, ((f i).subst θ).constantCoeff=0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero hθ0 (f i) (hf0 i)
  rw [formalValues_eq_polynomialValues _ hg0, formalValues_eq_polynomialValues _ hf0]
  exact polynomialValues_reparametrization f θ η hθ0 hη0 hθη

/-- A prescribed normalized coordinate can be made exactly t^m without changing the value set. -/
theorem normalize_formal_coordinate {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff=0) (i : Fin d) (m : ℕ) (hm : 0 < m)
    (hf : (f i).order=m) (hlead : PowerSeries.coeff m (f i)=1) :
    ∃ g : Fin d → PowerSeries ℂ, g i=PowerSeries.X^m ∧
      (∀ j, (g j).constantCoeff=0) ∧ formalValues g=formalValues f ∧
      (∀ j, (g j).order=(f j).order) := by
  obtain ⟨θ,η,hθ0,hη0,hθη,hηθ,hfη⟩ := exists_formal_normalization (f i) m hm hf hlead
  refine ⟨fun j => (f j).subst η, hfη, ?_, ?_, ?_⟩
  · intro j
    exact PowerSeries.constantCoeff_subst_eq_zero hη0 (f j) (hf0 j)
  · exact formalValues_reparametrization f hf0 η θ hη0 hθ0 hηθ
  · intro j
    exact order_subst_eq_of_inverse η θ hη0 hθ0 hηθ (f j)

end HonestEmbeddingDimension
