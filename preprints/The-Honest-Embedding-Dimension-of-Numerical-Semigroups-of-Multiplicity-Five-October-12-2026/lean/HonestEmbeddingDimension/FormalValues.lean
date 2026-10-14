import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Analysis.Complex.Basic

namespace HonestEmbeddingDimension

/-- The image values of multivariate formal substitution into the given coordinate series. -/
def formalValues {d : ℕ} (f : Fin d → PowerSeries ℂ) : Set ℕ :=
  {n | ∃ p : MvPowerSeries (Fin d) ℂ, PowerSeries.order (MvPowerSeries.subst f p) = n}

/-- The values of polynomial expressions in the same coordinates. -/
def polynomialValues {d : ℕ} (f : Fin d → PowerSeries ℂ) : Set ℕ :=
  {n | ∃ p : MvPolynomial (Fin d) ℂ, PowerSeries.order (MvPolynomial.aeval f p) = n}

/-- The actual vector of coefficients of orders below `N`. -/
noncomputable def formalJet (N : ℕ) (h : PowerSeries ℂ) : Fin N → ℂ :=
  fun j => PowerSeries.coeff j h

/-- Equality of total truncations implies equality of all the corresponding univariate coefficients. -/
theorem coeff_eq_of_truncTotal_eq {N : ℕ} {f g : PowerSeries ℂ}
    (h : MvPowerSeries.truncTotal N f = MvPowerSeries.truncTotal N g)
    {j : ℕ} (hj : j < N) : PowerSeries.coeff j f = PowerSeries.coeff j g := by
  have hh := congrArg (fun p : MvPolynomial Unit ℂ => p.coeff (Finsupp.single () j)) h
  have hd : (Finsupp.single () j).degree < N := by simpa using hj
  rw [MvPowerSeries.coeff_truncTotal f hd, MvPowerSeries.coeff_truncTotal g hd] at hh
  exact hh

/-- Every finite formal-substitution jet is the jet of a polynomial in the coordinates. -/
theorem formal_substitution_jet_eq_polynomial {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf : ∀ i, (f i).constantCoeff = 0) (p : MvPowerSeries (Fin d) ℂ) (N : ℕ) :
    formalJet N (MvPowerSeries.subst f p) =
      formalJet N (MvPolynomial.aeval f (p.truncTotal N)) := by
  have h := MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
    (f := p) (k := N) hf
  rw [MvPowerSeries.subst_coe] at h
  ext j
  exact coeff_eq_of_truncTotal_eq h j.isLt

/-- Formal and polynomial algebras have exactly the same finite values, without any genericity. -/
theorem formalValues_eq_polynomialValues {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf : ∀ i, (f i).constantCoeff = 0) : formalValues f = polynomialValues f := by
  ext n
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.truncTotal (n+1), ?_⟩
    have hjet := formal_substitution_jet_eq_polynomial f hf p (n+1)
    have hc (j : ℕ) (hj : j < n+1) :
        PowerSeries.coeff j (MvPowerSeries.subst f p) =
          PowerSeries.coeff j (MvPolynomial.aeval f (p.truncTotal (n+1))) :=
      congrFun hjet ⟨j,hj⟩
    obtain ⟨hpn, hplt⟩ := PowerSeries.order_eq_nat.mp hp
    apply PowerSeries.order_eq_nat.mpr
    constructor
    · rwa [← hc n (by omega)]
    · intro j hj
      rw [← hc j (by omega)]
      exact hplt j hj
  · rintro ⟨p, hp⟩
    exact ⟨p.toMvPowerSeries, by simpa only [MvPowerSeries.subst_coe] using hp⟩

theorem zero_mem_polynomialValues {d : ℕ} (f : Fin d → PowerSeries ℂ) :
    0 ∈ polynomialValues f := by
  refine ⟨1, ?_⟩
  simp

theorem add_mem_polynomialValues {d : ℕ} (f : Fin d → PowerSeries ℂ) {m n : ℕ}
    (hm : m ∈ polynomialValues f) (hn : n ∈ polynomialValues f) :
    m+n ∈ polynomialValues f := by
  obtain ⟨p,hp⟩ := hm
  obtain ⟨q,hq⟩ := hn
  refine ⟨p*q, ?_⟩
  rw [map_mul, PowerSeries.order_mul, hp, hq]
  norm_cast

/-- The actual formal value set is closed under addition. Cofiniteness is a separate generic result. -/
noncomputable def formalValueSubmonoid {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf : ∀ i, (f i).constantCoeff = 0) : AddSubmonoid ℕ where
  carrier := formalValues f
  zero_mem' := by rw [formalValues_eq_polynomialValues f hf]; exact zero_mem_polynomialValues f
  add_mem' := by
    rw [formalValues_eq_polynomialValues f hf]
    exact add_mem_polynomialValues f

/-- Monomials in the actual coordinate series. -/
noncomputable def coordinateMonomial {d : ℕ} (f : Fin d → PowerSeries ℂ) (α : Fin d → ℕ) :
    PowerSeries ℂ := ∏ i, f i ^ α i

theorem order_coordinateMonomial {d : ℕ} (f : Fin d → PowerSeries ℂ) (r α : Fin d → ℕ)
    (hf : ∀ i, PowerSeries.order (f i) = r i) :
    PowerSeries.order (coordinateMonomial f α) = (∑ i, α i * r i : ℕ) := by
  unfold coordinateMonomial
  rw [PowerSeries.order_prod]
  simp only [PowerSeries.order_pow, hf, nsmul_eq_mul]
  norm_cast

end HonestEmbeddingDimension
