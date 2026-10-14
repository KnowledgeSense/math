import HonestEmbeddingDimension.FormalValues
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution

namespace HonestEmbeddingDimension

/-- The rational binomial series obeys the expected integer power rule. -/
theorem binomialSeries_pow_rat (s : ℚ) (n : ℕ) :
    PowerSeries.binomialSeries ℂ s ^ n = PowerSeries.binomialSeries ℂ ((n : ℚ)*s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← PowerSeries.binomialSeries_add]
    congr 1
    push_cast
    ring

/-- A normalized formal unit has a normalized m-th root. -/
theorem exists_normalized_formal_root (u : PowerSeries ℂ) (hu : u.constantCoeff=1)
    (m : ℕ) (hm : 0 < m) :
    ∃ v : PowerSeries ℂ, v.constantCoeff=1 ∧ v^m=u := by
  have hzero : (u-1).constantCoeff=0 := by simp [hu]
  have hs : PowerSeries.HasSubst (u-1) := PowerSeries.HasSubst.of_constantCoeff_zero' hzero
  let v := (PowerSeries.binomialSeries ℂ (1/(m : ℚ))).subst (u-1)
  refine ⟨v, ?_, ?_⟩
  · dsimp [v]
    change MvPowerSeries.constantCoeff _ = 1
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hzero]
    simp
  · dsimp [v]
    rw [← PowerSeries.subst_pow hs, binomialSeries_pow_rat]
    have he : (m : ℚ)*(1/(m : ℚ))=1 := by
      have hmn : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      field_simp
    rw [he]
    have hb : PowerSeries.binomialSeries ℂ (1 : ℚ) = 1+PowerSeries.X := by
      simpa using (PowerSeries.binomialSeries_nat (R := ℚ) (A := ℂ) 1)
    rw [hb, PowerSeries.subst_add hs, PowerSeries.subst_X hs]
    have hone : (1 : PowerSeries ℂ).subst (u-1)=1 := by
      simpa only [PowerSeries.coe_substAlgHom] using
        (map_one (PowerSeries.substAlgHom (R := ℂ) hs))
    rw [hone]
    abel

/-- A series with leading term t^m is the m-th power of a parameter tangent to the identity. -/
theorem exists_formal_parameter (f : PowerSeries ℂ) (m : ℕ) (hm : 0 < m)
    (hf : f.order=m) (hlead : PowerSeries.coeff m f=1) :
    ∃ θ : PowerSeries ℂ, θ.constantCoeff=0 ∧ PowerSeries.coeff 1 θ=1 ∧ θ^m=f := by
  let u := f.divXPowOrder
  have hu : u.constantCoeff=1 := by
    simp [u, PowerSeries.constantCoeff_divXPowOrder, hf, hlead]
  obtain ⟨v,hv,hpow⟩ := exists_normalized_formal_root u hu m hm
  refine ⟨PowerSeries.X*v, by simp, ?_, ?_⟩
  · simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hv
  · rw [mul_pow, hpow]
    simpa [hf, u] using (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))

/-- Formal reparametrization can make any normalized coordinate exactly t^m. -/
theorem exists_formal_normalization (f : PowerSeries ℂ) (m : ℕ) (hm : 0 < m)
    (hf : f.order=m) (hlead : PowerSeries.coeff m f=1) :
    ∃ θ η : PowerSeries ℂ,
      θ.constantCoeff=0 ∧ η.constantCoeff=0 ∧
      θ.subst η=PowerSeries.X ∧ η.subst θ=PowerSeries.X ∧
      f.subst η=PowerSeries.X^m := by
  obtain ⟨θ,hθ0,hθ1,hpow⟩ := exists_formal_parameter f m hm hf hlead
  have hunit : IsUnit (PowerSeries.coeff 1 θ) := hθ1 ▸ isUnit_one
  let η := θ.substInvOfIsUnit hunit
  have hη0 : η.constantCoeff=0 := PowerSeries.constantCoeff_substInvOfIsUnit θ hunit
  have hθη : θ.subst η=PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right θ hθ0 hunit
  have hηθ : η.subst θ=PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left θ hθ0 hunit
  refine ⟨θ,η,hθ0,hη0,hθη,hηθ,?_⟩
  rw [← hpow, PowerSeries.subst_pow (PowerSeries.HasSubst.of_constantCoeff_zero' hη0), hθη]

end HonestEmbeddingDimension
