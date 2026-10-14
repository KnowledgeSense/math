import ASR312.SeriesChangeOfVariable

noncomputable section
open PowerSeries
open scoped PowerSeries
namespace ASR312

/-- A coefficientwise diagonal identity for a normalized implicit power series. -/
theorem diagonal_coefficient (φ H w T : PowerSeries ℚ)
    (hφ : constantCoeff φ=1) (hw0 : constantCoeff w=0)
    (hw : w=X*φ.subst w)
    (hT : T*(1-X*(derivative φ).subst w)=H.subst w) (n : ℕ) :
    coeff n T=coeff n (H*φ^n) := by
  let u : PowerSeries ℚ := φ⁻¹
  let g : PowerSeries ℚ := X*u
  have huv : u*φ=1 := PowerSeries.inv_mul_cancel φ (by rw [hφ]; norm_num)
  have hu : constantCoeff u=1 := by simp [u,hφ]
  have hg : HasSubst g := HasSubst.X'.mul_left
  have hw' : HasSubst w := HasSubst.of_constantCoeff_zero' hw0
  have hgw : g.subst w=X := by
    have hsub := congrArg (substAlgHom hw') huv
    simp only [map_mul,map_one,coe_substAlgHom] at hsub
    change (X*u).subst w=X
    rw [subst_mul hw',subst_X hw']
    calc
      _ = (X*φ.subst w)*u.subst w := congrArg (fun z : PowerSeries ℚ => z*u.subst w) hw
      _ = X*(u.subst w*φ.subst w) := by ring
      _ = X := by rw [hsub,mul_one]
  have hg0 : constantCoeff g=0 := by simp [g]
  have hg1 : IsUnit (coeff 1 g) := by
    have hc : coeff 1 g=1 := by
      change coeff (0+1) (X*u)=1
      rw [coeff_succ_X_mul,coeff_zero_eq_constantCoeff_apply,hu]
    rw [hc]
    exact isUnit_one
  have hwg : w.subst g=X :=
    subst_eq_X_of_subst_eq_X g hg0 hg1 hw' hgw
  have hsub := congrArg (substAlgHom hg) hT
  simp only [map_mul,map_sub,map_one,coe_substAlgHom,subst_X hg,
    subst_comp_subst_apply hw' hg,hwg,X_subst] at hsub
  have hder : derivative u = -u^2*derivative φ := by
    dsimp [u]
    exact derivative_inv' φ
  have he : T.subst g*(u+X*derivative u)*φ^(n+1)=H*φ^n := by
    have hp : u*φ^(n+1)=φ^n := by
      rw [pow_succ]
      calc
        u*(φ^n*φ)=(u*φ)*φ^n := by ring
        _ = φ^n := by rw [huv,one_mul]
    have hx : u+X*derivative u=u*(1-g*derivative φ) := by
      rw [hder]
      dsimp [g]
      ring
    rw [hx]
    calc
      _ = (T.subst g*(1-g*derivative φ))*(u*φ^(n+1)) := by ring
      _ = H*φ^n := by rw [hsub,hp]
  have hc := coefficient_change_of_variable T u φ huv n
  rw [he] at hc
  exact hc.symm

end ASR312
