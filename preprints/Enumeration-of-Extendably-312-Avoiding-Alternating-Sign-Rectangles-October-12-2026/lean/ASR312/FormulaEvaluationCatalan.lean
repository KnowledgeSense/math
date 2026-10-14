import ASR312.SeriesDefinitions
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution

noncomputable section
open PowerSeries
namespace ASR312

def catalanRationalSeries : PowerSeries ℚ :=
  PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

@[simp] theorem catalanRationalSeries_coeff (n : ℕ) :
    coeff n catalanRationalSeries=(catalan n:ℚ) := by simp [catalanRationalSeries]

@[simp] theorem catalanRationalSeries_constantCoeff :
    constantCoeff catalanRationalSeries=1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,catalanRationalSeries_coeff]
  norm_num

theorem catalanRationalSeries_quadratic :
    catalanRationalSeries=1+X*catalanRationalSeries^2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simpa only [map_add,map_mul,map_one,map_pow,map_X,catalanRationalSeries,mul_comm,add_comm]
    using h.symm

/-- Uniqueness of a quadratic formal series with zero-constant quadratic coefficient. -/
theorem quadratic_series_unique (a b t : PowerSeries ℚ) (ht : constantCoeff t=0)
    (ha : a=1+t*a^2) (hb : b=1+t*b^2) : a=b := by
  have he : (a-b)*(1-t*(a+b))=0 := by linear_combination ha-hb
  have hn : (1-t*(a+b):PowerSeries ℚ) ≠ 0 := by
    intro h
    have hc := congrArg constantCoeff h
    simp [ht] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hn)

def catalanArgument : PowerSeries ℚ := X*((1-X)⁻¹)^2

@[simp] theorem catalanArgument_constantCoeff : constantCoeff catalanArgument=0 := by
  simp [catalanArgument]

theorem catalan_subst_quadratic (t : PowerSeries ℚ) (ht : constantCoeff t=0) :
    catalanRationalSeries.subst t=1+t*(catalanRationalSeries.subst t)^2 := by
  have hs : HasSubst t := HasSubst.of_constantCoeff_zero' ht
  have h := congrArg (substAlgHom hs) catalanRationalSeries_quadratic
  simpa only [map_add,map_mul,map_one,map_pow,coe_substAlgHom,subst_X hs] using h

theorem catalanArgument_cancel : catalanArgument*(1-X)^2=X := by
  have hi : ((1-X):PowerSeries ℚ)⁻¹*(1-X)=1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  unfold catalanArgument
  rw [mul_assoc,← mul_pow,hi,one_pow,mul_one]

theorem catalan_positive_substitution :
    catalanRationalSeries.subst catalanArgument=(1-X)*R := by
  apply quadratic_series_unique _ _ catalanArgument catalanArgument_constantCoeff
    (catalan_subst_quadratic _ catalanArgument_constantCoeff)
  have hc := catalanArgument_cancel
  have hr := R_quadratic
  rw [mul_pow]
  linear_combination hr-R^2*hc

theorem catalan_negative_substitution :
    catalanRationalSeries.subst (-catalanArgument)=1-X := by
  apply quadratic_series_unique _ _ (-catalanArgument) (by simp)
    (catalan_subst_quadratic _ (by simp))
  have hc := catalanArgument_cancel
  linear_combination hc

/-- The even Catalan substitution, including its constant coefficient. -/
theorem even_catalan_substitution :
    C (1/2)*(catalanRationalSeries.subst catalanArgument+
      catalanRationalSeries.subst (-catalanArgument)) =
      C (1/2)*(1-X)*(1+R) := by
  rw [catalan_positive_substitution,catalan_negative_substitution]
  ring

def evenCatalanSeries : PowerSeries ℚ :=
  mk (fun n => if Even n then (catalan n:ℚ) else 0)

@[simp] theorem evenCatalanSeries_coeff (n : ℕ) :
    coeff n evenCatalanSeries=if Even n then (catalan n:ℚ) else 0 := by
  simp [evenCatalanSeries]

theorem evenCatalanSeries_split :
    evenCatalanSeries=C (1/2)*(catalanRationalSeries+rescale (-1) catalanRationalSeries) := by
  ext n
  rw [evenCatalanSeries_coeff,coeff_C_mul,map_add,coeff_rescale,catalanRationalSeries_coeff]
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  · simp [pow_mul]
    ring
  · simp [pow_add,pow_mul]

theorem evenCatalanSeries_subst (t : PowerSeries ℚ) (ht : constantCoeff t=0) :
    evenCatalanSeries.subst t=C (1/2)*
      (catalanRationalSeries.subst t+catalanRationalSeries.subst (-t)) := by
  have hs : HasSubst t := HasSubst.of_constantCoeff_zero' ht
  have hx : HasSubst (-(X:PowerSeries ℚ)) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [evenCatalanSeries_split,subst_mul hs,subst_C,subst_add hs,rescale_eq_subst]
  simp only [neg_one_smul]
  rw [subst_comp_subst_apply hx hs]
  have he : (-X:PowerSeries ℚ).subst t = -t := by
    rw [← coe_substAlgHom (R:=ℚ) hs,map_neg,substAlgHom_X hs]
  rw [he]
  rfl

theorem evenCatalanSeries_argument :
    evenCatalanSeries.subst catalanArgument=C (1/2)*(1-X)*(1+R) := by
  rw [evenCatalanSeries_subst _ catalanArgument_constantCoeff,even_catalan_substitution]

end ASR312
