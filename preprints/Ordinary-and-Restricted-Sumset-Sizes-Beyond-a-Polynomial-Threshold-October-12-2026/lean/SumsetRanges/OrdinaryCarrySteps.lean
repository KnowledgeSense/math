import SumsetRanges.CarryHSeries
import Mathlib.RingTheory.PowerSeries.Inverse

open Finset
namespace SumsetRanges

theorem ordinary_carryG_step (m r : ℕ) (hm : 2≤m) :
    geometricSeries^2*ordinarySeries (carryG m r)-ordinarySeries (carryG m (r+1))=
      PowerSeries.X^m*geometricSeries^2*ordinarySeries (carryG m r) := by
  rw [ordinarySeries_carryG m r hm,ordinarySeries_carryG m (r+1) hm]
  have he : 2*(r+1)+1=(2*r+1)+2 := by omega
  rw [he,pow_add,pow_succ]
  ring

theorem geometricSeries_sub_one :
    geometricSeries-1=PowerSeries.X*geometricSeries := by
  have he := geometricSeries_identity
  calc
    _ = geometricSeries-geometricSeries*(1-PowerSeries.X) := by rw [he]
    _ = _ := by ring

theorem geometricSeries_sub_polynomial (m : ℕ) :
    geometricSeries-(geometricPolynomial m : PowerSeries ℤ)=PowerSeries.X^m*geometricSeries := by
  rw [geometricPolynomial_series]
  ring

theorem geometricPolynomial_sub_one (m : ℕ) (hm : 1≤m) :
    (geometricPolynomial m : PowerSeries ℤ)-1=
      PowerSeries.X*geometricSeries*(1-PowerSeries.X^(m-1)) := by
  have hpow : (PowerSeries.X : PowerSeries ℤ)^m=PowerSeries.X*PowerSeries.X^(m-1) := by
    rw [←pow_succ']; congr 1; omega
  rw [geometricPolynomial_series,hpow]
  have he := geometricSeries_sub_one
  calc
    _ = (geometricSeries-1)-PowerSeries.X*PowerSeries.X^(m-1)*geometricSeries := by ring
    _ = _ := by rw [he]; ring

theorem geometricPolynomial_power_sub_one (m u : ℕ) :
    (geometricPolynomial m : PowerSeries ℤ)^u-1=
      ((geometricPolynomial m : PowerSeries ℤ)-1)*
        ∑j∈range u,(geometricPolynomial m : PowerSeries ℤ)^j := by
  rw [mul_comm,geom_sum_mul]

theorem ordinary_carryH_step (m u : ℕ) (hm : 2≤m) :
    geometricSeries^2*ordinarySeries (carryH m u)-ordinarySeries (carryH m (u+1))=
      PowerSeries.X^(m+1)*geometricSeries^(u+3)*
        ∑j∈range u,(geometricPolynomial m : PowerSeries ℤ)^j := by
  let J : PowerSeries ℤ := geometricPolynomial m
  let D : PowerSeries ℤ := 1-PowerSeries.X^(m-1)
  have hn : IsUnit D := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [D,show m-1≠0 by omega]
  apply hn.mul_right_cancel
  have hu := ordinarySeries_carryH m u hm
  have hu' := ordinarySeries_carryH m (u+1) hm
  change ordinarySeries (carryH m u)*D=(geometricSeries*J)^u-PowerSeries.X^(m-1)*geometricSeries^u at hu
  change ordinarySeries (carryH m (u+1))*D=(geometricSeries*J)^(u+1)-PowerSeries.X^(m-1)*geometricSeries^(u+1) at hu'
  have hm' : (PowerSeries.X : PowerSeries ℤ)^(m-1)*PowerSeries.X=PowerSeries.X^m := by
    rw [←pow_succ]; congr 1; omega
  calc
    _ = geometricSeries^2*(ordinarySeries (carryH m u)*D)-ordinarySeries (carryH m (u+1))*D := by ring
    _ = geometricSeries^(u+1)*(J^u*(geometricSeries-J)-PowerSeries.X^(m-1)*(geometricSeries-1)) := by
      rw [hu,hu',mul_pow,pow_succ,mul_pow,pow_succ]
      ring
    _ = geometricSeries^(u+2)*PowerSeries.X^m*(J^u-1) := by
      rw [show geometricSeries-J=PowerSeries.X^m*geometricSeries from geometricSeries_sub_polynomial m,
        geometricSeries_sub_one]
      have he : PowerSeries.X^(m-1)*(PowerSeries.X*geometricSeries)=PowerSeries.X^m*geometricSeries := by rw [←mul_assoc,hm']
      rw [he,show u+2=(u+1)+1 by omega,pow_succ]
      ring
    _ = _ := by
      rw [show J^u-1=(J-1)*∑j∈range u,J^j from geometricPolynomial_power_sub_one m u,
        show J-1=PowerSeries.X*geometricSeries*D from geometricPolynomial_sub_one m (by omega)]
      rw [show u+3=(u+2)+1 by omega,pow_succ,pow_succ]
      ring

end SumsetRanges
