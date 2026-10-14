import SumsetRanges.CarryHPolynomial

open Finset
namespace SumsetRanges

theorem geometric_agree_bound (q n : ℕ) (hqn : q<n) :
    AgreeThrough q (geometricPolynomial n : PowerSeries ℤ) geometricSeries := by
  intro i hi
  simp [Polynomial.coeff_coe,geometricPolynomial,Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow,geometricSeries,show i<n by omega]

theorem AgreeThrough.sub {q : ℕ} {A B C D : PowerSeries ℤ}
    (hAB : AgreeThrough q A B) (hCD : AgreeThrough q C D) :
    AgreeThrough q (A-C) (B-D) := by
  intro i hi
  simp only [map_sub,hAB i hi,hCD i hi]

/-- Complete ordinary H-block identity, without a division convention for formal series. -/
theorem ordinarySeries_carryH (m r : ℕ) (hm : 2≤m) :
    ordinarySeries (carryH m r)*(1-PowerSeries.X^(m-1))=
      (geometricSeries*(geometricPolynomial m : PowerSeries ℤ))^r-
        PowerSeries.X^(m-1)*geometricSeries^r := by
  apply PowerSeries.ext
  intro q
  have hleft := (carryHPolynomial_agree m r q hm).mul
    (show AgreeThrough q (1-PowerSeries.X^(m-1)) (1-PowerSeries.X^(m-1)) from fun _ _ => rfl)
  have ha := ((geometric_agree q).mul
    (show AgreeThrough q (geometricPolynomial m : PowerSeries ℤ) (geometricPolynomial m : PowerSeries ℤ) from fun _ _ => rfl)).pow r
  have hb := (show AgreeThrough q (PowerSeries.X^(m-1)) (PowerSeries.X^(m-1)) from fun _ _ => rfl).mul
    ((geometric_agree_bound q ((q+1)*m) (by nlinarith)).pow r)
  have he := congrArg (fun p : Polynomial ℤ => (p : PowerSeries ℤ)) (carryHPolynomial_identity m r q (by omega))
  simp only [Polynomial.coe_mul,Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_X,Polynomial.coe_pow] at he
  rw [←hleft q (le_refl _),he]
  exact (ha.sub hb) q (le_refl _)

/-- The rational generating formula in denominator-cleared form. -/
theorem ordinarySeries_carryH_denominator (m r : ℕ) (hm : 2≤m) :
    ordinarySeries (carryH m r)*(1-PowerSeries.X)^(2*r)*(1-PowerSeries.X^(m-1))=
      (1-PowerSeries.X^m)^r-PowerSeries.X^(m-1)*(1-PowerSeries.X)^r := by
  have hgeo : geometricSeries^r*(1-PowerSeries.X)^r=1 := by
    rw [←mul_pow,geometricSeries_identity,one_pow]
  have hJ := geometricPolynomial_series m
  have he := ordinarySeries_carryH m r hm
  calc
    _ = (ordinarySeries (carryH m r)*(1-PowerSeries.X^(m-1)))*(1-PowerSeries.X)^(2*r) := by ring
    _ = ((geometricSeries*(geometricPolynomial m : PowerSeries ℤ))^r-
      PowerSeries.X^(m-1)*geometricSeries^r)*(1-PowerSeries.X)^(2*r) := by rw [he]
    _ = _ := by
      rw [hJ,show 2*r=r+r by omega,pow_add,sub_mul]
      have hp : (geometricSeries*((1-PowerSeries.X^m)*geometricSeries))^r=
          (1-PowerSeries.X^m)^r*geometricSeries^r*geometricSeries^r := by
        rw [mul_pow,mul_pow]
        ring
      rw [hp]
      calc
        _ = (1-PowerSeries.X^m)^r*(geometricSeries^r*(1-PowerSeries.X)^r)*
              (geometricSeries^r*(1-PowerSeries.X)^r)-
            PowerSeries.X^(m-1)*(geometricSeries^r*(1-PowerSeries.X)^r)*(1-PowerSeries.X)^r := by ring
        _ = _ := by rw [hgeo]; ring

end SumsetRanges
