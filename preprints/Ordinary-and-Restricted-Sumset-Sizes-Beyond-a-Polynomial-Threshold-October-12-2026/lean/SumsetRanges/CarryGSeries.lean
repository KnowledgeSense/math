import SumsetRanges.SeriesAgreement

open Finset
namespace SumsetRanges

theorem geometricPolynomial_identity (m : ℕ) :
    geometricPolynomial m*(1-Polynomial.X)=1-(Polynomial.X : Polynomial ℤ)^m := by
  induction m with
  | zero => simp [geometricPolynomial]
  | succ m ih =>
      have he : geometricPolynomial (m+1)=geometricPolynomial m+Polynomial.X^m := by
        simp [geometricPolynomial,Finset.sum_range_succ]
      rw [he,add_mul,ih,pow_succ]
      ring

theorem geometricSeries_identity :
    geometricSeries*(1-PowerSeries.X)=1 := by
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℤ

theorem geometricPolynomial_series (m : ℕ) :
    (geometricPolynomial m : PowerSeries ℤ)=(1-PowerSeries.X^m)*geometricSeries := by
  have hp := congrArg (fun p : Polynomial ℤ => (p : PowerSeries ℤ)) (geometricPolynomial_identity m)
  simp only [Polynomial.coe_mul,Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_X,Polynomial.coe_pow] at hp
  calc
    _ = (geometricPolynomial m : PowerSeries ℤ)*(geometricSeries*(1-PowerSeries.X)) := by rw [geometricSeries_identity,mul_one]
    _ = ((geometricPolynomial m : PowerSeries ℤ)*(1-PowerSeries.X))*geometricSeries := by ring
    _ = _ := by rw [hp]

/-- The complete ordinary generating series of the actual carry block G. -/
theorem ordinarySeries_carryG (m r : ℕ) (hm : 2≤m) :
    ordinarySeries (carryG m r)=(1-PowerSeries.X^m)^r*geometricSeries^(2*r+1) := by
  rw [carryG_series_geometric m r hm,geometricPolynomial_series]
  calc
    _ = (1-PowerSeries.X^m)^r*(geometricSeries*geometricSeries)^r*geometricSeries := by
      have he : geometricSeries*((1-PowerSeries.X^m)*geometricSeries)=
          (1-PowerSeries.X^m)*(geometricSeries*geometricSeries) := by ring
      rw [he,mul_pow]
      ring
    _ = _ := by rw [←pow_two,←pow_mul,pow_succ,mul_assoc]

/-- The denominator-cleared form of the carry-block identity. -/
theorem ordinarySeries_carryG_denominator (m r : ℕ) (hm : 2≤m) :
    ordinarySeries (carryG m r)*(1-PowerSeries.X)^(2*r+1)=(1-PowerSeries.X^m)^r := by
  rw [ordinarySeries_carryG m r hm,mul_assoc,←mul_pow,geometricSeries_identity,one_pow,mul_one]

end SumsetRanges
